/* eslint-disable @typescript-eslint/no-non-null-assertion */
import { program, Option } from 'commander';
import * as http from 'http';

import { Connection, Commitment, Keypair, PublicKey } from '@solana/web3.js';
import {
	SearcherClient,
	searcherClient,
} from 'jito-ts/dist/sdk/block-engine/searcher';

import { getAssociatedTokenAddress } from '@solana/spl-token';
import {
	BulkAccountLoader,
	DriftClient,
	User,
	initialize,
	EventSubscriber,
	SlotSubscriber,
	convertToNumber,
	QUOTE_PRECISION,
	SpotMarkets,
	BN,
	TokenFaucet,
	DriftClientSubscriptionConfig,
	LogProviderConfig,
	getMarketsAndOraclesForSubscription,
	AuctionSubscriber,
	FastSingleTxSender,
	OracleInfo,
	UserMap,
} from '@drift-labs/sdk';
import { promiseTimeout } from '@drift-labs/sdk/lib/util/promiseTimeout';

import { logger, setLogLevel } from './logger';
import { constants } from './types';
import { FillerBot } from './bots/filler';
import { SpotFillerBot } from './bots/spotFiller';
import { TriggerBot } from './bots/trigger';
import { JitMaker } from './bots/jitMaker';
import { LiquidatorBot } from './bots/liquidator';
import { FloatingPerpMakerBot } from './bots/floatingMaker';
import { Bot } from './types';
import { IFRevenueSettlerBot } from './bots/ifRevenueSettler';
import { UserPnlSettlerBot } from './bots/userPnlSettler';
import { UserIdleFlipperBot } from './bots/userIdleFlipper';
import {
	getOrCreateAssociatedTokenAccount,
	sleepMs,
	TOKEN_FAUCET_PROGRAM_ID,
	getWallet,
	loadKeypair,
	waitForAllSubscribesToFinish,
} from './utils';
import {
	Config,
	configHasBot,
	loadConfigFromFile,
	loadConfigFromOpts,
} from './config';
import { FundingRateUpdaterBot } from './bots/fundingRateUpdater';
import { FillerLiteBot } from './bots/fillerLite';
import { JitProxyClient, JitterSniper } from '@drift-labs/jit-proxy/lib';
import { MakerBidAskTwapCrank } from './bots/makerBidAskTwapCrank';
import { UncrossArbBot } from './bots/uncrossArbBot';

require('dotenv').config();
const commitHash = process.env.COMMIT ?? '';

const stateCommitment: Commitment = 'processed';
const healthCheckPort = process.env.HEALTH_CHECK_PORT || 8888;

program
	.option('-d, --dry-run', 'Dry run, do not send transactions on chain')
	.option(
		'--init-user',
		'calls driftClient.initializeUserAccount if no user account exists'
	)
	.option('--filler', 'Enable filler bot')
	.option('--filler-lite', 'Enable filler lite bot')
	.option('--spot-filler', 'Enable spot filler bot')
	.option('--trigger', 'Enable trigger bot')
	.option('--jit-maker', 'Enable JIT auction maker bot')
	.option('--floating-maker', 'Enable floating maker bot')
	.option('--liquidator', 'Enable liquidator bot')
	.option(
		'--if-revenue-settler',
		'Enable Insurance Fund revenue pool settler bot'
	)
	.option('--funding-rate-updater', 'Enable Funding Rate updater bot')
	.option('--user-pnl-settler', 'Enable User PnL settler bot')
	.option('--user-idle-flipper', 'Flips eligible users to idle')
	.option('--mark-twap-crank', 'Enable bid/ask twap crank bot')

	.option('--cancel-open-orders', 'Cancel open orders on startup')
	.option('--close-open-positions', 'close all open positions')
	.option('--test-liveness', 'Purposefully fail liveness test after 1 minute')
	.option(
		'--force-deposit <number>',
		'Force deposit this amount of USDC to collateral account, the program will end after the deposit transaction is sent'
	)
	.option('--metrics <number>', 'Enable Prometheus metric scraper (deprecated)')
	.addOption(
		new Option(
			'-p, --private-key <string>',
			'private key, supports path to id.json, or list of comma separate numbers'
		).env('KEEPER_PRIVATE_KEY')
	)
	.option('--debug', 'Enable debug logging')
	.option(
		'--run-once',
		'Exit after running bot loops once (only for supported bots)'
	)
	.option(
		'--websocket',
		'Use websocket instead of RPC polling for account updates'
	)
	.option(
		'--disable-auto-derisking',
		'Set to disable auto derisking (primarily used for liquidator to close inherited positions)'
	)
	.option(
		'--subaccount <string>',
		'subaccount(s) to use (comma delimited), specify which subaccountsIDs to load',
		'0'
	)
	.option(
		'--perp-markets <string>',
		'comma delimited list of perp market ID(s) for applicable bots (willing to inherit risk), omit for all',
		''
	)
	.option(
		'--spot-markets <string>',
		'comma delimited list of spot market ID(s) for applicable bots (willing to inherit risk), omit for all',
		''
	)
	.option(
		'--config-file <string>',
		'Config file to load (yaml format), will override any other config options',
		''
	)
	.option(
		'--use-jito',
		'Submit transactions to a Jito relayer if the bot supports it'
	)
	.option(
		'--event-susbcriber',
		'Explicitly intialize an eventSubscriber (RPC heavy'
	)
	.parse();

const opts = program.opts();
let config: Config;
if (opts.configFile) {
	logger.info(`Loading config from ${opts.configFile}`);
	config = loadConfigFromFile(opts.configFile);
} else {
	logger.info(`Loading config from command line options`);
	config = loadConfigFromOpts(opts);
}
logger.info(
	`Bot config:\n${JSON.stringify(
		config,
		(k, v) => {
			if (k === 'keeperPrivateKey') {
				return '*'.repeat(v.length);
			}
			return v;
		},
		2
	)}`
);

// @ts-ignore
const sdkConfig = initialize({ env: config.global.driftEnv });
setLogLevel(config.global.debug ? 'debug' : 'info');

const endpoint = config.global.endpoint!;
const wsEndpoint = config.global.wsEndpoint;
logger.info(`RPC endpoint: ${endpoint}`);
logger.info(`WS endpoint:  ${wsEndpoint}`);
logger.info(`DriftEnv:     ${config.global.driftEnv}`);
logger.info(`Commit:       ${commitHash}`);

const bots: Bot[] = [];
const runBot = async () => {
	logger.info(`Loading wallet keypair`);
	const privateKeyOrFilepath = config.global.keeperPrivateKey;
	if (!privateKeyOrFilepath) {
		throw new Error(
			'Must set environment variable KEEPER_PRIVATE_KEY with the path to a id.json or a list of commma separated numbers'
		);
	}
	const [keypair, wallet] = getWallet(privateKeyOrFilepath);
	const driftPublicKey = new PublicKey(sdkConfig.DRIFT_PROGRAM_ID);

	const connection = new Connection(endpoint, {
		wsEndpoint: wsEndpoint,
		commitment: stateCommitment,
	});

	let bulkAccountLoader: BulkAccountLoader | undefined;
	let lastBulkAccountLoaderSlot: number | undefined;
	let accountSubscription: DriftClientSubscriptionConfig = {
		type: 'websocket',
		resubTimeoutMs: config.global.resubTimeoutMs,
	};
	let logProviderConfig: LogProviderConfig = {
		type: 'websocket',
	};

	if (!config.global.websocket) {
		const bulkAccountLoaderConnection = new Connection(endpoint, {
			wsEndpoint: wsEndpoint,
			commitment: stateCommitment,
			disableRetryOnRateLimit: true,
		});
		bulkAccountLoader = new BulkAccountLoader(
			bulkAccountLoaderConnection,
			stateCommitment,
			config.global.bulkAccountLoaderPollingInterval
		);
		lastBulkAccountLoaderSlot = bulkAccountLoader.mostRecentSlot;
		accountSubscription = {
			type: 'polling',
			accountLoader: bulkAccountLoader,
		};
		logProviderConfig = {
			type: 'polling',
			frequency: config.global.eventSubscriberPollingInterval,
		};
	}

	const opts = {
		commitment: stateCommitment,
		skipPreflight: false,
		preflightCommitment: stateCommitment,
	};
	const sendTxConnection = new Connection(endpoint, {
		wsEndpoint: wsEndpoint,
		commitment: stateCommitment,
		disableRetryOnRateLimit: true,
	});
	const txSender = new FastSingleTxSender({
		connection: sendTxConnection,
		wallet,
		opts,
	});

	/**
	 * Creating and subscribing to the drift client
	 */
	let perpMarketIndexes: number[] | undefined;
	let spotMarketIndexes: number[] | undefined;
	let oracleInfos: OracleInfo[] | undefined;
	if (configHasBot(config, 'fillerLite')) {
		({ perpMarketIndexes, spotMarketIndexes, oracleInfos } =
			getMarketsAndOraclesForSubscription(config.global.driftEnv!));
	}

	const driftClient = new DriftClient({
		connection,
		wallet,
		programID: driftPublicKey,
		opts,
		accountSubscription,
		env: config.global.driftEnv,
		userStats: true,
		perpMarketIndexes,
		spotMarketIndexes,
		oracleInfos,
		activeSubAccountId: config.global.subaccounts![0],
		subAccountIds: config.global.subaccounts ?? [0],
		txSender,
	});

	let eventSubscriber: EventSubscriber | undefined = undefined;
	if (config.global.eventSubscriber) {
		eventSubscriber = new EventSubscriber(connection, driftClient.program, {
			maxTx: 4096,
			maxEventsPerType: 4096,
			orderBy: 'blockchain', // Possible options are 'blockchain' or 'client'
			orderDir: 'desc',
			commitment: stateCommitment,
			logProviderConfig,
		});
	}

	const slotSubscriber = new SlotSubscriber(connection, {});
	const startupTime = Date.now();

	const lamportsBalance = await connection.getBalance(wallet.publicKey);
	logger.info(
		`DriftClient ProgramId: ${driftClient.program.programId.toBase58()}`
	);
	logger.info(`Wallet pubkey: ${wallet.publicKey.toBase58()}`);
	logger.info(` . SOL balance: ${lamportsBalance / 10 ** 9}`);

	try {
		const tokenAccount = await getOrCreateAssociatedTokenAccount(
			connection,
			new PublicKey(constants[config.global.driftEnv!].USDCMint),
			wallet
		);
		const usdcBalance = await connection.getTokenAccountBalance(tokenAccount);
		logger.info(` . USDC balance: ${usdcBalance.value.uiAmount}`);
	} catch (e) {
		logger.info(`Failed to load USDC token account: ${e}`);
	}

	while (!(await driftClient.subscribe())) {
		logger.info('waiting to subscribe to DriftClient');
		await sleepMs(1000);
	}
	const driftUser = driftClient.getUser();
	const subscribePromises = [driftUser.subscribe()];
	if (eventSubscriber !== undefined && !configHasBot(config, 'fillerLite')) {
		subscribePromises.push(eventSubscriber.subscribe());
	}
	await waitForAllSubscribesToFinish(subscribePromises);

	driftClient.eventEmitter.on('error', (e) => {
		logger.info('clearing house error');
		logger.error(e);
	});

	await slotSubscriber.subscribe();

	if (!(await driftClient.getUser().exists())) {
		logger.error(`User for ${wallet.publicKey} does not exist`);
		if (config.global.initUser) {
			logger.info(`Creating User for ${wallet.publicKey}`);
			const [txSig] = await driftClient.initializeUserAccount();
			logger.info(`Initialized user account in transaction: ${txSig}`);
		} else {
			throw new Error("Run with '--init-user' flag to initialize a User");
		}
	}

	logger.info(
		`User PublicKey: ${driftUser.getUserAccountPublicKey().toBase58()}`
	);
	await driftClient.getUser().fetchAccounts();

	printUserAccountStats(driftUser);
	if (config.global.closeOpenPositions) {
		logger.info(`Closing open perp positions`);
		let closedPerps = 0;
		for await (const p of driftUser.getUserAccount().perpPositions) {
			if (p.baseAssetAmount.isZero()) {
				logger.info(`no position on market: ${p.marketIndex}`);
				continue;
			}
			logger.info(`closing position on ${p.marketIndex}`);
			logger.info(` . ${await driftClient.closePosition(p.marketIndex)}`);
			closedPerps++;
		}
		console.log(`Closed ${closedPerps} spot positions`);

		let closedSpots = 0;
		for await (const p of driftUser.getUserAccount().spotPositions) {
			if (p.scaledBalance.isZero()) {
				logger.info(`no position on market: ${p.marketIndex}`);
				continue;
			}
			logger.info(`closing position on ${p.marketIndex}`);
			logger.info(` . ${await driftClient.closePosition(p.marketIndex)}`);
			closedSpots++;
		}
		console.log(`Closed ${closedSpots} spot positions`);
	}

	/**
	 * Look for collateral and force deposit before running if flag is set
	 */
	const freeCollateral = driftUser.getFreeCollateral('Maintenance');
	if (
		freeCollateral.isZero() &&
		configHasBot(config, 'jitMaker') &&
		!config.global.forceDeposit
	) {
		throw new Error(
			`No collateral in account, collateral is required to run JitMakerBot, run with --force-deposit flag to deposit collateral`
		);
	}
	if (config.global.forceDeposit) {
		logger.info(
			`Depositing (${new BN(
				config.global.forceDeposit
			).toString()} USDC to collateral account)`
		);

		if (config.global.forceDeposit < 0) {
			logger.error(`Deposit amount must be greater than 0`);
			throw new Error('Deposit amount must be greater than 0');
		}

		const mint = SpotMarkets[config.global.driftEnv!][0].mint; // TODO: are index 0 always USDC???, support other collaterals
		const ata = await getAssociatedTokenAddress(mint, wallet.publicKey);
		const amount = new BN(config.global.forceDeposit).mul(QUOTE_PRECISION);

		if (config.global.driftEnv === 'devnet') {
			const tokenFaucet = new TokenFaucet(
				connection,
				wallet,
				TOKEN_FAUCET_PROGRAM_ID,
				mint,
				opts
			);
			await tokenFaucet.mintToUser(ata, amount);
		}

		const tx = await driftClient.deposit(
			amount,
			0, // USDC bank
			ata
		);
		logger.info(`Deposit transaction: ${tx}`);
		logger.info(`exiting...run again without --force-deposit flag`);
		return;
	}

	/**
	 * Jito info here
	 */
	let jitoSearcherClient: SearcherClient | undefined;
	let jitoAuthKeypair: Keypair | undefined;
	if (config.global.useJito) {
		const jitoBlockEngineUrl = config.global.jitoBlockEngineUrl;
		const privateKey = config.global.jitoAuthPrivateKey;
		if (!jitoBlockEngineUrl) {
			throw new Error(
				'Must configure or set JITO_BLOCK_ENGINE_URL environment variable '
			);
		}
		if (!privateKey) {
			throw new Error(
				'Must configure or set JITO_AUTH_PRIVATE_KEY environment variable'
			);
		}
		logger.info(`Loading jito keypair`);
		jitoAuthKeypair = loadKeypair(privateKey);
		jitoSearcherClient = searcherClient(jitoBlockEngineUrl, jitoAuthKeypair);
		jitoSearcherClient.onBundleResult(
			(bundle) => {
				logger.info(`JITO bundle result: ${JSON.stringify(bundle)}`);
			},
			(error) => {
				logger.error(`JITO bundle error: ${error}`);
			}
		);
	}

	/*
	 * Start bots depending on flags enabled
	 */
	const userMap = new UserMap(
		driftClient,
		driftClient.userAccountSubscriptionConfig,
		false
	);
	if (configHasBot(config, 'filler')) {
		await userMap.subscribe();
		bots.push(
			new FillerBot(
				slotSubscriber,
				bulkAccountLoader,
				driftClient,
				userMap,
				eventSubscriber,
				{
					rpcEndpoint: endpoint,
					commit: commitHash,
					driftEnv: config.global.driftEnv!,
					driftPid: driftPublicKey.toBase58(),
					walletAuthority: wallet.publicKey.toBase58(),
				},
				config.botConfigs!.filler!,
				jitoSearcherClient,
				jitoAuthKeypair,
				keypair
			)
		);
	}

	if (configHasBot(config, 'fillerLite')) {
		logger.info(`Starting filler lite bot`);
		bots.push(
			new FillerLiteBot(
				slotSubscriber,
				driftClient,
				{
					rpcEndpoint: endpoint,
					commit: commitHash,
					driftEnv: config.global.driftEnv!,
					driftPid: driftPublicKey.toBase58(),
					walletAuthority: wallet.publicKey.toBase58(),
				},
				config.botConfigs!.fillerLite!,
				jitoSearcherClient,
				jitoAuthKeypair,
				keypair
			)
		);
	}

	if (configHasBot(config, 'spotFiller')) {
		await userMap.subscribe();
		bots.push(
			new SpotFillerBot(
				slotSubscriber,
				driftClient,
				userMap,
				{
					rpcEndpoint: endpoint,
					commit: commitHash,
					driftEnv: config.global.driftEnv!,
					driftPid: driftPublicKey.toBase58(),
					walletAuthority: wallet.publicKey.toBase58(),
				},
				config.botConfigs!.spotFiller!,
				eventSubscriber
			)
		);
	}

	if (configHasBot(config, 'trigger')) {
		await userMap.subscribe();
		bots.push(
			new TriggerBot(
				driftClient,
				slotSubscriber,
				userMap,
				{
					rpcEndpoint: endpoint,
					commit: commitHash,
					driftEnv: config.global.driftEnv!,
					driftPid: driftPublicKey.toBase58(),
					walletAuthority: wallet.publicKey.toBase58(),
				},
				config.botConfigs!.trigger!
			)
		);
	}

	if (configHasBot(config, 'jitMaker')) {
		await userMap.subscribe();
		const jitProxyClient = new JitProxyClient({
			driftClient,
			programId: new PublicKey(sdkConfig.JIT_PROXY_PROGRAM_ID!),
		});

		const auctionSubscriber = new AuctionSubscriber({ driftClient });
		await auctionSubscriber.subscribe();

		const jitter = new JitterSniper({
			auctionSubscriber,
			driftClient,
			slotSubscriber,
			jitProxyClient,
		});
		await jitter.subscribe();

		const txSenderConnection = new Connection(endpoint, {
			wsEndpoint: wsEndpoint,
			commitment: stateCommitment,
			disableRetryOnRateLimit: true,
		});
		driftClient.txSender = new FastSingleTxSender({
			connection: txSenderConnection,
			wallet,
		});

		bots.push(
			new JitMaker(
				driftClient,
				jitter,
				userMap,
				config.botConfigs!.jitMaker!,
				config.global.driftEnv!
			)
		);
	}

	if (configHasBot(config, 'markTwapCrank')) {
		await userMap.subscribe();
		bots.push(
			new MakerBidAskTwapCrank(
				driftClient,
				slotSubscriber,
				userMap,
				config.botConfigs!.markTwapCrank!,
				config.global.runOnce ?? false,
				config.botConfigs!.markTwapCrank!.crankIntervalToMarketIndicies
			)
		);
	}

	if (configHasBot(config, 'liquidator')) {
		const startUserMapSubscribe = Date.now();
		logger.info(`subscribing to userMap`);
		await userMap.subscribe();
		logger.info(
			`userMap.subscribe took ${Date.now() - startUserMapSubscribe}ms`
		);
		bots.push(
			new LiquidatorBot(
				driftClient,
				userMap,
				{
					rpcEndpoint: endpoint,
					commit: commitHash,
					driftEnv: config.global.driftEnv!,
					driftPid: driftPublicKey.toBase58(),
					walletAuthority: wallet.publicKey.toBase58(),
				},
				config.botConfigs!.liquidator!,
				config.global.subaccounts![0]
			)
		);
	}

	if (configHasBot(config, 'floatingMaker')) {
		bots.push(
			new FloatingPerpMakerBot(
				driftClient,
				slotSubscriber,
				{
					rpcEndpoint: endpoint,
					commit: commitHash,
					driftEnv: config.global.driftEnv!,
					driftPid: driftPublicKey.toBase58(),
					walletAuthority: wallet.publicKey.toBase58(),
				},
				config.botConfigs!.floatingMaker!
			)
		);
	}

	if (configHasBot(config, 'userPnlSettler')) {
		await userMap.subscribe();
		bots.push(
			new UserPnlSettlerBot(
				driftClient,
				config.botConfigs!.userPnlSettler!,
				userMap
			)
		);
	}

	if (configHasBot(config, 'userIdleFlipper')) {
		await userMap.subscribe();
		bots.push(
			new UserIdleFlipperBot(
				driftClient,
				config.botConfigs!.userIdleFlipper!,
				userMap
			)
		);
	}

	if (configHasBot(config, 'ifRevenueSettler')) {
		bots.push(
			new IFRevenueSettlerBot(driftClient, config.botConfigs!.ifRevenueSettler!)
		);
	}

	if (configHasBot(config, 'fundingRateUpdater')) {
		bots.push(
			new FundingRateUpdaterBot(
				driftClient,
				config.botConfigs!.fundingRateUpdater!
			)
		);
	}

	if (configHasBot(config, 'uncrossArb')) {
		await userMap.subscribe();
		const jitProxyClient = new JitProxyClient({
			driftClient,
			programId: new PublicKey(sdkConfig.JIT_PROXY_PROGRAM_ID!),
		});
		bots.push(
			new UncrossArbBot(
				driftClient,
				jitProxyClient,
				slotSubscriber,
				userMap,
				config.botConfigs!.uncrossArb!,
				config.global.driftEnv!
			)
		);
	}

	logger.info(`initializing bots`);
	await Promise.all(bots.map((bot) => bot.init()));

	logger.info(`starting bots (runOnce: ${config.global.runOnce})`);
	await Promise.all(
		bots.map((bot) => bot.startIntervalLoop(bot.defaultIntervalMs))
	);

	// start http server listening to /health endpoint using http package
	http
		.createServer(async (req, res) => {
			if (req.url === '/health') {
				if (config.global.testLiveness) {
					if (Date.now() > startupTime + 60 * 1000) {
						res.writeHead(500);
						res.end('Testing liveness test fail');
						return;
					}
				}

				if (config.global.websocket) {
					/* @ts-ignore */
					if (!driftClient.connection._rpcWebSocketConnected) {
						logger.error(`Connection rpc websocket disconnected`);
						res.writeHead(500);
						res.end(`Connection rpc websocket disconnected`);
						return;
					}
				}

				if (bulkAccountLoader) {
					// we expect health checks to happen at a rate slower than the BulkAccountLoader's polling frequency
					if (
						lastBulkAccountLoaderSlot &&
						bulkAccountLoader.mostRecentSlot === lastBulkAccountLoaderSlot
					) {
						res.writeHead(502);
						res.end(`bulkAccountLoader.mostRecentSlot is not healthy`);
						logger.error(
							`Health check failed due to stale bulkAccountLoader.mostRecentSlot`
						);
						return;
					}
					lastBulkAccountLoaderSlot = bulkAccountLoader.mostRecentSlot;
				}

				// check all bots if they're live
				for (const bot of bots) {
					const healthCheck = await promiseTimeout(bot.healthCheck(), 1000);
					if (!healthCheck) {
						logger.error(`Health check failed for bot ${bot.name}`);
						res.writeHead(503);
						res.end(`Bot ${bot.name} is not healthy`);
						return;
					}
				}

				// liveness check passed
				res.writeHead(200);
				res.end('OK');
			} else {
				res.writeHead(404);
				res.end('Not found');
			}
		})
		.listen(healthCheckPort);
	logger.info(`Health check server listening on port ${healthCheckPort}`);

	if (config.global.runOnce) {
		process.exit(0);
	}
};

recursiveTryCatch(() => runBot());

async function recursiveTryCatch(f: () => void) {
	try {
		f();
	} catch (e) {
		console.error(e);
		for (const bot of bots) {
			bot.reset();
			await bot.init();
		}
		await sleepMs(15000);
		await recursiveTryCatch(f);
	}
}

function printUserAccountStats(clearingHouseUser: User) {
	const freeCollateral = clearingHouseUser.getFreeCollateral();
	logger.info(
		`User free collateral: $${convertToNumber(
			freeCollateral,
			QUOTE_PRECISION
		)}:`
	);

	logger.info(
		`CHUser unrealized funding PnL: ${convertToNumber(
			clearingHouseUser.getUnrealizedFundingPNL(),
			QUOTE_PRECISION
		)}`
	);
	logger.info(
		`CHUser unrealized PnL:         ${convertToNumber(
			clearingHouseUser.getUnrealizedPNL(),
			QUOTE_PRECISION
		)}`
	);
}
