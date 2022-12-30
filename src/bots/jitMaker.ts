import {
	AccountService,
	Reserve,
	FLASH_LOAN_ID,
} from '@texture-finance/solana-flash-loan-sdk';

import {
	BN,
	isVariant,
	calculateAskPrice,
	calculateBidPrice,
	DriftClient,
	PerpMarketAccount,
	SlotSubscriber,
	PositionDirection,
	OrderType,
	OrderRecord,
	NewUserRecord,
	BASE_PRECISION,
	QUOTE_PRECISION,
	convertToNumber,
	PRICE_PRECISION,
	PerpPosition,
	SpotPosition,
	DLOB,
	DLOBNode,
	UserMap,
	UserStatsMap,
	getOrderSignature,
	MarketType,
} from '@drift-labs/sdk';
import { Mutex, tryAcquire, withTimeout, E_ALREADY_LOCKED } from 'async-mutex';

import {
	TransactionSignature,
	PublicKey,
	Transaction,
	Keypair,
	Connection,
} from '@solana/web3.js';
import { getErrorCode } from '../error';
import { logger } from '../logger';
import { Bot } from '../types';
import { Metrics } from '../metrics';
import fs from 'fs';
import { bs58 } from '@project-serum/anchor/dist/cjs/utils/bytes';
import {
	ASSOCIATED_TOKEN_PROGRAM_ID,
	TOKEN_PROGRAM_ID,
} from '@solana/spl-token';
type Action = {
	baseAssetAmount: BN;
	marketIndex: number;
	direction: PositionDirection;
	price: BN;
	node: DLOBNode;
};

// State enum
enum StateType {
	/** Flat there is no open position */
	NEUTRAL = 'neutral',

	/** Long position on this market */
	LONG = 'long',

	/** Short position on market */
	SHORT = 'short',

	/** Current closing a long position (shorts only) */
	CLOSING_LONG = 'closing-long',

	/** Current closing a short position (long only) */
	CLOSING_SHORT = 'closing-short',
}

type State = {
	stateType: Map<number, StateType>;
	spotMarketPosition: Map<number, SpotPosition>;
	perpMarketPosition: Map<number, PerpPosition>;
};

const dlobMutexError = new Error('dlobMutex timeout');

/**
 *
 * This bot is responsible for placing small trades during an order's JIT auction
 * in order to partially fill orders and collect maker fees. The bot also tracks
 * its position on all available markets in order to limit the size of open positions.
 *
 */
export class JitMakerBot implements Bot {
	public readonly name: string;
	public readonly dryRun: boolean;
	public readonly defaultIntervalMs: number = 1000;

	private clearingHouse: DriftClient;
	private slotSubscriber: SlotSubscriber;
	private dlobMutex = withTimeout(
		new Mutex(),
		this.defaultIntervalMs,
		dlobMutexError
	);
	start: number = new Date().getTime();
	total: number = 0;
	private dlob: DLOB;
	private periodicTaskMutex = new Mutex();
	private userMap: UserMap;
	private userStatsMap: UserStatsMap;
	private orderLastSeenBaseAmount: Map<string, BN> = new Map(); // need some way to trim this down over time

	private intervalIds: Array<NodeJS.Timer> = [];
	private metrics: Metrics | undefined;

	private agentState: State;

	private watchdogTimerMutex = new Mutex();
	private watchdogTimerLastPatTime = Date.now();

	/**
	 * Set true to enforce max position size
	 */
	private RESTRICT_POSITION_SIZE = false;

	/**
	 * if a position's notional value passes this percentage of account
	 * collateral, the position enters a CLOSING_* state.
	 */
	private MAX_POSITION_EXPOSURE = 100000000000000000000;

	/**
	 * The max amount of quote to spend on each order.
	 */
	private MAX_TRADE_SIZE_QUOTE = 100000000000000000000;
	constructor(
		name: string,
		dryRun: boolean,
		clearingHouse: DriftClient,
		slotSubscriber: SlotSubscriber,
		metrics?: Metrics | undefined
	) {
		this.name = name;
		this.dryRun = dryRun;
		this.clearingHouse = clearingHouse;
		this.slotSubscriber = slotSubscriber;
		this.metrics = metrics;
	}

	public async init() {
		logger.info(`${this.name} initing`);
		const initPromises: Array<Promise<any>> = [];
		initPromises.push(this.clearingHouse.subscribe());
		this.userMap = new UserMap(
			this.clearingHouse,
			this.clearingHouse.userAccountSubscriptionConfig
		);
		initPromises.push(this.userMap.fetchAllUsers());

		this.userStatsMap = new UserStatsMap(
			this.clearingHouse,
			this.clearingHouse.userAccountSubscriptionConfig
		);
		initPromises.push(this.userStatsMap.fetchAllUserStats());

		this.dlob = new DLOB();
		initPromises.push(this.dlob.initFromUserMap(this.userMap));

		this.agentState = {
			stateType: new Map<number, StateType>(),
			spotMarketPosition: new Map<number, SpotPosition>(),
			perpMarketPosition: new Map<number, PerpPosition>(),
		};
		initPromises.push(this.updateAgentState());

		await Promise.all(initPromises);
	}

	public async reset() {
		for (const intervalId of this.intervalIds) {
			clearInterval(intervalId);
		}
		this.intervalIds = [];
		if (this.dlob) {
			this.dlob.clear();
			delete this.dlob;
		}
		delete this.userMap;
		delete this.userStatsMap;
	}

	public async startIntervalLoop(intervalMs: number) {
		await this.tryMake();
		const intervalId = setInterval(this.tryMake.bind(this), intervalMs);
		this.intervalIds.push(intervalId);

		logger.info(`${this.name} Bot started!`);
	}

	public async healthCheck(): Promise<boolean> {
		let healthy = false;
		await this.watchdogTimerMutex.runExclusive(async () => {
			healthy =
				this.watchdogTimerLastPatTime > Date.now() - 2 * this.defaultIntervalMs;
		});
		return healthy;
	}

	public async trigger(record: any): Promise<void> {
		if (record.eventType === 'OrderRecord') {
			try {
				await this.userMap.updateWithOrderRecord(record as OrderRecord);
				await this.userStatsMap.updateWithOrderRecord(
					record as OrderRecord,
					this.userMap
				);
				await this.tryMake();
			} catch {
				console.log(1);
				await this.tryMake();
			}
		} else if (record.eventType === 'NewUserRecord') {
			await this.userMap.mustGet((record as NewUserRecord).user.toString());
			await this.userStatsMap.mustGet(
				(record as NewUserRecord).user.toString()
			);
		}
	}

	public viewDlob(): DLOB {
		return this.dlob;
	}

	/**
	 * This function creates a distribution of the values in array based on the
	 * weights array. The returned array should be used in randomIndex to make
	 * a random draw from the distribution.
	 *
	 */
	private createDistribution(
		array: Array<any>,
		weights: Array<number>,
		size: number
	): Array<number> {
		const distribution = [];
		const sum = weights.reduce((a: number, b: number) => a + b);
		const quant = size / sum;
		for (let i = 0; i < array.length; ++i) {
			const limit = quant * weights[i];
			for (let j = 0; j < limit; ++j) {
				distribution.push(i);
			}
		}
		return distribution;
	}

	/**
	 * Make a random choice from distribution
	 * @param distribution array of values that can be drawn from
	 * @returns
	 */
	private randomIndex(distribution: Array<number>): number {
		const index = Math.floor(distribution.length * Math.random()); // random index
		return distribution[index];
	}

	/**
	 * Generates a random number between [min, max]
	 * @param min minimum value to generate random number from
	 * @param max maximum value to generate random number from
	 * @returns the random number
	 */
	private randomIntFromInterval(min: number, max: number): number {
		return Math.floor(Math.random() * (max - min + 1) + min);
	}

	/**
	 * Updates the agent state based on its current market positions.
	 *
	 * Our goal is to participate in JIT auctions while limiting the delta
	 * exposure of the bot.
	 *
	 * We achieve this by allowing deltas to increase until MAX_POSITION_EXPOSURE
	 * is hit, after which orders will only reduce risk until the position is
	 * closed.
	 *
	 * @returns {Promise<void>}
	 */
	private async updateAgentState(): Promise<void> {
		// TODO: SPOT
		for await (const p of this.clearingHouse.getUserAccount().perpPositions) {
			if (p.baseAssetAmount.isZero()) {
				continue;
			}

			// update current position based on market position
			this.agentState.perpMarketPosition.set(p.marketIndex, p);

			// update state
			let currentState = this.agentState.stateType.get(p.marketIndex);
			if (!currentState) {
				this.agentState.stateType.set(p.marketIndex, StateType.NEUTRAL);
				currentState = StateType.NEUTRAL;
			}

			let canUpdateStateBasedOnPosition = true;
			if (
				(currentState === StateType.CLOSING_LONG &&
					p.baseAssetAmount.gt(new BN(0))) ||
				(currentState === StateType.CLOSING_SHORT &&
					p.baseAssetAmount.lt(new BN(0)))
			) {
				canUpdateStateBasedOnPosition = false;
			}

			if (canUpdateStateBasedOnPosition) {
				// check if need to enter a closing state
				const accountCollateral = convertToNumber(
					this.clearingHouse.getUser().getTotalCollateral(),
					QUOTE_PRECISION
				);
				const positionValue = convertToNumber(
					p.quoteAssetAmount,
					QUOTE_PRECISION
				);
				const exposure = positionValue / accountCollateral;

				if (exposure >= this.MAX_POSITION_EXPOSURE) {
					// state becomes closing only
					if (p.baseAssetAmount.gt(new BN(0))) {
						this.agentState.stateType.set(
							p.marketIndex,
							StateType.CLOSING_LONG
						);
					} else {
						this.agentState.stateType.set(
							p.marketIndex,
							StateType.CLOSING_SHORT
						);
					}
				} else {
					// update state to be whatever our current position is
					if (p.baseAssetAmount.gt(new BN(0))) {
						this.agentState.stateType.set(p.marketIndex, StateType.LONG);
					} else if (p.baseAssetAmount.lt(new BN(0))) {
						this.agentState.stateType.set(p.marketIndex, StateType.SHORT);
					} else {
						this.agentState.stateType.set(p.marketIndex, StateType.NEUTRAL);
					}
				}
			}
		}
	}

	private nodeCanBeFilled(
		node: DLOBNode,
		userAccountPublicKey: PublicKey
	): boolean {
		if (node.haveFilled) {
			logger.error(
				`already made the JIT auction for ${node.userAccount} - ${node.order.orderId}`
			);
			return false;
		}

		// jitter can't fill its own orders
		if (node.userAccount.equals(userAccountPublicKey)) {
			return false;
		}

		const orderSignature = getOrderSignature(
			node.order.orderId,
			node.userAccount
		);
		const lastBaseAmountFilledSeen =
			this.orderLastSeenBaseAmount.get(orderSignature);
		if (lastBaseAmountFilledSeen?.eq(node.order.baseAssetAmountFilled)) {
			return false;
		}

		return true;
	}

	/**
	 *
	 */
	private determineJitAuctionBaseFillAmount(
		orderBaseAmountAvailable: BN,
		orderPrice: BN
	): BN {
		const priceNumber = convertToNumber(orderPrice, PRICE_PRECISION);
		const worstCaseQuoteSpend = orderBaseAmountAvailable
			.mul(orderPrice)
			.div(BASE_PRECISION.mul(PRICE_PRECISION))
			.mul(QUOTE_PRECISION);

		const minOrderQuote = 20;
		let orderQuote = minOrderQuote;
		let maxOrderQuote = convertToNumber(worstCaseQuoteSpend, QUOTE_PRECISION);

		if (maxOrderQuote > this.MAX_TRADE_SIZE_QUOTE) {
			maxOrderQuote = this.MAX_TRADE_SIZE_QUOTE;
		}

		if (maxOrderQuote >= minOrderQuote) {
			orderQuote = this.randomIntFromInterval(minOrderQuote, maxOrderQuote);
		}

		const baseFillAmountNumber = orderQuote / priceNumber;
		let baseFillAmountBN = new BN(
			baseFillAmountNumber * BASE_PRECISION.toNumber()
		);
		if (baseFillAmountBN.gt(orderBaseAmountAvailable)) {
			baseFillAmountBN = orderBaseAmountAvailable;
		}
		logger.info(
			`jitMaker will fill base amount: ${convertToNumber(
				baseFillAmountBN,
				BASE_PRECISION
			).toString()} of remaining order ${convertToNumber(
				orderBaseAmountAvailable,
				BASE_PRECISION
			)}.`
		);

		return baseFillAmountBN;
	}

	/**
	 * Draws an action based on the current state of the bot.
	 *
	 */
	async drawAndExecuteAction(market: PerpMarketAccount) {
		const sleep = (ms) => new Promise((resolve) => setTimeout(resolve, ms));
		this.clearingHouse.connection = new Connection(
			process.env.ALT_RPC_LIST.split(',')[
				Math.floor(Math.random() * process.env.ALT_RPC_LIST.split(',').length)
			]
		);
		// get nodes available to fill in the jit auction
		const nodesToFill = this.dlob.findJitAuctionNodesToFill(
			market.marketIndex,
			this.slotSubscriber.getSlot(),
			MarketType.PERP
		);

		for (const nodeToFill of nodesToFill) {
			if (
				!this.nodeCanBeFilled(
					nodeToFill.node,
					await this.clearingHouse.getUserAccountPublicKey()
				)
			) {
				continue;
			}

			logger.info(
				`node slot: ${
					nodeToFill.node.order.slot
				}, cur slot: ${await this.slotSubscriber.getSlot()}`
			);
			this.orderLastSeenBaseAmount.set(
				getOrderSignature(
					nodeToFill.node.order.orderId,
					nodeToFill.node.userAccount
				),
				nodeToFill.node.order.baseAssetAmountFilled
			);

			logger.info(
				`${
					this.name
				} quoting order for node: ${nodeToFill.node.userAccount.toBase58()} - ${nodeToFill.node.order.orderId.toString()}, orderBaseFilled: ${convertToNumber(
					nodeToFill.node.order.baseAssetAmountFilled,
					BASE_PRECISION
				)}/${convertToNumber(
					nodeToFill.node.order.baseAssetAmount,
					BASE_PRECISION
				)}`
			);

			// calculate jit maker order params
			const orderMarketIdx = nodeToFill.node.order.marketIndex;
			const orderDirection = nodeToFill.node.order.direction;
			const jitMakerDirection = isVariant(orderDirection, 'long')
				? PositionDirection.SHORT
				: PositionDirection.LONG;

			const oracle =
				this.clearingHouse.getOracleDataForPerpMarket(orderMarketIdx);
			const vAsk = calculateAskPrice(market, oracle);
			const vBid = calculateBidPrice(market, oracle);

			let jitMakerPrice =
				jitMakerDirection == PositionDirection.SHORT
					? new BN(vAsk.toNumber() + (vAsk.toNumber() - vBid.toNumber()) * 4)
					: new BN(vBid.toNumber() - (vAsk.toNumber() - vBid.toNumber()) * 4); //nodeToFill.node.order.auctionStartPrice;

			console.log(vAsk.toNumber());
			console.log(vBid.toNumber());
			console.log(jitMakerPrice.toNumber());
			let jitMakerBaseAssetAmount = this.determineJitAuctionBaseFillAmount(
				nodeToFill.node.order.baseAssetAmount.sub(
					nodeToFill.node.order.baseAssetAmountFilled
				),
				jitMakerPrice
			);
			console.log(jitMakerBaseAssetAmount.toNumber());
			console.log(jitMakerBaseAssetAmount.toNumber());
			console.log(jitMakerBaseAssetAmount.toNumber());
			console.log(jitMakerBaseAssetAmount.toNumber());

			let orderSlot = nodeToFill.node.order.slot.toNumber();
			let currSlot = await this.slotSubscriber.getSlot();
			let aucDur = nodeToFill.node.order.auctionDuration;
			let aucEnd = orderSlot + aucDur;
			let diff = (currSlot - orderSlot) / aucDur;

			logger.info(currSlot - orderSlot);
			console.log(diff);
			if (diff < -0.9) {
				nodeToFill.node.haveFilled = false;

				//return await this.drawAndExecuteAction(market)
			} else {
				logger.info(
					`${
						this.name
					} propose to fill jit auction on market ${orderMarketIdx}: ${JSON.stringify(
						jitMakerDirection
					)}: ${convertToNumber(
						jitMakerBaseAssetAmount,
						BASE_PRECISION
					).toFixed(4)}, limit price: ${convertToNumber(
						jitMakerPrice,
						PRICE_PRECISION
					).toFixed(4)}, it has been ${
						currSlot - orderSlot
					} slots since order, auction ends in ${aucEnd - currSlot} slots`
				);

				try {
					const txSig = await this.executeAction({
						baseAssetAmount: jitMakerBaseAssetAmount,
						marketIndex: nodeToFill.node.order.marketIndex,
						direction: jitMakerDirection,
						price: jitMakerPrice,
						node: nodeToFill.node,
					});

					this.metrics?.recordFilledOrder(
						this.clearingHouse.provider.wallet.publicKey,
						this.name
					);
					logger.info(
						`${
							this.name
						}: JIT auction filled (account: ${nodeToFill.node.userAccount.toString()} - ${nodeToFill.node.order.orderId.toString()}), Tx: ${txSig}`
					);
					return txSig;
				} catch (error) {
					console.log(error);
					nodeToFill.node.haveFilled = false;

					// If we get an error that order does not exist, assume its been filled by somebody else and we
					// have received the history record yet
					// TODO this might not hold if events arrive out of order
					const errorCode = getErrorCode(error);
					this.metrics?.recordErrorCode(
						errorCode,
						this.clearingHouse.provider.wallet.publicKey,
						this.name
					);

					logger.error(
						`Error (${errorCode}) filling JIT auction (account: ${nodeToFill.node.userAccount.toString()} - ${nodeToFill.node.order.orderId.toString()})`
					);

					/* todo remove this, fix error handling
				if (errorCode === 6042) {
					this.dlob.remove(
						nodeToFill.node.order,
						nodeToFill.node.userAccount,
						() => {
							logger.error(
								`Order ${nodeToFill.node.order.orderId.toString()} not found when trying to fill. Removing from order list`
							);
						}
					);
				}
				*/

					// console.error(error);
				}
			}
		}
	}

	private async executeAction(action: Action): Promise<TransactionSignature> {
		const currentState = this.agentState.stateType.get(action.marketIndex);

		const takerUserAccount = (
			await this.userMap.mustGet(action.node.userAccount.toString())
		).getUserAccount();
		const takerAuthority = takerUserAccount.authority;

		const takerUserStats = await this.userStatsMap.mustGet(
			takerAuthority.toString()
		);
		const takerUserStatsPublicKey = takerUserStats.userStatsAccountPublicKey;
		const referrerInfo = takerUserStats.getReferrerInfo();
		// total: 6548.327280202056 60.205416666666665 mins
		let borrowing =
			action.baseAssetAmount.toNumber() > 0
				? convertToNumber(action.baseAssetAmount, BASE_PRECISION) *
				  convertToNumber(action.price, PRICE_PRECISION) *
				  10 ** 6
				: -1 *
				  convertToNumber(action.baseAssetAmount, BASE_PRECISION) *
				  convertToNumber(action.price, PRICE_PRECISION) *
				  10 ** 6;
		if (borrowing < 0) {
			borrowing = borrowing * -1;
		}
		console.log(Math.ceil(borrowing));
		console.log(Math.ceil(borrowing));
		console.log(Math.ceil(borrowing));
		console.log(Math.ceil(borrowing));
		this.total += borrowing / 10 ** 6;
		console.log(
			'total: ' +
				this.total.toString() +
				' ' +
				((new Date().getTime() - this.start) / 1000 / 60).toString() +
				' mins'
		);
		const me = Keypair.fromSecretKey(
			new Uint8Array(JSON.parse('[' + process.env.KEEPER_PRIVATE_KEY + ']'))
		);
		console.log(action.baseAssetAmount.toNumber());
		console.log(action.baseAssetAmount.toNumber());
		console.log(action.baseAssetAmount.toNumber());
		console.log(action.baseAssetAmount.toNumber());
		//		const accountService = new AccountService(this.clearingHouse.connection);
		// reserve =await accountService.getReserveInfo(new PublicKey("8qow5YNnT9NfvxVsxYMiKV4ddggT5gEe3uLUvjQ6uYaZ"))
		let twofiddy = parseFloat(
			(
				await this.clearingHouse.connection.getTokenAccountBalance(
					new PublicKey('Ho9gUv6Y5KKZzxat5pbnf2skppcVpniss6zrabhWwi1n')
				)
			).value.amount
		);
		//let twofiddy = 198 * 10 ** 6
		if (borrowing >= twofiddy) {
			let diff = borrowing / twofiddy;
			console.log(diff);
			let hmm = new BN(Math.floor(action.baseAssetAmount.toNumber() / diff));
			action.baseAssetAmount = this.determineJitAuctionBaseFillAmount(
				hmm,
				action.price
			);
			borrowing = twofiddy;
		} /*
		const [token] = PublicKey.findProgramAddressSync(
            [me.publicKey.toBuffer(), TOKEN_PROGRAM_ID.toBuffer(), (new PublicKey("EPjFWdd5AufqSSqeM2qN1xzybapC8G4wEGGkZwyTDt1v")).toBuffer()],
            ASSOCIATED_TOKEN_PROGRAM_ID
        );*/

		if (borrowing <= twofiddy && borrowing >= 10 * 10 ** 6) {
			let jaregm = new PublicKey(
				'HDuQnmkrezSY5FcPaERXA7pfnHSXDBYr5qMHd8CrwVRx'
			);
			console.log(action.price.toNumber());
			try {
				return '';
				/*
				await this.clearingHouse.txSender.send(
					new Transaction()
						// this probably works
						// and now; magik
						.add(
							flashBorrowReserveLiquidityInstruction(
								Math.ceil(borrowing),
								new PublicKey(reserve.config.liquidityAddress),
								new PublicKey('dNwoCR9f1cbk52ansXiR18sxJgr5JFcA1bPYa7Gjsj7'),
								new PublicKey(reserve.config.address),
								new PublicKey(this.market.config.address),
								SOLEND_PRODUCTION_PROGRAM_ID
							)
						
						//reserve.flashBorrow(BigInt(Math.ceil( borrowing)), token),
						)
						
						.add(
							await this.clearingHouse.getDepositInstruction(
								new BN(Math.ceil(borrowing)),
								action.marketIndex,
								new PublicKey('dNwoCR9f1cbk52ansXiR18sxJgr5JFcA1bPYa7Gjsj7')
							)
						)
						.add(
							await this.clearingHouse.getPlaceAndMakePerpOrderIx(
								{
									orderType: OrderType.LIMIT,
									marketIndex: action.marketIndex,
									baseAssetAmount: action.baseAssetAmount,
									direction: action.direction,
									price: action.price,
									postOnly: true,
									immediateOrCancel: true,
								},
								{
									taker: action.node.userAccount,
									order: action.node.order,
									takerStats: takerUserStatsPublicKey,
									takerUserAccount: takerUserAccount,
								},
								referrerInfo
							)
						)
						.add(
							await this.clearingHouse.getWithdrawIx(
								new BN(Math.ceil(borrowing) * 1.00000005),
								action.marketIndex,
								new PublicKey('dNwoCR9f1cbk52ansXiR18sxJgr5JFcA1bPYa7Gjsj7')
							)
						)
						.add(
							flashRepayReserveLiquidityInstruction(
								Math.ceil(borrowing),
								0,
								new PublicKey('dNwoCR9f1cbk52ansXiR18sxJgr5JFcA1bPYa7Gjsj7'),
								new PublicKey(reserve.config.liquidityAddress),
								new PublicKey(reserve.config.liquidityAddress), //liquidityFeeReceiverAddress),
								new PublicKey('dNwoCR9f1cbk52ansXiR18sxJgr5JFcA1bPYa7Gjsj7'),
								new PublicKey(reserve.config.address),
								new PublicKey(this.market.config.address),
								me.publicKey,
								SOLEND_PRODUCTION_PROGRAM_ID,
								jaregm,
								new PublicKey(reserve.config.liquidityToken.mint)
							)
							//reserve.flashRepay(BigInt(Math.ceil(borrowing)), token, me.publicKey),

						),
					[me]
				)
				 
				
			).txSig;
			*/
			} catch (err) {
				this.reset();
				this.startIntervalLoop(1000);
			}
		}
		return '';
	}

	private async tryMakeJitAuctionForMarket(market: PerpMarketAccount) {
		await this.updateAgentState();

		// get nodes available to fill in the jit auction
		const nodesToFill = this.dlob.findJitAuctionNodesToFill(
			market.marketIndex,
			await this.slotSubscriber.getSlot(),
			MarketType.PERP
		);
		let bad = false;
		let currSlot = await this.slotSubscriber.getSlot();
		for (const nodeToFill of nodesToFill) {
			let orderSlot = nodeToFill.node.order.slot.toNumber();
			let aucDur = nodeToFill.node.order.auctionDuration;
			let aucEnd = orderSlot + aucDur;
			let diff = (currSlot - orderSlot) / aucDur;
			console.log;
			if (diff > -0.9) {
			} else {
				bad = true;
			}
		}
		if (!bad) {
			await this.drawAndExecuteAction(market);
			//	await this.updateAgentState();
			//			await this.tryMakeJitAuctionForMarket(market)
		} else {
			//	await this.updateAgentState();
			//		await this.tryMakeJitAuctionForMarket(market)
		}
	}

	private async tryMake() {
		const start = Date.now();
		let ran = false;
		try {
			await tryAcquire(this.periodicTaskMutex).runExclusive(async () => {
				await this.dlobMutex.runExclusive(async () => {
					if (this.dlob) {
						this.dlob.clear();
						delete this.dlob;
					}
					this.dlob = new DLOB();
					/*
					const initPromises: Array<Promise<any>> = [];

					for (const user of this.userMap.values() ){
						initPromises.push((user.subscribe()))
					}
					await Promise.all(initPromises); */
					await this.dlob.initFromUserMap(this.userMap);
				});

				await Promise.all(
					// TODO: spot
					this.clearingHouse.getPerpMarketAccounts().map((marketAccount) => {
						this.tryMakeJitAuctionForMarket(marketAccount);
					})
				);

				ran = true;
			});
		} catch (e) {
			if (e === E_ALREADY_LOCKED) {
				this.metrics?.recordMutexBusy(this.name);
			} else if (e === dlobMutexError) {
				logger.error(`${this.name} dlobMutexError timeout`);
			} else {
				throw e;
			}
		} finally {
			if (ran) {
				const duration = Date.now() - start;
				this.metrics?.recordRpcDuration(
					this.clearingHouse.connection.rpcEndpoint,
					'tryMake',
					duration,
					false,
					this.name
				);
				logger.debug(`${this.name} Bot took ${Date.now() - start}ms to run`);
				await this.watchdogTimerMutex.runExclusive(async () => {
					this.watchdogTimerLastPatTime = Date.now();
				});
			}
		}
	}
}
