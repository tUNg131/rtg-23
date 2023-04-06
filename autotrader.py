import asyncio
import itertools
import math
import copy
import sys
import collections
import time

from typing import List, Dict, Any
from queue import Empty

from ready_trader_go import BaseAutoTrader, Instrument, Lifespan, Side
from ready_trader_go.messages import MessageType, HEDGE_FILLED_MESSAGE_SIZE

TICK_SIZE_IN_CENTS = 100
PRICE_MAX = 99999999

MESSAGE_FREQUENCY_LIMIT = 47
TARGET_FREQUENCY = 30

UNHEDGED_DURATION_LIMIT = 30.0
FAST_HEDGE_PERIOD = 0.5
UNHEDGED_VOLUME_LIMIT = 10
FORCED_HEDGE_WIDTH = 200
FAST_HEDGE_WIDTH = 200

POSITION_LIMIT = 100
ACTIVE_ORDER_LIMIT = 10

M0 = 1
M1 = 3

W1 = 200
W0 = 100

MIN_VOLUME = 15

IOC_VOLUME = 25
GFD_VOLUME = POSITION_LIMIT - IOC_VOLUME

HEDGE_WIDTH_LIMIT = 200
HEDGE_VOLUME_LIMIT = 6
HEDGE_FRACTION = 0.2

FIRST_PRIORITY = 0
SECOND_PRIORITY = 1
THIRD_PRIORITY = 2
FOURTH_PRIORITY = 3


def floor(price):
    return int(math.floor(price / TICK_SIZE_IN_CENTS)) * TICK_SIZE_IN_CENTS


def ceil(price):
    return int(math.ceil(price / TICK_SIZE_IN_CENTS)) * TICK_SIZE_IN_CENTS


class FrequencyLimitError(Exception):
    def __init__(self, timeout, *args: object) -> None:
        super().__init__(*args)
        self.timeout = timeout


class FrequencyLimiter:
    def __init__(self, limit, target, loop, logger, interval=1.0):
        self.limit = limit
        self.target = target
        self.loop = loop
        self.logger = logger
        self.interval = interval

        self.event_count = 0
        self.events = collections.deque()
        self.missing_events = collections.deque()

    def get_permission(self, limit=None):
        limit = limit if limit else self.limit
        now = self.loop.time()
        epsilon = sys.float_info.epsilon
        window_start = now - self.interval
        events = self.events

        while events and (events[0] - window_start) <= ((events[0] if events[0] > window_start else window_start) * epsilon):
            events.popleft()
            self.event_count -= 1

        # print(f"\r{self.event_count + 1}", end=" ")
        # print(f"{self.event_count + 1}")
        if self.event_count + 1 > limit:
            timeout = 0
            if events:
                timeout = events[-min(len(events), self.target)] - window_start
            raise FrequencyLimitError(timeout)

    def hedge_sent(self):
        self.event_count += 1

    def event_sent(self, id, typ):
        self.event_count += 1
        self.missing_events.append((id, typ))

    def hedge_received(self, now):
        self.events.append(now)

    def event_received(self, now, *args):
        id, typ = self.get_event_key(*args)

        try:
            self.missing_events.remove((id, typ))
        except ValueError:
            return
        self.events.append(now)

        if typ == "C":
            while True:
                # Remove all amend actions
                try:
                    self.missing_events.remove((id, "A"))
                except ValueError:
                    return
                self.events.append(now)

    def fill_received(self, now, id):
        try:
            self.missing_events.remove((id, "L"))
        except ValueError:
            return
        self.events.append(now)

    def get_event_key(self, order, fill_volume, remaining_volume, fees):
        if order.lifespan == Lifespan.IMMEDIATE_OR_CANCEL:
            return (order.id, "I")
        elif remaining_volume == 0 and not order.is_active:
            return (order.id, "C")
        elif remaining_volume != order.max_remaining_volume and order.is_active:
            return (order.id, "A")
        return (order.id, "L")


class OrderBook:
    def __init__(self):
        self.ask_prices = []
        self.ask_volumes = []
        self.bid_prices = []
        self.bid_volumes = []

        self.ticks = []

    def update(self, ask_prices, ask_volumes, bid_prices, bid_volumes):
        self.ask_prices = ask_prices
        self.ask_volumes = ask_volumes
        self.bid_prices = bid_prices
        self.bid_volumes = bid_volumes

    def tick(self, ask_prices, ask_volumes, bid_prices, bid_volumes):
        self.ticks.append((
            ask_prices,
            ask_volumes,
            bid_prices,
            bid_volumes
        ))


class FutureOrderBook(OrderBook):
    def __init__(self):
        super().__init__()

        self.prices = []

    def update(self, ask_prices, ask_volumes, bid_prices, bid_volumes):
        super().update(ask_prices, ask_volumes, bid_prices, bid_volumes)

        if ask_prices[0] == 0 or bid_prices[0] == 0:
            return

        av = math.sqrt(ask_volumes[0])
        bv = math.sqrt(bid_volumes[0])
        fut_price = (av * ask_prices[0] + bv * bid_prices[0]) / (av + bv)

        self.prices = [fut_price]

    def tick(self, ask_prices, ask_volumes, bid_prices, bid_volumes):
        super().tick(ask_prices, ask_volumes, bid_prices, bid_volumes)

        if ask_prices[0] == 0 or bid_prices[0] == 0:
            if ask_prices[0] != 0:
                self.prices.append(ask_prices[0])
            elif bid_prices[0] != 0:
                self.prices.append(bid_prices[0])
        else:
            if ask_prices[0] == bid_prices[0]:
                self.prices.append(ask_prices[0])
            elif ask_volumes[0] >= bid_volumes[0]:
                self.prices.append(ask_prices[0])
            else:
                self.prices.append(bid_prices[0])

    @property
    def price_est(self):
        if self.prices:
            return self.prices[-1]
        raise Empty


class ETFOrderBook(OrderBook):
    def __init__(self):
        super().__init__()

        self._best_ask = self._best_bid = 0

    def update(self, ask_prices, ask_volumes, bid_prices, bid_volumes):
        super().update(ask_prices, ask_volumes, bid_prices, bid_volumes)

        self._best_ask = ask_prices[0]
        self._best_bid = bid_prices[0]

    def tick(self, ask_prices, ask_volumes, bid_prices, bid_volumes):
        super().tick(ask_prices, ask_volumes, bid_prices, bid_volumes)

        if ask_prices[0] != 0 and bid_prices[0] != 0:
            self._best_ask = ask_prices[0]
            self._best_bid = bid_prices[0]

        if ask_prices[0] != 0:
            self._best_ask = self._best_bid = ask_prices[0]
        elif bid_prices[0] != 0:
            self._best_ask = self._best_bid = bid_prices[0]

    @property
    def best_ask(self):
        if self._best_ask != 0:
            return self._best_ask
        return PRICE_MAX

    @property
    def best_bid(self):
        if self._best_bid != 0:
            return self._best_bid
        return 0


class BaseOrder:
    order_ids = itertools.count(1)

    def __init__(self, side=Side.ASK, price=0, volume=0):
        self.side = side
        self.price = price
        self.fill_volume = 0
        self.remaining_volume = volume
        self._id = 0

    @property
    def id(self):
        return self._id

    def create(self):
        self._id = next(BaseOrder.order_ids)
        return self.get_insert_args()

    def get_insert_args(self):
        pass


class HedgeOrder(BaseOrder):
    def get_insert_args(self):
        return (self._id, self.side, self.price, self.remaining_volume)


class Order(BaseOrder):
    def __init__(self, lifespan=Lifespan.LIMIT_ORDER, *args, **kwargs):
        super().__init__(*args, **kwargs)
        self.amend_amount = 0
        self.lifespan = lifespan
        self.is_active = lifespan == Lifespan.LIMIT_ORDER

    def create(self):
        self._id = next(BaseOrder.order_ids)
        return self.get_insert_args()

    @property
    def max_remaining_volume(self):
        return self.remaining_volume + self.amend_amount

    def get_insert_args(self):
        return (self._id, self.side, self.price, self.remaining_volume, self.lifespan)

    def is_cross_with(self, order):
        if self.side != order.side:
            if order.side == Side.BID and self.price <= order.price:
                return True
            if order.side == Side.ASK and self.price >= order.price:
                return True
        return False

    def __repr__(self) -> str:
        side = "A" if self.side == Side.ASK else "B"
        lifespan = "IOC" if self.lifespan == Lifespan.IMMEDIATE_OR_CANCEL else "LIM"
        return f"{side}[{self.id}] {self.remaining_volume}|{self.fill_volume + self.remaining_volume}|{self.amend_amount} {self.price} {lifespan}"


class Operation:
    def __init__(self, target, args=(), kwargs={}):
        self.target = target
        self.args = args() if callable(args) else args
        self.kwargs = kwargs() if callable(kwargs) else kwargs

    def run(self):
        if callable(self.target):
            self.target(*self.args, **self.kwargs)

    def __repr__(self) -> str:
        return f"{self.target.__name__} {self.args} {self.kwargs}"

    def __call__(self, *args: Any, **kwds: Any) -> Any:
        return self.run()


class Execution(Operation):
    def __init__(self, target, args=(), priority=0, ev=0, kwargs={}):
        super().__init__(target, args, kwargs)
        self.priority = priority
        self.ev = ev

    # TODO: total_ordering


class Update(Operation):
    pass


def get_string(ask_prices, ask_volumes, bid_prices, bid_volumes):
    price_volumes = []
    for p, v in zip(reversed(bid_prices), reversed(bid_volumes)):
        price_volumes.append(f"{p // TICK_SIZE_IN_CENTS}|{v}")
    for p, v in zip(ask_prices, ask_volumes):
        price_volumes.append(f"{p // TICK_SIZE_IN_CENTS}|{v}")
    return " ".join(price_volumes)


class AutoTrader(BaseAutoTrader):
    def __init__(self, loop: asyncio.AbstractEventLoop, team_name: str, secret: str):
        """Initialise a new instance of the AutoTrader class."""
        super().__init__(loop, team_name, secret)

        self.fut_orderbook = FutureOrderBook()
        self.etf_orderbook = ETFOrderBook()

        self._fut_position = 0
        self._etf_position = 0

        self.orders: Dict[int, Order] = {}

        self.future_bid_id = 0
        self.future_ask_id = 0
        self.max_fut_position = 0
        self.min_fut_position = 0

        self.ticks = 1

        self.operation_count = 0

        self.frequency_limiter = FrequencyLimiter(
            limit=MESSAGE_FREQUENCY_LIMIT,
            target=TARGET_FREQUENCY,
            loop=self.event_loop,
            logger=self.logger)

        self.executions = []
        self.execute_handle = None

        self.hedge_orders: Dict[int, HedgeOrder] = {}
        self.last_hedged_event = None
        # self.fast_hedge_handle = self.event_loop.call_later(
        #     FAST_HEDGE_PERIOD, self.fast_hedge)
        self.forced_hedge_handle = self.event_loop.call_later(
            UNHEDGED_DURATION_LIMIT, self.forced_hedge)

    @property
    def fut_position(self):
        return self._fut_position

    @property
    def etf_position(self):
        return self._etf_position

    @etf_position.setter
    def etf_position(self, value):
        if abs(self._etf_position + self._fut_position) > UNHEDGED_VOLUME_LIMIT:
            if (self._fut_position + value) <= UNHEDGED_VOLUME_LIMIT:
                self.last_hedged_event = self.event_loop.time()
        self._etf_position = value

    @fut_position.setter
    def fut_position(self, value):
        if abs(self._etf_position + self._fut_position) > UNHEDGED_VOLUME_LIMIT:
            if (self._etf_position + value) <= UNHEDGED_VOLUME_LIMIT:
                self.last_hedged_event = self.event_loop.time()
        self._fut_position = value


    @property
    def active_order_count(self):
        return sum(1 for o in self.orders.values() if o.is_active)

    @property
    def active_ask_volume(self):
        volume = 0
        for order in self.orders.values():
            if order.is_active and order.side == Side.ASK:
                volume += order.max_remaining_volume
        return volume

    @property
    def active_bid_volume(self):
        volume = 0
        for order in self.orders.values():
            if order.is_active and order.side == Side.BID:
                volume += order.max_remaining_volume
        return volume

    @property
    def max_etf_position(self):
        position = self.etf_position
        for order in self.orders.values():
            if order.side == Side.BID:
                position += order.max_remaining_volume
        return position

    @property
    def min_etf_position(self):
        position = self.etf_position
        for order in self.orders.values():
            if order.side == Side.ASK:
                position -= order.max_remaining_volume
        return position

    def get_price_est(self):
        fut_price = self.fut_orderbook.price_est
        price = fut_price - M0 * (
            self.fut_position + self.etf_position) - M1 * self.etf_position
        return price

    def on_order_book_update_message(self, instrument: int, sequence_number: int, ask_prices: List[int],
                                     ask_volumes: List[int], bid_prices: List[int], bid_volumes: List[int]) -> None:
        """Called periodically to report the status of an order book.

        The sequence number can be used to detect missed or out-of-order
        messages. The five best available ask (i.e. sell) and bid (i.e. buy)
        prices are reported along with the volume available at each of those
        price levels.
        """

        if instrument == Instrument.FUTURE:
            self.fut_orderbook.update(
                ask_prices, ask_volumes, bid_prices, bid_volumes)

            if self.ticks % 4 == 0:
                best_bid_price = bid_prices[0] if bid_prices[0] != 0 else 0
                best_ask_price = ask_prices[0] if ask_prices[0] != 0 else PRICE_MAX
                self._hedge(best_ask_price, best_bid_price)
            self.ticks += 1

        elif instrument == Instrument.ETF:
            self.etf_orderbook.update(
                ask_prices, ask_volumes, bid_prices, bid_volumes)

    def on_trade_ticks_message(self, instrument: int, sequence_number: int, ask_prices: List[int],
                               ask_volumes: List[int], bid_prices: List[int], bid_volumes: List[int]) -> None:
        """Called periodically when there is trading activity on the market.

        The five best ask (i.e. sell) and bid (i.e. buy) prices at which there
        has been trading activity are reported along with the aggregated volume
        traded at each of those price levels.

        If there are less than five prices on a side, then zeros will appear at
        the end of both the prices and volumes arrays.
        """

        if instrument == Instrument.FUTURE:
            self.fut_orderbook.tick(
                ask_prices, ask_volumes, bid_prices, bid_volumes)
        elif instrument == Instrument.ETF:
            self.etf_orderbook.tick(
                ask_prices, ask_volumes, bid_prices, bid_volumes)

    def on_error_message(self, client_order_id: int, error_message: bytes) -> None:
        """Called when the exchange detects an error.

        If the error pertains to a particular order, then the client_order_id
        will identify that order, otherwise the client_order_id will be zero.
        """
        self.logger.warning("ERROR order %d: %s",
                            client_order_id, error_message.decode())
        if client_order_id != 0:
            self.on_order_status_message(client_order_id, 0, 0, 0)

    def on_hedge_filled_message(self, client_order_id: int, price: int, volume: int) -> None:
        """Called when one of your hedge orders is filled.

        The price is the average price at which the order was (partially) filled,
        which may be better than the order's limit price. The volume is
        the number of lots filled at that price.
        """

        try:
            order: HedgeOrder = self.hedge_orders.pop(client_order_id)
            self.frequency_limiter.hedge_received(self.event_loop.time())
        except:
            return

        # Log info
        initial = self.fut_position

        if volume == 0:
            return

        if order.side == Side.ASK:
            self.fut_position -= volume
            self.max_fut_position -= volume
            if order.remaining_volume == volume:
                # Filled
                price_est = price + TICK_SIZE_IN_CENTS // 2
            else:
                # Partially
                price_est = price - TICK_SIZE_IN_CENTS // 2
        elif order.side == Side.BID:
            self.fut_position += volume
            self.min_fut_position += volume
            if order.remaining_volume == volume:
                price_est = price - TICK_SIZE_IN_CENTS // 2
            else:
                price_est = price + TICK_SIZE_IN_CENTS // 2

        self.fut_orderbook.prices.append(price_est)

    def on_order_filled_message(self, client_order_id: int, price: int, volume: int) -> None:
        """Called when one of your orders is filled, partially or fully.

        The price is the price at which the order was (partially) filled,
        which may be better than the order's limit price. The volume is
        the number of lots filled at that price.
        """

        order = self.orders.get(client_order_id, None)
        if order is None:
            return

        self.frequency_limiter.fill_received(
            self.event_loop.time(), client_order_id)

        # Log info
        initial_order = repr(order)
        initial_pos = self.etf_position
        initial_pos_min = self.min_etf_position
        initial_pos_max = self.max_etf_position

        order.remaining_volume -= volume
        order.fill_volume += volume

        if order.side == Side.BID:
            self.etf_position += volume
        elif order.side == Side.ASK:
            self.etf_position -= volume

        if order.lifespan == Lifespan.IMMEDIATE_OR_CANCEL and volume == 0:
            self.etf_orderbook._best_ask = 0
            self.etf_orderbook._best_bid = 0

    def on_order_status_message(self, client_order_id: int, fill_volume: int, remaining_volume: int,
                                fees: int) -> None:
        """Called when the status of one of your orders changes.

        The fill_volume is the number of lots already traded, remaining_volume
        is the number of lots yet to be traded and fees is the total fees for
        this order. Remember that you pay fees for being a market taker, but
        you receive fees for being a market maker, so fees can be negative.

        If an order is cancelled its remaining volume will be zero.
        """

        order = self.orders.get(client_order_id, None)
        if order is None:
            return

        now = self.event_loop.time()

        self.frequency_limiter.event_received(
            now, order, fill_volume, remaining_volume, fees)

        initial_order = repr(order)

        order.amend_amount -= remaining_volume - order.remaining_volume
        order.remaining_volume = remaining_volume

        order.fill_volume = fill_volume

        if remaining_volume == 0:
            self.orders.pop(client_order_id)

        if order.lifespan == Lifespan.IMMEDIATE_OR_CANCEL and fill_volume == 0:
            self.etf_orderbook._best_ask = 0
            self.etf_orderbook._best_bid = 0

    def insert_order(self, order: Order):
        self.send_insert_order(*order.create())
        self.orders[order.id] = order
        if order.lifespan == Lifespan.LIMIT_ORDER:
            self.frequency_limiter.event_sent(order.id, "L")
        elif order.lifespan == Lifespan.IMMEDIATE_OR_CANCEL:
            self.frequency_limiter.event_sent(order.id, "I")

    def cancel_order(self, id):
        self.send_cancel_order(id)
        self.frequency_limiter.event_sent(id, "C")

        order = self.orders.get(id, None)
        if order:
            self.orders[id].is_active = False

    def amend_order(self, id, volume):
        self.send_amend_order(id, volume)
        self.frequency_limiter.event_sent(id, "A")
        order = self.orders.get(id, None)
        if order:
            order.amend_amount += order.remaining_volume - volume
            order.remaining_volume = volume

    def hedge_order(self, order: Order):
        self.send_hedge_order(*order.create())
        self.hedge_orders[order.id] = order

    def _hedge(self, best_ask_price, best_bid_price):
        if best_ask_price - best_bid_price >= HEDGE_WIDTH_LIMIT:
            return

        net_position = self.etf_position + self.fut_position
        volume = 0
        price = 0
        side = Side.ASK

        if net_position >= HEDGE_VOLUME_LIMIT:
            side = Side.ASK
            price = best_bid_price
            volume = min(int(abs(net_position) * HEDGE_FRACTION),
                         POSITION_LIMIT + self.min_fut_position)
        elif net_position <= -HEDGE_VOLUME_LIMIT:
            side = Side.BID
            price = best_ask_price
            volume = min(int(abs(net_position) * HEDGE_FRACTION),
                         POSITION_LIMIT - self.max_fut_position)
        else:
            return

        try:
            self.frequency_limiter.get_permission()
            pass
        except FrequencyLimitError:
            return

        if volume > 0:
            order = HedgeOrder(side=side, price=price, volume=volume)
            self.hedge_order(order)

            if order.side == Side.ASK:
                self.min_fut_position -= volume
            else:
                self.max_fut_position += volume

            self.frequency_limiter.hedge_sent()

    def forced_hedge(self):
        # If unhedged for limit minute hedge immediately
        now = self.event_loop.time()
        if self.last_hedged_event and now - self.last_hedged_event > UNHEDGED_DURATION_LIMIT:
            while True:
                try:
                    self.frequency_limiter.get_permission()
                    net_position = self.etf_position + self.fut_position
                    fut_price = self.fut_orderbook.price_est

                    if net_position > 0:
                        side = Side.ASK
                        price = ceil(fut_price - FORCED_HEDGE_WIDTH)
                        volume = min(net_position - UNHEDGED_VOLUME_LIMIT,
                                     POSITION_LIMIT + self.min_fut_position)
                    else:
                        side = Side.BID
                        price = floor(fut_price + FORCED_HEDGE_WIDTH)
                        volume = min(-net_position - UNHEDGED_VOLUME_LIMIT,
                                     POSITION_LIMIT - self.max_fut_position)
                    order = HedgeOrder(side=side, price=price, volume=volume)

                    self.hedge_order(order)

                    if side == Side.ASK:
                        self.min_fut_position -= volume
                    elif side == Side.BID:
                        self.max_fut_position += volume

                    self.frequency_limiter.hedge_sent()
                    break
                except FrequencyLimitError as e:
                    # Retry until have permission!
                    time.sleep(e.timeout)
        self.slow_hedge_handle = self.event_loop.call_later(
            UNHEDGED_DURATION_LIMIT, self.forced_hedge)

    def fast_hedge(self):
        timeout = FAST_HEDGE_PERIOD
        try:
            fut_price = self.fut_orderbook.price_est
            hedge_orders = [
                HedgeOrder(side=Side.ASK, price=ceil(
                    fut_price + FAST_HEDGE_WIDTH), volume=1),
                HedgeOrder(side=Side.BID, price=floor(
                    fut_price - FAST_HEDGE_WIDTH), volume=1),
            ]

            for order in hedge_orders:
                self.frequency_limiter.get_permission()

                self.hedge_order(order)
                if order.side == Side.ASK:
                    self.min_fut_position -= 1
                else:
                    self.max_fut_position += 1

                self.frequency_limiter.hedge_sent()

            self.fast_hedge_handle = self.event_loop.call_later(
                FAST_HEDGE_PERIOD, self.fast_hedge)
        except FrequencyLimitError as e:
            timeout = e.timeout
        except Empty:
            pass
        finally:
            self.fast_hedge_handle = self.event_loop.call_later(
                timeout, self.fast_hedge)

    def get_expected_value(self, side, price, volume):
        return (1 if side == Side.ASK else -1) * volume * (price - self.fut_orderbook.price_est)

    def get_executions(self, limit_orders: List[Order], ioc_orders: List[Order]) -> List[Execution]:
        executions = []

        prev_orders: List[Order] = copy.deepcopy(
            [o for o in self.orders.values() if o.is_active])
        prev_orders.sort(key=lambda o: o.id)

        # Cancel within range
        high = PRICE_MAX
        low = 0
        for o in limit_orders:
            if o.side == Side.ASK:
                high = min(high, o.price)
            elif o.side == Side.BID:
                low = max(low, o.price)

        uncancelled = []
        for prev in prev_orders:
            if prev.price >= high or prev.price <= low:
                uncancelled.append(prev)
                continue
            ev = 0
            transferred = 0
            for ioc in ioc_orders:
                if ioc.price == prev.price and ioc.side == prev.side and ioc.remaining_volume > 0:
                    smaller = min(ioc.remaining_volume, prev.remaining_volume)
                    ioc.remaining_volume -= smaller
                    prev.remaining_volume -= smaller
                    transferred += smaller
                    if prev.remaining_volume <= 0:
                        break
            # Send cancel
            ev = self.get_expected_value(prev.side, prev.price, transferred)
            priority = FIRST_PRIORITY if transferred == 0 else SECOND_PRIORITY
            executions.append(
                Execution(self.cancel_order, (prev.id,), priority, ev))
        prev_orders = uncancelled

        available_lots = [POSITION_LIMIT + self.min_etf_position,
                          POSITION_LIMIT - self.max_etf_position]

        # Insert IOCs
        for ioc in ioc_orders:
            if ioc.remaining_volume <= 0:
                continue
            if available_lots[ioc.side] <= 0:
                continue
            # Insert IOC
            ioc.remaining_volume = min(
                ioc.remaining_volume, available_lots[ioc.side])
            ev = self.get_expected_value(
                ioc.side, ioc.price, ioc.remaining_volume)
            executions.append(
                Execution(self.insert_order, (ioc,), SECOND_PRIORITY, ev))
            available_lots[ioc.side] -= ioc.remaining_volume

        # Cancel previous orders
        for prev in prev_orders:
            if prev.remaining_volume <= 0:
                continue
            transferred = 0
            for limit in limit_orders:
                if prev.price == limit.price and prev.side == limit.side and limit.remaining_volume > 0:
                    transferred = min(limit.remaining_volume,
                                      prev.remaining_volume)
                    limit.remaining_volume -= transferred
                    prev.remaining_volume -= transferred
                    if prev.remaining_volume <= 0:
                        break
            if transferred == 0:
                # Cancel prev
                executions.append(Execution(
                    self.cancel_order, (prev.id,), THIRD_PRIORITY, prev.remaining_volume))
            elif prev.remaining_volume > 0:
                # Amend prev to transferred
                executions.append(Execution(
                    self.amend_order, (prev.id, transferred), THIRD_PRIORITY, prev.remaining_volume))
        # Insert limit orders
        for order in limit_orders:
            if order.remaining_volume <= 0:
                continue
            if available_lots[order.side] <= 0:
                continue
            # Insert (remaining_volume)
            order.remaining_volume = min(
                order.remaining_volume, available_lots[order.side])
            ev = self.get_expected_value(
                order.side, order.price, order.remaining_volume)
            executions.append(Execution(self.insert_order,
                              (order,), FOURTH_PRIORITY, ev))
            available_lots[order.side] -= order.remaining_volume
        return executions

    def execute(self, immediately=False) -> None:
        try:
            price_est = self.get_price_est()
        except:
            return

        # Inversed
        ask_volume = bid_volume = max(
            GFD_VOLUME - abs(self.etf_position), MIN_VOLUME)
        limit_orders = [
            Order(side=Side.ASK, price=ceil(price_est + W1),
                  volume=ask_volume, lifespan=Lifespan.LIMIT_ORDER),
            Order(side=Side.BID, price=floor(price_est - W1),
                  volume=bid_volume, lifespan=Lifespan.LIMIT_ORDER),
        ]

        ioc_orders = []
        ioc_ask_price = ceil(price_est + W0)
        ioc_bid_price = floor(price_est - W0)
        if self.etf_orderbook.best_ask <= ioc_bid_price:
            ioc_orders.append(Order(
                side=Side.BID,
                price=ioc_bid_price,
                volume=IOC_VOLUME,
                lifespan=Lifespan.IMMEDIATE_OR_CANCEL))
        if self.etf_orderbook.best_bid >= ioc_ask_price:
            ioc_orders.append(Order(
                side=Side.ASK,
                price=ioc_ask_price,
                volume=IOC_VOLUME,
                lifespan=Lifespan.IMMEDIATE_OR_CANCEL))

        self.executions = self.get_executions(limit_orders, ioc_orders)
        self.executions.reverse()
        # self.executions.sort(key=lambda op: (-op.priority, op.ev))

        if immediately or self.execute_handle is None:
            self._execute()

    def _execute(self):
        if self.execute_handle:
            self.execute_handle.cancel()
            self.execute_handle = None
        while self.executions:
            exe = self.executions[-1]
            try:
                self.frequency_limiter.get_permission()
            except FrequencyLimitError as e:
                self.execute_handle = self.event_loop.call_later(
                    e.timeout, self._execute)
                return

            self.executions.pop()
            exe()

    def on_datagram(self, *args, **kwargs) -> None:
        super().on_datagram(*args, **kwargs)
        self.execute(immediately=True)

    def on_message(self, *args, **kwargs) -> None:
        super().on_message(*args, **kwargs)
        typ, *_, length = args
        if typ == MessageType.HEDGE_FILLED and length == HEDGE_FILLED_MESSAGE_SIZE:
            self.execute(immediately=True)
        else:
            self.execute()
