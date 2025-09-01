
#!/usr/bin/env python
import traceback
from ctrader_open_api import Client, Protobuf, TcpProtocol, Auth, EndPoints
from twisted.internet.defer import TimeoutError as TwistedTimeoutError
from typing import Optional
from types import SimpleNamespace
from ctrader_open_api.endpoints import EndPoints
from message_handlers import dispatch_message, log_exec_event_error
from re import sub
import select
import logging
import termios, tty
import pyautogui
import time
from prompt_toolkit.shortcuts import radiolist_dialog
from ctrader_open_api.messages.OpenApiCommonMessages_pb2 import *
from ctrader_open_api.messages.OpenApiMessages_pb2 import *
from ctrader_open_api.messages.OpenApiModelMessages_pb2 import *
from twisted.internet import reactor
from inputimeout import inputimeout, TimeoutOccurred
from datetime import datetime, timezone, timedelta
import datetime
import calendar
from dotenv import load_dotenv
import os
import uuid
from rich.table import Table
from rich.live import Live
from rich.console import Console
from rich.console import Group
from rich import box
import sys
import contextlib
import threading
from colorama import Fore, Style
from graceful_shutdown import ShutdownManager
import ui_helpers as H
from message_handlers import dispatch_message
from time import time
from collections import deque

console = Console(emoji=False)
live = None
accountMetadata = {}
pendingReconciliations = set()
symbolIdToName = {}
symbolIdToPrice = {}  # Symbol ID -> (bid, ask)
symbolIdToPips = {}  # Symbol ID -> pipsPosition
ordersById = {}  # orderId -> order (only active/pending)
subscribedSymbols = set()
expectedSpotSubscriptions = 0
receivedSpotConfirmations = 0
positionsById = {}
positionPnLById = {}
showStartupOutput = False
liveViewerActive = False
symbolIdToDetails = {}
currentAccountId = None
selected_position_index = 0
error_messages = []
liveLaunchInProgress = False
view_offset = 0
inFlightCancels: set[int] = set()
cancelTombstones: dict[int, float] = {}
closeTombstonesPositions: dict[int, float] = {}

MESSAGE_TTL_SEC = 10.0  # how long messages stay visible

# --- Cancel scheduler state ---
_cancel_queue = deque()                # items: (orderId, t_enqueued)
_cancel_inflight: set[int] = set()     # actually on the wire
_cancel_retries: dict[int,int] = {}    # orderId -> tries
CANCEL_MAX_RETRIES = 2                 # after first send, allow 2 retries max
CANCEL_SPACING_SEC = 0.15              # rate limit between sends
CANCEL_TOMBSTONE_SEC = 20.0            # how long to hide after timeout
CANCEL_BACKOFF_BASE = 0.6              # first retry after 0.6s, then 1.2s, ...



selected_order_index = 0
view_offset_orders = 0   # orders
focused_panel = "positions"   # "positions" | "orders"
last_visible_order_ids = []
#

# ---- cached sort for positions (to avoid re-sorting on every keypress) ----
menuScheduled = False
slByPositionId = {}            # positionId -> SL in account currency
slInput = {                    # inline input state
    "mode": "idle",            # idle | armed | typing
    "positionId": None,
    "buffer": ""
}
# order-inline edit state
orderEdit = {
    "mode": "idle",     # idle | armed | typing
    "orderId": None,
    "buffer": "",
}

H.init_ordering(positionsById, positionPnLById)
H.set_close_tombstones_ref(closeTombstonesPositions)


log_flow   = logging.getLogger("flow")        # general app flow
log_exec   = logging.getLogger("exec")        # execution events
log_prices = logging.getLogger("prices")      # spot/tick data
log_ui     = logging.getLogger("ui_silent")   # completely silent in UI



class LiveUiMuteFilter(logging.Filter):
    """Block console logs when live viewer is active."""
    def filter(self, record: logging.LogRecord) -> bool:
        # mute everything while the live viewer owns the screen
        return not liveViewerActive
        # If you prefer to allow warnings/errors through during live view:
        # return (not liveViewerActive) or (record.levelno >= logging.WARNING)

def setup_logging():
    fmt = "%(asctime)s [%(name)s] [%(levelname)s] %(message)s"

    file_handler = logging.FileHandler("ctrader.log", encoding="utf-8")
    file_handler.setFormatter(logging.Formatter(fmt))

    stream_handler = logging.StreamHandler()
    stream_handler.setFormatter(logging.Formatter(fmt))
    stream_handler.addFilter(LiveUiMuteFilter())

    logging.basicConfig(
        level=logging.INFO,         # or DEBUG for more verbosity
        format=fmt,
        handlers=[file_handler, stream_handler],
    )





if __name__ == "__main__":
    setup_logging()
    load_dotenv()
    accountIdsEnv = os.getenv("ACCOUNT_IDS", "")
    envAccountIds = [int(acc.strip()) for acc in accountIdsEnv.split(",") if acc.strip().isdigit()]

    while True:
        hostType = input("Host (Live/Demo): ").strip().lower()
        if hostType in ["live", "demo"]:
            break
        print(f"{hostType} is not a valid host type.")

    appClientId = os.getenv("CLIENT_ID")
    appClientSecret = os.getenv("CLIENT_SECRET")
    accessToken = os.getenv("ACCESS_TOKEN")

    client = Client(EndPoints.PROTOBUF_LIVE_HOST if hostType.lower() == "live" else EndPoints.PROTOBUF_DEMO_HOST, EndPoints.PROTOBUF_PORT, TcpProtocol)

    def _stop_live_ui():
        global liveViewerActive, live
        liveViewerActive = False
        try:
            if live:
                live.stop()
        except Exception:
            pass
        finally:
            live = None  # <— important so we know there's no active Live


    # main.py
    def get_account_ccy() -> str:
        ccy = accountMetadata.get(currentAccountId, {}).get("currency")
        # treat unknowns as missing and fall back to USD
        if not ccy or ccy in {"?", "UNKNOWN", "N/A", ""}:
            return "USD"
        return ccy

    # Create and wire the shutdown manager
    shutdown = ShutdownManager(
        reactor=reactor,
        client=client,
        get_subscribed_symbols=lambda: list(subscribedSymbols),
        unsubscribe_symbol=lambda sid: sendProtoOAUnsubscribeSpotsReq(sid),
        account_logout=lambda: sendProtoOAAccountLogoutReq(),
        stop_live_ui=_stop_live_ui,
    )
    shutdown.install_signal_handlers()
    
    # Ensure Twisted calls our cleanup on reactor shutdown as well
    reactor.addSystemEventTrigger(
        'before', 'shutdown',
        lambda: shutdown.cleanup(reason='reactor-shutdown')
    )

    def returnToMenu():
        global menuScheduled
        if liveViewerActive:
            # The live viewer owns stdin; don’t start the menu now.
            return
        menuScheduled = False
        reactor.callLater(0, executeUserCommand)


    
    def build_modify_req(account_id: int, order_id: int):
        """
        Return (req, req_name) using ProtoOAModifyOrderReq when available,
        else fall back to ProtoOAAmendOrderReq.
        """
        try:
            req = ProtoOAModifyOrderReq()
            req_name = "ProtoOAModifyOrderReq"
        except NameError:
            req = ProtoOAAmendOrderReq()
            req_name = "ProtoOAAmendOrderReq"
            logging.getLogger("modify_order").warning("Using fallback request type: %s", req_name)
    
        req.ctidTraderAccountId = int(account_id)
        req.orderId = int(order_id)
        return req, req_name
    
    
    def _ok(orderId, res):
        """
        Shared OK-callback for order modify requests.
        Logs and schedules a reconcile so UI converges to server truth.
        """
        log = logging.getLogger("modify_order")
        log.info("Deferred OK for modify order %s (type=%s)", orderId, type(res).__name__)
        try:
            reactor.callLater(0.3, runWhenReady, sendProtoOAReconcileReq, currentAccountId)
        except Exception:
            pass
        return res
    
    
    def sendProtoOAModifyOrderReq(orderId: int, new_price: float, clientMsgId=None):
        log = logging.getLogger("modify_order")
    
        o = ordersById.get(orderId)
        if not o:
            log.error("Order %s not found. Known orders: %s", orderId, list(ordersById.keys()))
            return
    
        # Snapshot for diagnostics
        try:
            order_type_name = ProtoOAOrderType.Name(getattr(o, "orderType", 0))
        except Exception:
            order_type_name = str(getattr(o, "orderType", "?"))
    
        try:
            order_status_name = ProtoOAOrderStatus.Name(getattr(o, "orderStatus", 0))
        except Exception:
            order_status_name = str(getattr(o, "orderStatus", "?"))
    
        symbol_id = getattr(o, "symbolId", None) or getattr(getattr(o, "tradeData", None) or (), "symbolId", None)
        snapshot = {
            "orderId": getattr(o, "orderId", None),
            "type": order_type_name,
            "status": order_status_name,
            "symbolId": symbol_id,
            "limitPrice": getattr(o, "limitPrice", None),
            "stopPrice": getattr(o, "stopPrice", None),
            "accountId": currentAccountId,
        }
        log.info("Preparing modify -> new_price=%s | snapshot=%s", new_price, snapshot)
    
        # Build request with fallback handled in one place
        req, req_name = build_modify_req(currentAccountId, orderId)
    
        # Decide target field
        if order_is_limit(o):
            req.limitPrice = float(new_price)
            target_field, target_value = "limitPrice", req.limitPrice
        elif order_is_stop(o):
            req.stopPrice = float(new_price)
            target_field, target_value = "stopPrice", req.stopPrice
        else:
            log.warning("Unsupported inline modify for order type: %s", order_type_name)
            return
    
        print(f"✍️ Modifying order {orderId} -> {target_field}={target_value}")
        log.debug(
            "Sending %s | account=%s orderId=%s %s=%s",
            req_name, currentAccountId, orderId, target_field, target_value
        )
    
        # --- Optimistic local update so the live table reflects your edit immediately ---
        loc = ordersById.get(orderId)
        if loc:
            try:
                if target_field == "limitPrice":
                    setattr(loc, "limitPrice", float(new_price))
                else:
                    setattr(loc, "stopPrice", float(new_price))
                if is_live_viewer_active():
                    # Use your existing render scheduler
                    reactor.callFromThread(_request_render)
            except Exception:
                pass
        # -------------------------------------------------------------------------------
    
        d = client.send(req, clientMsgId=clientMsgId)
        d.addCallback(lambda res: _ok(orderId, res))
        d.addErrback(lambda failure: (log.error("Deferred ERROR for modify order %s: %s", orderId, failure), onError(failure)))


    def refreshSpotPrices():
        if not isAccountInitialized(currentAccountId):
            return
        for symbolId in subscribedSymbols.copy():
            sendProtoOASubscribeSpotsReq(symbolId)
        reactor.callLater(15, refreshSpotPrices)

    def connected(client):
        print("\nConnected")
        request = ProtoOAApplicationAuthReq()
        request.clientId = appClientId
        request.clientSecret = appClientSecret

        def onAppAuthSuccess(_):
            logging.getLogger("gateway").info("Application authorized")
#             print("📥 Fetching available accounts from access token...")
            sendProtoOAGetAccountListByAccessTokenReq()

        deferred = client.send(request)
        deferred.addCallback(onAppAuthSuccess)
        deferred.addErrback(onError)


    def disconnected(client, reason):
        log = logging.getLogger("gateway")
        log.warning("Disconnected: %s", reason)
        if shutdown.shutting_down:
            return
        log.info("Attempting reconnect in 5s…")
        reactor.callLater(5, client.startService)


    def promptUserToSelectAccount():
        print("\n👉 Select the account you want to activate:")
        for idx, accId in enumerate(availableAccounts, 1):
            trader = accountTraderInfo.get(accId)
            meta = accountMetadata.get(accId, {})
            is_live = meta.get("isLive", "?")
            broker = meta.get("broker", "?")
            currency = meta.get("currency", "?")
            if trader:
                print(f" {idx}. {accId} — [{is_live}] Equity: {trader.equity / 100:.2f}, Free Margin: {trader.freeMargin / 100:.2f}, Broker: {broker}, Currency: {currency}")
            else:
                print(f" {idx}. {accId} — [{is_live}], Broker: {broker}, Currency: {currency}")

        while True:
            try:
                choice = int(input("Enter number of account to activate: ").strip())
                if 1 <= choice <= len(availableAccounts):
                    selectedAccountId = availableAccounts[choice - 1]
                    setAccount(selectedAccountId)
                    break
                else:
                    print("Invalid choice. Try again.")
            except ValueError:
                print("Enter a number.")

    #

    def _prune_messages_now() -> None:
        """Remove expired messages in-place."""
        now = time()
        # accept both legacy str entries and (msg, expiry) tuples
        error_messages[:] = [
            m for m in error_messages
            if (isinstance(m, tuple) and len(m) == 2 and m[1] > now) or isinstance(m, str)
        ]
    
    def _messages_for_view() -> list[str]:
        """Return current messages as strings (after pruning)."""
        _prune_messages_now()
        out = []
        for m in error_messages:
            out.append(m[0] if isinstance(m, tuple) else m)
        # cap to what your UI shows
        return out[-6:]

    def push_info(msg: str, *, render: bool = True, ttl: float = MESSAGE_TTL_SEC):
        """Add a transient UI message that auto-expires after `ttl` seconds."""
        now = time()
        # store as (text, expire_ts)
        error_messages.append((msg, now + float(ttl)))
        # keep buffer small
        if len(error_messages) > 12:
            del error_messages[:-12]
        if render and is_live_viewer_active():
            reactor.callFromThread(_request_render)

    _render_pending = False
    def _request_render():
        """Schedule a single render on the next reactor turn."""
        global _render_pending
        if _render_pending:
            return
        _render_pending = True
        reactor.callLater(0, _run_render_once)
    
    def _run_render_once():
        global _render_pending
        _render_pending = False
        printLivePnLTable()

    def _sl_prompt(sl_state: dict, get_ccy) -> str:
        mode = sl_state.get("mode")
        pid = sl_state.get("positionId")
        if mode == "armed":
            return f"Threshold for Record {pid} [{get_ccy()}]: (type a number, Enter=save, Esc=cancel) — j/k moves target"
        if mode == "typing":
            buf = sl_state.get("buffer", "")
            return f"Threshold for Record {pid} [{get_ccy()}]: {buf}_  (Enter=save, Esc=cancel, ⌫=backspace)"
        return ""


    def _order_prompt(state: dict) -> str:
        mode = state.get("mode")
        oid  = state.get("orderId")
        if mode == "armed":
            o = ordersById.get(oid)
            cur = order_current_target(o) if o else None
            cur_s = f"(current: {cur})" if cur is not None else ""
            return f"Edit Order {oid} target: type a price {cur_s} — Enter=save, Esc=cancel, j/k to move"
        if mode == "typing":
            buf = state.get("buffer","")
            return f"Edit Order {oid} target: {buf}_  (Enter=save, Esc=cancel, ⌫=backspace)"
        return ""

    def printLivePnLTable():
        global live, selected_position_index, view_offset, _last_render
        global selected_order_index, view_offset_orders, focused_panel, last_visible_order_ids
        if not live:
            return

#         prompt_line = _sl_prompt(slInput, get_account_ccy)

        prompt_line = "  •  ".join(
            p for p in (
                _sl_prompt(slInput, get_account_ccy),
                _order_prompt(orderEdit),
            ) if p
        )

        view, selected_position_index, view_offset, \
            selected_order_index, view_offset_orders, last_visible_order_ids = H.buildLivePnLView(
                console_height=console.size.height,
                positions_sorted=H.ordered_positions(),
                selected_index=selected_position_index,
                orders=_orders_for_view(),              
                view_offset=view_offset,
                symbolIdToName=symbolIdToName,
                symbolIdToDetails=symbolIdToDetails,
                symbolIdToPrice=symbolIdToPrice,
                positionPnLById=positionPnLById,
                error_messages=_messages_for_view(),
                slByPositionId=slByPositionId,
                account_currency=get_account_ccy(),
                footer_prompt=prompt_line,
                orders_selected_index=selected_order_index,
                orders_view_offset=view_offset_orders,
                focused_panel=focused_panel,
                order_edit_state=orderEdit,
        )
#         live.update(view)
        live.update(view, refresh=True)   # instead of just live.update(view)


    def _update_pnl_cache_for_symbol(symbol_id: int):
        bid, ask = symbolIdToPrice.get(symbol_id, (None, None))
        if bid is None or ask is None:
            return
        contract_size = (symbolIdToDetails.get(symbol_id, {}) or {}).get("contractSize", 100000) or 100000
        for pos_id, pos in positionsById.items():
            if pos.tradeData.symbolId != symbol_id:
                continue
            side = H.trade_side_name(pos.tradeData.tradeSide)
            entry = pos.price
            lots = pos.tradeData.volume / 100.0
            mkt = bid if side == "BUY" else ask
            positionPnLById[pos_id] = (mkt - entry if side == "BUY" else entry - mkt) * lots * contract_size
        H.mark_positions_dirty()


    def add_position(pos):
        global selected_position_index, view_offset
        pos_id = pos.positionId
        slByPositionId.setdefault(pos_id, None) 
        positionsById[pos_id] = pos
        sendProtoOASubscribeSpotsReq(pos.tradeData.symbolId)
        H.mark_positions_dirty()
        sendProtoOAGetPositionUnrealizedPnLReq()  # get real PnL 
    
        ops = H.ordered_positions()
        total = len(ops)
        if total == 1:
            selected_position_index = 0
            view_offset = 0
        elif selected_position_index >= total:
            selected_position_index = total - 1
    
        reactor.callFromThread(_request_render)

    accountTraderInfo = {}  # To store info like balance for each account
    availableAccounts = []  # Fetched account IDs


    authorizedAccounts = set()
    authInProgress = set()

    def fetchTraderInfo(accountId):
        print(f"🔍 Starting auth flow for account: {accountId}")

        # If fully authorized already
        if accountId in authorizedAccounts:
            log_flow.info("✅ Already authorized: %s", accountId)
            sendProtoOAReconcileReq(accountId)
            return

        # If auth is already in progress, don’t do it twice
        if accountId in authInProgress:
            log_flow.info("⏳ Auth already in progress for %s", accountId)
            return

        authInProgress.add(accountId)

        def onAuthSuccess(_):
            print(f"✅ Account {accountId} authorized successfully")
            authorizedAccounts.add(accountId)
            pendingReconciliations.add(accountId)
            reactor.callLater(0.5, sendProtoOAReconcileReq, accountId)

        request = ProtoOAAccountAuthReq()
        request.ctidTraderAccountId = accountId
        request.accessToken = accessToken

        deferred = client.send(request)
        deferred.addCallback(onAuthSuccess)
        deferred.addErrback(onError)


#     def onAccountListReceived(res):
#         global availableAccounts, accountMetadata
#         availableAccounts = [acc.ctidTraderAccountId for acc in res.ctidTraderAccount]
#         
# #         print("Available accounts:")
#         for acc in res.ctidTraderAccount:
#             acc_id = acc.ctidTraderAccountId
#             currency = getattr(acc, "depositCurrency", "?")
#             broker = getattr(acc, "brokerName", "?")
#             is_live = "Live" if getattr(acc, "isLive", False) else "Demo"
#             
#             # Save metadata for later use
#             accountMetadata[acc_id] = {
#                 "currency": currency,
#                 "broker": broker,
#                 "isLive": is_live
#             }
#     
#             print(f" - ID: {acc_id}, Type: {is_live}, Broker: {broker}, Currency: {currency}")
#         
#         returnToMenu()


    def onError(failure):
        logging.getLogger("gateway").error("Message Error: %s", failure)
        reactor.callLater(3, callable=executeUserCommand)

    def showHelp():
        print("Commands (Parameters with an * are required), ignore the description inside ()")
        print("setAccount(For all subsequent requests this account will be used) *accountId")
        print("ProtoOAVersionReq clientMsgId")
        print("ProtoOAGetAccountListByAccessTokenReq clientMsgId")
        print("ProtoOAAssetListReq clientMsgId")
        print("ProtoOAAssetClassListReq clientMsgId")
        print("ProtoOASymbolCategoryListReq clientMsgId")
        print("ProtoOASymbolsListReq includeArchivedSymbols(True/False) clientMsgId")
        print("ProtoOATraderReq clientMsgId")
        print("ProtoOASubscribeSpotsReq *symbolId *timeInSeconds(Unsubscribes after this time) subscribeToSpotTimestamp(True/False) clientMsgId")
        print("ProtoOAReconcileReq clientMsgId")
        print("ProtoOAGetTrendbarsReq *weeks *period *symbolId clientMsgId")
        print("ProtoOAGetTickDataReq *days *type *symbolId clientMsgId")
        print("NewMarketOrder *symbolId *tradeSide *volume clientMsgId")
        print("NewLimitOrder *symbolId *tradeSide *volume *price clientMsgId")
        print("NewStopOrder *symbolId *tradeSide *volume *price clientMsgId")
        print("ClosePosition *positionId *volume clientMsgId")
        print("CancelOrder *orderId clientMsgId")
        print("DealOffsetList *dealId clientMsgId")
        print("GetPositionUnrealizedPnL clientMsgId")
        print("OrderDetails clientMsgId")
        print("OrderListByPositionId *positionId fromTimestamp toTimestamp clientMsgId")

        reactor.callLater(3, callable=executeUserCommand)


    def setAccount(accountId):
        global currentAccountId
        if currentAccountId is not None:
            sendProtoOAAccountLogoutReq()
        currentAccountId = int(accountId)
        fetchTraderInfo(currentAccountId)


    def sendProtoOAVersionReq(clientMsgId = None):
        request = ProtoOAVersionReq()
        deferred = client.send(request, clientMsgId = clientMsgId)
        deferred.addErrback(onError)

    def sendProtoOAGetAccountListByAccessTokenReq(clientMsgId = None):
        request = ProtoOAGetAccountListByAccessTokenReq()
        request.accessToken = accessToken
        deferred = client.send(request, clientMsgId = clientMsgId)
        deferred.addErrback(onError)

    def sendProtoOAAccountLogoutReq(clientMsgId = None):
        request = ProtoOAAccountLogoutReq()
        request.ctidTraderAccountId = currentAccountId
        deferred = client.send(request, clientMsgId = clientMsgId)
        deferred.addErrback(onError)



    def sendProtoOAAccountAuthReq(clientMsgId = None):
        request = ProtoOAAccountAuthReq()
        request.ctidTraderAccountId = currentAccountId
        request.accessToken = accessToken

        def onAccountAuthSuccess(_):
            print("✅ Account authorization successful")
#             sendProtoOAReconcileReq()  # <-- This is essential!
            sendProtoOAReconcileReq(currentAccountId)

        deferred = client.send(request, clientMsgId=clientMsgId)
        deferred.addCallback(onAccountAuthSuccess)
        deferred.addErrback(onError)


    def sendProtoOAAssetListReq(clientMsgId = None):
        global client
        request = ProtoOAAssetListReq()
        request.ctidTraderAccountId = currentAccountId
        deferred = client.send(request, clientMsgId = clientMsgId)
        deferred.addErrback(onError)


    def sendProtoOAAssetClassListReq(clientMsgId = None):
        global client
        request = ProtoOAAssetClassListReq()
        request.ctidTraderAccountId = currentAccountId
        deferred = client.send(request, clientMsgId = clientMsgId)
        deferred.addErrback(onError)

    def sendProtoOASymbolCategoryListReq(clientMsgId = None):
        global client
        request = ProtoOASymbolCategoryListReq()
        request.ctidTraderAccountId = currentAccountId
        deferred = client.send(request, clientMsgId = clientMsgId)
        deferred.addErrback(onError)

    def isAccountInitialized(accountId):
        return (
            accountId in authorizedAccounts and
            accountId not in pendingReconciliations
        )

    def sendProtoOASymbolsListReq(includeArchivedSymbols=False, clientMsgId=None):
        if not isAccountInitialized(currentAccountId):
            logging.getLogger("flow").warning(
                        "Cannot fetch symbols yet — account %s not authorized or still reconciling",
                        currentAccountId
                    )
            returnToMenu()
            return

        request = ProtoOASymbolsListReq()
        request.ctidTraderAccountId = currentAccountId
        request.includeArchivedSymbols = bool(includeArchivedSymbols)
        deferred = client.send(request, clientMsgId=clientMsgId)
        deferred.addErrback(onError)


    def sendProtoOATraderReq(accountId, clientMsgId = None):

        if accountId not in authorizedAccounts:
            print(f"⛔ Cannot request trader info: account {accountId} not authorized.")
            return
        if accountId in pendingReconciliations:
            print(f"⏳ Cannot request trader info: reconciliation still pending for account {accountId}.")
            return
        print(f"📤 Requesting trader info for account: {accountId}")
        request = ProtoOATraderReq()
        request.ctidTraderAccountId = accountId
        deferred = client.send(request, clientMsgId = clientMsgId)
        deferred.addErrback(onError)



    def sendProtoOAUnsubscribeSpotsReq(symbolId, clientMsgId = None):
        global client
        request = ProtoOAUnsubscribeSpotsReq()
        request.ctidTraderAccountId = currentAccountId
        request.symbolId.append(int(symbolId))
        deferred = client.send(request, clientMsgId = clientMsgId)
        deferred.addErrback(onError)


    def sendProtoOASubscribeSpotsReq(symbolId, timeInSeconds=None, subscribeToSpotTimestamp=False, clientMsgId=None):
        global client
    
        symbolId = int(symbolId)

        if symbolId in subscribedSymbols:
            return  # Already subscribed — skip
        subscribedSymbols.add(symbolId)
        request = ProtoOASubscribeSpotsReq()
        request.ctidTraderAccountId = currentAccountId
        request.symbolId.append(symbolId)
        request.subscribeToSpotTimestamp = subscribeToSpotTimestamp
    
        deferred = client.send(request, clientMsgId=clientMsgId)
        deferred.addErrback(onError)


    def sendProtoOAReconcileReq(accountId, clientMsgId = None):
        global client
        request = ProtoOAReconcileReq()
        request.ctidTraderAccountId = accountId
        deferred = client.send(request, clientMsgId = clientMsgId)
        deferred.addErrback(onError)


    def startPositionPolling(interval=5.0):
        if not liveViewerActive:
            return  # Don't poll if viewer is off
        if currentAccountId in authorizedAccounts:
            sendProtoOAReconcileReq(currentAccountId)
        reactor.callLater(interval, startPositionPolling, interval)

    def sendProtoOAGetTrendbarsReq(weeks, period, symbolId, clientMsgId = None):
        global client
        request = ProtoOAGetTrendbarsReq()
        request.ctidTraderAccountId = currentAccountId
        request.period = ProtoOATrendbarPeriod.Value(period)
        request.fromTimestamp = int(calendar.timegm((datetime.datetime.utcnow() - datetime.timedelta(weeks=int(weeks))).utctimetuple())) * 1000
        request.toTimestamp = int(calendar.timegm(datetime.datetime.utcnow().utctimetuple())) * 1000
        request.symbolId = int(symbolId)
        deferred = client.send(request, clientMsgId = clientMsgId)
        deferred.addErrback(onError)

    def sendProtoOAGetTickDataReq(days, quoteType, symbolId, clientMsgId = None):
        global client
        request = ProtoOAGetTickDataReq()
        request.ctidTraderAccountId = currentAccountId
        request.type = ProtoOAQuoteType.Value(quoteType.upper())
        request.fromTimestamp = int(calendar.timegm((datetime.datetime.utcnow() - datetime.timedelta(days=int(days))).utctimetuple())) * 1000
        request.toTimestamp = int(calendar.timegm(datetime.datetime.utcnow().utctimetuple())) * 1000
        request.symbolId = int(symbolId)
        deferred = client.send(request, clientMsgId = clientMsgId)
        deferred.addErrback(onError)

    def sendProtoOANewOrderReq(symbolId, orderType, tradeSide, volume, price = None, clientMsgId = None):
        global client
        request = ProtoOANewOrderReq()
        request.ctidTraderAccountId = currentAccountId
        request.symbolId = int(symbolId)
        request.orderType = ProtoOAOrderType.Value(orderType.upper())
        request.tradeSide = ProtoOATradeSide.Value(tradeSide.upper())
        request.volume = int(volume) * 100
        if request.orderType == ProtoOAOrderType.LIMIT:
            request.limitPrice = float(price)
        elif request.orderType == ProtoOAOrderType.STOP:
            request.stopPrice = float(price)
        deferred = client.send(request, clientMsgId = clientMsgId)
        deferred.addErrback(onError)

    def sendNewMarketOrder(symbolId, tradeSide, volume, clientMsgId = None):
        global client
        sendProtoOANewOrderReq(symbolId, "MARKET", tradeSide, volume, clientMsgId = clientMsgId)

    def sendNewLimitOrder(symbolId, tradeSide, volume, price, clientMsgId = None):
        global client
        sendProtoOANewOrderReq(symbolId, "LIMIT", tradeSide, volume, price, clientMsgId)

    def sendNewStopOrder(symbolId, tradeSide, volume, price, clientMsgId = None):
        global client
        sendProtoOANewOrderReq(symbolId, "STOP", tradeSide, volume, price, clientMsgId)

    def sendProtoOAClosePositionReq(positionId, volume, clientMsgId = None):
        global client
        request = ProtoOAClosePositionReq()
        request.ctidTraderAccountId = currentAccountId
        request.positionId = int(positionId)
        # convert lots -> centi-lots with rounding, not truncation
        request.volume = int(round(float(volume) * 100))
        deferred = client.send(request, clientMsgId = clientMsgId)
        deferred.addErrback(onError)



    
    def sendProtoOACancelOrderReq(orderId: int, clientMsgId=None):
        log = logging.getLogger("cancel_order")
        if not log.handlers:
            log.setLevel(logging.DEBUG)
            fh = logging.FileHandler("cancel_order_debug.log", encoding="utf-8")
            fh.setFormatter(logging.Formatter("%(asctime)s [%(levelname)s] %(message)s"))
            log.addHandler(fh)
    
        # 🚫 debounce duplicate cancels
        if orderId in inFlightCancels:
            # Already in flight — just extend the tombstone a bit and bail.
            cancelTombstones[orderId] = time() + 12.0
            return
        inFlightCancels.add(orderId)
    
        o = ordersById.get(orderId)
        snapshot = {}
        if o:
            try:
                snapshot = {
                    "orderId": getattr(o, "orderId", None),
                    "type": getattr(o, "orderType", None),
                    "status": getattr(o, "orderStatus", None),
                    "symbolId": getattr(o, "symbolId", getattr(getattr(o, "tradeData", None) or (), "symbolId", None)),
                    "limitPrice": getattr(o, "limitPrice", None),
                    "stopPrice": getattr(o, "stopPrice", None),
                }
            except Exception:
                pass
        log.info("Sending cancel for order %s | snapshot=%s", orderId, snapshot)
    
        # Optimistic UI removal + tombstone
        ordersById.pop(orderId, None)
        cancelTombstones[orderId] = time() + 12.0
        if is_live_viewer_active():
            reactor.callFromThread(_request_render)
    
        request = ProtoOACancelOrderReq()
        request.ctidTraderAccountId = currentAccountId
        request.orderId = int(orderId)
    
        d = client.send(request, clientMsgId=clientMsgId)
    
        # If your client.send doesn’t already set a timeout, make this more forgiving
        try:
            d.addTimeout(15, reactor)  # no-op if already timed by library
        except Exception:
            pass
    
        def _ok(res):
            log.info("Cancel OK for order %s: %s", orderId, type(res).__name__)
            inFlightCancels.discard(orderId)
            # We can drop the tombstone now; server confirmed cancel.
            cancelTombstones.pop(orderId, None)
            # Double reconcile to converge UI
            reactor.callLater(0.2, lambda: runWhenReady(sendProtoOAReconcileReq, currentAccountId))
            reactor.callLater(1.0, lambda: runWhenReady(sendProtoOAReconcileReq, currentAccountId))
            return res
    
        def _err(failure):
            inFlightCancels.discard(orderId)
            log.error("Cancel ERROR for order %s: %s", orderId, failure)
            logging.error("❌ Cancel failed for order %s: %s", orderId, failure)
    
            # If this was only a timeout, keep tombstone longer and try to converge
            if failure.check(TwistedTimeoutError):
                # keep it hidden a bit longer; server may still process it
                cancelTombstones[orderId] = time() + 20.0
                # multiple reconciles to catch late ORDER_CANCEL/EXECUTION
                reactor.callLater(0.6, lambda: runWhenReady(sendProtoOAReconcileReq, currentAccountId))
                reactor.callLater(2.0, lambda: runWhenReady(sendProtoOAReconcileReq, currentAccountId))
                # one best-effort retry after a short delay (idempotent server-side)
                reactor.callLater(0.8, lambda: runWhenReady(sendProtoOACancelOrderReq, orderId))
                return
    
            # Non-timeout error: let reconcile rehydrate if needed, but remove tombstone
            cancelTombstones.pop(orderId, None)
            runWhenReady(sendProtoOAReconcileReq, currentAccountId)
            onError(failure)
    
        d.addCallback(_ok)
        d.addErrback(_err)

    def sendProtoOADealOffsetListReq(dealId, clientMsgId=None):
        global client
        request = ProtoOADealOffsetListReq()
        request.ctidTraderAccountId = currentAccountId
        request.dealId = int(dealId)
        deferred = client.send(request, clientMsgId=clientMsgId)
        deferred.addErrback(onError)

    def waitUntilAllPositionPrices(callback, max_wait=1.0, check_interval=0.1):
        symbolIds = {pos.tradeData.symbolId for pos in positionsById.values()}
        attempts = int(max_wait / check_interval)

        def check(remaining):
            missing = [sid for sid in symbolIds if sid not in symbolIdToPrice]
            if not missing:
                callback()
            elif remaining <= 0:
                logging.getLogger("prices").warning("Timeout waiting for all spot prices.")
                callback()
            else:
                reactor.callLater(check_interval, check, remaining - 1)

        check(attempts)


    def remove_position(pos_id):
        global selected_position_index, view_offset
    
        if pos_id in positionsById:
            # get symbol for potential unsubscribe
            symbol_id = positionsById[pos_id].tradeData.symbolId
    
            positionsById.pop(pos_id, None)
            positionPnLById.pop(pos_id, None)

    
            # NEW: if no positions left for this symbol, unsubscribe
            still_used = any(p.tradeData.symbolId == symbol_id for p in positionsById.values())
            if not still_used:
                try:
                    sendProtoOAUnsubscribeSpotsReq(symbol_id)
                    subscribedSymbols.discard(symbol_id)
                except Exception:
                    pass  # best-effort
    
            H.mark_positions_dirty()
    
            # selection / viewport housekeeping (unchanged)
            total = len(H.ordered_positions())
            if total == 0:
                selected_position_index = 0
                view_offset = 0
            elif selected_position_index >= total:
                selected_position_index = total - 1
    
            term_height = console.size.height
            max_rows = term_height - 8
            if selected_position_index < view_offset:
                view_offset = selected_position_index
            elif selected_position_index >= view_offset + max_rows:
                view_offset = max(0, selected_position_index - max_rows + 1)
    
            printLivePnLTable()
    #
   

    def is_live_viewer_active() -> bool:
        return liveViewerActive


    # --- add near other helpers ---
    def _move_positions_selection(delta: int):
        """Move selection in positions panel, preserve viewport logic."""
        global selected_position_index, view_offset
        ops = H.ordered_positions()
        n = len(ops)
        if n == 0:
            return
        selected_position_index = (selected_position_index + delta) % n
        term_height = console.size.height
        max_rows = term_height - 8
        if selected_position_index < view_offset:
            view_offset = selected_position_index
        elif selected_position_index >= view_offset + max_rows:
            view_offset = selected_position_index - max_rows + 1
        reactor.callFromThread(_request_render)
    
    def _move_orders_selection(delta: int):
        """Move selection in orders panel; UI clamps on render."""
        global selected_order_index
        selected_order_index = max(0, selected_order_index + delta)
        reactor.callFromThread(_request_render)


#     def _close_selected_position():
#         sel = H.safe_current_selection(selected_position_index)
#         if not sel:
#             return
#         pos_id, pos = sel
#         volume_units = pos.tradeData.volume
#     
#         # ✉️ immediate UI toast so the user sees feedback for the hotkey
#         push_info(f"Close sent for Record {pos_id}…")
#     
#         reactor.callFromThread(sendProtoOAClosePositionReq, pos_id, volume_units / 100)
#         reactor.callFromThread(remove_position, pos_id)
#     
#         # a couple of reconciles to converge even if server acks late
#         reactor.callLater(0.6, lambda: runWhenReady(sendProtoOAReconcileReq, currentAccountId))
#         reactor.callLater(1.8, lambda: runWhenReady(sendProtoOAReconcileReq, currentAccountId))
# 


    def _orders_for_view():
        now = time()
        out = []
        for o in ordersById.values():
            # Hide if tombstoned
            oid = getattr(o, "orderId", None)
            if oid in cancelTombstones and cancelTombstones[oid] > now:
                continue
    
            # Hide MARKET orders from the "Active Pending" table
            otype = getattr(o, "orderType", None)
            if otype == ProtoOAOrderType.MARKET:
                continue
    
            # Hide terminal states (belt & suspenders)
            status = getattr(o, "orderStatus", None)
            try:
                sname = ProtoOAOrderStatus.Name(status)
            except Exception:
                sname = ""
            if sname in {"ORDER_STATUS_FILLED", "ORDER_STATUS_CANCELED", "ORDER_STATUS_EXPIRED"}:
                continue
    
            out.append(o)
        return out



    # ui code (e.g., live table key handler)
    def _close_selected_position():
        sel = H.safe_current_selection(selected_position_index)
        if not sel:
            return
    
        pos_id, pos = sel
        volume_units = pos.tradeData.volume
    
        # Immediate UI feedback
        push_info(f"Close sent for Record {pos_id}…")
    
        # 🔇 Arm echo suppression where the handler looks for it (ctx)
        if not hasattr(ctx, "pendingCloseEcho"):
            ctx.pendingCloseEcho = {}
        ctx.pendingCloseEcho[int(pos_id)] = time() + 8.0   # NOTE: use time(), not time.time()

        # 🪦 tombstone so reconcile won’t re-add the row while server is catching up
        ctx.closeTombstones[int(pos_id)] = time() + 12.0   # 10–20s is fine
    
        reactor.callFromThread(sendProtoOAClosePositionReq, pos_id, volume_units / 100)
        reactor.callFromThread(remove_position, pos_id)
        closeTombstonesPositions[pos_id] = time() + 12.0  # keep it hidden briefly
    
        reactor.callLater(0.6,  lambda: runWhenReady(sendProtoOAReconcileReq, currentAccountId))
        reactor.callLater(1.8,  lambda: runWhenReady(sendProtoOAReconcileReq, currentAccountId))

    def _cancel_process_next():
        # Nothing to do or we’re already sending one
        if not _cancel_queue or _cancel_inflight:
            reactor.callLater(0.05, _cancel_process_next)
            return
    
        oid, _ = _cancel_queue.popleft()
    
        # Maybe resolved meanwhile (no tombstone -> don’t send)
        if oid in _cancel_inflight or oid not in cancelTombstones:
            reactor.callLater(CANCEL_SPACING_SEC, _cancel_process_next)
            return
    
        _cancel_inflight.add(oid)
    
        req = ProtoOACancelOrderReq()
        req.ctidTraderAccountId = currentAccountId
        req.orderId = int(oid)
        d = client.send(req)
    
        # --- proper closures over this oid ---
        def _ok(res, oid=oid):
            inFlightCancels.discard(oid)
            _cancel_inflight.discard(oid)
            cancelTombstones.pop(oid, None)
            _cancel_retries.pop(oid, None)
    
            # converge to server truth
            reactor.callLater(0.2, lambda: runWhenReady(sendProtoOAReconcileReq, currentAccountId))
            reactor.callLater(0.9, lambda: runWhenReady(sendProtoOAReconcileReq, currentAccountId))
            reactor.callLater(CANCEL_SPACING_SEC, _cancel_process_next)
            return res
    
        def _err(failure, oid=oid):
            _cancel_inflight.discard(oid)
            inFlightCancels.discard(oid)
    
            if failure.check(TwistedTimeoutError):
                # Likely processed server-side; keep it hidden and retry a bit
                cancelTombstones[oid] = time() + CANCEL_TOMBSTONE_SEC
                tries = _cancel_retries.get(oid, 0)
                if tries < CANCEL_MAX_RETRIES:
                    _cancel_retries[oid] = tries + 1
                    backoff = CANCEL_BACKOFF_BASE * (2 ** tries)
                    reactor.callLater(backoff, lambda: _enqueue_cancel(oid))
            else:
                # Real error: show again and let reconcile resync
                cancelTombstones.pop(oid, None)
    
            reactor.callLater(0.3, lambda: runWhenReady(sendProtoOAReconcileReq, currentAccountId))
            reactor.callLater(CANCEL_SPACING_SEC, _cancel_process_next)
    
        d.addCallbacks(_ok, _err)

    def _enqueue_cancel(order_id: int):
        # Don’t enqueue duplicates; extend tombstone window if already on screen
        if order_id in _cancel_inflight:
            return
        # Put a short tombstone if not present so reconcile won’t re-add
        cancelTombstones.setdefault(order_id, time() + 12.0)
        _cancel_queue.append((order_id, time()))
        reactor.callLater(0, _cancel_process_next)
 
 
    def _cancel_focused_order() -> None:
        row_idx = selected_order_index - view_offset_orders
        if row_idx < 0 or row_idx >= len(last_visible_order_ids):
            return
        order_id = last_visible_order_ids[row_idx]
        if not order_id:
            return
    
        if order_id in inFlightCancels or order_id in _cancel_inflight:
            push_info(f"Order {order_id} cancellation already in progress…")
            return
    
        # optimistic removal + tombstone (short; scheduler may extend)
        ordersById.pop(order_id, None)
        cancelTombstones[order_id] = time() + 12.0
        inFlightCancels.add(order_id)
        push_info(f"Canceling order {order_id}…")
        if is_live_viewer_active():
            reactor.callFromThread(_request_render)
    
        # enqueue actual send (serialized)
        _enqueue_cancel(order_id)
    
        # a couple of reconciles to converge even if we timeout
        reactor.callLater(0.4, lambda: runWhenReady(sendProtoOAReconcileReq, currentAccountId))
        reactor.callLater(1.2, lambda: runWhenReady(sendProtoOAReconcileReq, currentAccountId))

    
    def set_live_viewer_active(val: bool) -> None:
        global liveViewerActive
        liveViewerActive = bool(val)
    
    def get_current_account_id() -> Optional[int]:
        return currentAccountId



    # --- keys / predicates ---
    KEY_ESC = "\x1b"
    KEY_BS  = "\x7f"
    KEY_ENTERS = ("\r", "\n")
    NUMERIC_CHARS = "0123456789.-"
    
    def is_esc(k: str) -> bool: return k == KEY_ESC
    def is_backspace(k: str) -> bool: return k == KEY_BS
    def is_enter(k: str) -> bool: return k in KEY_ENTERS
    def is_numeric(k: str) -> bool: return k in NUMERIC_CHARS
    
    # --- SL state predicates ---
    def sl_is_idle(sl: dict) -> bool: return sl.get("mode") == "idle"
    def sl_is_armed(sl: dict) -> bool: return sl.get("mode") == "armed"
    def sl_is_typing(sl: dict) -> bool: return sl.get("mode") == "typing"
    
    # --- SL actions (pure helpers; no globals) ---
    def sl_arm_on_current(sl: dict, selected_index: int, safe_current_selection, request_render) -> bool:
        sel = safe_current_selection(selected_index)
        if not sel:
            return False
        pid, _ = sel
        sl.update({"mode": "armed", "positionId": pid, "buffer": ""})
        request_render()
        return True
    
    def sl_cancel(sl: dict, request_render) -> None:
        sl.update({"mode": "idle", "positionId": None, "buffer": ""})
        request_render()
    
    def sl_begin_typing(sl: dict, selected_index: int, first_char: str, safe_current_selection, request_render) -> None:
        sel = safe_current_selection(selected_index)
        if not sel:
            return
        pid, _ = sel
        sl.update({"mode": "typing", "positionId": pid, "buffer": first_char})
        request_render()
    
    def sl_append_char(sl: dict, ch: str, request_render) -> None:
        sl["buffer"] += ch
        request_render()
    
    def sl_backspace(sl: dict, request_render) -> None:
        sl["buffer"] = sl["buffer"][:-1]
        request_render()
    
    def sl_commit_if_number(sl: dict, sl_by_pid: dict, request_render) -> None:
        try:
            val = float(sl["buffer"].strip())
            sl_by_pid[sl["positionId"]] = abs(val)
        except Exception:
            pass
        sl_cancel(sl, request_render)
 


    def _focused_order_id() -> Optional[int]:
        row_idx = selected_order_index - view_offset_orders
        if 0 <= row_idx < len(last_visible_order_ids):
            return last_visible_order_ids[row_idx]
        return None
    
    def order_is_limit(o) -> bool:
        try:
            return getattr(o, "orderType", None) == ProtoOAOrderType.LIMIT
        except Exception:
            return False
    
    def order_is_stop(o) -> bool:
        try:
            return getattr(o, "orderType", None) == ProtoOAOrderType.STOP
        except Exception:
            return False
    

    def order_current_target(o) -> Optional[float]:
        """Return the pending order's target, ignoring zeros and checking tradeData."""
        if not o:
            return None
        td = getattr(o, "tradeData", None)
    
        def first_nonzero(*vals):
            for v in vals:
                try:
                    if v is not None and float(v) != 0.0:
                        return float(v)
                except Exception:
                    pass
            return None
    
        return first_nonzero(
            getattr(o,  "limitPrice", None),
            getattr(o,  "stopPrice",  None),
            getattr(o,  "price",      None),
            getattr(td, "limitPrice", None) if td else None,
            getattr(td, "stopPrice",  None) if td else None,
            getattr(td, "price",      None) if td else None,
        )


    
    # ---- order edit state predicates ----
    def ord_is_idle(s: dict) -> bool: return s.get("mode") == "idle"
    def ord_is_armed(s: dict) -> bool: return s.get("mode") == "armed"
    def ord_is_typing(s: dict) -> bool: return s.get("mode") == "typing"
    
    # ---- order edit actions ----
    def ord_arm_on_current(s: dict, get_focused_id, request_render) -> bool:
        oid = get_focused_id()
        if not oid: 
            return False
        s.update({"mode": "armed", "orderId": oid, "buffer": ""})
        request_render()
        return True
    
    def ord_cancel(s: dict, request_render) -> None:
        s.update({"mode": "idle", "orderId": None, "buffer": ""})
        request_render()
    
    def ord_begin_typing(s: dict, first_char: str, request_render) -> None:
        s.update({"mode": "typing", "buffer": first_char})
        request_render()
    
    def ord_append_char(s: dict, ch: str, request_render) -> None:
        s["buffer"] += ch
        request_render()
    
    def ord_backspace(s: dict, request_render) -> None:
        s["buffer"] = s["buffer"][:-1]
        request_render()
    
    def ord_commit_if_number(s: dict, request_render) -> None:
        try:
            new_px = float(s["buffer"].strip())
            if not s.get("orderId"):
                ord_cancel(s, request_render); return
            sendProtoOAModifyOrderReq(s["orderId"], new_px)
            # ask server for a quick refresh after the modify
            reactor.callLater(0.5, lambda: runWhenReady(sendProtoOAReconcileReq, currentAccountId))
        except Exception:
            pass
        ord_cancel(s, request_render)



    def listen_for_keys() -> None:
        global selected_position_index, liveViewerActive, slInput, slByPositionId
        global selected_order_index, view_offset_orders, focused_panel, last_visible_order_ids
        global view_offset  # positions viewport
    
        # Prefer the controlling TTY so we don't compete with input()/inputimeout()
        try:
            tty_in = open('/dev/tty', 'rb', buffering=0)
        except Exception:
            tty_in = sys.stdin  # fallback if /dev/tty is unavailable (e.g., some containers)
    
        fd = tty_in.fileno()
        old_settings = termios.tcgetattr(fd)
        shutdown.set_tty_old_settings(old_settings)
    
        try:
            tty.setcbreak(fd)
                # ----- main loop -----
            while liveViewerActive:
                try:
                    r, _, _ = select.select([tty_in], [], [], 0.1)  # 100ms poll
                    if not r:
                        continue
                    b = tty_in.read(1)
                    if not b:
                        continue
                    key = b.decode('utf-8', errors='ignore')
    
                    # ----------------- SL input state machine (unchanged) -----------------
                    request_render = lambda: reactor.callFromThread(_request_render)
                   
                    # ----------------- SL input state machine (via helpers) -----------------
                    if sl_is_armed(slInput):
                        if key == "j":
                            _move_positions_selection(+1); continue
                        elif key == "k":
                            _move_positions_selection(-1); continue
                        elif is_esc(key):
                            sl_cancel(slInput, request_render); continue
                        elif is_numeric(key):
                            sl_begin_typing(
                                slInput, selected_position_index, key,
                                H.safe_current_selection, request_render
                            ); continue
    
                    elif sl_is_typing(slInput):
                        if is_enter(key):
                            sl_commit_if_number(slInput, slByPositionId, request_render); continue
                        elif is_esc(key):
                            sl_cancel(slInput, request_render); continue
                        elif is_backspace(key):
                            sl_backspace(slInput, request_render); continue
                        elif is_numeric(key):
                            sl_append_char(slInput, key, request_render); continue
                        else:
                            continue  # swallow everything else while typing
    
                    # start SL input
                    if key == "y" and sl_is_idle(slInput):
                        sl_arm_on_current(
                            slInput, selected_position_index,
                            H.safe_current_selection, request_render
                        )
                        continue
                    # ----------------------------------------------------------------------
    
                    # -------- normal hotkeys (panel-aware) --------
                    if key == "q":
                        liveViewerActive = False
                        reactor.callFromThread(getattr(live, "stop", lambda: None))
                        print("👋 Exiting Live PnL Viewer...")
                        reactor.callLater(0.5, executeUserCommand)
                        break
    
                    elif key == "\t" or key == "o":   # TAB or 'o' to toggle focus
                        focused_panel = "orders" if focused_panel == "positions" else "positions"
                        reactor.callFromThread(_request_render)
   

                    elif key == "j":
                        if focused_panel == "orders":
                            _move_orders_selection(+1)
                        else:
                            _move_positions_selection(+1)
                        continue
                    
                    elif key == "k":
                        if focused_panel == "orders":
                            _move_orders_selection(-1)
                        else:
                            _move_positions_selection(-1)
                        continue

                    # --- order inline edit state machine (panel must be 'orders') ---
                    if focused_panel == "orders":
                        if ord_is_armed(orderEdit):
                            if key == "j":
                                _move_orders_selection(+1); continue
                            elif key == "k":
                                _move_orders_selection(-1); continue
                            elif is_esc(key):
                                ord_cancel(orderEdit, request_render); continue
                            elif is_numeric(key):
                                ord_begin_typing(orderEdit, key, request_render); continue
                    
                        elif ord_is_typing(orderEdit):
                            if is_enter(key):
                                ord_commit_if_number(orderEdit, request_render); continue
                            elif is_esc(key):
                                ord_cancel(orderEdit, request_render); continue
                            elif is_backspace(key):
                                ord_backspace(orderEdit, request_render); continue
                            elif is_numeric(key):
                                ord_append_char(orderEdit, key, request_render); continue
                            else:
                                continue  # swallow others while typing
                    
                        # start order edit
                        if key == "e" and ord_is_idle(orderEdit):
                            if ord_arm_on_current(orderEdit, _focused_order_id, request_render):
                                continue
                    # ----------------------------------------------------------------
                    #  
                    if key == "x":
                        if focused_panel == "orders":
                            _cancel_focused_order()
                            reactor.callLater(1.0, lambda: runWhenReady(sendProtoOAReconcileReq, currentAccountId))
                        else:
                            _close_selected_position()
                    elif key == "\r":
                        if focused_panel == "orders":
                            # optional: show order details for the focused order
                            row_idx = selected_order_index - view_offset_orders
                            if 0 <= row_idx < len(last_visible_order_ids):
                                oid = last_visible_order_ids[row_idx]
                                if oid:
                                    reactor.callFromThread(sendProtoOAOrderDetailsReq, oid)
                        else:
                            # existing placeholder for position details
                            sel = H.safe_current_selection(selected_position_index)
                            if sel:
                                pos_id, pos = sel
                                # you can plug in a details view here if desired
                                pass
    
                    # (any other keys fall through silently)
    
                except Exception as e:
                    logging.error("Key thread error: %s\n%s", e, traceback.format_exc())
                    # keep the loop alive
        finally:
            try:
                termios.tcsetattr(fd, termios.TCSADRAIN, old_settings)
            finally:
                shutdown.clear_tty_old_settings()
                try:
                    if tty_in is not sys.stdin:
                        tty_in.close()
                except Exception:
                    pass
    
    def choosePositionFromLiveList():
        choices = []
        for posId, pos in positionsById.items():
            symbol_id = pos.tradeData.symbolId
            symbol_name = symbolIdToName.get(symbol_id, f"ID:{symbol_id}")
            choices.append((posId, f"{posId} — {symbol_name}"))
    
        result = radiolist_dialog(
            title="🎯 Select Position",
            text="Use ↑ ↓ to move, [Enter] to select, [Esc] to cancel",
            values=choices,
        ).run()
    
        if result:
            print(f"\n✅ You selected position: {result}")
            volume_units = positionsById[result].tradeData.volume
            runWhenReady(sendProtoOAClosePositionReq, result, volume_units / 100)
        else:
            print("\n❌ No selection made.")


    def startPnLUpdateLoop(interval=0.5):
        if not currentAccountId or currentAccountId not in authorizedAccounts:
            log_flow.warning("⚠️ Cannot start PnL loop – account not ready.")
            return
        if not liveViewerActive:
            return
        sendProtoOAGetPositionUnrealizedPnLReq()
        reactor.callLater(interval, startPnLUpdateLoop, interval)



    def sendProtoOAGetPositionUnrealizedPnLReq(clientMsgId=None):
        global client

        request = ProtoOAGetPositionUnrealizedPnLReq()
        request.ctidTraderAccountId = currentAccountId

#         print("📤 Sending Unrealized PnL request (no position IDs needed)...")

        deferred = client.send(request, clientMsgId=clientMsgId)
        deferred.addErrback(onError)

    def sendProtoOAOrderDetailsReq(orderId, clientMsgId=None):
        global client
        request = ProtoOAOrderDetailsReq()
        request.ctidTraderAccountId = currentAccountId
        request.orderId = int(orderId)
        deferred = client.send(request, clientMsgId=clientMsgId)
        deferred.addErrback(onError)


    def sendProtoOAOrderListByPositionIdReq(positionId, fromTimestamp=None, toTimestamp=None, clientMsgId=None):
        global client
        request = ProtoOAOrderListByPositionIdReq()
        request.ctidTraderAccountId = currentAccountId
        request.positionId = int(positionId)

        # Default to full range if not provided
        if fromTimestamp is None:
            fromTimestamp = 0
        if toTimestamp is None:
            toTimestamp = int(calendar.timegm(datetime.datetime.utcnow().utctimetuple())) * 1000

        request.fromTimestamp = int(fromTimestamp)
        request.toTimestamp = int(toTimestamp)

        deferred = client.send(request, clientMsgId=clientMsgId)
        deferred.addErrback(onError)


    tickFetchQueue = set()

    def subscribeToSymbolsFromOpenPositions(duration=None):
        seen = set()
        for pos in positionsById.values():
            sid = pos.tradeData.symbolId
            if sid not in seen:
                seen.add(sid)
                sendProtoOASubscribeSpotsReq(sid, timeInSeconds=duration)


    
    def _order_symbol_id(o):
        sid = getattr(o, "symbolId", None)
        if sid in (None, 0, "", "0"):
            td = getattr(o, "tradeData", None)
            sid = getattr(td, "symbolId", sid)
        try:
            return int(sid) if sid not in (None, "") else None
        except Exception:
            return None
    
    def subscribeToSymbolsFromActiveOrders():
        # use robust extractor
        sids = { _order_symbol_id(o) for o in ordersById.values() }
        sids = { sid for sid in sids if sid is not None }
    
        for sid in sids:
            if sid not in subscribedSymbols:
                sendProtoOASubscribeSpotsReq(sid)
    
        def fetch_missing_ticks():
            for sid in sids:
                if sid not in symbolIdToPrice:
                    # either side works, just need one to seed Market/Dist
                    sendProtoOAGetTickDataReq(1, "BID", sid)
    
        reactor.callLater(0.5, fetch_missing_ticks)

    def launchLivePnLViewer():
        global liveViewerActive, live, selected_position_index, view_offset, liveLaunchInProgress
        global selected_order_index, view_offset_orders, last_visible_order_ids, focused_panel
        if liveLaunchInProgress:
             log_flow.info("⏳ Live viewer is already starting...")
             return

        liveViewerActive = True

        liveViewerActive = True
        startPositionPolling(5.0)
    
        log_flow.info("🔃 Subscribing to spot prices for open positions…")
        subscribeToSymbolsFromOpenPositions()
        subscribeToSymbolsFromActiveOrders()
    
        (
            view,
            selected_position_index,
            view_offset,
            selected_order_index,
            view_offset_orders,
            last_visible_order_ids,
        ) = H.buildLivePnLView(
            console_height=console.size.height,
            orders=_orders_for_view(),
            positions_sorted=H.ordered_positions(),
            selected_index=selected_position_index,
            view_offset=view_offset,
            symbolIdToName=symbolIdToName,
            symbolIdToDetails=symbolIdToDetails,
            symbolIdToPrice=symbolIdToPrice,
            positionPnLById=positionPnLById,
            error_messages=_messages_for_view(),
            slByPositionId=slByPositionId,
            account_currency=get_account_ccy(),
            orders_selected_index=selected_order_index,
            orders_view_offset=view_offset_orders,
            focused_panel=focused_panel,
            order_edit_state=orderEdit,
        )
    
        live = Live(view, refresh_per_second=20, screen=True, console=console, auto_refresh=False)
        live.start()
    
        sendProtoOAGetPositionUnrealizedPnLReq()
        startPnLUpdateLoop(0.3)
        threading.Thread(target=listen_for_keys, daemon=True).start()

    def printActiveOrdersOnce():
        t = H.make_pending_orders_table(
            orders=_orders_for_view(),
            symbolIdToName=symbolIdToName,
            account_currency=get_account_ccy(),
        )
        Console().print(t)
    
    def is_order_active(status: int) -> bool:
        try:
            name = ProtoOAOrderStatus.Name(status)
        except Exception:
            return False
        # Keep anything that is not terminal
        return name not in {"ORDER_STATUS_FILLED", "ORDER_STATUS_CANCELED", "ORDER_STATUS_EXPIRED"}


    def printUpdatedPriceBoard():
        logging.info("📊 Updated Spot Prices:")
        missing = []
    
        # show only the symbols we're actually subscribed to
        for symbolId in sorted(subscribedSymbols):
            name = symbolIdToName.get(symbolId, f"ID:{symbolId}")
            bid_ask = symbolIdToPrice.get(symbolId)
            if bid_ask:
                bid, ask = bid_ask
                if bid == 0 or ask == 0:
                    logging.warning(" - %s (ID: %s) — ⚠️ Price: 0.0 — retrying...", name, symbolId)
                    missing.append(symbolId)
                else:
                    logging.info(" - %s (ID: %s) — Bid: %s, Ask: %s", name, symbolId, bid, ask)
            else:
                logging.info(" - %s (ID: %s) — Price: [pending]", name, symbolId)
                missing.append(symbolId)
    
        if missing:
            logging.info("⏳ Retrying %s missing prices...", len(missing))
            for i, sid in enumerate(missing):
                reactor.callLater(i * 0.05, sendProtoOAGetTickDataReq, 1, "BID", sid)
            reactor.callLater(3, printUpdatedPriceBoard)
        else:
            return None


    menu = {
        "1": ("List Accounts", sendProtoOAGetAccountListByAccessTokenReq),
        "2": ("Set Account", setAccount),
        "3": ("Version Info", sendProtoOAVersionReq),
        "4": ("List Assets", sendProtoOAAssetListReq),
        "5": ("List Asset Classes", sendProtoOAAssetClassListReq),
        "6": ("List Symbol Categories", sendProtoOASymbolCategoryListReq),
        "7": ("Show Price Board", printUpdatedPriceBoard),  # <-- new label & function
        "8": ("Trader Info", sendProtoOATraderReq),
        "9": ("Subscribe to Spot", sendProtoOASubscribeSpotsReq),
        "10": ("Reconcile (Show Positions)", lambda: sendProtoOAReconcileReq(currentAccountId)),
        "11": ("Get Trendbars", sendProtoOAGetTrendbarsReq),
        "12": ("Get Tick Data", sendProtoOAGetTickDataReq),
        "13": ("New Market Order", sendNewMarketOrder),
        "14": ("New Limit Order", sendNewLimitOrder),
        "15": ("New Stop Order", sendNewStopOrder),
        "16": ("Close Position", sendProtoOAClosePositionReq),
        "17": ("Cancel Order", sendProtoOACancelOrderReq),
        "18": ("Deal Offset List", sendProtoOADealOffsetListReq),
        "19": (
            "Unrealized PnL (Live Viewer)",
            lambda: runWhenReady(launchLivePnLViewer)
        ),
        "20": ("Order Details", sendProtoOAOrderDetailsReq),
        "21": ("Orders by Position ID", sendProtoOAOrderListByPositionIdReq),
        "22": ("Help", showHelp),
        "23": ("List Active Orders", printActiveOrdersOnce),   # ✅ FIXED
    }
    commands = {v[0].replace(" ", ""): v[1] for v in menu.values()}



def ensureAccountSet():
    if not currentAccountId:
        print("⚠️ Please set a valid account first using option 2.")
        return False
    if not isAccountReady(currentAccountId):
        print(f"⚠️ Account {currentAccountId} is not fully ready yet. Please wait for trader info.")
        return False
    return True

def isAccountReady(accountId):
    return (
        accountId in authorizedAccounts
        and accountId not in pendingReconciliations
    )



def waitUntilAccountReady(accountId, callback, interval=0.5):
    if isAccountReady(accountId):
        print(f"✅ Account {accountId} is now ready.")
        callback()
    else:
        print(f"⏳ Waiting for account {accountId} to be ready...")
        reactor.callLater(interval, waitUntilAccountReady, accountId, callback, interval)


def runWhenReady(fn, *args, **kwargs):
    def call():
        fn(*args, **kwargs)
    waitUntilAccountReady(currentAccountId, call)


def set_current_account_id(val: int) -> None:
    global currentAccountId
    currentAccountId = val




ctx = SimpleNamespace(
    sendProtoOAModifyOrderReq=sendProtoOAModifyOrderReq,
    pendingCloseEcho={},
    cancelTombstones=cancelTombstones,          # (orders)
    closeTombstones=closeTombstonesPositions,
    is_live_viewer_active=is_live_viewer_active,
    set_live_viewer_active=set_live_viewer_active,
    get_current_account_id=get_current_account_id,
    set_current_account_id=set_current_account_id,
    request_render=_request_render,
    ordersById=ordersById,
    update_pnl_cache_for_symbol=_update_pnl_cache_for_symbol,
    # shared state
    accountMetadata=accountMetadata,
    sendProtoOASymbolsListReq=sendProtoOASymbolsListReq,
    pendingReconciliations=pendingReconciliations,
    symbolIdToName=symbolIdToName,
    symbolIdToPrice=symbolIdToPrice,
    symbolIdToPips=symbolIdToPips,
    subscribedSymbols=subscribedSymbols,
    expectedSpotSubscriptions=expectedSpotSubscriptions,
    receivedSpotConfirmations=receivedSpotConfirmations,
    positionsById=positionsById,
    positionPnLById=positionPnLById,
    showStartupOutput=showStartupOutput,
    liveViewerActive=liveViewerActive,
    symbolIdToDetails=symbolIdToDetails,
    currentAccountId=currentAccountId,
    selected_position_index=selected_position_index,
    error_messages=error_messages,
    view_offset=view_offset,
    slByPositionId=slByPositionId,
    accountTraderInfo=accountTraderInfo,
    availableAccounts=availableAccounts,
    authorizedAccounts=authorizedAccounts,
    authInProgress=authInProgress,
    envAccountIds=envAccountIds,
    subscribeToSymbolsFromActiveOrders=subscribeToSymbolsFromActiveOrders,

    # functions used by handlers
    printLivePnLTable=printLivePnLTable,
    printUpdatedPriceBoard=printUpdatedPriceBoard,
    returnToMenu=returnToMenu,
    runWhenReady=runWhenReady,
    isAccountInitialized=isAccountInitialized,
    remove_position=remove_position,
    add_position=add_position,
    log_exec_event_error=log_exec_event_error,
    get_account_ccy=get_account_ccy,
    push_info=push_info,

    sendProtoOASubscribeSpotsReq=sendProtoOASubscribeSpotsReq,
    sendProtoOAUnsubscribeSpotsReq=sendProtoOAUnsubscribeSpotsReq,
    sendProtoOAGetTickDataReq=sendProtoOAGetTickDataReq,
    sendProtoOAGetPositionUnrealizedPnLReq=sendProtoOAGetPositionUnrealizedPnLReq,
    sendProtoOAReconcileReq=sendProtoOAReconcileReq,
    sendProtoOATraderReq=sendProtoOATraderReq,
    sendProtoOAOrderDetailsReq=sendProtoOAOrderDetailsReq,
    sendProtoOAClosePositionReq=sendProtoOAClosePositionReq,
    sendProtoOAGetAccountListByAccessTokenReq=sendProtoOAGetAccountListByAccessTokenReq,
    fetchTraderInfo=fetchTraderInfo,
    setAccount=setAccount,
    promptUserToSelectAccount=promptUserToSelectAccount,

    reactor=reactor,

    # minimal stub used by on_execution handler
)


def onMessageReceived(client, message):
    if liveViewerActive:
        with H.suppress_stdout(liveViewerActive):
            dispatch_message(client, message, ctx)
    else:
        dispatch_message(client, message, ctx)


def executeUserCommand():
    global menuScheduled
    if liveViewerActive:
        # Safety: never prompt while viewer is active
        menuScheduled = False
        return
    if menuScheduled:
        return  # 👈 Prevent multiple overlapping menu renderings
    menuScheduled = True
    print(f"📌 Active Account ID: {currentAccountId}")
    print("\nMenu Options:")
    for key, (desc, _) in sorted(menu.items(), key=lambda x: int(x[0])):
        print(f" {key}. {desc}")
    print("Or type command name directly (e.g. help, NewMarketOrder, etc.)")

    try:
        userInput = inputimeout("Select option or type command: ", timeout=20).strip()
    except TimeoutOccurred:
        print("⏱️ Timeout – no input detected.")
        menuScheduled = False
        reactor.callLater(3, executeUserCommand)
        return
    menuScheduled = False

    if userInput not in ["1", "2"] and not ensureAccountSet():
        returnToMenu()
        return

    # If it's a menu number
    if userInput in menu:
        desc, func = menu[userInput]
        try:
            if desc == "Set Account":
                if not availableAccounts:
                    print("⚠️ No accounts available. Use option 1 to fetch them first.")
                    returnToMenu()
                    return

                print("\n👉 Select the account you want to activate:")
                for idx, accId in enumerate(availableAccounts, 1):
                    trader = accountTraderInfo.get(accId)
                    if trader:
                        print(f" {idx}. {accId} — Equity: {trader.equity / 100:.2f}, Free Margin: {trader.freeMargin / 100:.2f}")
                    else:
                        print(f" {idx}. {accId}")

                while True:
                    try:
                        choice = int(input("Enter number of account to activate: ").strip())
                        if 1 <= choice <= len(availableAccounts):
                            selectedAccountId = availableAccounts[choice - 1]
                            setAccount(selectedAccountId)
                            break
                        else:
                            print("Invalid choice. Try again.")
                    except ValueError:
                        print("Enter a valid number.")

            elif desc == "Subscribe to Spot":
                symbolId = input("Symbol ID: ")
                seconds = input("Time in seconds: ")
                func(symbolId, seconds)
                runWhenReady(func, symbolId, seconds)


            elif desc == "Show Price Board":
                def fetchSymbolsAndThenShowBoard():
                    def afterSymbols():
                        reactor.callLater(3, func)  # func is printUpdatedPriceBoard

                    print("📥 Fetching symbol list...")
                    def symbolsCallback():
                        runWhenReady(afterSymbols)  # Wait for account & spot subs

                    runWhenReady(lambda: sendProtoOASymbolsListReq(False))
                    reactor.callLater(1.5, symbolsCallback)  # give time for subs to dispatch

                runWhenReady(fetchSymbolsAndThenShowBoard)


            elif desc == "Get Trendbars":
                weeks = input("Weeks: ")
                period = input("Period (e.g., M1): ")
                symbolId = input("Symbol ID: ")
                runWhenReady(func, weeks, period, symbolId)

            elif desc == "Get Tick Data":
                days = int(input("Days: "))
                tickType = input("Type (BID/ASK/BOTH): ")
                symbolId = int(input("Symbol ID: "))
                runWhenReady(func, days, tickType, symbolId)

            elif desc == "New Market Order":
                symbolId = input("Symbol ID: ")
                side = input("Side (BUY/SELL): ")
                volume = input("Volume: ")
                runWhenReady(func, symbolId, side, volume)

            elif desc == "New Limit Order" or desc == "New Stop Order":
                symbolId = input("Symbol ID: ")
                side = input("Side (BUY/SELL): ")
                volume = input("Volume: ")
                price = input("Price: ")
                runWhenReady(func, symbolId, side, volume, price)

            elif desc == "Close Position":
                positionId = input("Position ID: ")
                volume = input("Volume: ")
                runWhenReady(func, positionId, volume)

            elif desc == "Cancel Order":
                orderId = input("Order ID: ")
                runWhenReady(func, orderId)

            elif desc == "Deal Offset List":
                dealId = input("Deal ID: ")
                runWhenReady(func, dealId)

            elif desc == "Order Details":
                orderId = input("Order ID: ")
                runWhenReady(func, orderId)

            elif desc == "Orders by Position ID":
                positionId = input("Position ID: ")
                fromTs = input("From Timestamp (or press Enter): ") or None
                toTs = input("To Timestamp (or press Enter): ") or None
                runWhenReady(func, positionId, fromTs, toTs)


            else:
                def run():
                    if desc == "Trader Info":
                        func(currentAccountId)
                    else:
                        func()
                waitUntilAccountReady(currentAccountId, run)
        except Exception as e:
            print(f"❌ Error executing {desc}: {e}")

    # Else if it's a typed command
    elif userInput in commands:
        try:
            if not ensureAccountSet():
                returnToMenu()
                return
            raw = input("Enter parameters (separated by spaces): ").strip()
            args = raw.split() if raw else []
            commands[userInput](*args)
        except Exception as e:
            print(f"❌ Error: {e}")
    else:
        print("❌ Invalid input")
    if not liveViewerActive:
        reactor.callLater(3, executeUserCommand)

# Setting optional client callbacks
client.setConnectedCallback(connected)
client.setDisconnectedCallback(disconnected)
client.setMessageReceivedCallback(onMessageReceived)
# Starting the client service
client.startService()
reactor.run()
