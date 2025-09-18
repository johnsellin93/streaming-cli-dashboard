
[![Demo](https://fx-metrics.com/images/demo-thumb.jpg)](https://fx-metrics.com/watch.html)
# Realtime Metrics Dashboard

A personal experiment in **streaming systems, terminal UIs, and realtime data pipelines**.
This project explores how to build a **resilient client (Twisted + Protobuf/WebSockets)** and a **live-updating dashboard** in the terminal (Rich + prompt_toolkit).

### Features
• Protobuf-based WebSocket client with message framing, heartbeats, and resilient reconnect logic
• Live-updating metrics dashboard with Vim-style navigation (j/k, TAB, x, e)
• Inline editing with optimistic UI updates and rollback on reconciliation
• Realtime status indicators, thresholds, and age markers
• Backpressure-aware refresh logic, throttling, and cached subscriptions

### Tech
Python, Twisted (async I/O), Protobuf, Rich, prompt_toolkit
