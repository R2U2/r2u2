# Multi-monitor

Each monitor instance can evaluate many formulas at once, but operates on a whole specification set at a time.
This enables powerful MLTL optimizations to be applied by the formula compiler, but limits control of individual formulas at runtime.

To support more complex verification architectures, such as starting/stopping/resetting formulas independently or running formulas at different rates, multiple instances of the monitor can be instantiated.

This would involve one specification binary per monitor and following the [embedding](./embedding.md) instructions for each monitor.
