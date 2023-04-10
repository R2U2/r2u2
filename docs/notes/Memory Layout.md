Memory Layout

Monitor: {
    Metadata - ???
    /* Runtime variable */
    timestamp_t now
    /* Inst Mem */
    Inst[]
    ???
}

Inst {
    Execution Unit Tag
    Metadata
    bytes
}

Parse:
  - TL Inst
  - Interval
  - SCQ size
  - AT Inst

  - Inst
  - 

-------------------------------------------------------------------------------

Monitor:
  Logical 

Config:
  Compile monitor 

Formula:
 A singular 

Spec:
  A set of formulas that share a common description of time. They must be started
  stopped, ect together. In return, they can share intermidiate restuls for effiency.

The most common use cases are either to set up a signle monitor, with a single spec
or to have a monitor that changes between a set of specs depending on the host device's mode.

More complex setups are possible

-------------------------------------------------------------------------------

Weights

ePolling

-------------------------------------------------------------------------------

Debug var usage check
Debug Generation Check?