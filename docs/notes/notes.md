A Monitor contains 

Instructions Domain:
  |- Time
  |  |
  |  |- now
  |  |
  |  |- loop_progress
  |  |
  |  |- program_counter
  |
  |- 


The R2U2 framework consists of two types of submodules:
  - Execution engines
  - Memory Domains

Controllers 


Highlevel API
  - R2U2 Init (monitor, spec) ->
  - R2U2 Tic (monitor)

Under the hood
  - Loader -> monitor
  -

Monitor is just a memory domain, can have multiple

All engines can be defied by the type of memory they need and if it is RO or RW

Need two types of loaders: 

Engines all are R/W to one domina, R-only to all others