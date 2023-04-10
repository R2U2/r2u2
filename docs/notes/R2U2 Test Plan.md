# R2U2 Test Plan

Testing Campaigns:
  Unit Test - per function
    - line coverage
    - branch coverage

  Component Tests - per module/datatype
    - dataflow
    - contract (?)
    - property-based

  Integration Tests - full system
    - Functional
    - Correctness (oracle)
    - Fuzzing

Additional Reports
  - Coverage
  - Style
  - Lints
  - Static Analysis

Order of operations:
  1) Select provider (or build our own)
  2) Write tests
  3) collate results
  4) Add to CI

Additional Features:
  - Set Aggregation
  - Unified MLTL(M) frontend
  - Memory Advisor

NASA Requires:
    - Memory Advisor
    - Unit tests (line and branch)
    - Set aggregation
    - Documentation
    - VxWorks Integration

