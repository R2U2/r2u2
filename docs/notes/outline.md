Docs Outline & Progress

Key:
  [ ] Todo
  [-] Created
  [=] Written
  [X] Proofed & Complete

-------------------------------------------------------------------------------

[=] Overview:

  [=] Overview (Home Page)
      Describe R2U2 Framework -- what it does, how it fits into a system, what components it consists of and outline the specification development + monitoring processes

  [=] Quick-Start Guide
      Give instructions on how to build and run C2PO/R2U2 over a small example and the test suite

  [=] Installation
      More details on environment setup and platform compatibility

  [=] Project Structure
      Directory of repository layout and descriptions of other available documentation

-------------------------------------------------------------------------------

[-] Specification and Runtime Verification with Mission-time Temporal Logic:
  A brief tutorial on what MLTL is, what specifications are used for, and how C2PO and R2U2 provide system monitoring though RV of MLTL

  [ ] Temporal Logic
      Quick overview of temporal logic, ending with description of MLTL

  [=] Runtime Monitoring
      A section on verifying MLTL formulas over streams of data

  [=] Specification Writing
      A section on how to write MLTL specifications

  [=] MLTL Monitoring
      Goes over how an MLTL formula is evaluated in real-time

  [=] R2U2 Framework
      Familiarization with the C2P0-R2U2 tool chain ConOps and some of the prominent features provided

-------------------------------------------------------------------------------

[-] User Guides:
  Per-tool usage and integration documentation

  [-] C2PO
    [ ] CLI Usage
      [ ] Required arguments
      [ ] Options
    [ ] C2PO Specification Language
      The richer input language that extends MLTL and enables C2P0's and R2U2's extended features as well as quality of life improvements like meaningful naming
    [ ] R2U2 Front-End Selection
      A quick note about selecting atomic-checker vs booleanizer when running C2P0 with a link to the R2U2 docs for more information
    [ ] Assembly
      Description of resulting output file as well as selecting endiness
    [ ] Formula Optimization Features
      Description of operators for optimization passes and when to (dis)able them
      [ ] Common Subexpression Elimination
      [ ] Extended Operators
      [ ] Formula Rewriting
    [ ] Troubleshooting & Errors
      Common error messages with troubleshooting

  [=] R2U2
    [=] Building R2U2
      How to build release and debug R2U2 binaries and libraries
    [=] Running R2U2
      Instruction on executing R2U2 as a commandline tool
    [-] Embedding R2U2
      [=] Reserving Memory
      [=] Signal Input
      [=] Verdict Output
      [=] Initializing and running the monitor
      [=] Platform constraints
      [=] Common sources of incompatibility
        Syndromes of alignment, endiness, and other platform-dependent configuration
    [=] Deciphering Output
      [=] Verdict Output
        Meaning of the R2U2.log verdict stream
      [=] Debug Output
        Quick overview with link to developer docs with more info
    [=] Multi-monitor configurations
      Describe uses and tradeoffs in using multiple monitor instances
    [=] Design-time Configurations
      Extra features that must be enabled when built to use
      [=] R2U2_AT_EXTRA_FILTERS
      [=] R2U2_AT_FFT_Filter
      [=] R2U2_AT_Prognostics
      [=] R2U2_AT_Signal_Sets
      [=] R2U2_TL_SCQ_Verdict_Aggregation
      [=] R2U2_TL_Formula_Names
      [=] R2U2_TL_Contract_Status
      [=] R2U2_CSV_Header_Mapping
      [=] R2U2_DEBUG
      [=] R2U2_TRACE

  [=] GUI
    A web-based visualizer for MLTL operator structure
    [=] Running the GUI locally
    [=] Running the GUI with Docker
    [=] Description of visualization features

  [=] Test
    End-to-end test of the C2P0-R2U2 tool flow
    [=] Running the test suite
    [=] Interpreting test output
    [=] Included test cases

  [-] Tools
    Quick descriptions of the utilities provided in the tools directory

  [-] Examples:
    A section showcasing and explaining a series of increasingly complex specifications utilizing various C2P0 and R2U2 features
    [ ] Simple MLTL
    [ ] Set-based Spec
    [ ] Assume-Guarantee Contracts
    [ ] Booleanizer/Atomic Checker
    [ ] Request Arbiter System (most complex)

-------------------------------------------------------------------------------

[-] Development Guide:

  [=] Contributing Guidelines
    Information for developers contributing to R2U2 code upstream
    [ ] Repository, Hosting, and Organization Logistics
    [ ] Workflow
      Standard issue, branch, test, merge, and release procedures
    [ ] Language Standards
      Project and Per-language requirements and conventions
      [ ] Project-wide
          [ ] Use auto-formatted
          [ ] Select Style Guide
      [ ] C
      [ ] C++
      [ ] Make
      [ ] Python
      [ ] Shell (Bash)
      [ ] VHDL
    [ ] Versioning
      Numbering scheme and history

  [=] Documentation
    Describe the system that allows us to build linked, unified docs across all subprojects
    [ ] Configuration and Toolflow
    [ ] Adding Documentation
    [ ] Building Documentation

  [=] Continuous Integration & Testing
    [ ] Testing Stages
      List types of testing used, and direct to where they are located
    [ ] CI Plan Definition
      Describes stages of CI pipeline and location of configuration

  [-] C2PO Development
    [-] Architecture and Dataflow
    [-] C2P0 Language Parser
    [-] AST Objects
    [ ] AST Optimization
      [ ] CSE
      [ ] Rewriting
      [ ] Extended Operators
    [ ] SCQ Sizing
      Reference R2U2 manual SCQ definition
    [ ] Assembly with Python Structs
    [ ] UX/CLI
    [ ] Testing

  [-] R2U2 Static Monitor Development
    [ ] Design Goals of Static Monitor
    [ ] Architecture
      [ ] Controllers and Engines
        Describes code structure and separation of concerns
      [ ] Monitor Structure
        [ ] Vector time
          [ ] Loop Progress
        [ ] Memory Arenas
        [ ] Instruction Dispatch
        [ ] Lifecycle and Dataflow
      [ ] Main and library entry
        Describes external facing APIs
    [=] Internals
      [ ] Bounds checking
      [ ] Configuration flags
      [ ] Error codes and handling
      [ ] type definitions
      [ ] debug
        Link to later section
    [ ] Memory Controllers
      [ ] Box Queues
      [ ] Contract Status
      [ ] CSV Trace
      [ ] Instruction
      [ ] Monitor
      [ ] Register
      [ ] Shared Connection Queue (SCQ)
      [ ] Specification Binary
    [ ] Execution Engines
      Explain dispatching, architecture, and list of operations for each
      [ ] Atomic Checker
      [ ] Booleanizer
      [ ] Future MLTL
      [ ] Past MLTL
      [ ] Binary Load
    [=] Debug Builds
      [ ] Design Philosophy
        What should be enabled by debug flag
      [ ] Debug Levels (Debug vs Trace)
      [ ] Debug Output Format
    [=] Testing
      [ ] Unit testing with munit
      [ ] Unit test coverage analysis
      [ ] Static analysis with CodeCoverage

-------------------------------------------------------------------------------

[-] Specifications and References:
  Short documents related to cross-cutting design decisions, such as file formats used by multiple tools, and auto-generated documentation

  [=]  MLTL Specification
    [ ]  Execution Sequence Notation
    [ ]  MLTL Syntax
    [ ]  MLTL Semantics
    [ ]  MLTL Operator Algorithms
      Per operator:
        [ ]  Algorithm for evaluation over execution sequence
        [ ]  Proof of Correctness
        [ ]  Proof of Time Complexity
        [ ]  Proof of Space Complexity

  [=]  Format Specifications
      [=]  MLTL Formula Files [.mltl]
      [=]  Signal Trace Files [.csv]
      [=]  Signal Map Files [.map]
      [=]  R2U2 Assembly [.asm]
      [=]  R2U2 Configuration Binary Files [.bin]

  [ ]  API Reference
    Auto-generated via sphinx/doxygen/breath/api-doc, etc.
    [ ]  C2PO
    [ ]  R2U2 Static Monitor


-------------------------------------------------------------------------------

TODO:
  - Publications and How to Cite
  - Missing Test suites
  - Migrate CI to new test framework
  - Separate domains per guide
  - 