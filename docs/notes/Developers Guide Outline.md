Developers Guide:

  - Versioning:
    - SemVer [https://semver.org]
    - CalVer [https://calver.org] ? Probably not...
  - Language Standards
        * Include code style guides w/ autoformatter
        * include editorconfig [https://editorconfig.org]
    - C
      - Automation and Build: Make
      - Style Guide: TBD
      - Formatting: clang-format
      - Layout:
        - build
        - include
        - src
        - tests
        - examples
        - external
        - data
        - tools
        - docs
        - libs
        - extras
      - C std 99 (better compat with some old paltofrms, no need for C111/17 features)
      - Testing:
        * Unit Tests: Munit
        * Benchmakring: b63
        * Coverage: gcovr
      - Docs:
        * API: DOxygen
        * Complexity: gnu-complexity
        * Call Graph: cflow
      - Static Analysis:
        * SBMC
        * ESBMC
        * cppcheck
        * clang-tidy
        * IKOS?
      - Runtime Analysis:
        * Sanitizers
        * valgrind
    - C++
    - VHDL
    - Python
        - Poetry
        - Tox
        - Linted (flake8)
        - Sphinx Docs
        - 
    - Shell (Bash)
      - Shellcheck

  - CI/CD
    Roughly ordred fastest to slowest for quick iter loops
    - Build (does it blend?)
    - Tests (does it work?)
    - Coverage (Are we sure?)
    - Analysis (is it good?)
    - Benchmarks (is it fast?)
    - Package (Ship it out)

  - Repository, Hosting, 
    - Organization: Each monitor should be able to stand alone

  - PlatofrmIO Support?

  - We'd love to use (https://github.com/include-what-you-use/include-what-you-use) but it's a pain to setup.... maybe in CI?

  - Requirments, V&V 
    - gcovr
    - Use RFC 2119 Wording [https://www.rfc-editor.org/rfc/rfc2119]

  - Semantic Versioning

 - C design notes:
    - Prefix for all thing things
    - Return an error condition, I/O via ptrs (the one monitor structu if possible)
    - C++ calllable (extern c if cpp)
    - Makefile targets:
      deps
      build
      install
      default
      all
    - Main:
      * Output philsophphy
        - Argv for config
        - stdin for signals
        - stdout for verdicts (results only, pipeable)
        - stderr for communcation, only errors by default, verbose adds logging
            * -v adds basic human readable output
            * -vv adds "debug" logging - actually trace
    - Need to generate compille.json with:
      * Bear [https://github.com/rizsotto/Bear]
        - Very active, but relies on OS packages
        - Most full output, but paths are not relative
      * scan-build [https://github.com/rizsotto/scan-build]
        {No work on MacOS}
      * compiledb [https://github.com/nickdiego/compiledb]
      - Add header defs via
        * compdb [https://github.com/Sarcasm/compdb]

Workflow:
  - Checout
  - BVrnach
  - issue?
  - feature, docs, tests, bugs
  - push
  - PR
  - CI

Other Notes:
  - Most engines have (but are not required to have) a memory where they are the exclusive writter while others have read access
  - Some things can always make progress (AT/BZ latching new values) and should not report progress as such

Users Guide:
 Use breath to embed Docygen API docs in Sphinx for single system?

Avise
Automatic verification I systematic execution

ABVOLT
Automated Bruteforce Verifiaction of Logical Temproal Sequences

