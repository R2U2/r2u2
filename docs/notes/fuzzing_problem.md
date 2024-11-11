# Fuzzing Problem

Proofs are nice, but....
  - I don't trust the clib
  - Or the hardware
  - People don't belive me
  - I can't prove the proof == code
    - Can't use an autocode
    - How do I know the autocoder is good
  - I have more CPU hours than work hours

For many many reasons want to test, but
  - Super inefficent
  -

Current strat:
  - For a max interval J: (J+2)!/2 / J! (combinations w/ replacement) [parobolic]
  - With a max time T: 4^T (exponential)
