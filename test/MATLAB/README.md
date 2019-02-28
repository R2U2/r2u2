# Readme for Test Cases

Document will illustrate various test cases and their purpose

Denote Input Wave 1: x
Denote Input Wave 2: y


# test0000
  - Test Case will output the Negation of the First Input Wave
  - "!x"

# test0001
  - Test Case will output the Conjunction of the First and Second Input Wave
  - "(x & y)" 
 
# test0002
  - Test Case will output the invariant of zero steps of the First Input Wave
  - "G[0] (x)"
  
# test0003
  - Test Case will output the invariant of 5 time steps of the First Input Wave
  - "G[5] (x)"

# test0004
  - Test Case will output the invariant of a zero interval of the First Input Wave
  - "G[0,0] (x)"
  
# test0005
  - Test Case will output the invariant of 1 interval of the First Input Wave
  - "G[0,1] (x)"
  
# test0006
  - Test Case will output the variant of an interval [5,10] of the First Input Wave
  - "G[5,10] (x)"
  
# test0007
  - Test Case will output the First Input Wave Until an interval an zero interval, the Second Input Wave
  - "(x) U[0,0] (y)"
  
# test0008
  - Test Case will output the First Input Wave Until an interval of 1, the Second Input Wave
  - "(x) U[0,1] (y)"
  
# test0009
  - Test Case will output the First Input Wave Until an interval of [5,10], the Second Input Wave
  - "(x) U[5,10] (y)"
  
# test0010
  - Test Case will output the First Input Wave Until an interval of [0,2], the Second Input Wave
  - "(x) U[0,2] (y)"
  
  
# test0011
  - Test Case representing TACAS_examples
  - Test Case will output Altitude and Pitch Signals
  - Test Case Negation will output "!(Pitch)"
  - Test Case InvarNextTsteps will output "G[5] (Pitch)"
  - Test Case InvarFutInterval will output "G[5,10] (Altitude)"
  - Test Case Conjunction will output "(Altitude & Pitch)"
  - Test Case Until will output "Pitch U[5,10]  Altitude"
  - Test Case ConjunctionwithInvarNextTsteps will output "(Pitch & G[5] (Altitude))"

# test0012
  - Test Case will output the First Input Wave Until an interval of [1,2], the Second Input Wave
  - "(x) U[1,2] (y)"
  
  
# test0013
  - Test Case will output the First Input Wave Until an interval of [2,3], the Second Input Wave
  - "(x) U[2,3] (y)"

# test0014
  - Test Case will output AND result with two input under different time stamps
  - "a0 & G[2] (a1)"
  
# test0015
  - Test Case will test AND operation combined with NOT
  - " (!y) & (x)"
  
# test0016
  - Test Case testing embedding AND operations
  - " (x & x) & (y) "
  
# test0017
  - Test Case testing embedding NOT operations and AND
  - " (!(!x)) & (y) "

# test0018
  - Test Case testing negation of a value that should always be true
  - " !(x & x) "
  
# test0019
  - Test Case testing interval operation with an input that should always be true
  - " G[5] (x & x) "
  
# test0020
  - Test Case testing interval operation with an input that should always be true with added negations
  - " G[5] (!(!(x & x))) "
  
# test0021
  - Test Case testing negation of an future time operation
  - " !(G[2] x)"

# test0022
  - Test Case testing conjunction of two future time operations
  - " (G[2] x) & (G[2] y)"
  
# test0023
  - Test Case testing double negation
  - " !(!x) "
  
# test0024
  - Test Case testing global interval 5 steps of 2nd input
  - " G[5] y"
  
# test0025
  - Test Case testing negation of interval of negated input
  - " !(G[2] (!y) )"
  
# test0026
  - Test Case testing combination of conjunction with interval
  - " (G[2] x) & (y)"

# test0027
  - Test Case testing negation of conjunction of two different types of interval operations
  - "!( (G[5,10] x) & (G[2] y) )"
  
# test0028
  - Test Case testing double negation of interval and conjunction testing
  - "G[2(!(!x)) & y"
  
# test0029
  - Test Case testing Conjunction with future interval
  - "y & (G[0,8] x)"
  
# test0030
  - Test Case testing Conjunction of different interval operations
  - "(G[2] y) & (G[5,10] x)"
  
# test0031
  - Test Case testing interval of 2nd input
  - "G[2] y"
  
# test0032
  - Test Case testing multiple conjunctions with intervals
  - "(x & y) & (G[3,5] x)"

# test0034
  - Test Case testing multiple conjunctions with intervals
  - "y F[5,10] x"


# test0035
  - Test Case testing for complex global
  - "G[2,4](G[2]y)"