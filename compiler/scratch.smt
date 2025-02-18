; Let p be a bit-vector representing the truth value of the proposition p at each time step.

; cs(p)=010 cs(q)=110
; cs(p&q)=010

; cs(p) := p
; cs(! p) := ~ p
; cs(p & q) := cs(p) & cs(q)
; cs(p | q) := cs(p) | cs(q)
;
; cs(F[lb,lb] p) := cs(p) << lb   (pads with zeroes so trace length check is handled)
; cs(F[lb,lb+1] p) := cs(F[lb,lb] p) | cs(F[lb+1,lb+1] p)
; cs(F[lb,ub] p) := cs(F[lb,lb] p) | cs(F[lb+1,lb+1] p) | ... | cs(F[ub,ub] p)  
;                 = (cs(p) << lb) | (cs(p) << lb+1) | ... | (cs(p) << ub)
; 
; cs(G[lb,lb] p) := cs(p) << lb    (pad with ones so trace length check is handled)
; cs(G[lb,lb+1] p) := cs(G[lb,lb] p) & cs(G[lb+1,lb+1] p)
; cs(G[lb,ub] p) := cs(G[lb,lb] p) | cs(G[lb+1,lb+1] p) | ... | cs(G[ub,ub] p)  
;                 = (cs(p) << lb) & (cs(p) << lb+1) & ... & (cs(p) << ub)
;
; cs(p U[lb,lb] q) := cs(q) << lb
; cs(p U[lb,lb+1] q) := (cs(q) << lb) | ((cs(p) << lb) & cs(p U[lb+1,lb+1] q))
; cs(p U[lb,ub] q) := (cs(q) << lb) | ((cs(p) << lb) & cs(p U[lb+1,ub] q))
;
; exists a pi : pi,0 |= phi
;
;
; Alternative for F:
; cs(F[lb,ub] p) := reduce_or((cs(p) << lb)[0,ub-lb]) + 
;                   reduce_or((cs(p) << lb)[1,ub-lb+1]) + 
;                   reduce_or((cs(p) << lb)[2,ub-lb+2]) + 
;                   ... +
;                   reduce_or((cs(p) << lb)[ub-lb,ub-lb]) 
;
; **Need to address case where ub-lb > wpd (cannot index over the length of cs(p) << lb)**
;
; Alternative for U:
; cs(p U[lb,ub] q) := 
;
;
; If we define offline monitoring as the problem of computing pi,i |= phi for all i such that 0 <= i < |pi|,
; then we can encode this as follows: pi,i |= phi iff cs(phi)[i] 
;

(set-logic QF_BV)

; F[2,5] p
(declare-fun p () (_ BitVec 6))
(define-fun F_2_5_p () (_ BitVec 1) (bvredor ((_ extract 3 0) p)))
(assert (= F_2_5_p #b1))
(check-sat)

; F[l,u] p
(declare-fun p () (_ BitVec u+1))
(define-fun F_l_u_p () (_ BitVec 1) (bvredor ((_ extract u-l 0) p)))
(assert (= F_l_u_p #b1))
(check-sat)

; F[l,u] phi
(define-fun phi () (_ BitVec u+1) ...)
(define-fun F_l_u_phi () (_ BitVec 1) (bvredor ((_ extract u-l 0) p)))
(assert (= F_l_u_phi #b1))
(check-sat)

; F[1,3] F[2,5] p
(declare-fun p () (_ BitVec 9))
(define-fun F_2_5_p () (_ BitVec 4) ((concat (bvredor ((_ extract 6 3) p)) ; this bit's value is not used! we don't need to know pi,0 |= F[2,5] p
                                             (bvredor ((_ extract 5 2) p))
                                             (bvredor ((_ extract 4 1) p))
                                             (bvredor ((_ extract 3 0) p)))))
(define-fun F_1_3_F_2_5_p () (_ BitVec 1) (bvredor ((_ extract 2 0) F_2_5_p)))
(assert (= F_1_3_F_2_5_p #b1))
(check-sat)

; What if we want to check a trace of length less than wpd+1?
; F[1,3] F[2,5] p
(declare-fun p () (_ BitVec 7)) ; now checking a trace of length 7
(define-fun F_2_5_p () (_ BitVec 4) ((concat (bvredor ((_ extract 4 1) p)) ; this bit is still not used...
                                             (bvredor ((_ extract 3 0) p))
                                             #b0
                                             #b0))) ; append zeroes for all indices that violate the trace length constraint 
(define-fun F_1_3_F_2_5_p () (_ BitVec 1) (bvredor ((_ extract 2 0) F_2_5_p)))
(assert (= F_1_3_F_2_5_p #b1))
(check-sat)

; F[l,u] phi with aub,alb and phi is a not a proposition
(define-fun phi () (_ BitVec u+aub+1) ...)
(define-fun F_l_u_phi () (_ BitVec aub+1) ((concat (bvredor ((_ extract (aub-alb)+(u-l)    aub-alb  ) phi))
                                                   (bvredor ((_ extract (aub-alb)+(u-l)-1  aub-alb-1) phi))
                                                   (bvredor ((_ extract (aub-alb)+(u-l)-2  aub-alb-2) phi))
                                                   ...
                                                   (bvredor ((_ extract (u-l)              0        ) phi)))))

; p U[2,5] q
(declare-fun p () (_ BitVec 6))
(declare-fun q () (_ BitVec 6))

(define-fun cs_p_U_2_5_q () (_ BitVec 1) ())

(assert (bvugt cs_p_U_2_5_q #b000))

(check-sat)
(get-model)

