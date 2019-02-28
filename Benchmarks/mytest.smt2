(set-logic QF_FP)
(set-info :smt-lib-version 2.0)
(set-info :category "crafted")
(set-info :source |lijiaying for testing Xsat|)
(set-info :status unknown)
;; MathSAT API call trace

(declare-fun b0 () (_ FloatingPoint 8 24))
(define-fun _t_m () RoundingMode RNE)

(define-fun f_0_1 () (_ FloatingPoint 8 24) (fp #b0 #b00000000 #b00000000000000000000001))
(define-fun f_0_2 () (_ FloatingPoint 8 24) (fp #b0 #b00000000 #b00000000000000000000010))
(define-fun f_0_3 () (_ FloatingPoint 8 24) (fp #b0 #b00000000 #b00000000000000000000011))
(define-fun f_0_4 () (_ FloatingPoint 8 24) (fp #b0 #b00000000 #b00000000000000000000100))
(define-fun f_0_5 () (_ FloatingPoint 8 24) (fp #b0 #b00000000 #b00000000000000000000101))

(define-fun f_1_1 () (_ FloatingPoint 8 24) (fp #b0 #b00000001 #b00000000000000000000001))
(define-fun f_1_2 () (_ FloatingPoint 8 24) (fp #b0 #b00000001 #b00000000000000000000010))
(define-fun f_1_3 () (_ FloatingPoint 8 24) (fp #b0 #b00000001 #b00000000000000000000011))
(define-fun f_1_4 () (_ FloatingPoint 8 24) (fp #b0 #b00000001 #b00000000000000000000100))
(define-fun f_1_5 () (_ FloatingPoint 8 24) (fp #b0 #b00000001 #b00000000000000000000101))


(define-fun left_bound () (_ FloatingPoint 8 24) f_1_1)
(define-fun right_bound () (_ FloatingPoint 8 24) f_1_2)

(define-fun left_part () Bool (fp.lt left_bound b0))
(define-fun right_part () Bool (fp.lt b0 right_bound))
(define-fun full () Bool (and left_part right_part))

(assert full)
(check-sat)
