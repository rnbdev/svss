; Author : Ranadeep
;
; Description :
; y = x + 1 and z = x + 2 and
; x' = if a then x else y and
; y' = if a then y else z and
; z' = if a then z else y + 2 implies
; y' = x' + 1 and z' = x' + 2

(set-logic QF_UFLIA)
(set-option :produce-models true)

(declare-fun x (Int) Int)
(declare-fun y (Int) Int)
(declare-fun z (Int) Int)
(declare-fun a () Bool)

(define-fun property () Bool 
    (=> 
        (and 
            (and 
                (= (y 0) (+ (x 0) 1))
                (= (z 0) (+ (x 0) 2))
            )
            (= (x 1) (ite a (x 0) (y 0)))
            (= (y 1) (ite a (y 0) (z 0)))
            (= (z 1) (ite a (z 0) (+ (y 0) 2)))
        )
        (and 
            (= (y 1) (+ (x 1) 1))
            (= (z 1) (+ (x 1) 2))
        )
    )
)

(assert (not property))
(check-sat)