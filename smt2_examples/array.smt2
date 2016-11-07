; Author : Ranadeep
;
; Description :
; a[i] = a[i] + 1
; a[i + 1] = a[i - 1] - 1
; check whether the result is equivalent when the two statements are swapped

(set-logic QF_AUFLIA)
(set-option :produce-models true)

(declare-fun i (Int) Int)

(declare-fun a (Int) (Array Int Int))

(assert
    (and 
        (= 
            (a 1)
            (store
                (a 0)
                (i 0)
                (+ (select (a 0) (i 0)) 1)
            )
        )
        (= (i 1) (i 0))
    )
)

(assert 
    (and 
        (= 
            (a 2)
            (store
                (a 1)
                (+ (i 1) 1)
                (- (select (a 1) (- (i 1) 1)) 1)
            )
        )
        (= (i 2) (i 1))
    )
)

(assert 
    (and 
        (= 
            (a 3)
            (store
                (a 0)
                (+ (i 0) 1)
                (- (select (a 0) (- (i 0) 1)) 1)
            )
        )
        (= (i 3) (i 0))
    )
)

(assert
    (and 
        (= 
            (a 4)
            (store
                (a 3)
                (i 3)
                (+ (select (a 3) (i 3)) 1)
            )
        )
        (= (i 4) (i 3))
    )
)

(define-fun property () Bool 
    (and
        (= (i 2) (i 4))
        (= (a 2) (a 4))
    )
)

(assert (not property))
(check-sat)