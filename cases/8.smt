(set-logic QF_NRA)
(declare-fun a () Real)
(declare-fun b () Real)
(declare-fun c () Real)

(assert (> a 0))
(assert (> b 0))
(assert (> c 0))

(define-fun f () Real 
    (+ (/ a (sqrt (+ (^ a 2) (* 8 b c))))
       (/ b (sqrt (+ (^ b 2) (* 8 c a))))
       (/ c (sqrt (+ (^ c 2) (* 8 a b))))))

(assert (not (>= f 1)))

(check-sat)

(get-model)
(exit)

