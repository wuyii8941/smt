(set-logic QF_NRA)
(declare-const x Real)
(declare-const y Real)

(assert (> x 0))
(assert (> y 0))

(define-fun f () Real
  (+ x (* 2 y) (/ 32 (* x y))))

(assert (not (>= f 12)))

(check-sat)
(get-model)
(exit)
