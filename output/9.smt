(set-logic QF_NRA)
(declare-const a Real)
(declare-const b Real)

(assert (>= a 0))
(assert (>= b 0))
(assert (<= (+ a b) 1))

(define-fun f () Real
  (+ (^ a 3) (^ b 3) (^ (- 1 (+ a b)) 3) (* 6 a b (- 1 (+ a b)))))

(assert (not (>= f 0.25)))

(check-sat)

(get-model)
(exit)
