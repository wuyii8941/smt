(set-logic QF_NRA)
(declare-const u Real)
(declare-const v Real)

(define-fun f () Real
  (+ (^ u 2) (^ v 2) (/ 1 (^ u 2)) (/ v u)))

(assert (not (>= f 1.7320508075688772)))

(check-sat)
(get-model)
(exit)
