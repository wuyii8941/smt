(set-logic QF_NRA)
(declare-fun b () Real)
(declare-fun a () Real)
(assert (= (+ (^ a 2) (^ b 2)) (* 2 a b)))
(assert (not (>= (+ (^ a 2) (^ b 6)) (* 2 (^ a 2) (^ b 3)))))
(check-sat)
(get-model)
(exit)
