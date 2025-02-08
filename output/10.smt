(set-logic QF_NRA)
(declare-const x Real)


(assert (not (>= (^ (+ (^ x 2) 7) 2) (* 16 (+ (^ x 2) 3)))))

(check-sat)

(get-model)
(exit)
