(set-logic QF_NRA)
(declare-const a Real)
(declare-const b Real)
(declare-const c Real)

(assert (> a 0))
(assert (> b 0))
(assert (> c 0))

(assert (not (>= (+ (/ a (+ a 1)) (/ b (+ b 1)) (/ c (+ c 1))) 
             (/ (+ a b c) (+ (+ a b) c 1)))))

(check-sat)

(get-model)
(exit)
