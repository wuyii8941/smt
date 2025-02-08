(set-logic QF_NRA)
(declare-const a Real)
(declare-const b Real)
(declare-const c Real)

(assert (>= a 0))
(assert (<= a 1))
(assert (>= b 0))
(assert (<= b 1))
(assert (>= c 0))
(assert (<= c 1))

(define-fun f () Real
  (+ (/ a (+ 1 b c))
     (/ b (+ 1 a c))
     (/ c (+ 1 a b))
     (* (- 1 a) (- 1 b) (- 1 c))))

(assert (not (<= f 1)))

(check-sat)
(get-model)
(exit)
