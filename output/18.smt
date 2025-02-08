(set-logic QF_NRA)
(declare-const a Real)
(declare-const b Real)
(declare-const c Real)

(assert (> a 0))
(assert (> b 0))
(assert (> c 0))
(assert (> (+ a b) c))
(assert (> (+ a c) b))
(assert (> (+ b c) a))

(define-fun f () Real
  (+ (* a a (- (+ b c) a))
     (* b b (- (+ c a) b))
     (* c c (- (+ a b) c))))

(assert (not (<= f (* 3 a b c))))

(check-sat)
(get-model)
(exit)
