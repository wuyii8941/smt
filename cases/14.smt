(set-logic QF_NRA)
(declare-const a Real)
(declare-const b Real)
(declare-const c Real)

(assert (> a 0))
(assert (> b 0))
(assert (> c 0))

(assert (= (* a b c) 1))

(define-fun f () Real
  (+ (/ 1 (* (^ a 3) (+ b c)))
     (/ 1 (* (^ b 3) (+ a c)))
     (/ 1 (* (^ c 3) (+ a b)))))

(assert (not (>= f (/ 3 2))))

(check-sat)
(get-model)
(exit)