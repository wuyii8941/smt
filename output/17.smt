(set-logic QF_NRA)
(declare-const a Real)
(declare-const m Real)
(declare-const c Real)

(assert (> a 0))
(assert (> m 0))
(assert (> c 0))
(assert (= (+ a m c) 12))

(define-fun poly () Real
  (+ (* a m c) (* a m) (* m c) (* a c)))

(assert (not (< poly 112)))

(check-sat)
(get-model)
(exit)
