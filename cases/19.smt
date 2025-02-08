(set-logic QF_NRA)
(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(declare-const d Real)

(assert (> a 0))
(assert (> b 0))
(assert (> c 0))
(assert (> d 0))

(define-fun f () Real
  (+ (/ a (+ a b d))
     (/ b (+ b c a))
     (/ c (+ c d b))
     (/ d (+ d a c))))

(assert (not (> f 1)))

(check-sat)
(get-model)
(exit)
