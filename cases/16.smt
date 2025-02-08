(set-logic QF_NRA)
(declare-const a Real)
(declare-const b Real)
(declare-const c Real)

(assert (> a 0))
(assert (> b 0))
(assert (> c 0))
(assert (< a (+ b c)))
(assert (< b (+ c a)))
(assert (< c (+ a b)))

(define-fun f () Real
  (+ (* a a b (- a b)) 
     (* b b c (- b c)) 
     (* c c a (- c a))))

(assert (not (>= f 0)))

(check-sat)
(get-model)
(exit)
