(set-logic QF_NRA)
(declare-fun p () Real)
(declare-fun x () Real)

(assert (> p 0))
(assert (< p 15))
(assert (<= p x))
(assert (<= x 15))

(define-fun f () Real 
    (+ (abs (- x p)) 
       (abs (- x 15)) 
       (abs (- x (+ p 15)))))

(assert (not (>= f 15)))

(check-sat)

(get-model)
(exit)
