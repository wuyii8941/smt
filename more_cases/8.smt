(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (<= (+ (pow a 2) (pow b 2) (pow c 2) (* a b) (* a c) (* b c)) 2))
(assert (< 0 a))
(assert (< 0 b))
(assert (< 0 c))
(assert (not (<= 6 (+ (* 2 (pow (+ a b) -2)) (* 2 (pow (+ b c) -2)) (* 2 (pow 2 (/ 1 2)) (pow (+ a c) -1) (pow (+ (* 2 a b (pow (+ a b) -2)) (* 2 a c (pow (+ a c) -2)) (* 2 b c (pow (+ b c) -2))) (/ 1 2)))))))
(check-sat)
(get-model)
(exit)