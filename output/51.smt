(declare-const c Real)
(assert (< 0 c))
(declare-const b Real)
(assert (< 0 b))
(declare-const a Real)
(assert (< 0 a))
(assert (not (>= (+ (/ a b) (+ (/ b c) (/ c a))) (sqrt (/ (+ (^ a 2) 1) (+ 1 (^ b 2)))))))
(check-sat)
(get-model)
(exit)
