(assert (not (forall ((a Real)) (forall ((b Real)) (=> (and (> a 0) (> b 0)) (>= (* (+ (^ a 2) (^ b 2)) (sqrt (* (+ (^ a 2) 1) (+ (^ b 2) 1)))) (* (+ (^ a 2) (^ b 2)) (+ (* a b) 1))))))))
(check-sat)
(get-model)
(exit)