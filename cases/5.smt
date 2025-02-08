(set-logic QF_NRA)
(declare-fun a () Real)
(declare-fun b () Real)
(declare-fun c () Real)
(declare-fun d () Real)
(declare-fun e () Real)

(assert (> a 0))
(assert (> b 0))
(assert (> c 0))
(assert (> d 0))
(assert (> e 0))

(assert (not (>= (+ (/ a (+ a 1)) 
                (/ b (+ b 1)) 
                (/ c (+ c 1)) 
                (/ d (+ d 1)) 
                (/ e (+ e 1)))
            (/ (+ a b c d e) (+ (+ (+ (+ a b) c) d) e 1)))))

(check-sat)

(get-model)
(exit)
