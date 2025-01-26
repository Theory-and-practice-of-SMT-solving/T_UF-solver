(set-logic QF_UF)
(set-info :status sat)

(declare-sort Univ 0)
(declare-fun a () Univ)
(declare-fun b () Univ)
(declare-fun f (Univ) Univ)

(assert (= (f (f (f (f (f a))))) a))
(assert (= (f (f (f a))) a))
(assert (= (f a) b))
(assert (or (not (= a b)) (= a b)))