(set-logic QF_UF)

(declare-sort Univ 0)
(declare-fun a () Univ)
(declare-fun b () Univ)
(declare-fun x () Univ)
(declare-fun f (Univ Univ) Univ)

(assert (= (f (f a b) b) x))
(assert (= (f a b) a))

