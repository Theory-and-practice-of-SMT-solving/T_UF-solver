(set-logic QF_UF)

(declare-sort Univ 0)
(declare-fun l1 () Univ)
(declare-fun l2 () Univ)
(declare-fun l3 () Univ)
(declare-fun rev (Univ) Univ)
(declare-fun app (Univ Univ) Univ)

(assert (app (rev l1) (rev l2)))

