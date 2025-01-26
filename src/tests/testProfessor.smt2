(set-logic QF_UF)
(set-info :status unsat)

(declare-sort Univ 0)
(declare-fun l1 () Univ)
(declare-fun l2 () Univ)
(declare-fun rev (Univ) Univ)
(declare-fun app (Univ Univ) Univ)

(assert (= (rev (rev l1)) l1))
(assert (= (rev (rev l2)) l2))
(assert (= (rev (app (rev l1) (rev l2))) (app (rev (rev l2)) (rev (rev l1)))))
(assert (= (rev (app l2 l1)) (app (rev l1) (rev l2))))
(assert (not (= (rev (rev (app (rev l1) (rev l2)))) (app (rev l1) (rev l2)))))