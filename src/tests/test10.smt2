(set-logic QF_UF)
(set-info :status unsat)

(declare-fun a () Bool)
(declare-fun b () Bool)
(declare-fun c () Bool)
(declare-fun d () Bool)
(declare-fun e () Bool)
(declare-fun f () Bool)
(declare-fun g () Bool)

; !(a => b) & ((c | d) => !e)
(assert (and (not (=> a b)) (=> (or c d) (not e))))
; !a
(assert (not a))
