(set-logic QF_UF)

(declare-fun a () Bool)
(declare-fun b () Bool)
(declare-fun c () Bool)
(declare-fun d () Bool)
(declare-fun e () Bool)
(declare-fun f () Bool)
(declare-fun g () Bool)

; !(a => b) & ((c | d) => !e)
(assert (and a b c d))
