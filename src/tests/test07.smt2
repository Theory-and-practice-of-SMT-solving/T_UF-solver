(set-logic QF_UF)
(set-info :status sat)

(declare-fun a () Bool)
(declare-fun b () Bool)
(declare-fun c () Bool)
(declare-fun d () Bool)
(declare-fun e () Bool)
(declare-fun f () Bool)
(declare-fun g () Bool)

; !(a & b) | (c & d)
(assert (or (not (and a b)) (and c d)))

; (b & c)
(assert (and b c))

; (!a)
(assert (not a))
























