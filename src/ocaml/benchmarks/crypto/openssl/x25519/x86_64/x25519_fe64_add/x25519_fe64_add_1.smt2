(set-logic QF_BV)
(set-info :smt-lib-version 2.0)
(declare-fun rax_3 () (_ BitVec 64))
(declare-fun rax_2 () (_ BitVec 64))
(declare-fun r9_3 () (_ BitVec 64))
(declare-fun r9_2 () (_ BitVec 64))
(declare-fun r8_4 () (_ BitVec 64))
(declare-fun r8_3 () (_ BitVec 64))
(declare-fun r8_2 () (_ BitVec 64))
(declare-fun r11_3 () (_ BitVec 64))
(declare-fun r11_2 () (_ BitVec 64))
(declare-fun r10_3 () (_ BitVec 64))
(declare-fun r10_2 () (_ BitVec 64))
(declare-fun carry_9 () (_ BitVec 1))
(declare-fun carry_8 () (_ BitVec 1))
(declare-fun carry_7 () (_ BitVec 1))
(declare-fun carry_6 () (_ BitVec 1))
(declare-fun carry_5 () (_ BitVec 1))
(declare-fun carry_4 () (_ BitVec 1))
(declare-fun carry_3 () (_ BitVec 1))
(declare-fun carry_2 () (_ BitVec 1))
(declare-fun carry_1 () (_ BitVec 1))
(declare-fun b3_0 () (_ BitVec 64))
(declare-fun b2_0 () (_ BitVec 64))
(declare-fun b1_0 () (_ BitVec 64))
(declare-fun b0_0 () (_ BitVec 64))
(declare-fun a3_0 () (_ BitVec 64))
(declare-fun a2_0 () (_ BitVec 64))
(declare-fun a1_0 () (_ BitVec 64))
(declare-fun a0_0 () (_ BitVec 64))
(assert true)
(assert (and (= carry_1 ((_ extract 64 64) (bvadd ((_ zero_extend 1) b0_0) ((_ zero_extend 1) a0_0)))) (= r8_2 ((_ extract 63 0) (bvadd ((_ zero_extend 1) b0_0) ((_ zero_extend 1) a0_0))))))
(assert (and (= carry_2 ((_ extract 64 64) (bvadd (bvadd ((_ zero_extend 1) b1_0) ((_ zero_extend 1) a1_0)) ((_ zero_extend 64) carry_1)))) (= r9_2 ((_ extract 63 0) (bvadd (bvadd ((_ zero_extend 1) b1_0) ((_ zero_extend 1) a1_0)) ((_ zero_extend 64) carry_1))))))
(assert (and (= carry_3 ((_ extract 64 64) (bvadd (bvadd ((_ zero_extend 1) b2_0) ((_ zero_extend 1) a2_0)) ((_ zero_extend 64) carry_2)))) (= r10_2 ((_ extract 63 0) (bvadd (bvadd ((_ zero_extend 1) b2_0) ((_ zero_extend 1) a2_0)) ((_ zero_extend 64) carry_2))))))
(assert (and (= carry_4 ((_ extract 64 64) (bvadd (bvadd ((_ zero_extend 1) b3_0) ((_ zero_extend 1) a3_0)) ((_ zero_extend 64) carry_3)))) (= r11_2 ((_ extract 63 0) (bvadd (bvadd ((_ zero_extend 1) b3_0) ((_ zero_extend 1) a3_0)) ((_ zero_extend 64) carry_3))))))
(assert (= rax_2 (ite (= carry_4 #b1) #x0000000000000026 #x0000000000000000)))
(assert (= carry_4 #b0))
(assert (and (= carry_5 ((_ extract 64 64) (bvadd ((_ zero_extend 1) rax_2) ((_ zero_extend 1) r8_2)))) (= r8_3 ((_ extract 63 0) (bvadd ((_ zero_extend 1) rax_2) ((_ zero_extend 1) r8_2))))))
(assert (and (= carry_6 ((_ extract 64 64) (bvadd (bvadd ((_ zero_extend 1) r9_2) ((_ zero_extend 1) #x0000000000000000)) ((_ zero_extend 64) carry_5)))) (= r9_3 ((_ extract 63 0) (bvadd (bvadd ((_ zero_extend 1) r9_2) ((_ zero_extend 1) #x0000000000000000)) ((_ zero_extend 64) carry_5))))))
(assert (and (= carry_7 ((_ extract 64 64) (bvadd (bvadd ((_ zero_extend 1) r10_2) ((_ zero_extend 1) #x0000000000000000)) ((_ zero_extend 64) carry_6)))) (= r10_3 ((_ extract 63 0) (bvadd (bvadd ((_ zero_extend 1) r10_2) ((_ zero_extend 1) #x0000000000000000)) ((_ zero_extend 64) carry_6))))))
(assert (and (= carry_8 ((_ extract 64 64) (bvadd (bvadd ((_ zero_extend 1) r11_2) ((_ zero_extend 1) #x0000000000000000)) ((_ zero_extend 64) carry_7)))) (= r11_3 ((_ extract 63 0) (bvadd (bvadd ((_ zero_extend 1) r11_2) ((_ zero_extend 1) #x0000000000000000)) ((_ zero_extend 64) carry_7))))))
(assert (= rax_3 (ite (= carry_8 #b1) #x0000000000000026 #x0000000000000000)))
(assert (and (= carry_9 ((_ extract 64 64) (bvadd ((_ zero_extend 1) rax_3) ((_ zero_extend 1) r8_3)))) (= r8_4 ((_ extract 63 0) (bvadd ((_ zero_extend 1) rax_3) ((_ zero_extend 1) r8_3))))))
(assert (= carry_9 #b0))
(assert (not (= (bvurem (bvadd (bvadd (bvmul ((_ zero_extend 256) a0_0) #x00000000000000000000000000000000000000000000000000000000000000000000000000000001) (bvadd (bvmul ((_ zero_extend 256) a1_0) #x00000000000000000000000000000000000000000000000000000000000000010000000000000000) (bvadd (bvmul ((_ zero_extend 256) a2_0) #x00000000000000000000000000000000000000000000000100000000000000000000000000000000) (bvadd (bvmul ((_ zero_extend 256) a3_0) #x00000000000000000000000000000001000000000000000000000000000000000000000000000000) (bvmul ((_ zero_extend 256) #x0000000000000000) #x00000000000000010000000000000000000000000000000000000000000000000000000000000000))))) (bvadd (bvmul ((_ zero_extend 256) b0_0) #x00000000000000000000000000000000000000000000000000000000000000000000000000000001) (bvadd (bvmul ((_ zero_extend 256) b1_0) #x00000000000000000000000000000000000000000000000000000000000000010000000000000000) (bvadd (bvmul ((_ zero_extend 256) b2_0) #x00000000000000000000000000000000000000000000000100000000000000000000000000000000) (bvadd (bvmul ((_ zero_extend 256) b3_0) #x00000000000000000000000000000001000000000000000000000000000000000000000000000000) (bvmul ((_ zero_extend 256) #x0000000000000000) #x00000000000000010000000000000000000000000000000000000000000000000000000000000000)))))) #x00000000000000007FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFED) (bvurem (bvadd (bvmul ((_ zero_extend 256) r8_4) #x00000000000000000000000000000000000000000000000000000000000000000000000000000001) (bvadd (bvmul ((_ zero_extend 256) r9_3) #x00000000000000000000000000000000000000000000000000000000000000010000000000000000) (bvadd (bvmul ((_ zero_extend 256) r10_3) #x00000000000000000000000000000000000000000000000100000000000000000000000000000000) (bvadd (bvmul ((_ zero_extend 256) r11_3) #x00000000000000000000000000000001000000000000000000000000000000000000000000000000) (bvmul ((_ zero_extend 256) #x0000000000000000) #x00000000000000010000000000000000000000000000000000000000000000000000000000000000))))) #x00000000000000007FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFED))))
(check-sat)
(exit)
