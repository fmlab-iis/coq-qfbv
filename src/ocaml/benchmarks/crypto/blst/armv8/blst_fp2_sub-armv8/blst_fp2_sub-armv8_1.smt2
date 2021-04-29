(set-logic QF_BV)
(set-info :smt-lib-version 2.0)
(declare-fun x3_2 () (_ BitVec 64))
(declare-fun x3_1 () (_ BitVec 64))
(declare-fun x22_4 () (_ BitVec 64))
(declare-fun x22_2 () (_ BitVec 64))
(declare-fun x21_4 () (_ BitVec 64))
(declare-fun x21_2 () (_ BitVec 64))
(declare-fun x20_4 () (_ BitVec 64))
(declare-fun x20_2 () (_ BitVec 64))
(declare-fun x19_4 () (_ BitVec 64))
(declare-fun x19_2 () (_ BitVec 64))
(declare-fun x17_4 () (_ BitVec 64))
(declare-fun x17_2 () (_ BitVec 64))
(declare-fun x16_4 () (_ BitVec 64))
(declare-fun x16_2 () (_ BitVec 64))
(declare-fun x15_6 () (_ BitVec 64))
(declare-fun x15_5 () (_ BitVec 64))
(declare-fun x15_3 () (_ BitVec 64))
(declare-fun x15_2 () (_ BitVec 64))
(declare-fun x14_6 () (_ BitVec 64))
(declare-fun x14_5 () (_ BitVec 64))
(declare-fun x14_3 () (_ BitVec 64))
(declare-fun x14_2 () (_ BitVec 64))
(declare-fun x13_6 () (_ BitVec 64))
(declare-fun x13_5 () (_ BitVec 64))
(declare-fun x13_3 () (_ BitVec 64))
(declare-fun x13_2 () (_ BitVec 64))
(declare-fun x12_6 () (_ BitVec 64))
(declare-fun x12_5 () (_ BitVec 64))
(declare-fun x12_3 () (_ BitVec 64))
(declare-fun x12_2 () (_ BitVec 64))
(declare-fun x11_6 () (_ BitVec 64))
(declare-fun x11_5 () (_ BitVec 64))
(declare-fun x11_3 () (_ BitVec 64))
(declare-fun x11_2 () (_ BitVec 64))
(declare-fun x10_6 () (_ BitVec 64))
(declare-fun x10_5 () (_ BitVec 64))
(declare-fun x10_3 () (_ BitVec 64))
(declare-fun x10_2 () (_ BitVec 64))
(declare-fun m5_0 () (_ BitVec 64))
(declare-fun m4_0 () (_ BitVec 64))
(declare-fun m3_0 () (_ BitVec 64))
(declare-fun m2_0 () (_ BitVec 64))
(declare-fun m1_0 () (_ BitVec 64))
(declare-fun m0_0 () (_ BitVec 64))
(declare-fun dontcare_2 () (_ BitVec 1))
(declare-fun dontcare_1 () (_ BitVec 1))
(declare-fun d5_0 () (_ BitVec 64))
(declare-fun d4_0 () (_ BitVec 64))
(declare-fun d3_0 () (_ BitVec 64))
(declare-fun d2_0 () (_ BitVec 64))
(declare-fun d1_0 () (_ BitVec 64))
(declare-fun d0_0 () (_ BitVec 64))
(declare-fun carry_22 () (_ BitVec 1))
(declare-fun carry_21 () (_ BitVec 1))
(declare-fun carry_20 () (_ BitVec 1))
(declare-fun carry_19 () (_ BitVec 1))
(declare-fun carry_18 () (_ BitVec 1))
(declare-fun carry_17 () (_ BitVec 1))
(declare-fun carry_16 () (_ BitVec 1))
(declare-fun carry_15 () (_ BitVec 1))
(declare-fun carry_14 () (_ BitVec 1))
(declare-fun carry_13 () (_ BitVec 1))
(declare-fun carry_12 () (_ BitVec 1))
(declare-fun carry_11 () (_ BitVec 1))
(declare-fun carry_10 () (_ BitVec 1))
(declare-fun carry_9 () (_ BitVec 1))
(declare-fun carry_8 () (_ BitVec 1))
(declare-fun carry_7 () (_ BitVec 1))
(declare-fun carry_6 () (_ BitVec 1))
(declare-fun carry_5 () (_ BitVec 1))
(declare-fun carry_4 () (_ BitVec 1))
(declare-fun carry_3 () (_ BitVec 1))
(declare-fun carry_2 () (_ BitVec 1))
(declare-fun carry_1 () (_ BitVec 1))
(declare-fun c5_0 () (_ BitVec 64))
(declare-fun c4_0 () (_ BitVec 64))
(declare-fun c3_0 () (_ BitVec 64))
(declare-fun c2_0 () (_ BitVec 64))
(declare-fun c1_0 () (_ BitVec 64))
(declare-fun c0_0 () (_ BitVec 64))
(declare-fun b5_0 () (_ BitVec 64))
(declare-fun b4_0 () (_ BitVec 64))
(declare-fun b3_0 () (_ BitVec 64))
(declare-fun b2_0 () (_ BitVec 64))
(declare-fun b1_0 () (_ BitVec 64))
(declare-fun b0_0 () (_ BitVec 64))
(declare-fun a5_0 () (_ BitVec 64))
(declare-fun a4_0 () (_ BitVec 64))
(declare-fun a3_0 () (_ BitVec 64))
(declare-fun a2_0 () (_ BitVec 64))
(declare-fun a1_0 () (_ BitVec 64))
(declare-fun a0_0 () (_ BitVec 64))
(assert (and (and (and (and (and (and (and (and (and (= m0_0 #xB9FEFFFFFFFFAAAB) (= m1_0 #x1EABFFFEB153FFFF)) (= m2_0 #x6730D2A0F6B0F624)) (= m3_0 #x64774B84F38512BF)) (= m4_0 #x4B1BA7B6434BACD7)) (= m5_0 #x1A0111EA397FE69A)) (bvult (bvadd (bvmul ((_ zero_extend 320) a0_0) #x000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001) (bvadd (bvmul ((_ zero_extend 320) a1_0) #x000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000) (bvadd (bvmul ((_ zero_extend 320) a2_0) #x000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000) (bvadd (bvmul ((_ zero_extend 320) a3_0) #x000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000) (bvadd (bvmul ((_ zero_extend 320) a4_0) #x000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000) (bvmul ((_ zero_extend 320) a5_0) #x000000000000000100000000000000000000000000000000000000000000000000000000000000000000000000000000)))))) (bvadd (bvmul ((_ zero_extend 320) m0_0) #x000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001) (bvadd (bvmul ((_ zero_extend 320) m1_0) #x000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000) (bvadd (bvmul ((_ zero_extend 320) m2_0) #x000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000) (bvadd (bvmul ((_ zero_extend 320) m3_0) #x000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000) (bvadd (bvmul ((_ zero_extend 320) m4_0) #x000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000) (bvmul ((_ zero_extend 320) m5_0) #x000000000000000100000000000000000000000000000000000000000000000000000000000000000000000000000000)))))))) (bvult (bvadd (bvmul ((_ zero_extend 320) b0_0) #x000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001) (bvadd (bvmul ((_ zero_extend 320) b1_0) #x000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000) (bvadd (bvmul ((_ zero_extend 320) b2_0) #x000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000) (bvadd (bvmul ((_ zero_extend 320) b3_0) #x000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000) (bvadd (bvmul ((_ zero_extend 320) b4_0) #x000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000) (bvmul ((_ zero_extend 320) b5_0) #x000000000000000100000000000000000000000000000000000000000000000000000000000000000000000000000000)))))) (bvadd (bvmul ((_ zero_extend 320) m0_0) #x000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001) (bvadd (bvmul ((_ zero_extend 320) m1_0) #x000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000) (bvadd (bvmul ((_ zero_extend 320) m2_0) #x000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000) (bvadd (bvmul ((_ zero_extend 320) m3_0) #x000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000) (bvadd (bvmul ((_ zero_extend 320) m4_0) #x000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000) (bvmul ((_ zero_extend 320) m5_0) #x000000000000000100000000000000000000000000000000000000000000000000000000000000000000000000000000)))))))) (bvult (bvadd (bvmul ((_ zero_extend 320) c0_0) #x000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001) (bvadd (bvmul ((_ zero_extend 320) c1_0) #x000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000) (bvadd (bvmul ((_ zero_extend 320) c2_0) #x000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000) (bvadd (bvmul ((_ zero_extend 320) c3_0) #x000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000) (bvadd (bvmul ((_ zero_extend 320) c4_0) #x000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000) (bvmul ((_ zero_extend 320) c5_0) #x000000000000000100000000000000000000000000000000000000000000000000000000000000000000000000000000)))))) (bvadd (bvmul ((_ zero_extend 320) m0_0) #x000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001) (bvadd (bvmul ((_ zero_extend 320) m1_0) #x000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000) (bvadd (bvmul ((_ zero_extend 320) m2_0) #x000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000) (bvadd (bvmul ((_ zero_extend 320) m3_0) #x000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000) (bvadd (bvmul ((_ zero_extend 320) m4_0) #x000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000) (bvmul ((_ zero_extend 320) m5_0) #x000000000000000100000000000000000000000000000000000000000000000000000000000000000000000000000000)))))))) (bvult (bvadd (bvmul ((_ zero_extend 320) d0_0) #x000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001) (bvadd (bvmul ((_ zero_extend 320) d1_0) #x000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000) (bvadd (bvmul ((_ zero_extend 320) d2_0) #x000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000) (bvadd (bvmul ((_ zero_extend 320) d3_0) #x000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000) (bvadd (bvmul ((_ zero_extend 320) d4_0) #x000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000) (bvmul ((_ zero_extend 320) d5_0) #x000000000000000100000000000000000000000000000000000000000000000000000000000000000000000000000000)))))) (bvadd (bvmul ((_ zero_extend 320) m0_0) #x000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001) (bvadd (bvmul ((_ zero_extend 320) m1_0) #x000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000) (bvadd (bvmul ((_ zero_extend 320) m2_0) #x000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000) (bvadd (bvmul ((_ zero_extend 320) m3_0) #x000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000) (bvadd (bvmul ((_ zero_extend 320) m4_0) #x000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000) (bvmul ((_ zero_extend 320) m5_0) #x000000000000000100000000000000000000000000000000000000000000000000000000000000000000000000000000)))))))))
(assert (and (= carry_1 ((_ extract 64 64) (bvadd (bvadd ((_ zero_extend 1) a0_0) ((_ zero_extend 1) (bvnot c0_0))) #b00000000000000000000000000000000000000000000000000000000000000001))) (= x10_2 ((_ extract 63 0) (bvadd (bvadd ((_ zero_extend 1) a0_0) ((_ zero_extend 1) (bvnot c0_0))) #b00000000000000000000000000000000000000000000000000000000000000001)))))
(assert (and (= carry_2 ((_ extract 64 64) (bvadd (bvadd ((_ zero_extend 1) a1_0) ((_ zero_extend 1) (bvnot c1_0))) ((_ zero_extend 64) carry_1)))) (= x11_2 ((_ extract 63 0) (bvadd (bvadd ((_ zero_extend 1) a1_0) ((_ zero_extend 1) (bvnot c1_0))) ((_ zero_extend 64) carry_1))))))
(assert (and (= carry_3 ((_ extract 64 64) (bvadd (bvadd ((_ zero_extend 1) a2_0) ((_ zero_extend 1) (bvnot c2_0))) ((_ zero_extend 64) carry_2)))) (= x12_2 ((_ extract 63 0) (bvadd (bvadd ((_ zero_extend 1) a2_0) ((_ zero_extend 1) (bvnot c2_0))) ((_ zero_extend 64) carry_2))))))
(assert (and (= carry_4 ((_ extract 64 64) (bvadd (bvadd ((_ zero_extend 1) a3_0) ((_ zero_extend 1) (bvnot c3_0))) ((_ zero_extend 64) carry_3)))) (= x13_2 ((_ extract 63 0) (bvadd (bvadd ((_ zero_extend 1) a3_0) ((_ zero_extend 1) (bvnot c3_0))) ((_ zero_extend 64) carry_3))))))
(assert (and (= carry_5 ((_ extract 64 64) (bvadd (bvadd ((_ zero_extend 1) a4_0) ((_ zero_extend 1) (bvnot c4_0))) ((_ zero_extend 64) carry_4)))) (= x14_2 ((_ extract 63 0) (bvadd (bvadd ((_ zero_extend 1) a4_0) ((_ zero_extend 1) (bvnot c4_0))) ((_ zero_extend 64) carry_4))))))
(assert (and (= carry_6 ((_ extract 64 64) (bvadd (bvadd ((_ zero_extend 1) a5_0) ((_ zero_extend 1) (bvnot c5_0))) ((_ zero_extend 64) carry_5)))) (= x15_2 ((_ extract 63 0) (bvadd (bvadd ((_ zero_extend 1) a5_0) ((_ zero_extend 1) (bvnot c5_0))) ((_ zero_extend 64) carry_5))))))
(assert (= x3_1 (ite (= carry_6 #b1) #x0000000000000000 #xFFFFFFFFFFFFFFFF)))
(assert (= x16_2 (bvand m0_0 x3_1)))
(assert (= x17_2 (bvand m1_0 x3_1)))
(assert (and (= carry_7 ((_ extract 64 64) (bvadd ((_ zero_extend 1) x10_2) ((_ zero_extend 1) x16_2)))) (= x10_3 ((_ extract 63 0) (bvadd ((_ zero_extend 1) x10_2) ((_ zero_extend 1) x16_2))))))
(assert (= x19_2 (bvand m2_0 x3_1)))
(assert (and (= carry_8 ((_ extract 64 64) (bvadd (bvadd ((_ zero_extend 1) x11_2) ((_ zero_extend 1) x17_2)) ((_ zero_extend 64) carry_7)))) (= x11_3 ((_ extract 63 0) (bvadd (bvadd ((_ zero_extend 1) x11_2) ((_ zero_extend 1) x17_2)) ((_ zero_extend 64) carry_7))))))
(assert (= x20_2 (bvand m3_0 x3_1)))
(assert (and (= carry_9 ((_ extract 64 64) (bvadd (bvadd ((_ zero_extend 1) x12_2) ((_ zero_extend 1) x19_2)) ((_ zero_extend 64) carry_8)))) (= x12_3 ((_ extract 63 0) (bvadd (bvadd ((_ zero_extend 1) x12_2) ((_ zero_extend 1) x19_2)) ((_ zero_extend 64) carry_8))))))
(assert (= x21_2 (bvand m4_0 x3_1)))
(assert (and (= carry_10 ((_ extract 64 64) (bvadd (bvadd ((_ zero_extend 1) x13_2) ((_ zero_extend 1) x20_2)) ((_ zero_extend 64) carry_9)))) (= x13_3 ((_ extract 63 0) (bvadd (bvadd ((_ zero_extend 1) x13_2) ((_ zero_extend 1) x20_2)) ((_ zero_extend 64) carry_9))))))
(assert (= x22_2 (bvand m5_0 x3_1)))
(assert (and (= carry_11 ((_ extract 64 64) (bvadd (bvadd ((_ zero_extend 1) x14_2) ((_ zero_extend 1) x21_2)) ((_ zero_extend 64) carry_10)))) (= x14_3 ((_ extract 63 0) (bvadd (bvadd ((_ zero_extend 1) x14_2) ((_ zero_extend 1) x21_2)) ((_ zero_extend 64) carry_10))))))
(assert (and (= dontcare_1 ((_ extract 64 64) (bvadd (bvadd ((_ zero_extend 1) x15_2) ((_ zero_extend 1) x22_2)) ((_ zero_extend 64) carry_11)))) (= x15_3 ((_ extract 63 0) (bvadd (bvadd ((_ zero_extend 1) x15_2) ((_ zero_extend 1) x22_2)) ((_ zero_extend 64) carry_11))))))
(assert (and (= carry_12 ((_ extract 64 64) (bvadd (bvadd ((_ zero_extend 1) b0_0) ((_ zero_extend 1) (bvnot d0_0))) #b00000000000000000000000000000000000000000000000000000000000000001))) (= x10_5 ((_ extract 63 0) (bvadd (bvadd ((_ zero_extend 1) b0_0) ((_ zero_extend 1) (bvnot d0_0))) #b00000000000000000000000000000000000000000000000000000000000000001)))))
(assert (and (= carry_13 ((_ extract 64 64) (bvadd (bvadd ((_ zero_extend 1) b1_0) ((_ zero_extend 1) (bvnot d1_0))) ((_ zero_extend 64) carry_12)))) (= x11_5 ((_ extract 63 0) (bvadd (bvadd ((_ zero_extend 1) b1_0) ((_ zero_extend 1) (bvnot d1_0))) ((_ zero_extend 64) carry_12))))))
(assert (and (= carry_14 ((_ extract 64 64) (bvadd (bvadd ((_ zero_extend 1) b2_0) ((_ zero_extend 1) (bvnot d2_0))) ((_ zero_extend 64) carry_13)))) (= x12_5 ((_ extract 63 0) (bvadd (bvadd ((_ zero_extend 1) b2_0) ((_ zero_extend 1) (bvnot d2_0))) ((_ zero_extend 64) carry_13))))))
(assert (and (= carry_15 ((_ extract 64 64) (bvadd (bvadd ((_ zero_extend 1) b3_0) ((_ zero_extend 1) (bvnot d3_0))) ((_ zero_extend 64) carry_14)))) (= x13_5 ((_ extract 63 0) (bvadd (bvadd ((_ zero_extend 1) b3_0) ((_ zero_extend 1) (bvnot d3_0))) ((_ zero_extend 64) carry_14))))))
(assert (and (= carry_16 ((_ extract 64 64) (bvadd (bvadd ((_ zero_extend 1) b4_0) ((_ zero_extend 1) (bvnot d4_0))) ((_ zero_extend 64) carry_15)))) (= x14_5 ((_ extract 63 0) (bvadd (bvadd ((_ zero_extend 1) b4_0) ((_ zero_extend 1) (bvnot d4_0))) ((_ zero_extend 64) carry_15))))))
(assert (and (= carry_17 ((_ extract 64 64) (bvadd (bvadd ((_ zero_extend 1) b5_0) ((_ zero_extend 1) (bvnot d5_0))) ((_ zero_extend 64) carry_16)))) (= x15_5 ((_ extract 63 0) (bvadd (bvadd ((_ zero_extend 1) b5_0) ((_ zero_extend 1) (bvnot d5_0))) ((_ zero_extend 64) carry_16))))))
(assert (= x3_2 (ite (= carry_17 #b1) #x0000000000000000 #xFFFFFFFFFFFFFFFF)))
(assert (= x16_4 (bvand m0_0 x3_2)))
(assert (= x17_4 (bvand m1_0 x3_2)))
(assert (and (= carry_18 ((_ extract 64 64) (bvadd ((_ zero_extend 1) x10_5) ((_ zero_extend 1) x16_4)))) (= x10_6 ((_ extract 63 0) (bvadd ((_ zero_extend 1) x10_5) ((_ zero_extend 1) x16_4))))))
(assert (= x19_4 (bvand m2_0 x3_2)))
(assert (and (= carry_19 ((_ extract 64 64) (bvadd (bvadd ((_ zero_extend 1) x11_5) ((_ zero_extend 1) x17_4)) ((_ zero_extend 64) carry_18)))) (= x11_6 ((_ extract 63 0) (bvadd (bvadd ((_ zero_extend 1) x11_5) ((_ zero_extend 1) x17_4)) ((_ zero_extend 64) carry_18))))))
(assert (= x20_4 (bvand m3_0 x3_2)))
(assert (and (= carry_20 ((_ extract 64 64) (bvadd (bvadd ((_ zero_extend 1) x12_5) ((_ zero_extend 1) x19_4)) ((_ zero_extend 64) carry_19)))) (= x12_6 ((_ extract 63 0) (bvadd (bvadd ((_ zero_extend 1) x12_5) ((_ zero_extend 1) x19_4)) ((_ zero_extend 64) carry_19))))))
(assert (= x21_4 (bvand m4_0 x3_2)))
(assert (and (= carry_21 ((_ extract 64 64) (bvadd (bvadd ((_ zero_extend 1) x13_5) ((_ zero_extend 1) x20_4)) ((_ zero_extend 64) carry_20)))) (= x13_6 ((_ extract 63 0) (bvadd (bvadd ((_ zero_extend 1) x13_5) ((_ zero_extend 1) x20_4)) ((_ zero_extend 64) carry_20))))))
(assert (= x22_4 (bvand m5_0 x3_2)))
(assert (and (= carry_22 ((_ extract 64 64) (bvadd (bvadd ((_ zero_extend 1) x14_5) ((_ zero_extend 1) x21_4)) ((_ zero_extend 64) carry_21)))) (= x14_6 ((_ extract 63 0) (bvadd (bvadd ((_ zero_extend 1) x14_5) ((_ zero_extend 1) x21_4)) ((_ zero_extend 64) carry_21))))))
(assert (and (= dontcare_2 ((_ extract 64 64) (bvadd (bvadd ((_ zero_extend 1) x15_5) ((_ zero_extend 1) x22_4)) ((_ zero_extend 64) carry_22)))) (= x15_6 ((_ extract 63 0) (bvadd (bvadd ((_ zero_extend 1) x15_5) ((_ zero_extend 1) x22_4)) ((_ zero_extend 64) carry_22))))))
(assert (not (= (bvurem (bvadd (bvadd (bvmul ((_ zero_extend 320) x10_3) #x000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001) (bvadd (bvmul ((_ zero_extend 320) x11_3) #x000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000) (bvadd (bvmul ((_ zero_extend 320) x12_3) #x000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000) (bvadd (bvmul ((_ zero_extend 320) x13_3) #x000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000) (bvadd (bvmul ((_ zero_extend 320) x14_3) #x000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000) (bvmul ((_ zero_extend 320) x15_3) #x000000000000000100000000000000000000000000000000000000000000000000000000000000000000000000000000)))))) (bvadd (bvmul ((_ zero_extend 320) c0_0) #x000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001) (bvadd (bvmul ((_ zero_extend 320) c1_0) #x000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000) (bvadd (bvmul ((_ zero_extend 320) c2_0) #x000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000) (bvadd (bvmul ((_ zero_extend 320) c3_0) #x000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000) (bvadd (bvmul ((_ zero_extend 320) c4_0) #x000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000) (bvmul ((_ zero_extend 320) c5_0) #x000000000000000100000000000000000000000000000000000000000000000000000000000000000000000000000000))))))) (bvadd (bvmul ((_ zero_extend 320) m0_0) #x000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001) (bvadd (bvmul ((_ zero_extend 320) m1_0) #x000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000) (bvadd (bvmul ((_ zero_extend 320) m2_0) #x000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000) (bvadd (bvmul ((_ zero_extend 320) m3_0) #x000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000) (bvadd (bvmul ((_ zero_extend 320) m4_0) #x000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000) (bvmul ((_ zero_extend 320) m5_0) #x000000000000000100000000000000000000000000000000000000000000000000000000000000000000000000000000))))))) (bvurem (bvadd (bvmul ((_ zero_extend 320) a0_0) #x000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001) (bvadd (bvmul ((_ zero_extend 320) a1_0) #x000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000) (bvadd (bvmul ((_ zero_extend 320) a2_0) #x000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000) (bvadd (bvmul ((_ zero_extend 320) a3_0) #x000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000) (bvadd (bvmul ((_ zero_extend 320) a4_0) #x000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000) (bvmul ((_ zero_extend 320) a5_0) #x000000000000000100000000000000000000000000000000000000000000000000000000000000000000000000000000)))))) (bvadd (bvmul ((_ zero_extend 320) m0_0) #x000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001) (bvadd (bvmul ((_ zero_extend 320) m1_0) #x000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000) (bvadd (bvmul ((_ zero_extend 320) m2_0) #x000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000) (bvadd (bvmul ((_ zero_extend 320) m3_0) #x000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000) (bvadd (bvmul ((_ zero_extend 320) m4_0) #x000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000) (bvmul ((_ zero_extend 320) m5_0) #x000000000000000100000000000000000000000000000000000000000000000000000000000000000000000000000000))))))))))
(check-sat)
(exit)