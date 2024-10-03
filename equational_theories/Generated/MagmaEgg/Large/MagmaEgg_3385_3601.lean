import equational_theories.AllEquations
import equational_theories.Magma

private def congr_op {G: Type _} [Magma G] {a b c d: G} (h1: a = b) (h2: c = d): a ∘ c = b ∘ d := by
  rw [h1, h2]
private abbrev T := @Eq.trans
private abbrev S := @Eq.symm
private abbrev R := @Eq.refl
private abbrev M := @Magma.op
private abbrev C := @congr_op

set_option maxRecDepth 999999

@[equational_result]
theorem Equation3385_implies_Equation3601 (G: Type _) [Magma G] (h: Equation3385 G) : Equation3601 G := fun x y z =>
  let v0 := M y x
  let v1 := M v0 z
  have h2 := h z v1 v1
  have h3 := S h2
  have h4 := h v1 v0 z
  have h5 := h y x z
  have h6 := S h5
  let v7 := M z v1
  let v8 := M x z
  have h9 := h z (M y v8) v7
  have h10 := S h9
  have h11 := R v7
  have h12 := h y v8 v7
  have h13 := S h12
  have h14 := h x z v0
  have h15 := h z y x
  have h16 := R v0
  have h17 := R y
  have h18 := C h11 (C h17 (C (T (C h16 h15) (S h14)) h11))
  have h19 := h y (M v0 (M z y)) v7
  have h20 := h v0 z y
  have h21 := T (T (T h20 h19) h18) h13
  have h22 := C h21 h11
  have h23 := R z
  have h24 := C h11 (C h23 h22)
  have h25 := h z v1 v7
  have h26 := T (T (T h25 h24) h10) h6
  have h27 := S h20
  have h28 := S h19
  have h29 := S h15
  have h30 := C h11 (C h17 (C (T h14 (C h16 h29)) h11))
  have h31 := T (T (T h12 h30) h28) h27
  have h32 := C h31 h26
  have h33 := R v1
  have h34 := C h33 (T (T h22 h32) h4)
  have h35 := h v1 z v1
  have h36 := T (T (T (T (T (T h35 h34) h3) h25) h24) h10) h6
  have h37 := R x
  have h38 := C h31 h11
  have h39 := h v0 z z
  have h40 := S h39
  let v41 := M v0 (M z z)
  have h42 := h z v41 v1
  have h43 := S h42
  have h44 := h z z z
  have h45 := S h44
  have h46 := h z z v7
  have h47 := S h46
  have h48 := h z v0 z
  have h49 := h z v0 v0
  have h50 := S h49
  have h51 := C h26 (C h23 (C h36 h26))
  let v52 := M v1 z
  have h53 := h z v52 v7
  have h54 := h z v1 z
  have h55 := T (T h35 h34) h3
  have h56 := C h55 (T (T h54 (C h23 (T (T h53 h51) h50))) (C h23 h48))
  have h57 := C h23 (T h56 h47)
  have h58 := S h25
  have h59 := C h11 (C h23 h38)
  have h60 := T (T (T h5 h9) h59) h58
  have h61 := R v52
  have h62 := C h61 h60
  have h63 := C h23 h62
  have h64 := S h35
  have h65 := C h21 h60
  have h66 := S h4
  have h67 := C h33 (T (T h66 h65) h38)
  have h68 := T (T h2 h67) h64
  have h69 := C h68 (T (T (T (T (T h34 h3) h25) h24) h10) h6)
  have h70 := h v1 v1 v7
  have h71 := C h23 (T h70 h69)
  have h72 := C h26 (T (C h23 (T (T (T (T h32 h4) h71) h63) h57)) h45)
  have h73 := C (T (T (T (T (T h35 h34) h3) h25) h24) h72) h33
  have h74 := C h33 (C h23 h73)
  have h75 := h z v52 v1
  have h76 := C (T (T (T (T (T (T (T h75 h74) h43) h40) h20) h19) h18) h13) h11
  have h77 := S h54
  let v78 := M z v52
  have h79 := h z v78 v7
  have h80 := R v78
  have h81 := C h80 h60
  have h82 := C h80 h26
  have h83 := S h75
  have h84 := S h70
  have h85 := C h55 (T (T (T (T (T h5 h9) h59) h58) h2) h67)
  have h86 := C h23 (T h85 h84)
  have h87 := C h61 h26
  have h88 := C h23 h87
  have h89 := S h53
  have h90 := T (T (T (T (T (T h5 h9) h59) h58) h2) h67) h64
  have h91 := C h90 h60
  have h92 := C h60 (C h23 h91)
  have h93 := S h48
  have h94 := C h68 (T (T (C h23 h93) (C h23 (T (T h49 h92) h89))) h77)
  have h95 := C h23 (T h46 h94)
  have h96 := C h60 (T h44 (C h23 (T (T (T (T h95 h88) h86) h66) h65)))
  have h97 := C (T (T (T (T (T h96 h59) h58) h2) h67) h64) h33
  have h98 := C h33 (C h23 h97)
  have h99 := C (T (T (T (T (T (T (T h12 h30) h28) h27) h39) h42) h98) h83) h11
  have h100 := T (T (T h75 h74) h43) h40
  have h101 := T (T (T h93 h49) h92) h89
  have h102 := T (T (T h39 h42) h98) h83
  let v103 := M z v7
  have h104 := h v0 v103 v1
  have h105 := h v0 v103 v0
  have h106 := T (T (T h53 h51) h50) h48
  have h107 := R v41
  have h108 := h z v41 v0
  have h109 := T (T (T (T (T (T (T (C h90 h33) h73) (C (T (T h96 h10) h6) (T (T h39 h108) (C h16 (T (T (T (T (T (C h23 (C h107 h60)) (C h23 (T (C (T (T h96 h59) h58) (T h2 h67)) h84))) h66) h65) h99) (C h106 h26)))))) (S h105)) h104) (C h102 (T (T (C h60 (T (T (T (T (T (T (T (T (T (C h101 h33) (C h100 h33)) h70) h69) h62) h56) h47) h44) (C h23 (T (T (T (T (T (T h95 h88) h86) h66) h65) h99) h82))) (C h23 h81))) (S h79)) h77))) h76) h38
  have h110 := C h36 h33
  have h111 := T h34 h3
  have h112 := C (T (T h5 h9) h72) (T (T (C h16 (T (T (T (T (T (C h101 h60) h76) h32) h4) (C h23 (T h70 (C (T (T h25 h24) h72) h111)))) (C h23 (C h107 h26)))) (S h108)) h40)
  have h113 := h v1 y v0
  have h114 := h y v0 v1
  have h115 := S h114
  have h116 := h v1 v0 v7
  have h117 := S h116
  have h118 := h v0 z v1
  have h119 := C h11 h118
  have h120 := C h33 (T (C h17 (T (T (T h119 h117) h65) h38)) (C h17 (T (T (T (T (T (T (T h22 h99) (C h100 (T (T h54 h79) (C h26 (T (T (T (T (T (T (T (T (T (C h23 h82) (C h23 (T (T (T (T (T (T h81 h76) h32) h4) h71) h63) h57))) h45) h46) h94) h87) h85) h84) (C h102 h33)) (C h106 h33)))))) (S h104)) h105) h112) h97) h110)))
  have h121 := h y v7 v1
  have h122 := h y z v1
  have h123 := h y z v7
  have h124 := h y v1 z
  have h125 := h z y v7
  have h126 := C h26 (T (T (T (T (T (T (C h37 h93) h29) h125) (C h11 (T (T (T (C h23 (T (T (T h121 h120) h115) (C h17 h90))) (S h124)) (C h17 (T (T (T (T (T (T h39 h42) h98) h83) h53) h51) h50))) (C h17 h48)))) (S h123)) h122) (C h33 (T (T h121 h120) h115)))
  have h127 := h x z v7
  have h128 := C h17 (T (T (T (T (T (T h49 h92) h89) h75) h74) h43) h40)
  have h129 := C h17 h93
  have h130 := S h122
  have h131 := S h121
  have h132 := C h33 (T (C h17 h109) (C h17 (T (T (T h22 h32) h116) (C h11 (S h118)))))
  have h133 := C h33 (T (T h114 h132) h131)
  T (T (T (T (T (T (h x y x) (C h37 (T (T (h x v0 v0) (C h60 (T (C h37 (T (T (T h91 h87) h85) h84)) (C h37 (T h70 (C h11 h111)))))) (S (h x v7 v7))))) (C h37 (T (T (h x v7 v1) (C h33 (T (T (T (T (C h37 (T h119 h117)) (S (h v1 y x))) h113) (C h60 (T (T (T (T (T (T h133 h130) h123) (C h11 (T (T (T h129 h128) h124) (C h23 (T (T (T (C h17 h36) h114) h132) h131))))) (S h125)) h15) (C h37 h48)))) (S h127)))) (C h33 (T (T (T h127 h126) (C h16 (T (T (T (T (T (T h133 h130) h123) (C h11 (T (T (T (T h129 h128) (h y v1 x)) (C h37 (T (T (T (T (T (C h17 (T (h v1 x v7) (C h26 (T (T (T (T (T (S (h x z v1)) h127) h126) (S h113)) (C h102 h17)) (C h106 h17))))) (S (h v0 v103 y))) h105) h112) h97) h110))) (C h37 h109)))) (S (h x v1 v7))) (h x v1 z)) (C h23 (C h37 h36))))) (S (h z x v0))))))) (S (h v1 z x))) h35) h34) h3

