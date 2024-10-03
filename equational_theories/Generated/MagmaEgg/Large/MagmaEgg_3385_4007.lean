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
theorem Equation3385_implies_Equation4007 (G: Type _) [Magma G] (h: Equation3385 G) : Equation4007 G := fun x y z =>
  let v0 := M y x
  let v1 := M z v0
  have h2 := h v1 z z
  have h3 := S h2
  let v4 := M v1 z
  have h5 := h z (M v1 (M z z)) v4
  have h6 := S h5
  have h7 := R v4
  have h8 := h z z v0
  have h9 := R v1
  have h10 := C h9 (S h8)
  have h11 := h v0 z v1
  have h12 := h v0 z y
  have h13 := S h12
  have h14 := h z y x
  have h15 := S h14
  have h16 := R v0
  have h17 := C h16 h15
  have h18 := h x z v0
  have h19 := R y
  have h20 := C h19 (T h18 h17)
  have h21 := T (T (T h20 h13) h11) h10
  have h22 := R z
  have h23 := C h7 (C h22 (C h21 h7))
  have h24 := h z (M y (M x z)) v4
  have h25 := h y x z
  let v26 := M x y
  have h27 := R x
  have h28 := h z v0 z
  have h29 := S h28
  let v30 := M v0 z
  have h31 := h z (M z v30) v4
  have h32 := S h31
  have h33 := h z v30 v4
  have h34 := S h33
  have h35 := T h20 h13
  have h36 := C h7 (C h22 (C h35 h7))
  have h37 := T (T (T h25 h24) h36) h34
  have h38 := h v0 v1 z
  have h39 := h v0 v1 v1
  have h40 := S h39
  have h41 := h v1 z v0
  have h42 := C h9 h41
  have h43 := T (T (T (T h25 h24) h23) h6) h3
  have h44 := C h43 (T (T (T h42 h40) h38) (C h22 (C h37 h7)))
  have h45 := C h9 (S h41)
  have h46 := T h39 h45
  have h47 := C h16 h46
  have h48 := h v0 z v0
  have h49 := h x v1 z
  have h50 := S h25
  have h51 := S h24
  have h52 := S h18
  have h53 := C h16 h14
  have h54 := C h19 (T h53 h52)
  have h55 := S h11
  have h56 := C h9 h8
  have h57 := T (T (T h56 h55) h12) h54
  have h58 := C h7 (C h22 (C h57 h7))
  have h59 := T (T (T (T h2 h5) h58) h51) h50
  have h60 := C h59 (T (S h49) h15)
  have h61 := h z x v4
  have h62 := C h19 (T h61 h60)
  have h63 := C h27 (T (T (T (T (T (T h62 h13) h48) h47) h44) h32) h29)
  have h64 := h y z x
  have h65 := S h64
  have h66 := S h61
  have h67 := C h43 (T h14 h49)
  have h68 := C h19 (T h67 h66)
  have h69 := S h48
  have h70 := T h42 h40
  have h71 := C h16 h70
  have h72 := T h12 h54
  have h73 := C h7 (C h22 (C h72 h7))
  have h74 := T (T (T h33 h73) h51) h50
  have h75 := C h59 (T (T (T (C h22 (C h74 h7)) (S h38)) h39) h45)
  have h76 := C h27 (T (T (T (T (T (T h28 h31) h75) h71) h69) h12) h68)
  have h77 := C h74 h16
  have h78 := h z v30 v0
  have h79 := S h78
  have h80 := C h16 (T (C h22 (T (C (T (T (T (T (T (T h28 h31) h75) h71) h69) h11) h10) h43) (C h57 h59))) (C h22 (C h35 h16)))
  have h81 := h z v1 v0
  have h82 := h z v1 z
  have h83 := C (T (T (T (T h2 h5) h58) h36) h34) (T (T (T (T (T (T (T (S h82) h81) h80) h79) h33) h73) h51) h50)
  have h84 := h z z v4
  have h85 := h z z v1
  have h86 := S h81
  have h87 := C h16 (T (C h22 (C h72 h16)) (C h22 (T (C h21 h43) (C (T (T (T (T (T (T h56 h55) h48) h47) h44) h32) h29) h59))))
  have h88 := h y x v0
  have h89 := h x v0 z
  have h90 := S h89
  have h91 := C h27 (T h62 h13)
  have h92 := C h22 (T (T h14 h76) h91)
  have h93 := h z z y
  have h94 := C h22 (T (T (T (T (T (T (T (T (C h16 (T h93 (C h19 (T h92 h90)))) (S h88)) h25) h24) h36) h34) h78) h87) h86)
  have h95 := h v0 z z
  have h96 := h z v0 v1
  have h97 := h v1 v1 z
  have h98 := h v1 v1 v1
  have h99 := C h19 (T (T (T (T (T h98 (C h9 (T (T (T (T (T (T (T (T (C h9 (T h97 (C h22 h70))) (S h96)) h28) h31) h75) h71) h69) h95) h94))) (S h85)) h84) h83) h77)
  have h100 := S h98
  have h101 := S h95
  have h102 := C h27 (T h12 h68)
  have h103 := C h22 (T (T h102 h63) h15)
  have h104 := C h22 (T (T (T (T (T (T (T (T h81 h80) h79) h33) h73) h51) h50) h88) (C h16 (T (C h19 (T h89 h103)) (S h93))))
  have h105 := C h9 (T (T (T (T (T (T (T (T h104 h101) h48) h47) h44) h32) h29) h96) (C h9 (T (C h22 h46) (S h97))))
  have h106 := h z v0 y
  have h107 := S h106
  have h108 := h v0 y y
  have h109 := S h108
  have h110 := h y y v26
  have h111 := S h110
  have h112 := h y x y
  have h113 := R v26
  have h114 := C h113 h112
  have h115 := C h113 (S h112)
  have h116 := h y y x
  have h117 := h x y v0
  have h118 := C h19 (T (T h117 (C h16 (T (T (S h116) h110) h115))) (C h16 (T h114 h111)))
  have h119 := T h118 h109
  have h120 := C h19 (T (T (C h16 (T h110 h115)) (C h16 (T (T h114 h111) h116))) (S h117))
  have h121 := C h74 h19
  have h122 := C h37 h19
  have h123 := h v0 y z
  have h124 := S h123
  have h125 := h z y z
  have h126 := h z x v0
  have h127 := C h22 (T h126 (C h16 (T (T (T (T (C h22 (T h89 (C h22 (T h102 h65)))) (S h125)) h14) h76) h65)))
  have h128 := h z x z
  have h129 := h z x v1
  have h130 := h x v0 y
  have h131 := h z z x
  have h132 := S h84
  have h133 := C (T (T (T (T h33 h73) h23) h6) h3) (T (T (T (T (T (T (T h25 h24) h36) h34) h78) h87) h86) h82)
  have h134 := C h37 h16
  have h135 := h y v1 v1
  have h136 := C h19 (T (T (T (T (T (T h135 (C h9 (T (T (T (T (T h99 (C h19 (T (T (T (T (T h134 h133) h132) h131) (C h27 (T (T (T h127 h124) h108) h120))) (C h27 h119)))) (S h130)) h89) h103) (C h22 h14)))) (S h129)) h128) (C h22 (T (T (T (C h22 (T (T (T h18 h17) h67) h66)) h127) h124) h122))) (C h22 (T (T h121 h108) h120))) (C h22 h119))
  have h137 := S h131
  have h138 := C h22 (T (C h16 (T (T (T (T h64 h63) h15) h125) (C h22 (T (C h22 (T h64 h91)) h90)))) (S h126))
  have h139 := C h27 (T (T (T h118 h109) h123) h138)
  have h140 := T h108 h120
  T (T (T (T (T (T (T (h x y v26) (C h113 (T (T (T (T (T (T h139 h137) h85) (C h9 (T (T (T (T (T (T (T (T h104 h101) h48) h47) h44) h32) h29) h106) (C h19 (T (T (T (T (T (T (C h22 h140) (C h22 (T (T h118 h109) h122))) (C h22 (T (T (T h121 h123) h138) (C h22 (T (T (T h61 h60) h53) h52))))) (S h128)) h129) (C h9 (T (T (T (T (T (C h22 h15) h92) h90) h130) (C h19 (T (T (T (T (T (C h27 h140) h139) h137) h84) h83) h77))) (C h19 (T (T (T (T (T h134 h133) h132) h85) h105) h100))))) (S h135)))))) (C h9 (T (T (T (T (T (T (T (T (T (T h136 h107) h28) h31) h75) h71) h69) (h v0 z x)) (C h27 (T (T (T (T (C h16 (T (T (T (T (T h61 h60) h53) h52) (h x z z)) (C h22 (T (T (T (T (T (T (C h27 (T (T h84 h83) h77)) (S (h v0 y x))) h108) h120) (h y v26 v0)) (C h16 (T (C h19 (T (T (T (T (T h114 h111) (h y y v1)) (C h9 (T (T (T (T (T (T (T (T h136 h107) h28) h31) h75) h71) h69) h95) h94))) h105) h100)) h99))) (S (h y v0 v0)))))) (S (h z y v0))) h14) h76) h65))) (C h27 (T (T h64 h63) h15))) (C h27 h14)))) (S (h x x v1))) (h x x y)))) (S (h y x v26))) h25) h24) h23) h6) h3

