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
theorem Equation1165_implies_Equation759 (G: Type _) [Magma G] (h: Equation1165 G) : Equation759 G := fun x y z =>
  let v0 := M y x
  let v1 := M v0 z
  let v2 := M z v1
  let v3 := M y v2
  have h4 := h v3 x y
  let v5 := M x v3
  have h6 := R x
  have h7 := h v3 x x
  let v8 := M (M x v5) x
  have h9 := R z
  let v10 := M (M z v3) z
  have h11 := h v2 z x
  have h12 := S h11
  have h13 := h (M z v2) z x
  have h14 := R v2
  have h15 := h z v2 v0
  have h16 := R v0
  have h17 := h z v0 z
  have h18 := C h9 (C (T (C h14 (C h17 h16)) (S h15)) h14)
  have h19 := h v0 z v2
  have h20 := T h19 h18
  have h21 := h v0 z x
  have h22 := S h21
  let v23 := M z v0
  let v24 := M (M x v23) x
  have h25 := h v24 z x
  have h26 := h v24 z v2
  have h27 := C h9 (C (C h6 (T (T (T (T (C h9 (C (C h14 h21) h14)) (S h26)) h25) (C h9 (T (C (C h6 h22) h6) (C (C h6 h20) h6)))) (S h13))) h6)
  let v28 := M (M v2 v0) v2
  have h29 := h v28 z x
  have h30 := R y
  have h31 := h x y v2
  let v32 := M v0 y
  have h33 := R v3
  have h34 := h x x v3
  have h35 := S h34
  let v36 := M (M v3 (M x x)) v3
  have h37 := h v36 x v1
  have h38 := R v1
  have h39 := h x v2 z
  have h40 := S h39
  have h41 := C h38 h40
  have h42 := C h38 h39
  let v43 := M v1 v23
  have h44 := h v1 v43 z
  have h45 := S h44
  have h46 := h v0 z v1
  have h47 := S h19
  have h48 := C h9 (C (T h15 (C h14 (C (S h17) h16))) h14)
  have h49 := C h20 h9
  have h50 := R v43
  have h51 := C h50 (T h49 (C (T (T h48 h47) h46) h9))
  have h52 := h (M v43 v1) z x
  have h53 := S h52
  have h54 := h (M (M x v0) x) y x
  have h55 := S h54
  have h56 := h x y x
  have h57 := C h6 h40
  have h58 := C h6 h39
  have h59 := C h30 (T (C (T (C h6 (S h31)) h58) h6) (C (T h57 (C h6 h56)) h6))
  have h60 := h v28 y x
  have h61 := S h29
  have h62 := T h48 h47
  have h63 := C h9 (C (C h6 (T (T (T (T h13 (C h9 (T (C (C h6 h62) h6) (C (C h6 h21) h6)))) (S h25)) h26) (C h9 (C (C h14 h22) h14)))) h6)
  have h64 := C h9 (T (T (T (T (T (T h11 h63) h61) h60) h59) h55) (C (C h6 h46) h6))
  have h65 := S h60
  have h66 := C h30 (T (C (T (C h6 (S h56)) h58) h6) (C (T h57 (C h6 h31)) h6))
  have h67 := h v0 z y
  have h68 := S h67
  have h69 := C h9 (T (T (T (T (T (T (C (C h6 h68) h6) h54) h66) h65) h29) h27) h12)
  let v70 := M (M y v23) y
  have h71 := h v70 z x
  have h72 := h v70 x v0
  have h73 := S h72
  have h74 := S h71
  have h75 := C h9 (T (T (T (T (T (T h11 h63) h61) h60) h59) h55) (C (C h6 h67) h6))
  have h76 := S h46
  have h77 := C h9 (T (T (T (T (T (T (C (C h6 h76) h6) h54) h66) h65) h29) h27) h12)
  have h78 := C h62 h9
  have h79 := C h50 (T (C (T (T h76 h19) h18) h9) h78)
  have h80 := T (T (T (T (T h44 h79) h52) h77) h75) h74
  have h81 := C h6 h80
  let v82 := M x v1
  have h83 := h (M (M v0 v82) v0) x x
  have h84 := h v1 x v0
  have h85 := h (M v82 x) x x
  have h86 := S h85
  have h87 := h v1 x v3
  have h88 := S h87
  have h89 := C (C h6 h88) h6
  let v90 := M (M v3 v82) v3
  have h91 := h v90 x x
  have h92 := C h6 (C (T h87 (C h6 (T h91 (C h6 h89)))) h6)
  have h93 := h v90 x y
  have h94 := C h6 (C (T (C h6 (T (C h6 (C (C h30 h87) h30)) (S h93))) h88) h6)
  let v95 := M y v1
  let v96 := M v95 y
  have h97 := h v96 x x
  have h98 := h v96 y y
  have h99 := S h98
  have h100 := h v1 y y
  have h101 := S h100
  have h102 := h (M (M y v95) y) y y
  have h103 := C h30 (C (T h100 (C h30 (T h102 (C h30 (C (C h30 h101) h30))))) h30)
  have h104 := C h6 (T (T (C h6 (T (T (T (T (T (T h103 h99) h97) h94) h92) h86) (C (C h6 h84) h6))) (S h83)) (C (C h16 h81) h16))
  have h105 := C (T (T (T (T (T (T (T h104 h73) h71) h69) h64) h53) h51) h45) h6
  have h106 := C h30 (C (T (C h30 (T (C h30 (C (C h30 h100) h30)) (S h102))) h101) h30)
  have h107 := S h97
  have h108 := C h6 (C (T h87 (C h6 (T h93 (C h6 (C (C h30 h88) h30))))) h6)
  have h109 := S h91
  have h110 := C (C h6 h87) h6
  have h111 := C h6 (C (T (C h6 (T (C h6 h110) h109)) h88) h6)
  have h112 := T (T (T (T (T h71 h69) h64) h53) h51) h45
  have h113 := C h6 h112
  have h114 := C h6 (T (T (C (C h16 h113) h16) h83) (C h6 (T (T (T (T (T (T (C (C h6 (S h84)) h6) h85) h111) h108) h107) h98) h106)))
  have h115 := C (T (T (T (C h9 (T h104 h73)) h68) h19) h18) h9
  have h116 := h v70 y v3
  have h117 := S h116
  have h118 := C h30 h80
  have h119 := h (M (M v3 v95) v3) y x
  have h120 := h v1 y v3
  have h121 := C h30 (T (T (C h30 (T (T (T (T (T (T h103 h99) h97) h94) h92) h86) (C (C h6 h120) h6))) (S h119)) (C (C h33 h118) h33))
  have h122 := T (T (T h121 h117) h72) h114
  have h123 := C (C h9 h122) h9
  have h124 := C h30 h112
  have h125 := C h30 (T (T (C (C h33 h124) h33) h119) (C h30 (T (T (T (T (T (T (C (C h6 (S h120)) h6) h85) h111) h108) h107) h98) h106)))
  have h126 := h v2 z z
  have h127 := C (T h126 (C h9 (T (T (T (T (T (T (T (T h78 h44) h79) h52) h77) h75) h74) h116) h125))) h9
  have h128 := h (M v2 z) x x
  have h129 := S h128
  have h130 := S h126
  have h131 := h v90 x z
  have h132 := C h6 (C (T h87 (C h6 (T h131 (C h6 (C (T (C h9 (T h88 h49)) h130) h9))))) h6)
  let v133 := M y (M v1 y)
  have h134 := h v133 x y
  have h135 := h (M x v133) x y
  have h136 := S h135
  have h137 := C (C h30 h122) h30
  have h138 := C (T h118 (C h30 (T h116 h125))) h30
  have h139 := C h6 (C (T (C h6 (T (C h6 (C (T h126 (C h9 (T h78 h87))) h9)) (S h131))) h88) h6)
  have h140 := C (T (C h9 (T (T (T (T (T (T (T (T h121 h117) h71) h69) h64) h53) h51) h45) h49)) h130) h9
  have h141 := T (T (T h104 h73) h116) h125
  have h142 := C (C h9 h141) h9
  have h143 := C (T (T (T h48 h47) h67) (C h9 (T h72 h114))) h9
  have h144 := C h6 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h71 h69) h64) h53) h51) h45) h49) h143) h142) h140) h128) h139) h108) h107) h138) h137)
  have h145 := T h144 h136
  have h146 := h (M (M y v82) y) x x
  have h147 := h v1 x y
  have h148 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (C h6 (T (T (T (T (T h144 h136) (C h6 (T (T (T (T (T (T h103 h99) h97) h94) h92) h86) (C (C h6 h147) h6)))) (S h146)) (C (C h30 h81) h30)) (C (C h30 h145) h30))) (S h134)) h103) h99) h97) h94) h132) h129) h127) h123) h115) h78) h44) h79) h52) h77) h75) h74) h72) h114) h6
  have h149 := C (C h6 h81) h6
  have h150 := h (M (M x v82) x) x x
  have h151 := S h150
  have h152 := h v1 x x
  have h153 := C h6 (T (T (T (T (T (T h103 h99) h97) h94) h92) h86) (C (C h6 h152) h6))
  have h154 := h v90 x v3
  have h155 := h (M (M v3 v1) v3) x x
  have h156 := h v133 x v1
  have h157 := h (M (M v1 v82) v1) x x
  have h158 := h v1 x v1
  have h159 := C (T (C h30 (T h121 h117)) h124) h30
  have h160 := C (C h30 h141) h30
  have h161 := C h6 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h160 h159) h97) h94) h132) h129) h127) h123) h115) h78) h44) h79) h52) h77) h75) h74)
  have h162 := T h135 h161
  have h163 := C h33 h162
  have h164 := C h33 h145
  have h165 := C h6 (T (T (T (T (T (T (C (C h6 (S h152)) h6) h85) h111) h108) h107) h98) h106)
  have h166 := C (C h6 h113) h6
  have h167 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h104 h73) h71) h69) h64) h53) h51) h45) h49) h143) h142) h140) h128) h139) h108) h107) h98) h106) h134) (C h6 (T (T (T (T (T (C (C h30 h162) h30) (C (C h30 h113) h30)) h146) (C h6 (T (T (T (T (T (T (C (C h6 (S h147)) h6) h85) h111) h108) h107) h98) h106))) h135) h161))) h6
  have h168 := C (T (T (T (T (T (T (T h44 h79) h52) h77) h75) h74) h72) h114) h6
  have h169 := h (M (M v3 (M v1 x)) v3) v1 y
  have h170 := h x v1 v3
  let v171 := M v1 v32
  have h172 := h v171 x v3
  have h173 := h (M v171 v1) v0 x
  have h174 := h y v0 v1
  have h175 := h y v0 z
  let v176 := M (M z v32) z
  have h177 := h v176 v0 x
  T (T h34 (C h6 (T (T (T h37 (C h6 (T (T (T (T (T (T (T (T (T (T (C (T (C h38 h35) h42) h38) (C (T (T (T (T (T (T (T (T h41 h168) h167) h166) h150) h165) h135) (C h6 (T (T (T (T (T (T (T (T h160 h159) h97) h94) (C h6 (C (T h87 (C h6 (T h154 (C h6 (C (C h33 h88) h33))))) h6))) (S h155)) (C (C h33 (T (T (T (T (T (T (T h44 h79) h52) h77) h75) h74) h116) h125)) h33)) (C (C h33 h122) h33)) (C (C h33 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h104 h73) h71) h69) h64) h53) h51) h45) h49) h143) h142) h140) h128) h139) h108) h107) h98) h106) h156) (C h6 (T (T (T (T (T (T (T (T (T (C (C h38 h162) h38) (C (C h38 h113) h38)) h157) (C h6 (T (C (C h6 (S h158)) h6) h110))) h109) (C (C h33 h81) h33)) (C h164 h33)) (C (T h163 (C h33 (T (T (T (T (T (T h144 h136) h153) h151) h149) h148) h105))) h33)) h169) (C h38 (C (C h30 (S h170)) h30)))))) h33)))) (S h172)) h38)) h173) (C h16 (C (T (C h6 (S h174)) (C h6 h175)) h6))) (S h177)) (h v176 x v3)) (C h6 (C (T (C h33 (T (C h6 (T (T (T (T h177 (C h16 (C (T (C h6 (S h175)) (C h6 h174)) h6))) (S h173)) (C (T (T (T (T (T (T (T (T h172 (C h6 (T (T (T (T (T (T (T (T (C (C h33 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (C h6 (T (T (T (T (T (T (T (T (T (C h38 (C (C h30 h170) h30)) (S h169)) (C (T (C h33 (T (T (T (T (T (T h168 h167) h166) h150) h165) h135) h161)) h164) h33)) (C h163 h33)) (C (C h33 h113) h33)) h91) (C h6 (T h89 (C (C h6 h158) h6)))) (S h157)) (C (C h38 h81) h38)) (C (C h38 h145) h38))) (S h156)) h103) h99) h97) h94) h132) h129) h127) h123) h115) h78) h44) h79) h52) h77) h75) h74) h72) h114)) h33) (C (C h33 h141) h33)) (C (C h33 (T (T (T (T (T (T (T h121 h117) h71) h69) h64) h53) h51) h45)) h33)) h155) (C h6 (C (T (C h6 (T (C h6 (C (C h33 h87) h33)) (S h154))) h88) h6))) h108) h107) h138) h137))) h136) h153) h151) h149) h148) h105) h42) h38)) (C (T h41 (C h38 h34)) h38))) (S h37))) (C h33 (T (h v36 x y) (C h6 (C (C h30 h35) h30))))) h33))) (S (h v32 x v3))) (h v32 y x)) (C h30 (T (C (C h6 (T (T (T (T (C h30 (C (C h30 h31) h30)) (S (h v28 y y))) h29) h27) h12)) h6) (C (C h6 (h v2 y z)) h6)))) (S (h v10 y x))))) (C h6 (T (T (T (h v10 x x) (C h6 (C (C h6 (T (T (T (C h6 (C (C h9 h7) h9)) (S (h v8 x z))) (h v8 x x)) (C h6 (C (C h6 (S h7)) h6)))) h6))) (S (h (M v5 x) x x))) (C (C h6 h4) h6)))) (S (h (M (M y v5) y) x x))))) (S h4)

