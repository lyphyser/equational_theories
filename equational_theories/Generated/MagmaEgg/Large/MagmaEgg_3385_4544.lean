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
theorem Equation3385_implies_Equation4544 (G: Type _) [Magma G] (h: Equation3385 G) : Equation4544 G := fun x y z =>
  let v0 := M z y
  let v1 := M y z
  let v2 := M x x
  have h3 := h y z v0
  have h4 := S h3
  have h5 := h z z y
  have h6 := h z z v1
  have h7 := S h6
  have h8 := h z y z
  have h9 := R v1
  have h10 := C h9 h8
  let v11 := M x v1
  have h12 := h v1 v0 v11
  have h13 := S h12
  have h14 := h v0 x v1
  have h15 := R v11
  have h16 := C h15 h14
  have h17 := R v0
  have h18 := C h17 (T (T (T (T h16 h13) h10) h7) h5)
  have h19 := C h15 (S h14)
  have h20 := h z y x
  have h21 := S h20
  let v22 := M v0 x
  let v23 := M y x
  have h24 := h x (M z v23) v22
  have h25 := S h24
  have h26 := R v22
  have h27 := h z v23 v22
  have h28 := h y x v0
  have h29 := h x z y
  have h30 := R z
  have h31 := h z (M v0 (M x z)) v22
  have h32 := h v0 x z
  have h33 := T (T (T h32 h31) (C h26 (C h30 (C (T (C h17 h29) (S h28)) h26)))) (S h27)
  have h34 := C h33 h26
  have h35 := R x
  have h36 := C h26 (C h35 h34)
  have h37 := h x v22 v22
  have h38 := T (T (T h37 h36) h25) h21
  have h39 := C h9 h38
  have h40 := S h37
  have h41 := T (T (T h27 (C h26 (C h30 (C (T h28 (C h17 (S h29))) h26)))) (S h31)) (S h32)
  have h42 := C h41 h26
  have h43 := C h26 (C h35 h42)
  have h44 := T (T (T h20 h24) h43) h40
  have h45 := h y z v1
  have h46 := S h45
  have h47 := h z v1 v1
  have h48 := h v1 y z
  have h49 := R y
  have h50 := h v1 v1 y
  have h51 := C h9 (T h50 (C h49 (T (C h9 h48) (S h47))))
  have h52 := h v1 v1 v11
  have h53 := S h52
  have h54 := h v1 x v1
  have h55 := h v1 x v22
  have h56 := S h55
  have h57 := C h9 h44
  have h58 := h v1 v0 x
  have h59 := S h58
  have h60 := C h26 (T h59 h57)
  have h61 := h x v1 v22
  have h62 := C h15 (T (T (T h61 h60) h56) h54)
  have h63 := T h62 h53
  have h64 := C h9 h63
  have h65 := S h61
  have h66 := C h26 (T h39 h58)
  have h67 := S h54
  have h68 := C h15 (T (T (T h67 h55) h66) h65)
  have h69 := h v1 v1 x
  have h70 := S h69
  have h71 := h v1 v11 v11
  have h72 := S h71
  have h73 := T h52 h68
  have h74 := C h9 h73
  have h75 := S h48
  have h76 := C h9 (T (C h49 (T h47 (C h9 h75))) (S h50))
  have h77 := T (T h45 h76) h74
  have h78 := C h15 h77
  have h79 := C h9 (T (C h9 (T h78 h72)) h67)
  have h80 := h v1 v11 v1
  have h81 := h x v11 v1
  have h82 := T (T (T (T h81 (C h9 (T (T (T (C h35 (T (T (T h78 h72) h80) h79)) h70) h52) h68))) h64) h51) h46
  have h83 := T (T (C h17 (T (T (T (C h82 h44) h39) h12) h19)) h18) h4
  have h84 := h v0 v2 v22
  have h85 := h x x v11
  have h86 := S h85
  have h87 := T (T h64 h51) h46
  have h88 := C h15 h87
  have h89 := S h80
  have h90 := C h9 (T h54 (C h9 (T h71 h88)))
  have h91 := T (T (T (T h45 h76) h74) (C h9 (T (T (T h62 h53) h69) (C h35 (T (T (T h90 h89) h71) h88))))) (S h81)
  have h92 := C h35 h91
  have h93 := C h15 (T (T (T (T h67 h55) h66) h65) h92)
  have h94 := h v1 v1 z
  have h95 := S h94
  have h96 := h v1 z y
  have h97 := C h9 (S h8)
  have h98 := T h6 h97
  have h99 := h v1 v22 v11
  have h100 := S h99
  have h101 := h v1 x v0
  have h102 := h x v0 v11
  have h103 := S h102
  have h104 := h v0 v11 v22
  have h105 := S h104
  have h106 := C h17 (T (T (T (T (S h5) h6) h97) h12) h19)
  have h107 := C h26 (T h3 h106)
  have h108 := C h26 (T h18 h4)
  have h109 := C h17 (T (T (T (C h82 h35) h55) h66) h65)
  have h110 := C h35 (T (T h109 h104) h108)
  let v111 := M x v11
  have h112 := h v0 v111 x
  have h113 := C h15 (T (T h112 h110) (C h35 (T h107 h105)))
  have h114 := h v0 x v11
  have h115 := C h26 (T (T (T (T (C h17 (C h82 (T (T h114 h113) h103))) (S h101)) h55) h66) h65)
  have h116 := h v0 v111 v22
  have h117 := S h112
  have h118 := C h17 (T (T (T h61 h60) h56) (C h91 h35))
  have h119 := C h35 (T (T h107 h105) h118)
  have h120 := C h9 (T (T (T h119 h117) h116) h115)
  have h121 := h x v22 v1
  have h122 := h x v1 y
  have h123 := h y (M x (M v1 y)) v22
  have h124 := h v1 y y
  have h125 := S h124
  have h126 := h y y z
  have h127 := h z y v1
  have h128 := C h49 (T h127 (C h9 (S h126)))
  have h129 := T h128 h125
  have h130 := C h49 (T (C h9 h126) (S h127))
  have h131 := C h35 h82
  have h132 := C h15 (T (T (T (T h131 h61) h60) h56) h54)
  have h133 := h z x x
  let v134 := M z x
  have h135 := h y v134 v22
  have h136 := T (T (T h135 (C h26 (C h49 (C (T (T h133 (C h35 (T (T (T (T (C h30 (T (T h85 h132) h68)) (C h30 h63)) h75) h124) h130))) (C h35 h129)) h26)))) (S h123)) (S h122)
  have h137 := C h136 (T (T (T (T (T h20 h24) h43) h40) h121) h120)
  have h138 := C h35 (T h137 h100)
  have h139 := T (T h62 h93) h86
  have h140 := T h124 h130
  have h141 := T (T (T h122 h123) (C h26 (C h49 (C (T (T (C h35 h140) (C h35 (T (T (T (T h128 h125) h48) (C h30 h73)) (C h30 h139)))) (S h133)) h26)))) (S h135)
  have h142 := C h141 h17
  have h143 := C h35 h142
  have h144 := C h136 h17
  have h145 := S h121
  have h146 := S h116
  have h147 := S h114
  have h148 := C h15 (T (T (C h35 (T h104 h108)) h119) h117)
  have h149 := C h26 (T (T (T (T h61 h60) h56) h101) (C h17 (C h91 (T (T h102 h148) h147))))
  have h150 := C h9 (T (T (T h149 h146) h112) h110)
  have h151 := C h141 (T (T (T (T (T h150 h145) h37) h36) h25) h21)
  have h152 := h v1 v22 v22
  have h153 := h x v0 x
  have h154 := C h33 (T (T (T (S h153) h102) h148) h147)
  have h155 := h x x v22
  have h156 := h x (M y v134) v1
  have h157 := h y z x
  have h158 := C h35 (T (T (T (T (T (T h109 h104) (C h26 (T (T (T (T h18 h4) h157) h156) (C h9 (T (T (T (T (T (T (T (C h35 (T (T (T (C h136 h77) h72) h80) h79)) h70) h52) h93) h86) h155) h154) h42))))) (S h152)) h99) h151) h144)
  have h159 := T (T (T (T (T (T (T (T h149 h146) h112) h158) h143) h138) h59) h10) h7
  have h160 := h v0 v111 v0
  have h161 := S h160
  have h162 := C h17 (T (T h3 h106) (C h17 (T (T (T h16 h13) h57) (C h91 h38))))
  have h163 := h y z y
  have h164 := C h17 (S h163)
  have h165 := h y y v0
  have h166 := S h165
  have h167 := C h17 h163
  have h168 := h y v0 v1
  have h169 := C h30 (T h168 (C h9 (T (T (T (T (C h49 (T h167 h166)) (C h49 (T (T (T (T (T h165 h164) h162) h161) h116) h115))) (C h49 h159)) (C h49 h98)) (S h96))))
  have h170 := h v0 (M z (M y v0)) v22
  have h171 := h z y v0
  have h172 := T (T (T h171 h170) (C h26 (C h17 (C (T (T (T (T h169 h95) h52) h93) h86) h26)))) (S h84)
  have h173 := S h155
  have h174 := C h41 (T (T (T h114 h113) h103) h153)
  have h175 := C h35 (T (T (T (T (T (T h142 h137) h100) h152) (C h26 (T (T (T (T (C h9 (T (T (T (T (T (T (T h34 h174) h173) h85) h132) h53) h69) (C h35 (T (T (T h90 h89) h71) (C h141 h87))))) (S h156)) (S h157)) h3) h106))) h105) h118)
  have h176 := C h35 h144
  have h177 := C h35 (T h99 h151)
  have h178 := C h49 (T (T (T (T (T h149 h146) h160) (C h17 h83)) h167) h166)
  have h179 := T (T (T (T (T (T (T (T h6 h97) h58) h177) h176) h175) h117) h116) h115
  have h180 := C h49 h179
  have h181 := T h10 h7
  have h182 := C h49 h181
  have h183 := C h9 h159
  have h184 := h x z v1
  have h185 := h z v1 y
  have h186 := C h30 (T (C h9 (T (T (T (T h96 h182) h180) h178) (C h49 (T h165 h164)))) (S h168))
  have h187 := h y x x
  have h188 := h v1 v1 v0
  T (T (T (h x v1 v1) (C h9 (T (T (T (T (T (C h35 h73) (C h35 h139)) (C h35 (T h85 (C h141 h131)))) (C h35 (T (T (T (C h136 h92) h86) h155) h154))) (C h35 (T (T (T (T (T (T h174 h173) h85) h132) h53) h188) (C h172 (T (T (T (T (T (T (T (C h9 h181) (C h9 h179)) h150) h145) h37) h36) h25) h21))))) (C h35 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (C (T (T (T h84 (C h26 (C h17 (C (T (T (T (T h85 h132) h53) h94) h186) h26)))) (S h170)) (S h171)) (T (T (T (T (T (T (T h20 h24) h43) h40) h121) h120) h183) (C h9 h98))) (S h188)) h52) h93) h86) (h x x z)) (C h30 (T (T (T (T (T (C h35 (T h184 (C h9 (T (C h35 (T (T h185 (C h49 (T (T (T (T (T (T (T (T (C h30 h140) h169) h95) h52) h93) h86) h155) h154) h42))) (C h49 (T (T h34 h174) h173)))) (S h187))))) (C h35 (T (T (T (T (T (C h9 (T h187 (C h35 (T (T (C h49 (T (T h155 h154) h42)) (C h49 (T (T (T (T (T (T (T (T h34 h174) h173) h85) h132) h53) h94) h186) (C h30 h129)))) (S h185))))) (S h184)) (h x z v22)) (C h26 (T (T (T (T (T (S (h z v0 x)) (C h30 (T (T (T (T (T (T h20 h24) h43) h40) h121) h120) h183))) (S (h v1 z z))) h96) h182) (C h49 (T (T (T h6 h97) h12) h19))))) (S (h y v11 v22))) (C h49 (T (T h61 h60) h56))))) (S (h y v1 x))) (h y v1 z)) (C h30 (T (T (T (T (T (T (T (T (T (T (T (T (C h49 (T (T (T h96 h182) h180) h178)) (S (h y y y))) h165) h164) h162) h161) h112) h158) h143) h138) h59) h12) h19))) (C h30 (T (T (T h16 h13) h10) h7))))) (S (h z z z))) h6) h97) h58) h177) h176) h175) h117) h160) (C h172 h83)))))) (S (h x (M v0 v2) v1))) (S (h v0 x x))

