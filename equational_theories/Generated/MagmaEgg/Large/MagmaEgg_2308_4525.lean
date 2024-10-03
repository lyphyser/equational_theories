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
theorem Equation2308_implies_Equation4525 (G: Type _) [Magma G] (h: Equation2308 G) : Equation4525 G := fun x y z =>
  have h0 := R z
  let v1 := M y z
  have h2 := h x x v1
  have h3 := R y
  have h4 := C (C h3 (S h2)) h0
  let v5 := M x v1
  let v6 := M x v5
  have h7 := h (M x v6) y z
  have h8 := R v6
  have h9 := h x y z
  have h10 := S h9
  have h11 := h v5 z v1
  have h12 := C (C h3 (S h11)) h0
  let v13 := M z (M v5 (M z v1))
  have h14 := h v13 y z
  have h15 := T (T h14 h12) h10
  have h16 := C h15 h8
  have h17 := R v5
  have h18 := C h15 h17
  have h19 := S h14
  have h20 := C (C h3 h11) h0
  have h21 := T (T h9 h20) h19
  have h22 := C h21 h18
  have h23 := C h21 h17
  have h24 := h x v5 x
  have h25 := S h24
  have h26 := R x
  let v27 := M (M y x) z
  let v28 := M v5 x
  let v29 := M v5 (M x v28)
  have h30 := h v29 v27 v1
  have h31 := h v1 v5 x
  have h32 := S h31
  have h33 := h v13 x v1
  have h34 := S h33
  have h35 := R v1
  have h36 := C h21 h8
  have h37 := S h7
  have h38 := C (C h3 h2) h0
  have h39 := T (T (T h38 h37) h36) (C h15 h23)
  have h40 := C h39 h35
  have h41 := T (T (T (T h40 h34) h14) h12) h10
  let v42 := M v1 v28
  let v43 := M v5 v42
  have h44 := R v43
  have h45 := C h44 h41
  have h46 := T (T (T h22 h16) h7) h4
  have h47 := C h46 h35
  have h48 := T (T (T (T h9 h20) h19) h33) h47
  have h49 := h v43 v27 v1
  have h50 := S h49
  have h51 := h v1 y v5
  have h52 := S h51
  have h53 := h (M y (M v1 (M y v5))) x v1
  have h54 := T (C (T (C (C h26 h51) h35) (S h53)) h17) h52
  have h55 := C h44 h48
  have h56 := C h46 (T h31 h55)
  have h57 := C (T (T (T (T h9 h20) h19) h33) h56) h54
  have h58 := T h51 (C (T h53 (C (C h26 h52) h35)) h17)
  have h59 := C h26 h58
  have h60 := T (T h59 h57) h50
  have h61 := C h60 h48
  have h62 := T (T h61 h45) h32
  have h63 := R v29
  have h64 := C h63 h48
  have h65 := R v27
  have h66 := C h65 (T h24 h64)
  have h67 := C h26 h54
  have h68 := C h39 (T h45 h32)
  have h69 := C (T (T (T (T h68 h34) h14) h12) h10) h58
  have h70 := T (T h49 h69) h67
  have h71 := C h70 h41
  have h72 := T (T h31 h55) h71
  have h73 := C h63 h41
  have h74 := C h65 (T h73 h25)
  let v75 := M v27 v1
  have h76 := h v75 v5 x
  have h77 := C (T h68 h47) h72
  have h78 := C h17 (T (T h59 h57) h77)
  have h79 := h (M v5 v5) v27 v1
  have h80 := C (T h40 h56) h62
  have h81 := C h17 (T (T h80 h69) h67)
  have h82 := C h62 h72
  have h83 := R v28
  have h84 := C h83 h62
  have h85 := C h17 (T h84 h82)
  have h86 := C h72 h72
  have h87 := C h17 h86
  let v88 := M v5 (M v1 v1)
  have h89 := h v88 v1 v1
  have h90 := C h62 h62
  have h91 := C h83 h72
  have h92 := C h72 h62
  have h93 := C h17 h90
  have h94 := C h17 (T h92 h91)
  have h95 := T (T (T (T h59 h57) h50) h94) h93
  have h96 := C h95 (T (T h92 h91) h90)
  have h97 := C h72 h17
  have h98 := C (T (T (T (T (T (C h17 (T (T (T (T (T (C (T h97 (C h62 (T (T (T h59 h57) h50) h96))) h62) (S h89)) h87) h85) h49) h77)) h81) h79) (C (T (C h65 (T (T (T (T (T (T (T (T (C h78 h41) (S h76)) h40) h34) h14) h12) h10) h24) h64)) h74) h72)) (C h66 h62)) (S h30)) h26
  let v99 := M v1 v5
  have h100 := h v99 v5 x
  have h101 := h v88 v5 x
  have h102 := S h101
  have h103 := h v28 x v1
  have h104 := S h103
  have h105 := S h100
  have h106 := C h62 h17
  have h107 := T (T (T (T h87 h85) h49) h69) h67
  have h108 := C (T (T (T (T (T h30 (C h74 h72)) (C (T h66 (C h65 (T (T (T (T (T (T (T (T h73 h25) h9) h20) h19) h33) h47) h76) (C h81 h48)))) h62)) (S h79)) h78) (C h17 (T (T (T (T (T h80 h50) h94) h93) h89) (C (T (C h72 (T (T (T (C h107 (T (T h86 h84) h82)) h49) h69) h67)) h106) h72)))) h26
  have h109 := h x v1 v5
  have h110 := S h109
  have h111 := h (M x v99) y z
  have h112 := S h111
  have h113 := h v1 x v1
  have h114 := h v1 y v1
  have h115 := C h3 (S h114)
  have h116 := C (T h115 (C h3 h113)) h0
  have h117 := C h3 h114
  have h118 := h v28 v27 v1
  have h119 := S h118
  have h120 := C (C h65 (C h72 h48)) h62
  let v121 := M v27 (M v1 x)
  have h122 := R v121
  have h123 := h v121 y z
  have h124 := C (C h35 (T (T (T h123 (C (T (C h3 (T (T (T (T (T (C h122 h72) h120) h119) h61) h45) h32)) h117) h0)) h116) h112)) h17
  have h125 := C (C h65 (C h62 h41)) h72
  have h126 := C (T (C h3 (S h113)) h117) h0
  have h127 := C (C h35 (T (T (T h111 h126) (C (T h115 (C h3 (T (T (T (T (T h31 h55) h71) h118) h125) (C h122 h62)))) h0)) (S h123))) h17
  have h128 := h v13 x v5
  have h129 := S h128
  have h130 := C (C h26 (T (T h38 h37) h36)) h17
  have h131 := C h26 (T (T (T (T (T (T h130 h129) h14) h12) h10) h109) h127)
  have h132 := C (C h26 (T (T h16 h7) h4)) h17
  have h133 := C h26 (T (T (T (T h9 h20) h19) h128) h132)
  let v134 := M x x
  have h135 := h v134 y z
  have h136 := S h135
  have h137 := h x y v5
  have h138 := C h26 (S h137)
  have h139 := C h26 h137
  have h140 := C h26 (T (T (T (T h130 h129) h14) h12) h10)
  have h141 := C h26 (T (T (T (T (T (T h124 h110) h9) h20) h19) h128) h132)
  have h142 := C h141 h35
  let v143 := M v1 v121
  have h144 := h v143 x v1
  have h145 := h v143 v27 v1
  have h146 := S h145
  have h147 := R v143
  have h148 := h v27 v1 x
  have h149 := C h65 (T h148 (C h147 h48))
  have h150 := C h149 h35
  have h151 := C (C h3 (T (T (T (T (T h150 h146) h144) h142) (C (T h140 h139) h35)) (C h138 h35))) h0
  let v152 := M v27 v27
  have h153 := h v152 y z
  have h154 := C h65 (T (C h147 h41) (S h148))
  have h155 := C h154 h72
  have h156 := S h153
  have h157 := C h154 h35
  have h158 := S h144
  have h159 := C h131 h35
  have h160 := C (C h3 (T (T (T (T (T (C h139 h35) (C (T h138 h133) h35)) h159) h158) h145) h157)) h0
  have h161 := T (T h135 h160) h156
  have h162 := C h161 h62
  have h163 := T (T h153 h151) h136
  have h164 := C h163 h72
  have h165 := C h149 h62
  let v166 := M x v27
  have h167 := h v166 x v1
  have h168 := C h17 (T (T (T (T h167 h159) h158) h145) h155)
  have h169 := h (M v5 v166) v27 v1
  have h170 := C h17 (T (T (T (T h165 h146) h144) h142) (S h167))
  have h171 := h v152 v5 x
  have h172 := C h65 h161
  have h173 := C h17 (T (T (T (T (C (T h172 (C h65 (T h171 (C h170 h48)))) h62) (S h169)) h168) (C h17 (T (T h165 h157) h164))) (C h95 (T (T (T (T h162 h150) h155) (C (T (T (T (T (T h153 h151) h136) h133) h131) (C h26 (T (T (T (T (T h124 h110) h24) h108) h105) h97))) h62)) h104)))
  have h174 := C h173 h26
  let v175 := M v27 v134
  have h176 := h v175 v5 x
  have h177 := C h65 h163
  let v178 := M v27 v152
  have h179 := C (R v178) (T (T (T (T (T (T (T h40 h34) h14) h12) h10) h24) h108) h105)
  have h180 := S h176
  have h181 := C (T (C h65 (T (C h168 h41) (S h171))) h177) h72
  have h182 := C h17 (T (T h162 h150) h155)
  have h183 := C h107 (T (T (T (T h103 (C (T (T (T (T (T (C h26 (T (T (T (T (T h106 h100) h98) h25) h109) h127)) h141) h140) h135) h160) h156) h72)) h165) h157) h164)
  have h184 := C (C h17 (T (T (T (T h183 h182) h170) h169) h181)) h26
  have h185 := C (T (T (T h101 h184) h180) h172) (R v75)
  have h186 := C h93 h48
  have h187 := h v28 v5 x
  let v188 := M v5 v1
  have h189 := h v188 x v1
  have h190 := S h189
  have h191 := C (T h49 h69) h62
  have h192 := C (T h57 h50) h72
  have h193 := h (M y (M v1 (M y v1))) y z
  have h194 := C (T (T (T h193 h116) h112) (C h26 h97)) h62
  have h195 := C (T (T (T (C h26 h106) h111) h126) (S h193)) h72
  T (T (T (T (T (T (T (T (T (T (T (T (T h59 h57) h50) h94) h93) h101) h184) h180) (h v175 v5 v1)) (C (T (T (T (T (T (C h17 (C h172 (R v188))) (C h17 (T (T (C (T (T (T (T (T (T (T (T h177 h176) h174) h102) h87) h85) h49) h69) h67) (T (T (T (T (T (T (T (T (T h189 h192) (C h70 (T h118 h125))) (C h17 (T (T (T h120 h119) h103) h195))) (C h95 (T h194 h104))) h183) h182) h170) h169) h181)) h173) (C h95 (T (T (T (T (C h107 (T h103 h195)) (C h17 (T (T (T h194 h104) h118) h125))) (C h60 (T h120 h119))) h191) h190))))) (C h17 (T (C h107 (T h189 h192)) (C h17 (T h191 h190))))) (h (M v5 (M v5 v188)) y z)) (C (C h3 (S (h v5 v5 v1))) h0)) h10) (T (T (T (T (T (T (T (T (T h31 h55) h71) h187) h186) h185) h179) (C (T (T (T (T (T (T (T h177 h176) h174) h102) h87) h85) h96) (C h107 (T (T (T (T h86 h84) h82) (h v42 x v1)) (C (T (C h21 (T (T (T (T (T (T (T (T (T (T (C (C h35 (T (T (T h187 h186) h185) h179)) h17) (S (h v178 v1 v5))) h177) h176) h174) h102) h87) h85) h49) h69) h67)) h18) h72)))) (T (T h100 h98) h25))) (S (h v6 v5 x))) h23))) h22) h16) h7) h4

