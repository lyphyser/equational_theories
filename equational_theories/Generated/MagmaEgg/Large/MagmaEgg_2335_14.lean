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
theorem Equation2335_implies_Equation14 (G: Type _) [Magma G] (h: Equation2335 G) : Equation14 G := fun x y =>
  let v0 := M x y
  have h1 := R v0
  let v2 := M y v0
  have h3 := h y v2 y
  have h4 := S h3
  have h5 := h y v2 v0
  have h6 := S h5
  let v7 := M y y
  let v8 := M v2 (M v2 v7)
  have h9 := R v8
  have h10 := C (T (C h9 (T (C h9 h6) h4)) h4) h1
  let v11 := M v2 (M v2 v2)
  have h12 := h v11 v8 v0
  have h13 := h v11 x v0
  have h14 := S h13
  have h15 := R x
  have h16 := C h15 (C h15 h5)
  have h17 := h y x v0
  have h18 := S h17
  have h19 := C (T (C h15 (C h15 h18)) h16) h1
  let v20 := M x v2
  let v21 := M x v20
  have h22 := h v21 x v0
  have h23 := h v21 x x
  have h24 := S h23
  have h25 := h v2 x x
  have h26 := S h25
  have h27 := C (C h15 (C h15 h26)) h15
  let v28 := M v2 x
  let v29 := M x (M x v28)
  have h30 := h v29 x x
  let v31 := M v2 v11
  have h32 := h v29 v31 x
  have h33 := S h32
  have h34 := R v31
  have h35 := h v2 v2 v2
  have h36 := C (T h35 (C h34 (T h35 (C h34 h25)))) h15
  have h37 := S h35
  have h38 := T h25 (C (T h32 (C (T (C h34 (T (C h34 h26) h37)) h37) h15)) h15)
  have h39 := R v2
  have h40 := S (h v0 y v0)
  let v41 := M y (M y (M v0 v0))
  have h42 := R v41
  let v43 := M v0 (M v0 v2)
  have h44 := S h30
  have h45 := C (C h15 (C h15 h25)) h15
  have h46 := S h22
  have h47 := C h15 (C h15 h6)
  have h48 := C (T h47 (C h15 (C h15 h17))) h1
  have h49 := h v11 x y
  have h50 := S h49
  have h51 := R y
  let v52 := M v11 y
  have h53 := h v52 v31 y
  have h54 := S h53
  have h55 := h v2 x y
  have h56 := C (T (T (T (C h15 (C h15 (S h55))) h22) h19) h14) h51
  let v57 := M v2 y
  have h58 := h (M x (M x v57)) x y
  have h59 := C (T (T (T (T h22 h19) h14) h12) h10) h51
  have h60 := C h15 (C h15 h59)
  have h61 := C (T (T h60 h58) h56) h51
  have h62 := h v21 x y
  have h63 := S h12
  have h64 := C (T h3 (C h9 (T h3 (C h9 h5)))) h1
  have h65 := C h34 (T (T (T (T (T (T h64 h63) h13) h48) h46) h62) h61)
  have h66 := S h62
  have h67 := C (T (T (T (T h64 h63) h13) h48) h46) h51
  have h68 := C h15 (C h15 h67)
  have h69 := S h58
  have h70 := C (T (T (T h13 h48) h46) (C h15 (C h15 h55))) h51
  have h71 := C (T (T h70 h69) h68) h51
  have h72 := C (T (T (T (T (T (T (T h22 h19) h14) h12) h10) h35) h65) (C h34 (T (T (T (T (T (T (T (T h71 h66) h22) h19) h14) h12) h10) h35) h65))) h51
  have h73 := C (T (T (T (T (T (T h67 h72) h54) h70) h69) h68) (C h15 (C h15 (T h72 h54)))) h51
  have h74 := C h34 (T (T (T (T (T (T h71 h66) h22) h19) h14) h12) h10)
  have h75 := C (T (T (T (T (T (T (T (C h34 (T (T (T (T (T (T (T (T h74 h37) h64) h63) h13) h48) h46) h62) h61)) h74) h37) h64) h63) h13) h48) h46) h51
  have h76 := C (T (T (T (T (T (T (C h15 (C h15 (T h53 h75))) h60) h58) h56) h53) h75) h59) h51
  have h77 := T (T (T (T (T (T h71 h66) h22) h19) h14) h49) h76
  have h78 := h v11 y v0
  have h79 := S h78
  have h80 := C (C h51 (C h51 h5)) h1
  have h81 := T (T (T (T (T (T h80 h79) h13) h48) h46) h62) h61
  have h82 := C (C h51 (C h51 h6)) h1
  have h83 := h x y x
  have h84 := S h83
  have h85 := h x x y
  have h86 := S h85
  let v87 := M x x
  let v88 := M y (M y v87)
  have h89 := R v88
  have h90 := C (T (C h89 (T (C h89 h86) h84)) h84) h51
  let v91 := M x v0
  let v92 := M x v91
  have h93 := h v92 v88 y
  have h94 := h v92 x y
  have h95 := S h94
  have h96 := h x y y
  have h97 := C (T (C h15 (C h15 (S h96))) (C h15 (C h15 h85))) h51
  let v98 := M y v2
  have h99 := h v98 x y
  have h100 := h y y v2
  have h101 := C (T (C h9 (T (C h9 (S h100)) h4)) h4) h39
  let v102 := M y v98
  have h103 := h (M y v102) v8 v2
  have h104 := h v102 x x
  have h105 := h v29 y x
  have h106 := C h51 (T (T (T (T (T (T (T h73 h50) h13) h48) h46) h23) (C (C h15 (C h15 (T (T (T h45 h44) h105) (C (C h51 (C h51 h26)) h15)))) h15)) (S h104))
  have h107 := C h51 h77
  have h108 := C h51 h81
  have h109 := C h51 (T (C (T h36 h33) h15) h26)
  have h110 := C h51 (T (T (T (T (T h109 h99) h97) h95) h93) h90)
  have h111 := C h51 h38
  have h112 := C h51 (T (T (T h106 h103) h101) h111)
  have h113 := C h51 h107
  have h114 := C h51 h108
  have h115 := C h51 (T (T (T (T (T (T h71 h66) h22) h19) h14) h78) h82)
  have h116 := C h51 (T (T (T (T (T (T h73 h50) h13) h48) h46) h62) h61)
  have h117 := C h51 (T (T (T (T (T (T (T h104 (C (C h15 (C h15 (T (T (T (C (C h51 (C h51 h25)) h15) (S h105)) h30) h27))) h15)) h24) h22) h19) h14) h49) h76)
  have h118 := S h103
  have h119 := C (T h3 (C h9 (T h3 (C h9 h100)))) h39
  have h120 := S h99
  have h121 := C (T (C h15 (C h15 h86)) (C h15 (C h15 h96))) h51
  have h122 := S h93
  have h123 := C (T h83 (C h89 (T h83 (C h89 h85)))) h51
  have h124 := C (T (T (T (T (T (T (T (T h114 h113) h112) h110) h64) h63) h13) h48) h46) h1
  let v125 := M y v7
  have h126 := h v125 y v0
  have h127 := h v125 x v0
  have h128 := S h127
  have h129 := C (C h15 (C h15 (T (T (T (C h16 h1) h14) h78) h82))) h1
  have h130 := h v91 x v0
  have h131 := h v91 x x
  have h132 := S h131
  have h133 := h y x x
  have h134 := S h133
  let v135 := M y x
  let v136 := M x (M x v135)
  have h137 := h v136 x x
  have h138 := h v136 v2 x
  have h139 := C (C h15 (C h15 (T (T (T (C (C h39 (C h39 h133)) h15) (S h138)) h137) (C (C h15 (C h15 h134)) h15)))) h15
  have h140 := h (M v2 v57) x x
  have h141 := h v52 y y
  have h142 := S h141
  have h143 := C h39 (T (T h53 h75) h59)
  have h144 := C h51 h116
  have h145 := C h51 (T (T (T h109 h119) h118) h117)
  have h146 := C h51 (T (T (T (T (T h123 h122) h94) h121) h120) h111)
  have h147 := C (T (T h146 h145) h144) (T (T (T (T (T (T (T (T (T h143 h140) h139) h132) h130) h129) h128) h126) h124) h18)
  have h148 := C h39 (T (T h67 h72) h54)
  have h149 := S h140
  have h150 := C (C h15 (C h15 (T (T (T (C (C h15 (C h15 h133)) h15) (S h137)) h138) (C (C h39 (C h39 h134)) h15)))) h15
  have h151 := h x v2 v0
  have h152 := S h151
  let v153 := M v2 (M v2 v91)
  have h154 := h v153 v88 v0
  have h155 := h v153 x v0
  have h156 := C h39 (T (T (T (T (T (C h39 (T (T (T (T (T (T (T (C (C h15 (C h15 h151)) h1) (S h155)) h154) (C (T (C h89 (T (C h89 h152) h84)) h84) h1)) h131) h150) h149) h148)) h147) h142) h53) h75) h59)
  have h157 := C (T (T (T (T (T (T (T (T (T h156 h140) h139) h132) h130) h129) h128) h126) h124) h18) (T (T (T (T (T (T (T (T (T h123 h122) h94) h121) h120) h119) h118) h117) h116) h115)
  let v158 := M x v87
  have h159 := h v158 v2 v0
  have h160 := h v158 x v2
  have h161 := S h160
  have h162 := h x v2 v2
  have h163 := S h162
  let v164 := M v2 (M v2 v20)
  have h165 := h v164 x v2
  have h166 := h v164 y v2
  have h167 := C (C h15 (C h15 (T (T (T (C (C h51 (C h51 h162)) h39) (S h166)) h165) (C (C h15 (C h15 h163)) h39)))) h39
  have h168 := h (M y v135) x v2
  have h169 := C h51 (T (T (T (T (T (T (T (T (T (T (T (T h168 h167) h161) h159) h157) h114) h113) h112) h110) h64) h63) h78) h82)
  have h170 := S h168
  have h171 := C (C h15 (C h15 (T (T (T (C (C h15 (C h15 h162)) h39) (S h165)) h166) (C (C h51 (C h51 h163)) h39)))) h39
  have h172 := S h159
  have h173 := C h39 (T (T (T (T (T (T (T h143 h140) h139) h132) (C (T h83 (C h89 (T h83 (C h89 h151)))) h1)) (S h154)) h155) (C (C h15 (C h15 h152)) h1))
  have h174 := S h130
  have h175 := C (C h15 (C h15 (T (T (T h80 h79) h13) (C h47 h1)))) h1
  have h176 := S h126
  have h177 := C h51 h115
  have h178 := C (T (T (T (T (T (T (T (T h22 h19) h14) h12) h10) h146) h145) h144) h177) h1
  have h179 := C (T (T h113 h112) h110) (T (T (T (T (T (T (T (T (T h17 h178) h176) h127) h175) h174) h131) h150) h149) h148)
  have h180 := C (T (T (T (T (T (T (T (T (T h17 h178) h176) h127) h175) h174) h131) h150) h149) (C h39 (T (T (T (T (T h67 h72) h54) h141) h179) h173))) (T (T (T (T (T (T (T (T (T h108 h107) h106) h103) h101) h99) h97) h95) h93) h90)
  have h181 := h y y x
  have h182 := S h181
  have h183 := C h51 (T (T (T (T (T (T (T (T (T (T (T (T h80 h79) h12) h10) h146) h145) h144) h177) h180) h172) h160) h171) h170)
  have h184 := C (T (T (T (T (T (T (T (T (T (T h123 h122) h94) h121) h120) h119) h118) h117) h116) h115) h183) h15
  have h185 := C (T h184 h182) (T (T (T (T (T (T (T (T h146 h145) h144) h177) h180) h172) h160) h171) h170)
  have h186 := C (T (T (T (T (T (T (T (T (T (T h169 h108) h107) h106) h103) h101) h99) h97) h95) h93) h90) h15
  have h187 := C h39 (T (T (T (T (T (T (T (T (C (T (T (T h146 h145) h144) h177) (T (T (T (T (T (T (T (T (T (T (T h185 h169) h108) h107) h106) h103) h101) h99) h97) h95) h93) h90)) h176) h127) h175) h174) h131) h150) h149) h148)
  have h188 := C (T (T (T h114 h113) h112) h110) (T (T (T (T (T (T (T (T (T (T (T h123 h122) h94) h121) h120) h119) h118) h117) h116) h115) h183) (C (T h181 h186) (T (T (T (T (T (T (T (T h168 h167) h161) h159) h157) h114) h113) h112) h110)))
  have h189 := h (M v0 x) v2 v2
  T (T (T (T (T (T (T h83 (C (T (T (T (T (T (T (h v88 v88 x) (C (T (C h89 (T (C h89 h84) h84)) h84) h15)) (C (T (T (T (T (T (h x v41 y) (C (T (C h42 h40) h40) h51)) (C h1 (T (T (T h181 h186) h189) (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h187 h147) h142) h53) h75) h59) (h v57 v2 v2)) (C (T (T (T (T (T (T (T (T (T (T (T (T (C h39 (T (T (C h39 (T (T (T (T (T (T (C (T (T (T (T (T h67 h72) h54) h141) h179) (C h39 (T (T (T (T (T (T (T (T h143 h140) h139) h132) h130) h129) h128) h126) h188))) h39) (S h189)) h184) h182) h17) h178) h188)) h187) h173)) h156) h140) h139) h132) h130) h129) h128) h126) h124) h18) h181) h186) h39)) h185) h169) h108) h107) h106) h103) h101) h99) h97) h95) h93) h90) (T (T (T h64 h63) h78) h82))))) (C h1 (C h1 h81))) (C h1 (C h1 h77))) (C h1 (T (T (T (C h1 (T (T (T (T (T (T (T h73 h50) h13) h48) h46) h23) (C (C h15 (C h15 (T (T (T h45 h44) (h v29 v0 x)) (C (C h1 (C h1 h26)) h15)))) h15)) (S (h v43 x x)))) (h (M v0 v43) v41 v2)) (C (T (C h42 (T (C h42 (S (h v0 v0 v2))) h40)) h40) h39)) (C h1 h38)))) h15)) (S (h v28 v0 x))) h36) h33) (C h15 (C h15 (T (T (T h36 h33) h30) h27)))) h15)) h24) h22) h19) h14) h12) h10

