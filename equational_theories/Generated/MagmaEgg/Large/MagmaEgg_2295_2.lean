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
theorem Equation2295_implies_Equation2 (G: Type _) [Magma G] (h: Equation2295 G) : Equation2 G := fun x y =>
  have h0 := h y x y
  have h1 := S h0
  have h2 := R y
  let v3 := M y x
  let v4 := M x (M y v3)
  have h5 := h v4 x v4
  have h6 := S h5
  have h7 := h v4 x x
  have h8 := S h7
  have h9 := R x
  have h10 := h y x x
  have h11 := R v4
  have h12 := C h9 (T h0 (C h11 h10))
  have h13 := C h12 h9
  have h14 := C h12 (T h13 h8)
  have h15 := C h9 (T (C h11 (S h10)) h1)
  have h16 := C h15 h9
  have h17 := h v4 y v4
  have h18 := S h17
  have h19 := h v4 y x
  have h20 := S h19
  have h21 := C h2 (T h0 (C h11 h0))
  have h22 := C h21 h9
  have h23 := C h21 (T h22 h20)
  have h24 := C h2 (T (C h11 h1) h1)
  have h25 := C h24 h9
  have h26 := h v4 y y
  have h27 := S h26
  have h28 := C h21 h2
  let v29 := M y y
  have h30 := R v29
  have h31 := C h30 (T (T (T h28 h27) h19) h25)
  let v32 := M v29 (M v29 y)
  have h33 := h v32 x y
  have h34 := S h33
  have h35 := C h30 (T (T (T h22 h20) h26) (C h24 h2))
  have h36 := C h24 (T h19 h25)
  have h37 := T (T (T (T h14 h6) h17) h36) h35
  have h38 := C h37 h9
  have h39 := C h15 (T h7 h16)
  have h40 := h y y y
  have h41 := S h40
  have h42 := h y y x
  have h43 := S h42
  let v44 := M y v29
  let v45 := M y v44
  have h46 := R v45
  have h47 := C (T (C h9 (T (C h46 h43) h41)) h12) h9
  have h48 := h v45 x x
  have h49 := T (T (T (T h48 h47) h8) h5) h39
  have h50 := C h49 h9
  have h51 := S h48
  have h52 := C (T h15 (C h9 (T h40 (C h46 h42)))) h9
  have h53 := T (T (T (T h14 h6) h7) h52) h51
  have h54 := C h53 h2
  let v55 := M x y
  let v56 := M v55 (M v55 x)
  have h57 := R v56
  have h58 := C h57 (T h54 h41)
  have h59 := C h49 h2
  have h60 := C h53 h9
  have h61 := C h57 (T (T (T h60 h43) h40) h59)
  have h62 := T (T (T (T h31 h23) h18) h5) h39
  have h63 := C h62 (T h42 h50)
  have h64 := R v32
  have h65 := C h64 (T (T (T (T (T (T (T h63 h61) h58) h54) h41) h42) h50) h38)
  have h66 := C h37 (T h60 h43)
  have h67 := C h57 (T (T (T h54 h41) h42) h50)
  have h68 := C h57 (T h40 h59)
  have h69 := C h64 (T (T (T (T h40 h59) h68) h67) h66)
  have h70 := h v55 x y
  have h71 := S h70
  have h72 := R (M x v56)
  have h73 := C (T (C h9 (T (T (T h23 h18) h5) h39)) h72) h2
  have h74 := h v29 x y
  have h75 := C h2 (T (T h58 h54) h41)
  have h76 := C h64 (T (T (T (T h63 h61) h58) h54) h41)
  have h77 := C h2 (T (T h76 h63) h61)
  have h78 := C h62 h9
  have h79 := C h64 (T (T (T (T (T (T (T h78 h60) h43) h40) h59) h68) h67) h66)
  have h80 := h v44 x v44
  have h81 := S h80
  have h82 := h v44 x x
  have h83 := S h82
  let v84 := M x (M v44 (M v44 x))
  have h85 := R v84
  have h86 := C h85 h83
  have h87 := h v44 x y
  have h88 := C h2 (T (T (C h85 (T (S h87) h82)) h86) h81)
  have h89 := C (T (T (T (T (T (T h88 h48) h47) h8) h17) h36) h35) (T (T h42 h50) h38)
  have h90 := h v84 y y
  have h91 := T h86 h81
  have h92 := C h9 (C h91 (C h91 h9))
  have h93 := C (T (T (T (T (T (T (T (T (T h92 h90) h89) h79) h76) h63) h61) h58) h54) h41) (T (T (T (T (T h40 h59) h68) h67) h66) h69)
  let v94 := M v84 (M v84 x)
  have h95 := h v94 x y
  have h96 := C (T (T (T (T (T (T (T (T h95 h93) h77) h75) h74) h73) h71) (C h9 (T (T (T h40 h59) h68) h67))) (C h9 (T (T h66 h69) h65))) h2
  have h97 := C (T (T (T (T (T (T h95 h93) h77) h75) h74) h73) h71) (T (T (T (T (T (T h96 h34) h31) h23) h18) h7) h16)
  have h98 := C h85 h82
  have h99 := T h80 h98
  have h100 := C h99 (C h99 h2)
  have h101 := C (T (T (T h100 h97) h14) h6) h2
  have h102 := h (M (M v44 (M v44 y)) y) y y
  have h103 := S h102
  have h104 := S h95
  have h105 := C h9 (C h99 (C h99 h9))
  have h106 := S h90
  have h107 := C h2 (T (T h80 h98) (C h85 (T h83 h87)))
  have h108 := C (T (T (T (T (T (T h31 h23) h18) h7) h52) h51) h107) (T (T h78 h60) h43)
  have h109 := C (T (T (T (T (T (T (T (T (T h40 h59) h68) h67) h66) h69) h65) h108) h106) h105) (T (T (T (T (T h76 h63) h61) h58) h54) h41)
  have h110 := C h2 (T (T h67 h66) h69)
  have h111 := C h2 (T (T h40 h59) h68)
  have h112 := S h74
  have h113 := C (T h72 (C h9 (T (T (T h14 h6) h17) h36))) h2
  have h114 := C (T (T (T (T (T (T (T (T (C h9 (T (T h79 h76) h63)) (C h9 (T (T (T h61 h58) h54) h41))) h70) h113) h112) h111) h110) h109) h104) h2
  have h115 := C (T (T (T (T (T (T h70 h113) h112) h111) h110) h109) h104) (T (T (T (T (T (T h13 h8) h17) h36) h35) h33) h114)
  have h116 := C (T (T (T (T (T (T (T h88 h48) h47) h8) h5) h39) h115) (C h91 (C h91 h2))) h2
  have h117 := C (T (T h92 h90) h116) h2
  have h118 := T (T (T (T (T (T (T (T h40 h59) h68) h67) h66) h69) h65) h108) h116
  have h119 := C h118 (T (T (T h111 h110) h109) h117)
  have h120 := C (T (T (T (T (T (T (T h100 h97) h14) h6) h7) h52) h51) h107) h2
  have h121 := C (T (T h120 h106) h105) h2
  have h122 := T h101 h1
  have h123 := C h122 (T (T (T (T h121 h104) h86) h81) h119)
  have h124 := h v94 y x
  have h125 := S h124
  have h126 := h x y x
  have h127 := S h126
  have h128 := h x y y
  have h129 := S h128
  let v130 := M y (M x v55)
  have h131 := h v130 x x
  have h132 := R v130
  have h133 := h x x x
  have h134 := S h133
  let v135 := M x x
  let v136 := M x (M x v135)
  have h137 := R v136
  have h138 := C h9 (T (C h137 h134) h134)
  have h139 := C h138 h9
  have h140 := h v136 x x
  have h141 := h v136 y v136
  have h142 := S h141
  have h143 := h v136 y x
  have h144 := S h143
  have h145 := h x x y
  have h146 := C h2 (T h133 (C h137 h145))
  have h147 := C h146 h9
  have h148 := C h146 (T h147 h144)
  have h149 := T (T (T (T (T h148 h142) h140) h139) (C (C h9 (T h126 (C h132 h126))) h9)) (S h131)
  have h150 := C h149 h2
  have h151 := T h150 h129
  have h152 := C h149 h151
  have h153 := C h2 (T (C h137 (S h145)) h134)
  have h154 := C h153 h9
  have h155 := C h153 (T h143 h154)
  have h156 := S h140
  have h157 := C h9 (T h133 (C h137 h133))
  have h158 := C h157 h9
  have h159 := T (T (T (T (T h131 (C (C h9 (T (C h132 h127) h127)) h9)) h158) h156) h141) h155
  have h160 := C h159 h2
  have h161 := T h128 h160
  have h162 := R (M v3 (M v3 x))
  have h163 := C h162 h161
  have h164 := C h162 (T (T h163 h152) h127)
  have h165 := C h162 h151
  have h166 := C h159 h161
  have h167 := h v136 x v136
  have h168 := S h167
  have h169 := C h157 (T h158 h156)
  have h170 := h v136 x y
  have h171 := R v135
  have h172 := C h171 (T (T (T (C h157 h2) (S h170)) h140) h139)
  have h173 := T (T (T (T h172 h169) h168) h141) h155
  have h174 := C h173 (T (T (T (T (T (C h173 h2) h150) h129) h126) h166) h165)
  have h175 := C h122 (T (T (T h121 h93) h77) h75)
  have h176 := C h118 (T (T (T (T h175 h80) h98) h95) h117)
  have h177 := C h122 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h40 h59) h68) h67) h66) h69) h65) h108) h116) h102) (C (T (T (T h176 h175) h80) h98) h2)) h96) h34) h31) h23) h18) h5) h39) h115)
  have h178 := h v94 y y
  have h179 := S h178
  have h180 := C (T (T (T (T (T (T h176 h175) h80) h98) h95) h117) h177) h2
  have h181 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T h40 h59) h68) h67) h66) h69) h65) h108) h116) h102) h180) h179) h95) h117) h177) (T (T (T (T h174 h164) h163) h152) h127)
  have h182 := h (M v135 (M v135 y)) y y
  have h183 := C h138 h2
  have h184 := C h171 (T h170 h183)
  have h185 := C h138 h137
  have h186 := h v136 y y
  have h187 := R v3
  have h188 := C h187 (T (T (T (C h146 h2) (S h186)) h143) h154)
  have h189 := C h2 (T h152 h127)
  have h190 := C h2 (T (T h174 h164) h163)
  have h191 := C h171 (T (T (T h158 h156) h170) h183)
  have h192 := C h138 (T h140 h139)
  have h193 := T (T (T (T h148 h142) h167) h192) h191
  have h194 := C h118 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h97 h14) h6) h17) h36) h35) h33) h114) (C (T (T (T h86 h81) h119) h123) h2)) h103) h120) h89) h79) h76) h63) h61) h58) h54) h41)
  have h195 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T h194 h121) h104) h178) (C (T (T (T (T (T (T h194 h121) h104) h86) h81) h119) h123) h2)) h103) h120) h89) h79) h76) h63) h61) h58) h54) h41) (T (T (T (T h126 h166) h165) (C h162 (T (T h126 h166) h165))) (C h193 (T (T (T (T (T h163 h152) h127) h128) h160) (C h193 h2))))
  let v196 := M y (M v3 (M v3 y))
  have h197 := h v3 y y
  have h198 := h v3 y x
  have h199 := C h2 (T (T (T (T (T h172 h169) h168) h141) h155) (C h187 (T (T (T h147 h144) h186) (C h153 h2))))
  have h200 := h v135 y y
  T (T (T (T (T (T (T (T (T (T (T (T h133 (C (T (T (T (T (T (T (T (T (T (T (T (T h167 h185) h184) h182) (C (T (T (T h181 h125) h95) h93) h2)) (S (h v32 y y))) (C h21 (T h28 h27))) h18) h7) h52) h51) (C h2 (T (T (T (T (T h80 h98) h124) h195) h190) h189))) (C h2 (T (T (T (T (T h197 (C (C h2 (T (T (T (T (T h188 h148) h142) h167) h192) h191)) h2)) (S h200)) (h v135 y v135)) (C h199 (T (T (T h200 (C h199 h2)) (S h197)) h198))) (C (R v196) (T (S h198) h197))))) h9)) (S (h v196 y x))) (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h40 h59) h68) h67) h66) h69) h65) h108) h116) h102) h180) h179) h124) h195) h190) h189) h146) (T (T h188 h148) h142))) h142) h167) h185) h184) h182) (C (T (T (T (T (T h181 h125) h86) h81) h119) h123) h2)) h103) h101) h1

