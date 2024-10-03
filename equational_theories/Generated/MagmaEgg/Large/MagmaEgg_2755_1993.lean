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
theorem Equation2755_implies_Equation1993 (G: Type _) [Magma G] (h: Equation2755 G) : Equation1993 G := fun x y z =>
  let v0 := M z z
  let v1 := M y v0
  let v2 := M x y
  let v3 := M v1 v2
  have h4 := h v2 (M v3 v3) v1
  have h5 := S h4
  have h6 := R v1
  have h7 := h v3 v3 v3
  have h8 := C h7 h6
  have h9 := T h8 h5
  have h10 := C (S h7) h6
  have h11 := T h4 h10
  have h12 := h v0 v0 y
  have h13 := S h12
  let v14 := M v0 v1
  have h15 := h y z v14
  have h16 := S h15
  have h17 := R v14
  have h18 := h v0 z y
  have h19 := R v0
  have h20 := C (C h19 h18) h17
  let v21 := M v0 v0
  let v22 := M v21 v14
  have h23 := h v22 z v1
  have h24 := S h23
  have h25 := S h18
  have h26 := C (C h19 h25) h17
  have h27 := T h15 h26
  have h28 := C h6 h27
  have h29 := R y
  have h30 := h v1 v1 v1
  have h31 := C (S h30) h29
  let v32 := M v1 v1
  have h33 := h v0 v32 y
  have h34 := C h19 (T (T h33 h31) h28)
  have h35 := C h34 h6
  have h36 := T (T (T h35 h24) h20) h16
  have h37 := S h33
  have h38 := C h30 h29
  have h39 := T h20 h16
  have h40 := C h6 h39
  have h41 := T (T h40 h38) h37
  have h42 := C h19 h41
  have h43 := C h42 h6
  have h44 := T (T (T h15 h26) h23) h43
  have h45 := C h44 h36
  have h46 := C h29 h44
  have h47 := T (T h46 h45) h13
  have h48 := C h29 h47
  have h49 := C h29 h36
  have h50 := C h36 h44
  have h51 := T (T h12 h50) h49
  have h52 := h y y y
  have h53 := S h52
  have h54 := h y v21 v14
  have h55 := S h54
  have h56 := R (M v21 v21)
  have h57 := h v0 v0 v0
  have h58 := C (T h57 (C h56 h18)) h17
  have h59 := C h19 h48
  let v60 := M y y
  have h61 := R (M y v60)
  have h62 := C h47 h61
  have h63 := C h29 h51
  have h64 := R v60
  have h65 := C h64 h63
  have h66 := T (T h65 h62) h59
  have h67 := C h19 h66
  let v68 := M v21 v1
  have h69 := R (M y v68)
  have h70 := C h51 h69
  have h71 := T h35 h24
  have h72 := C h6 h71
  have h73 := C h19 (T (T (T (T (T h72 h40) h38) h37) h12) h50)
  have h74 := T h23 h43
  have h75 := C h6 h74
  have h76 := C h19 h75
  have h77 := C (T (T (T (T h34 h76) h73) h70) (C h64 h49)) (T (T h67 h58) h55)
  have h78 := C (T h77 h53) h51
  let v79 := M v60 v1
  have h80 := h v79 v0 v0
  have h81 := T (T h80 h78) h48
  have h82 := C h51 h81
  have h83 := C h64 h48
  have h84 := C h51 h61
  have h85 := C h19 h63
  have h86 := T (T h85 h84) h83
  have h87 := C h19 h86
  have h88 := S h57
  have h89 := C (T (C h56 h25) h88) h17
  have h90 := h y (M v2 v2) x
  have h91 := S h90
  have h92 := R x
  have h93 := h v2 v2 v2
  have h94 := C h93 h92
  have h95 := h v60 v0 y
  have h96 := S h95
  have h97 := S h80
  have h98 := C h19 h72
  have h99 := C h19 (T (T (T (T (T h45 h13) h33) h31) h28) h75)
  have h100 := C h47 h69
  have h101 := C (T (T (T (T (C h64 h46) h100) h99) h98) h42) (T (T h54 h89) h87)
  have h102 := C (T h52 h101) h47
  have h103 := T (T h63 h102) h97
  have h104 := C h47 h103
  have h105 := h v22 y v1
  have h106 := C (T (T (T (T (T (T (T (T (T (T h63 h102) h97) h104) h67) h58) h55) h15) h26) h105) (C (T (T (T (T (C h64 (T (T (T (T h40 h38) h37) h12) h50)) h100) h99) h98) h42) h63)) (T (T (T h104 h67) h58) h55)
  have h107 := C h6 h103
  have h108 := T (T (T (T (T h107 h106) h96) h46) h45) h13
  have h109 := C h108 (T (T (T (T (T h94 h91) h54) h89) h87) h82)
  have h110 := C (S h93) h92
  have h111 := R v32
  have h112 := C h111 (T (T (T (T (T (T (T (T h85 h84) h83) h104) h67) h58) h55) h90) h110)
  have h113 := C h111 (T (T (T (T (T h63 h102) h97) h65) h62) h59)
  have h114 := C h111 h48
  have h115 := C h111 (T (T (T h87 h82) h80) h78)
  have h116 := C (T (T (T (T (T (T (T (T h63 h102) h97) h104) h67) h58) h55) h52) h101) h108
  have h117 := T (T (T (T (T (T h54 h89) h87) h82) h80) h78) h48
  have h118 := C h117 h111
  have h119 := C h6 h81
  have h120 := C (T (T (T (T (T (T (T (T (T (T (C (T (T (T (T h34 h76) h73) h70) (C h64 (T (T (T (T h45 h13) h33) h31) h28))) h48) (S h105)) h20) h16) h54) h89) h87) h82) h80) h78) h48) (T (T (T h54 h89) h87) h82)
  have h121 := T (T h95 h120) h119
  have h122 := C h121 (T (T (T (T h118 h116) h97) h104) h67)
  have h123 := R (M y v32)
  have h124 := T (T h107 h106) h96
  have h125 := C h124 h123
  have h126 := T (T (T (T (T (T h63 h102) h97) h104) h67) h58) h55
  have h127 := C h126 h111
  have h128 := C h121 h127
  have h129 := R (M v1 v32)
  have h130 := C h124 h129
  have h131 := T (T (T (T (T h12 h50) h49) h95) h120) h119
  have h132 := C (T (T (T (T (T (T (T (T h77 h53) h54) h89) h87) h82) h80) h78) h48) h131
  have h133 := C h121 (T (T (T h87 h82) h80) h132)
  have h134 := C h51 (T (T (T (T (T h35 h24) h20) h16) h54) h89)
  have h135 := C h19 h44
  let v136 := M v0 y
  have h137 := C h19 (T h109 h82)
  have h138 := C h131 (T (T (T (T (T h104 h67) h58) h55) h90) h110)
  have h139 := C h19 h112
  let v140 := M v32 v14
  have h141 := R (M v0 v140)
  have h142 := C h19 h36
  have h143 := C h111 h142
  have h144 := C h47 (T (T (T (T (T h58 h55) h15) h26) h23) h43)
  have h145 := C h124 (T (T (T h116 h97) h104) h67)
  have h146 := C h121 h129
  have h147 := C h124 h118
  have h148 := C h121 h123
  have h149 := C h124 (T (T (T (T h87 h82) h80) h132) h127)
  have h150 := C h111 (T (T (T h102 h97) h104) h67)
  have h151 := C h111 h63
  have h152 := C h131 (T (T (T (T (T (T (T h151 h150) h149) h148) h147) h146) h145) h144)
  have h153 := T (T h152 h143) (C h108 (T (T (T (T (T (T (T (T (T h135 h134) h133) h130) h128) h125) h122) h115) h114) h113))
  let v154 := M v32 v1
  have h155 := R (M v0 v154)
  have h156 := C h108 (T (T (T (T (T (T (T h134 h133) h130) h128) h125) h122) h115) h114)
  have h157 := R (M v0 v68)
  have h158 := C h121 h157
  have h159 := C h51 h157
  have h160 := C h19 h135
  have h161 := T (T (T h160 h159) h158) h156
  have h162 := C h19 h142
  have h163 := C h47 h157
  have h164 := C h124 h157
  have h165 := C h111 h135
  have h166 := T (T (T h165 h164) h163) h162
  have h167 := R (M y v136)
  have h168 := C h111 (T (T (T (T (T h85 h84) h83) h80) h78) h48)
  have h169 := C h111 (T (T (T (T (T (T (T (T h94 h91) h54) h89) h87) h82) h65) h62) h59)
  let v170 := M v32 (M v2 x)
  have h171 := R v170
  have h172 := T (T (T h54 h89) h87) h138
  have h173 := C h108 (R (M v1 v79))
  have h174 := h z y v0
  have h175 := S h174
  have h176 := R z
  have h177 := C h88 h176
  have h178 := h z v21 z
  have h179 := C h51 (T h178 h177)
  have h180 := C (T (T h178 h177) h179) h19
  have h181 := T h180 h175
  have h182 := C h176 h181
  have h183 := C h121 (T (T (T (T (T h182 h12) h50) h49) h95) h120)
  let v184 := M z v0
  have h185 := R (M z v184)
  have h186 := C h51 h185
  have h187 := S h178
  have h188 := C h57 h176
  have h189 := C h47 (T h188 h187)
  have h190 := C (T (T h189 h188) h187) h19
  have h191 := T h174 h190
  have h192 := C h47 (T (T h45 h13) (C h176 h191))
  have h193 := R v21
  have h194 := h v60 v1 z
  have h195 := h v184 y z
  have h196 := S h195
  have h197 := C (T (T (T (T (T h34 h76) h73) h70) h192) h186) h181
  have h198 := C h51 (T (T (T (T (T h197 h196) h180) h175) h178) h177)
  have h199 := C (T (T (T (T (T (C h47 h185) (C h51 (T (T h182 h12) h50))) h100) h99) h98) h42) h191
  have h200 := C h19 (T (T (T (T (T (T (T h198 h189) h188) h187) h174) h190) h195) h199)
  have h201 := R (M v0 (M v21 v184))
  have h202 := C h47 h201
  have h203 := C h47 (T (T (T (T (T h188 h187) h174) h190) h195) h199)
  have h204 := T (T (T (T (T h180 h175) h178) h177) h179) h203
  have h205 := C h51 h204
  have h206 := T (T (T (T (T (T (T (T h205 h202) h200) h198) h189) h188) h187) h174) h190
  have h207 := C h19 h206
  have h208 := C h19 h207
  have h209 := R (M v0 (M v0 v184))
  have h210 := C h47 h209
  have h211 := T (T (T (T (T h198 h189) h188) h187) h174) h190
  have h212 := C h47 h211
  have h213 := C h51 h201
  have h214 := C h19 (T (T (T (T (T (T (T h197 h196) h180) h175) h178) h177) h179) h203)
  have h215 := T (T (T (T (T (T (T (T h180 h175) h178) h177) h179) h203) h214) h213) h212
  have h216 := C h19 h215
  have h217 := C h64 h216
  have h218 := C h64 h215
  have h219 := T (T (T h188 h187) h174) h190
  have h220 := C h124 h219
  have h221 := T (T (T h180 h175) h178) h177
  have h222 := C h111 h221
  have h223 := C h51 (T (T (T (T (T (T (T (T (T (T (T (T (T h218 h217) h210) h208) h207) h205) h202) h200) h198) h189) h188) h187) h174) h190)
  let v224 := M v60 v184
  have h225 := R (M v0 v224)
  have h226 := h v224 y v0
  have h227 := C h64 h206
  have h228 := C h64 h207
  have h229 := C h51 h209
  have h230 := C h19 h216
  have h231 := C h47 (T (T (T (T (T (T (T (T (T (T (T (T (T h180 h175) h178) h177) h179) h203) h214) h213) h212) h216) h230) h229) h228) h227)
  have h232 := C h111 h219
  have h233 := C h121 h221
  have h234 := R (M z (M v32 v184))
  have h235 := T (T (T h160 h159) h158) h143
  have h236 := T (T (C h64 h135) h163) h162
  have h237 := T (T h160 h159) (C h64 h142)
  have h238 := C h131 (T (T (T (T (T (T (T (T (T h168 h151) h150) h149) h148) h147) h146) h145) h144) h142)
  have h239 := C h19 h169
  have h240 := C h19 (T h104 h138)
  have h241 := h x v1 v2
  have h242 := R v3
  have h243 := C h242 h81
  have h244 := C h242 (T (T (T (T (T (T (T h35 h24) h20) h16) h54) h89) h87) h82)
  have h245 := C h242 h74
  have h246 := C h242 h27
  have h247 := R (M v3 y)
  have h248 := C h242 h39
  have h249 := C h242 h71
  have h250 := C h242 (T (T (T (T (T (T (T h104 h67) h58) h55) h15) h26) h23) h43)
  have h251 := C h242 h103
  T (T (T (T (T (T (T h241 (C (T (T (T h109 h67) h58) h55) (T (T (T (T (T h4 h10) h251) h250) h249) h248))) (C h117 h247)) (C h126 (T (T (T h246 h245) h244) h243))) (C h29 h9)) (h (M y v2) v0 v2)) (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (C h193 (T (T (T (T (T (T (T (T (T (T (T (T (C (R v2) (T (T (T (T (C h29 h11) (C h117 (T (T (T h251 h250) h249) h248))) (C h126 h247)) (C h172 (T (T (T (T (T h246 h245) h244) h243) h8) h5))) (S h241))) h94) h91) h54) h89) h87) h240) h239) h238) h165) h164) h163) h162)) (C h193 h161)) (C h193 h153)) (C h193 h139)) (C h193 (T (T (T (T (T (T (T (T (T (C h131 (T h109 h240)) (C h124 h239)) (C h121 h141)) (C h124 (T (T h238 h165) h156))) (C h121 h155)) (C h111 (T (T (T h152 h164) h163) h162))) (C h108 h235)) (C h51 h166)) (C h47 h237)) (C h19 h236)))) (C h193 (C h19 h237))) (C h193 (T (C h51 h236) (C h47 h235)))) (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h34 h76) h73) h70) h192) h186) h183) h173) (C h51 (C h6 h66))) (C h121 (T (T (T (T (C h6 h86) h106) h96) h194) (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (C h111 (T (T (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T h178 h177) h179) h203) h214) h213) h212) h216) h230) h229) h228) h227) h231) (C h19 h231)) (C h51 h225)) h47) (S h226)) h231)) (C h111 (T (T (T (T h223 h218) h217) h210) h208))) (C h111 h207)) (C h111 (T (T h205 h202) h200))) (C h111 h211)) h222) h220) h218) h217) h210) h208) h207) h205) h202) h200) h198) h189) h188) h187) (T (T (T (T (T (T (T (T (T (T (T (T (T h178 h177) h179) h203) h214) h213) h212) h216) h230) h229) h228) h227) h233) h232))))) (C h108 h234)) (C h51 h234)) (C h121 (T (T (T (T (T (T (T (T (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h178 h177) h179) h203) h214) h213) h212) h216) h230) h229) h228) h227) h233) h232) (C h111 h204)) (C h111 (T (T h214 h213) h212))) (C h111 h216)) (C h111 (T (T (T (T h230 h229) h228) h227) h231))) (C h111 (T (T h223 h226) (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (C h47 h225) (C h19 h223)) h223) h218) h217) h210) h208) h207) h205) h202) h200) h198) h189) h188) h187) h51)))) (T (T (T (T (T (T (T (T (T (T (T (T (T h222 h220) h218) h217) h210) h208) h207) h205) h202) h200) h198) h189) h188) h187)) (S h194)) h46) h45) h13) h33) h31) h28) h75))) (C h111 h72)) (C h111 h41)) (C h111 (T (T (T (T (T (T (T (T h12 h50) h49) h95) h120) h119) (h v32 v0 y)) (C (T (T (C h193 h118) (C (T (T (T (T (T (T (T (T h34 h76) h73) h70) h192) h186) h183) h173) (C h19 h119)) (T (T h116 h78) h48))) (S (h v1 z v1))) h172)) (C h126 h171)))) (C h124 (C h117 h171))) (C h121 (R (M v1 v170)))) (C h124 (C h126 h169))) (C h121 (R (M y v140)))) (C h124 (C h117 (R v140)))) (C h121 (R (M v1 v140)))) (C h124 (C h126 h168))) (C h121 (R (M y v154)))) (C h124 (C h117 (R v154)))) (C h121 (R (M v1 v154)))) (C h111 (C h126 (T (T (T (T (T (T (T (T h151 h150) h149) h148) h147) h146) h145) h144) h142)))) (C h124 h167)) (C h47 h167)) (T (T (T (T (T (T (T (T (T (T (C h131 h166) (C h111 h161)) (C h124 h155)) (C h121 h153)) (C h124 h141)) (C h121 h139)) (C h108 (T h137 h138))) h137) h67) h58) h55))) (S (h v136 z y))) h135) h134) h133) h130) h128) h125) h122) h115) h114) h113) h112) h109) h82) h80) h78) h48) h11)) (C h6 h9)

