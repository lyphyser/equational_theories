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
theorem Equation895_implies_Equation4620 (G: Type _) [Magma G] (h: Equation895 G) : Equation4620 G := fun x y z =>
  let v0 := M z y
  let v1 := M v0 z
  let v2 := M v1 x
  let v3 := M z x
  have h4 := h v1 v1 (M v3 v2)
  have h5 := S h4
  have h6 := h z v1 x
  have h7 := R v1
  have h8 := C h7 (C h6 h6)
  let v9 := M x x
  let v10 := M z z
  let v11 := M v1 v10
  have h12 := h v11 v9 v9
  have h13 := S h12
  have h14 := h x v9 x
  have h15 := S h14
  have h16 := R v9
  have h17 := C h16 (C h15 h15)
  have h18 := h v9 v9 (M v9 (M v9 x))
  have h19 := T h18 h17
  have h20 := S h6
  have h21 := C h7 (C h20 h20)
  have h22 := T h4 h21
  have h23 := C h22 h16
  have h24 := h x v1 x
  have h25 := S h24
  have h26 := C h7 (C h25 h25)
  have h27 := h v1 v1 (M v9 v2)
  have h28 := T (T (T (T h8 h5) h27) h26) h23
  have h29 := C h28 h19
  have h30 := C h16 (T (T (T h27 h26) h23) h29)
  let v31 := M v9 v1
  have h32 := h v31 v1 v9
  have h33 := S h32
  have h34 := T h27 h26
  have h35 := S h18
  have h36 := C h16 (C h14 h14)
  have h37 := T h36 h35
  have h38 := S h27
  have h39 := C h7 (C h24 h24)
  have h40 := T h8 h5
  have h41 := C h40 h16
  have h42 := T (T (T (T h41 h39) h38) h4) h21
  have h43 := C h42 h37
  have h44 := C h16 (T (T (T h43 h41) h39) h38)
  have h45 := T (T (T (T (T (T h41 h39) h38) h4) h21) h12) h44
  have h46 := C h45 h37
  have h47 := T (T (T (T (T (T (T (T h30 h13) h8) h5) h27) h26) h23) h29) h46
  have h48 := C h47 h34
  have h49 := T h39 h38
  have h50 := C h45 h49
  have h51 := C h28 h34
  have h52 := C h22 h7
  have h53 := C (T (T (T h30 h13) h8) h5) (T (T (T h52 h51) h50) h48)
  let v54 := M v1 v1
  let v55 := M v31 v54
  have h56 := h v55 z v9
  have h57 := S h56
  have h58 := h x z x
  have h59 := S h58
  have h60 := R z
  have h61 := C h60 (C h59 h59)
  have h62 := h z z (M v9 v3)
  have h63 := T h62 h61
  have h64 := C h40 h7
  have h65 := C h42 h49
  have h66 := T (T (T (T (T (T h30 h13) h8) h5) h27) h26) h23
  have h67 := C h66 h34
  have h68 := C h66 h19
  have h69 := T (T (T (T (T (T (T (T h68 h43) h41) h39) h38) h4) h21) h12) h44
  have h70 := C h69 h49
  have h71 := C (T (T (T h4 h21) h12) h44) (T (T (T h70 h67) h65) h64)
  have h72 := T (T (T (T (T (T (T (T (T (T h68 h43) h41) h39) h38) h4) h21) h12) h44) h32) h71
  have h73 := C h72 h37
  have h74 := C h47 h19
  have h75 := T (T (T (T (T (T (T (T (T (T (T (T h53 h33) h30) h13) h8) h5) h27) h26) h23) h29) h46) h74) h73
  have h76 := C h75 h63
  have h77 := S h62
  have h78 := C h60 (C h58 h58)
  have h79 := T h78 h77
  have h80 := C h72 h79
  have h81 := C h47 h63
  have h82 := C h45 h79
  have h83 := C h28 h63
  have h84 := C h22 h60
  have h85 := h z v9 y
  have h86 := S h85
  let v87 := M v9 y
  let v88 := M v0 v87
  have h89 := R v88
  have h90 := h v9 v1 v1
  have h91 := S h90
  have h92 := C h69 h37
  have h93 := T (T (T (T (T (T (T (T (T (T h53 h33) h30) h13) h8) h5) h27) h26) h23) h29) h46
  have h94 := C h93 h19
  have h95 := C (T (T (T (T (T (T h94 h92) h68) h43) h41) h39) h38) (T (T (T (T (T (T (T h39 h38) h4) h21) h12) h44) h32) h71)
  have h96 := C h75 h34
  have h97 := C h72 h49
  have h98 := T (T h96 h95) h91
  have h99 := C h98 (T (T (T (T (T (T (T h52 h51) h50) h48) h97) h96) h95) h91)
  have h100 := R v54
  have h101 := T h48 h97
  have h102 := C h101 h100
  have h103 := T h51 h50
  have h104 := C h103 h100
  have h105 := C h52 h100
  let v106 := M v54 v54
  have h107 := h v106 y y
  have h108 := S h107
  have h109 := R (M y y)
  have h110 := R y
  have h111 := C h64 h100
  have h112 := T h67 h65
  have h113 := C h112 h100
  have h114 := C h93 h34
  have h115 := T h114 h70
  have h116 := C h115 h100
  have h117 := T (T (T (T (T (T (T (T (T (T (T (T h94 h92) h68) h43) h41) h39) h38) h4) h21) h12) h44) h32) h71
  have h118 := C h117 h49
  have h119 := C (T (T (T (T (T (T h27 h26) h23) h29) h46) h74) h73) (T (T (T (T (T (T (T h53 h33) h30) h13) h8) h5) h27) h26)
  have h120 := T (T h90 h119) h118
  have h121 := C h120 (T (T (T (T (T (T (T h90 h119) h118) h114) h70) h67) h65) h64)
  have h122 := T (T (T (T (T h18 h17) h121) h116) h113) h111
  have h123 := h y v87 x
  have h124 := S h123
  have h125 := R v87
  let v126 := M v87 x
  let v127 := M y x
  have h128 := h v87 v87 (M v127 v126)
  have h129 := C h110 (T (T h128 (C h125 (C h124 h124))) (C (C h122 h110) h109))
  have h130 := T (T (T (T (T (T (T h129 h108) h105) h104) h102) h99) h36) h35
  have h131 := C h130 h89
  let v132 := M y v87
  have h133 := h (M v132 v88) y y
  have h134 := S h133
  have h135 := T (T (T (T (T h105 h104) h102) h99) h36) h35
  have h136 := C h135 h110
  have h137 := C h110 (T (T (C h136 h109) (C h125 (C h123 h123))) (S h128))
  have h138 := T (T (T (T (T (T (T h18 h17) h121) h116) h113) h111) h107) h137
  have h139 := C h138 h89
  have h140 := T h85 h139
  have h141 := h y v0 x
  have h142 := S h141
  have h143 := R v0
  let v144 := M v0 x
  have h145 := h v0 v0 (M v127 v144)
  have h146 := C h110 (T (T h145 (C h143 (C h142 h142))) (C (C h140 h110) h109))
  let v147 := M y v0
  have h148 := h v147 v0 z
  have h149 := S h148
  have h150 := h v147 v1 v9
  have h151 := T h131 h86
  have h152 := C h110 (T (T (C (C h151 h110) h109) (C h143 (C h141 h141))) (S h145))
  have h153 := T (T (T h85 h139) h133) h152
  have h154 := T h133 h152
  have h155 := h v55 v9 v9
  have h156 := S h155
  have h157 := C h135 (T (T (T (T (T (T (T h27 h26) h23) h29) h46) h74) h73) (C h75 h19))
  have h158 := T h129 h108
  have h159 := C h158 h7
  have h160 := T (T (T (T (T (T (T (T h159 h157) h156) h53) h33) h30) h13) h8) h5
  have h161 := T (T (T (T (T (C h160 (T (T (C h140 h7) (C h154 h7)) (C (T (T (T (T (T (T h146 h134) h131) h86) h62) h61) (C h153 h16)) h34))) (S h150)) h146) h134) h131) h86
  have h162 := C h153 h161
  have h163 := h v132 z v1
  have h164 := h v132 v9 v1
  have h165 := S h164
  have h166 := h v11 v1 v1
  have h167 := T h107 h137
  have h168 := C h167 h7
  have h169 := C h122 (T (T (T (T (T (T (T (C h117 h37) h94) h92) h68) h43) h41) h39) h38)
  have h170 := T (T (T (T (T (T (T (T h4 h21) h12) h44) h32) h71) h155) h169) h168
  have h171 := h v132 v1 v1
  have h172 := C h130 (T (T (T (T (T (T (T (T (T h18 h17) h121) h116) h113) h111) h107) h137) h171) (C h170 (T (T (T (T (C h159 h100) (C (T (T (T (T (T (T (T h157 h156) h53) h33) h30) h13) h8) h5) (T (T (T (T (T (T (T (T (T (T (T (T h52 h51) h50) h48) h97) h96) h95) h91) h18) h17) h121) h116) h113))) (S h166)) h12) h44)))
  have h173 := C (T (T (T h172 h165) h163) h162) h49
  have h174 := C h138 (T (T (T (T (T (T (T (T (T (C h160 (T (T (T (T h30 h13) h166) (C (T (T (T (T (T (T (T h4 h21) h12) h44) h32) h71) h155) h169) (T (T (T (T (T (T (T (T (T (T (T (T h104 h102) h99) h36) h35) h90) h119) h118) h114) h70) h67) h65) h64))) (C h168 h100))) (S h171)) h129) h108) h105) h104) h102) h99) h36) h35)
  have h175 := T h164 h174
  have h176 := C h175 h34
  have h177 := C h143 (T (T (T (T (T (T (T (T (T (T h4 h21) h12) h44) h32) h71) h155) h169) h168) h176) h173)
  let v178 := M v0 v1
  have h179 := h v178 v9 v9
  have h180 := S h179
  have h181 := S h163
  have h182 := T h146 h134
  have h183 := T (T (T h146 h134) h131) h86
  have h184 := T (T (T (T (T h85 h139) h133) h152) h150) (C h170 (T (T (C (T (T (T (T (T (T (C h183 h16) h78) h77) h85) h139) h133) h152) h49) (C h182 h7)) (C h151 h7)))
  have h185 := T (T (T (T (T h177 h149) h146) h134) h131) h86
  have h186 := C h185 h184
  have h187 := h v178 z z
  have h188 := S h187
  have h189 := C h151 h60
  have h190 := C h182 h60
  have h191 := T h172 h165
  have h192 := C h191 h49
  have h193 := C h183 h184
  have h194 := C (T (T (T h193 h181) h164) h174) h34
  have h195 := C h143 (T (T (T (T (T (T (T (T (T (T h194 h192) h159) h157) h156) h53) h33) h30) h13) h8) h5)
  have h196 := T (T (T (T (T h85 h139) h133) h152) h148) h195
  have h197 := C h196 h161
  have h198 := C (T (T (T (T (T (T (T (T (T h18 h17) h121) h116) h113) h111) h107) h137) h163) h197) (T (T (T (T (T (T (C h191 h37) h172) h165) h163) h162) h190) h189)
  have h199 := h v132 v9 v9
  have h200 := C h185 (T (T (T (T (T (T (T (T (T h18 h17) h121) h116) h113) h111) h107) h137) h199) h198)
  have h201 := C (T h200 h188) h79
  have h202 := S h199
  have h203 := C h154 h60
  have h204 := C h140 h60
  have h205 := C (T (T (T (T (T (T (T (T (T h186 h181) h129) h108) h105) h104) h102) h99) h36) h35) (T (T (T (T (T (T h204 h203) h193) h181) h164) h174) (C h175 h19))
  have h206 := C h196 (T (T (T (T (T (T (T (T (T h205 h202) h129) h108) h105) h104) h102) h99) h36) h35)
  have h207 := C (T (T (T (T (T (T (T h85 h139) h133) h152) h148) h195) h187) h206) (T (T (T (T (T (T (T (T h201 h186) h181) h129) h108) h105) h104) h102) h99)
  have h208 := h v178 z v9
  have h209 := C h98 (T h208 h207)
  have h210 := R v178
  have h211 := C h101 h210
  have h212 := C h103 h210
  have h213 := T (T (T (T (T (T (T h78 h77) h85) h139) h133) h152) h148) h195
  have h214 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h172 h165) h129) h108) h105) h104) h102) h99) h36) h35) h90) h119) h118) h114) h70) h67) h65) h213
  have h215 := C h175 h63
  have h216 := T (T (T (T (T (T (T (T (T (T (T h215 h214) h212) h211) h209) h180) h177) h149) h146) h134) h131) h86
  have h217 := C h216 (T (T (T (T (T h84 h83) h82) h81) h80) h76)
  let v218 := M v1 z
  have h219 := R v218
  have h220 := C h167 h60
  have h221 := C h220 h219
  have h222 := C h122 h60
  have h223 := C h222 h219
  let v224 := M v9 z
  let v225 := M v224 v218
  have h226 := h y y (M v9 v127)
  have h227 := h x y x
  have h228 := T (C h110 (C h227 h227)) (S h226)
  have h229 := S h227
  have h230 := T h226 (C h110 (C h229 h229))
  have h231 := h v9 z z
  have h232 := S h231
  have h233 := R v10
  have h234 := C h135 h60
  have h235 := C h234 h233
  have h236 := C h158 h60
  have h237 := C h236 h233
  have h238 := T (T (T (T (T (T (T (T (T h121 h116) h113) h111) h107) h137) h163) h162) h190) h189
  have h239 := h v224 z z
  have h240 := S h239
  have h241 := C h191 h79
  have h242 := T (T (T (T (T (T (T h177 h149) h146) h134) h131) h86) h62) h61
  have h243 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h51 h50) h48) h97) h96) h95) h91) h18) h17) h121) h116) h113) h111) h107) h137) h164) h174) h242
  have h244 := C h52 h210
  have h245 := T (T (T (T h244 h243) h241) h236) h234
  have h246 := C h245 h60
  have h247 := C h246 h233
  have h248 := C h64 h210
  have h249 := C h112 h210
  have h250 := C h115 h210
  have h251 := S h208
  have h252 := C (T h187 h206) h63
  have h253 := C (T (T (T (T (T (T (T h200 h188) h177) h149) h146) h134) h131) h86) (T (T (T (T (T (T (T (T h121 h116) h113) h111) h107) h137) h163) h197) h252)
  have h254 := C h120 (T h253 h251)
  have h255 := C (T (T (T (T (T (T h200 h188) h179) h254) h250) h249) h248) h79
  have h256 := C (T h252 h255) h233
  have h257 := C (T (T (T (T (T (T (T (T (T (T h244 h212) h211) h209) h180) h177) h149) h146) h134) h131) h86) (T (T (T (T (T (T (T (T (T (T (T h18 h17) h121) h116) h113) h111) h107) h137) h199) h198) h256) h247)
  have h258 := T (T (T (T h222 h220) h215) h214) h248
  have h259 := C h258 h16
  have h260 := C (T (T (T (T h259 h257) h240) h222) h220) h238
  have h261 := C (T (T (T (T (T (T h244 h212) h211) h209) h180) h187) h206) h63
  have h262 := R (M z v9)
  have h263 := C h245 h16
  have h264 := C (T h261 h201) h233
  have h265 := C h258 h60
  have h266 := C h265 h233
  have h267 := C (T (T (T (T (T (T (T (T (T (T h85 h139) h133) h152) h148) h195) h179) h254) h250) h249) h248) (T (T (T (T (T (T (T (T (T (T (T h266 h264) h205) h202) h129) h108) h105) h104) h102) h99) h36) h35)
  have h268 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h85 h139) h133) h152) h148) h195) h179) h254) h250) h249) h243) h241) h236) h234) h239) h267) h263) (T (T (T (T (T (T (T (T (T (T (T (C h259 h262) (C (T (T (T (T (T (T h257 h240) h222) h220) h215) h214) h248) h79)) h261) h201) h186) h181) h129) h108) h105) h104) h102) h99)
  have h269 := h v224 z v9
  have h270 := C h216 (T (T (T (T h269 h268) h260) h237) h235)
  have h271 := R v224
  have h272 := C h220 h271
  have h273 := C h222 h271
  let v274 := M v224 v224
  have h275 := h v274 v9 z
  have h276 := S h269
  have h277 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h259 h257) h240) h222) h220) h215) h214) h212) h211) h209) h180) h177) h149) h146) h134) h131) h86) (T (T (T (T (T (T (T (T (T (T (T h121 h116) h113) h111) h107) h137) h163) h197) h252) h255) (C (T (T (T (T (T (T h244 h243) h241) h236) h234) h239) h267) h63)) (C h263 h262))
  have h278 := T (T (T (T (T (T (T (T (T h204 h203) h193) h181) h129) h108) h105) h104) h102) h99
  have h279 := C (T (T (T (T h236 h234) h239) h267) h263) h278
  have h280 := C h220 h233
  have h281 := C h222 h233
  let v282 := M v224 v10
  have h283 := h v282 z v9
  have h284 := S h283
  have h285 := T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h52 h51) h50) h48) h97) h96) h95) h91) h18) h17) h121) h116) h113) h111) h107) h137) h163) h162) h190) h189
  have h286 := h v106 v1 z
  have h287 := S h286
  have h288 := C h236 h219
  have h289 := C h40 h60
  have h290 := C h42 h79
  have h291 := C h66 h63
  have h292 := C h69 h79
  have h293 := C h93 h63
  have h294 := C h117 h79
  have h295 := T (T (T (T (T (T (T (T (T (T (T h85 h139) h133) h152) h148) h195) h179) h254) h250) h249) h243) h241
  have h296 := C h295 (T (T (T (T (T h294 h293) h292) h291) h290) h289)
  have h297 := T (T (T (T (T (T (T (T (T h223 h221) h217) h57) h53) h33) h30) h13) h8) h5
  have h298 := C h297 (T (T (T (T (T (T (T (T h4 h21) h12) h44) h32) h71) h56) h296) h288)
  have h299 := C (T (T (T (T (T (T (T (T h298 h287) h107) h137) h163) h197) h252) h255) h246) h285
  have h300 := T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h204 h203) h193) h181) h129) h108) h105) h104) h102) h99) h36) h35) h90) h119) h118) h114) h70) h67) h65) h64
  have h301 := C h234 h219
  have h302 := T (T (T (T (T (T (T (T (T h4 h21) h12) h44) h32) h71) h56) h296) h288) h301
  have h303 := C h302 (T (T (T (T (T (T (T (T h221 h217) h57) h53) h33) h30) h13) h8) h5)
  have h304 := h v106 z z
  have h305 := S h304
  have h306 := T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h281 h280) h279) h277) h276) h222) h220) h215) h214) h212) h211) h209) h180) h177) h149) h146) h134) h131) h86
  have h307 := C h306 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h85 h139) h133) h152) h148) h195) h179) h254) h250) h249) h243) h241) h236) h234) h269) h268) h260) h237)
  have h308 := T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h85 h139) h133) h152) h148) h195) h179) h254) h250) h249) h243) h241) h236) h234) h269) h268) h260) h237) h235
  have h309 := C h308 (T (T (T (T (T (T (T (T (T (T (T (T (T (C (T (T (T h307 h305) h286) h303) h300) h299) h266) h264) h205) h202) h129) h108) h105) h104) h102) h99) h36) h35)
  have h310 := h v282 z z
  have h311 := C h308 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h280 h279) h277) h276) h222) h220) h215) h214) h212) h211) h209) h180) h177) h149) h146) h134) h131) h86)
  have h312 := S h310
  have h313 := C (T (T (T (T (T (T (T (T h265 h261) h201) h186) h181) h129) h108) h286) h303) h300
  have h314 := C h306 (T (T (T (T (T (T (T (T (T (T (T (T (T h18 h17) h121) h116) h113) h111) h107) h137) h199) h198) h256) h247) h313) (C (T (T (T h298 h287) h304) h311) h285))
  have h315 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h314 h312) h281) h280) h279) h277) h276) h222) h220) h215) h214) h212) h211) h209) h180) h177) h149) h146) h134) h131) h86) (T (T (T (T (T (T h121 h116) h113) h111) h304) h311) (C (T h310 h309) h63))
  have h316 := h v282 v9 v9
  have h317 := S h316
  have h318 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h85 h139) h133) h152) h148) h195) h179) h254) h250) h249) h243) h241) h236) h234) h269) h268) h260) h237) h235) h310) h309) (T (T (T (T (T (T (C (T h314 h312) h79) h307) h305) h105) h104) h102) h99)
  have h319 := T (T (T h273 h272) h270) h232
  have h320 := C h319 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h85 h139) h133) h152) h148) h195) h179) h254) h250) h249) h243) h241) h236) h234) h269) h268) h260) h237) h235) h283) h318)
  have h321 := C h234 h271
  have h322 := C h236 h271
  have h323 := C h295 (T (T (T (T h281 h280) h279) h277) h276)
  have h324 := T (T (T h231 h323) h322) h321
  have h325 := C h324 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h315 h284) h281) h280) h279) h277) h276) h222) h220) h215) h214) h212) h211) h209) h180) h177) h149) h146) h134) h131) h86)
  have h326 := h v274 z z
  have h327 := C (T (T (T (T (T (T (T (T (T (T (T h261 h201) h186) h181) h129) h108) h105) h104) h102) h99) h36) h35) (T (T (T (T (T (T (T (T (T h222 h220) h215) h214) h212) h211) h209) h180) h208) h207)
  have h328 := C h265 h271
  have h329 := C (T (T (T (T h193 h197) h252) h255) h246) h271
  have h330 := C h203 h271
  have h331 := C h204 h271
  have h332 := h (M v10 v224) v1 z
  have h333 := S h332
  have h334 := C h203 h7
  have h335 := C h204 h7
  have h336 := C h189 h7
  have h337 := C h190 h7
  have h338 := h v225 v1 v1
  have h339 := S h338
  have h340 := C h297 (T (T (T (T (T (T (T (T (T (T (T (T h18 h17) h121) h116) h113) h111) h107) h137) h199) h198) h256) h247) h313)
  have h341 := T h340 h339
  have h342 := C h302 (T (T (T (T (T (T (T (T (T (T (T (T h299 h266) h264) h205) h202) h129) h108) h105) h104) h102) h99) h36) h35)
  have h343 := h v225 v9 v9
  have h344 := S h343
  have h345 := T (T (T (T (T (T (T (T (T (T (T h4 h21) h12) h44) h32) h71) h56) h296) h288) h301) h338) h342
  have h346 := h v225 v1 v9
  have h347 := C (T (T (T (T (T (T (T h307 h305) h105) h104) h102) h99) h36) h35) (T (T (T (T (T (T (T (T (T (T (T h4 h21) h12) h44) h32) h71) h56) h296) h288) h301) h346) (C h345 (T (T (T (T (T (T (C h341 h49) h298) h287) h105) h104) h102) h99)))
  have h348 := C (T (T (T (T (T (T (T (T (T (T (T h273 h272) h270) h232) h18) h17) h121) h116) h113) h111) h304) h311) h7
  have h349 := C (T (T (T (T (T (T (T (T (T (T (T h307 h305) h105) h104) h102) h99) h36) h35) h231) h323) h322) h321) h7
  have h350 := T h338 h342
  have h351 := T (T (T (T (T (T (T (T (T (T (T h340 h339) h223) h221) h217) h57) h53) h33) h30) h13) h8) h5
  have h352 := C (T (T (T (T (T (T (T h18 h17) h121) h116) h113) h111) h304) h311) (T (T (T (T (T (T (T (T (T (T (T (C h351 (T (T (T (T (T (T h121 h116) h113) h111) h286) h303) (C h350 h34))) (S h346)) h223) h221) h217) h57) h53) h33) h30) h13) h8) h5)
  have h353 := C h189 h271
  have h354 := C h190 h271
  have h355 := C (T (T (T (T h265 h261) h201) h186) h162) h271
  have h356 := C h246 h271
  have h357 := C (T (T (T (T (T (T (T (T (T (T (T h18 h17) h121) h116) h113) h111) h107) h137) h163) h197) h252) h255) (T (T (T (T (T (T (T (T (T h253 h251) h179) h254) h250) h249) h243) h241) h236) h234)
  have h358 := h v0 v9 z
  have h359 := h v0 v0 (M v9 v144)
  have h360 := S h359
  have h361 := h x v0 x
  have h362 := C h143 (C h361 h361)
  have h363 := C h351 (T (T (T h362 h360) h358) (C (T (T (T (T (T (T (T (T (T (T (T (T (T h18 h17) h121) h116) h113) h111) h107) h137) h163) h197) h252) h255) h246) (C (T (T (T (T (T (T (T (T (T (T (T h222 h220) h215) h214) h212) h211) h209) h357) h356) h355) h354) h353) h60)) (T (T (T (T (T (T (T (T (T (T (T (C (T (T (T (T (T (T (T (T (T (T (T (T h4 h21) h12) h44) h32) h71) h56) h296) h288) h301) h343) h352) h349) (T (T (T (T (T (T (T h222 h220) h215) h214) h212) h211) h209) h180)) (C (T (T (T (T h348 h347) h344) h338) h342) h242)) (C h341 h79)) (C (T (T (T (T (T (T (T (T (T (T h223 h221) h217) h57) h155) h169) h168) h176) h173) h337) h336) h196)) (C (T (T (T (T h335 h334) h194) h192) h159) h210)) (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T h157 h156) h53) h33) h30) h13) h8) h5) h27) h26) h23) h29) h46) h74) h73) h242)) h294) h293) h292) h291) h290) h289)))
  have h364 := S h361
  have h365 := C h143 (C h364 h364)
  have h366 := T h359 h365
  have h367 := C h350 h366
  have h368 := T h362 h360
  have h369 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h94 h92) h68) h43) h41) h39) h38) h4) h21) h12) h44) h32) h71) h56) h296) h288) h301) h368
  have h370 := C h75 h366
  have h371 := C h72 h368
  have h372 := C h47 h366
  have h373 := C h45 h368
  have h374 := C h28 h366
  have h375 := C h22 h143
  let v376 := M v1 v0
  have h377 := R v376
  have h378 := C h341 h368
  have h379 := C h345 (T (T (T (C (T (T (T (T (T (T (T (T (T (T (T (T (T (C (T (T (T (T (T (T (T (T (T (T (T h331 h330) h329) h328) h327) h254) h250) h249) h243) h241) h236) h234) h60) h265) h261) h201) h186) h181) h129) h108) h105) h104) h102) h99) h36) h35) (T (T (T (T (T (T (T (T (T (T (T h84 h83) h82) h81) h80) h76) (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T h94 h92) h68) h43) h41) h39) h38) h4) h21) h12) h44) h32) h71) h155) h169) h213)) (C (T (T (T (T h168 h176) h173) h337) h336) h210)) (C (T (T (T (T (T (T (T (T (T (T h335 h334) h194) h192) h159) h157) h156) h56) h296) h288) h301) h185)) (C h350 h63)) (C (T (T (T (T h340 h339) h343) h352) h349) h213)) (C (T (T (T (T (T (T (T (T (T (T (T (T h348 h347) h344) h223) h221) h217) h57) h53) h33) h30) h13) h8) h5) (T (T (T (T (T (T (T h179 h254) h250) h249) h243) h241) h236) h234)))) (S h358)) h359) h365)
  have h380 := C h40 h143
  have h381 := C h42 h368
  have h382 := C h66 h366
  have h383 := C h69 h368
  have h384 := C h93 h366
  have h385 := C h117 h368
  have h386 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h223 h221) h217) h57) h53) h33) h30) h13) h8) h5) h27) h26) h23) h29) h46) h74) h73) h366
  have h387 := S (h x v87 x)
  T (T (T (T (T (T (T (T (T (T (T (T (T (h v87 v87 (M v9 v126)) (C h125 (C h387 h387))) (C h125 (T (T (T (T (T (T (T (T (T (T h231 h323) h322) h321) (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T h222 h220) h215) h214) h212) h211) h209) h357) h356) h355) h354) h353) h332) h379) h378) (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h222 h220) h215) h214) h212) h211) h209) h357) h356) h355) h354) h353) h332) h379) h378) h386) h385) h384) h383) h382) h381) h380))) (C (T h386 h385) h377)) (C (T h384 h383) h377)) (C (T h382 h381) h377)) (C h380 h377)) (h (M v376 v376) z y)) (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T h85 h139) h133) h152) h148) h195) h179) h357) h356) h355) h354) h353) h332) h379) h378) (T (T (T (C (T (C (T (T (T (T (T (T (C h375 h377) (C (T h374 h373) h377)) (C (T h372 h371) h377)) (C (T h370 h369) h377)) (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T h367 h363) h333) h331) h330) h329) h328) h327) h254) h250) h249) h243) h241) h236) h234) (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h375 h374) h373) h372) h371) h370) h369) h367) h363) h333) h331) h330) h329) h328) h327) h254) h250) h249) h243) h241) h236) h234))) h275) (C h324 (T (T (T (T (T (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h320 h317) h281) h280) h279) h277) h276) h222) h220) h215) h214) h212) h211) h209) h180) h177) h149) h146) h134) h131) h86) (T (T (T (T (T (T (T h269 h268) h260) h237) h235) h283) h318) (C (T (T (T h314 h312) h316) h325) h238))) (S h326)) h273) h272) h270) h232))) h230) (C (T (C h319 (T (T (T (T (T h231 h323) h322) h321) h326) (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h85 h139) h133) h152) h148) h195) h179) h254) h250) h249) h243) h241) h236) h234) h269) h268) h260) h237) h235) h316) h325) (T (T (T (T (T (T (T (C (T (T (T h320 h317) h310) h309) h278) h315) h284) h281) h280) h279) h277) h276)))) (S h275)) h228)) h143) (C (T (C (T (T (T (T (T (T (T (T (T (T (T (T (T h273 h272) h270) h232) h18) h17) h121) h116) h113) h111) h107) h137) h164) h174) h230) (C h191 h228)) h143)) (C (C h158 h110) h143)) (C h136 h143)))))) (S (h v225 v87 v0))) h223) h221) h217) h57) h53) h33) h30) h13) h8) h5

