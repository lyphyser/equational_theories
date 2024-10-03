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
theorem Equation725_implies_Equation522 (G: Type _) [Magma G] (h: Equation725 G) : Equation522 G := fun x y z =>
  let v0 := M x z
  let v1 := M z v0
  let v2 := M y v1
  let v3 := M y v2
  have h4 := h v3 v3 v1
  have h5 := S h4
  let v6 := M v1 v3
  let v7 := M v6 v1
  let v8 := M v3 v7
  have h9 := h v8 x v3
  have h10 := S h9
  have h11 := R v3
  have h12 := C h4 h11
  have h13 := h v3 v3 v0
  have h14 := R x
  have h15 := C h14 (C h14 (T (C (S h13) h11) h12))
  let v16 := M (M v0 v3) v0
  have h17 := h (M v3 v16) x v3
  have h18 := h v16 v3 v1
  have h19 := R v1
  have h20 := h (M v1 v16) x v1
  have h21 := h v3 v1 v0
  have h22 := h v3 v1 v3
  have h23 := C (S h22) h19
  let v24 := M v3 v3
  let v25 := M v24 v3
  let v26 := M v1 v25
  have h27 := h v26 x v1
  have h28 := S h27
  have h29 := C h22 h19
  have h30 := h v3 v1 v1
  have h31 := S h30
  have h32 := C h14 (C h14 (T (C h31 h19) h29))
  have h33 := h (M v1 v7) x v1
  have h34 := S h33
  have h35 := C h14 (C h14 (T h23 (C h30 h19)))
  have h36 := h v26 v3 v1
  have h37 := S h36
  have h38 := h v1 x v2
  have h39 := S h38
  let v40 := M v2 v1
  let v41 := M v40 v2
  have h42 := h (M x v41) x x
  have h43 := h v1 x y
  have h44 := S h43
  let v45 := M v2 y
  have h46 := h (M x v45) x x
  have h47 := R y
  have h48 := h v2 x y
  have h49 := S h48
  have h50 := h v3 y y
  let v51 := M (M y v3) y
  have h52 := h (M y v51) x y
  have h53 := C h14 (T (T (T (C h14 (C (T (T h52 (C h14 (C h14 (C (S h50) h47)))) h49) h47)) h46) (C h14 (C h14 (T (C h44 h14) (C h38 h14))))) (S h42))
  have h54 := h v51 x y
  have h55 := h v51 x v0
  have h56 := S h55
  have h57 := R v0
  have h58 := h (M v0 v51) x v0
  have h59 := h v3 v0 y
  have h60 := h v3 v0 v3
  have h61 := h (M v0 v25) x v0
  have h62 := C h14 (C h14 (C (T (T h61 (C h14 (C h14 (T (C (S h60) h57) (C h59 h57))))) (S h58)) h57))
  have h63 := h v25 x v0
  have h64 := h v25 x v2
  have h65 := S h64
  have h66 := R v2
  have h67 := h (M v2 v25) x v2
  have h68 := h v3 v2 v3
  have h69 := h v3 v2 v1
  have h70 := C (S h69) h66
  have h71 := h (M v2 v7) x v2
  have h72 := C h14 (C h14 (C (T (T h71 (C h14 (C h14 (T h70 (C h68 h66))))) (S h67)) h66))
  have h73 := h v7 x v2
  have h74 := h v6 v3 v1
  have h75 := S h74
  have h76 := h y v2 v2
  have h77 := S h76
  have h78 := C h77 h66
  have h79 := C h19 h78
  let v80 := M v45 v2
  let v81 := M v2 v80
  have h82 := h v81 v1 v2
  have h83 := h v81 x v3
  have h84 := S h83
  have h85 := h v81 v3 v2
  have h86 := C h76 h66
  have h87 := C h5 h11
  have h88 := h v8 v3 v3
  have h89 := C h14 (C h14 (C (T h88 (C h11 (T (C h11 (T h87 (C h11 h86))) (S h85)))) h11))
  have h90 := h v7 x v3
  have h91 := S h73
  have h92 := C h69 h66
  have h93 := C h14 (C h14 (C (T (T h67 (C h14 (C h14 (T (C (S h68) h66) h92)))) (S h71)) h66))
  have h94 := S h63
  have h95 := C h14 (C h14 (C (T (T h58 (C h14 (C h14 (T (C (S h59) h57) (C h60 h57))))) (S h61)) h57))
  have h96 := S h54
  have h97 := C h14 (T (T (T h42 (C h14 (C h14 (T (C h39 h14) (C h43 h14))))) (S h46)) (C h14 (C (T (T h48 (C h14 (C h14 (C h50 h47)))) (S h52)) h47)))
  have h98 := T (T (T (T (T (T (T (T (T (T (T (T (T h38 h97) h96) h55) h95) h94) h64) h93) h91) h90) h89) h84) h82) (C h19 h79)
  have h99 := h v1 v1 x
  have h100 := C (S h99) h19
  have h101 := T h100 (C h98 h19)
  have h102 := C h11 h101
  have h103 := C h11 h102
  let v104 := M (M x v1) x
  let v105 := M v1 v104
  have h106 := h v105 v3 v1
  have h107 := h v104 v3 v1
  have h108 := C h11 (T h107 (C h11 (T (C h11 (T (T (T (T (T (T (T (T (T (C (T (T h106 h103) h75) h19) h73) h72) h65) h63) h62) h56) h54) h53) h39)) h29)))
  have h109 := h (M v3 v104) x v3
  have h110 := S h109
  have h111 := h v1 v3 x
  have h112 := h v1 v3 v2
  have h113 := S h112
  have h114 := C h113 h11
  have h115 := C h14 (C h14 (T h114 (C h111 h11)))
  let v116 := M v3 v41
  have h117 := h v116 x v3
  have h118 := h v116 v1 v3
  have h119 := C h112 h11
  have h120 := h v81 v3 v1
  have h121 := T (T (T (T (T (T (T (T (T (T (T (T (T (T h38 h97) h96) h55) h95) h94) h64) h93) h91) h90) h89) h84) h120) (C h11 (C h11 (T (T (C (T (T (T (T (T (T (T (T (T (C h19 (T h82 (C h19 (T h79 h119)))) (S h118)) h117) h115) h110) h108) h37) h27) h35) h34) h19) (C (T (T h33 h32) h28) h19)) (C (T (T h27 (C h14 (C h14 (T h23 (C h21 h19))))) (S h20)) h19))))) (S h18)
  have h122 := C (T (C h19 (T (T (T (T (T (T (T h117 h115) h110) h108) h37) h27) h35) h34)) h31) h121
  have h123 := C h11 (T (T (T h122 h17) h15) h10)
  have h124 := S h90
  have h125 := C h14 (C h14 (C (T (C h11 (T h85 (C h11 (T (C h11 h78) h12)))) (S h88)) h11))
  have h126 := S h82
  have h127 := C h19 h86
  have h128 := S h117
  have h129 := C h14 (C h14 (T (C (S h111) h11) h119))
  have h130 := S h106
  have h131 := C h99 h19
  have h132 := T (T (T (T (T (T (T (T (T (T (T (T (T (C h19 h127) h126) h83) h125) h124) h73) h72) h65) h63) h62) h56) h54) h53) h39
  have h133 := T (C h132 h19) h131
  have h134 := C h11 h133
  have h135 := C h11 h134
  have h136 := C h11 (T (C h11 (T h23 (C h11 (T (T (T (T (T (T (T (T (T h38 h97) h96) h55) h95) h94) h64) h93) h91) (C (T (T h74 h135) h130) h19))))) (S h107))
  have h137 := T (T (T (T (T (T (T (T (T (T (T (T (T (T h18 (C h11 (C h11 (T (T (C (T (T h20 (C h14 (C h14 (T (C (S h21) h19) h29)))) h28) h19) (C (T (T h27 h35) h34) h19)) (C (T (T (T (T (T (T (T (T (T h33 h32) h28) h36) h136) h109) h129) h128) h118) (C h19 (T (C h19 (T h114 h127)) h126))) h19))))) (S h120)) h83) h125) h124) h73) h72) h65) h63) h62) h56) h54) h53) h39
  have h138 := C (T h30 (C h19 (T (T (T (T (T (T (T h33 h32) h28) h36) h136) h109) h129) h128))) h137
  have h139 := h v3 v1 v2
  have h140 := S h139
  let v141 := M v2 v3
  let v142 := M v141 v2
  have h143 := h (M v1 v142) x v1
  have h144 := h v116 v3 v1
  have h145 := S h144
  have h146 := S h17
  have h147 := C h14 (C h14 (T h87 (C h13 h11)))
  have h148 := C h11 (T (T (T h9 h147) h146) h138)
  have h149 := C h11 (T h4 h148)
  have h150 := C h19 (T (T (T (T (T (T (T (T (T (T h87 h149) h145) h117) h115) h110) h108) h37) h27) (C h14 (C h14 (T h23 (C h139 h19))))) (S h143))
  have h151 := C (T (T (C h19 h12) h150) h140) h121
  have h152 := C h11 (T h151 h138)
  have h153 := C h11 (T h123 h5)
  have h154 := C h19 (T (T (T (T (T (T (T (T (T (T h143 (C h14 (C h14 (T (C h140 h19) h29)))) h28) h36) h136) h109) h129) h128) h144) h153) h12)
  have h155 := C (T (T h139 h154) (C h19 h87)) h137
  have h156 := h v8 v1 v3
  have h157 := S h156
  have h158 := C h19 (T h139 h154)
  have h159 := C h11 (T (T (T (T (T (T h114 h158) h157) h9) h147) h146) h155)
  have h160 := h v6 v1 v3
  have h161 := S h160
  have h162 := C h11 (T (T (T h106 h103) h75) h119)
  have h163 := C (T h162 (C h11 h114)) h11
  have h164 := C h19 h163
  have h165 := C h11 (T (T (T h114 h74) h135) h130)
  have h166 := C h19 (T h150 h140)
  have h167 := C h11 (T (T (T (T (T (T h151 h17) h15) h10) h156) h166) h119)
  have h168 := C h11 (T h122 h155)
  have h169 := C (T (T (T (T h4 h148) h168) h167) h165) (T (T h152 h123) h5)
  have h170 := h v24 v3 v1
  have h171 := C h19 (T (T h87 h170) h169)
  have h172 := S h170
  have h173 := C (T (T (T (T h162 h159) h152) h123) h5) (T (T h4 h148) h168)
  have h174 := C h11 (T (T (T h173 h172) h149) h145)
  have h175 := C (T (C h11 h119) h165) h11
  have h176 := C h11 h175
  have h177 := h v24 v1 v1
  have h178 := C h19 (T (T (T (T (T (T h79 h158) h157) h9) h147) h146) h155)
  have h179 := T (T (T (T (C h132 (T (T (T (T (T (T (T (T (T (T (T (T (T h38 h97) h96) h55) h95) h94) h64) h93) h91) h90) h89) h84) h82) h178)) (S h177)) h170) h169) h163
  have h180 := C h11 h179
  have h181 := C (T (T (T (T (T (C h11 h131) h102) h180) h176) h174) h113) (T (T (T h139 h154) h171) h164)
  have h182 := C h11 (T (T h181 h161) h119)
  have h183 := C h19 (T (T h173 h172) h12)
  have h184 := C h19 h175
  have h185 := C h19 (T (T (T (T (T (T h151 h17) h15) h10) h156) h166) h127)
  have h186 := T (T (T (T h175 h173) h172) h177) (C h98 (T (T (T (T (T (T (T (T (T (T (T (T (T h185 h126) h83) h125) h124) h73) h72) h65) h63) h62) h56) h54) h53) h39))
  have h187 := C h11 h186
  have h188 := C h11 h163
  have h189 := C h11 (T (T (T h144 h153) h170) h169)
  have h190 := C (T (T (T (T (T h112 h189) h188) h187) h134) (C h11 h100)) (T (T (T h184 h183) h150) h140)
  have h191 := C (T (T (T (T (T (T (C h19 h131) (C h19 h101)) (C h19 h179)) h184) h183) h150) h140) (T (T (T (T h112 h189) h188) h187) h134)
  have h192 := T (T (T (T h191 h103) h75) h160) h190
  have h193 := C h11 h192
  have h194 := C (T (T (T (T (T (T h139 h154) h171) h164) (C h19 h186)) (C h19 h133)) (C h19 h100)) (T (T (T (T h102 h180) h176) h174) h113)
  have h195 := h v8 v3 v1
  have h196 := h (M v1 v1) v1 v1
  have h197 := h v105 x v1
  have h198 := h v1 v1 v0
  let v199 := M (M v0 v1) v0
  have h200 := h (M v1 v199) x v1
  have h201 := C h11 (T (T (T (T (T (T (C h11 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (C (T (T (T (T (T h200 (C h14 (C h14 (T (C (S h198) h19) h131)))) (S h197)) h106) h103) h75) h19) h73) h72) h65) h63) h62) h56) h54) h53) h39) h112) h189) h188) h187) h134) (C h11 (T (T h100 h196) (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T h38 h97) h96) h55) h95) h94) h64) h93) h91) h90) h89) h84) h82) h178) (C h19 (T (T (T h151 h17) h15) h10))) (T (T (T (T (T (T (T (T (T (T (T (T (T (T (C h19 h192) (C h19 (T (T h181 h161) h127))) h126) h83) h125) h124) h73) h72) h65) h63) h62) h56) h54) h53) h39)))))) (S h195)) h156) h166) h74) h135) h194)
  have h202 := h v199 v3 v1
  have h203 := h v199 v2 v2
  have h204 := S h203
  have h205 := S h202
  have h206 := T (T (T (T h181 h161) h74) h135) h194
  have h207 := C h11 (T (T (T (T (T (T h191 h103) h75) h158) h157) h195) (C h11 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (C h11 (T (T (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (C h19 (T (T (T h9 h147) h146) h155)) h185) h126) h83) h125) h124) h73) h72) h65) h63) h62) h56) h54) h53) h39) (T (T (T (T (T (T (T (T (T (T (T (T (T (T h38 h97) h96) h55) h95) h94) h64) h93) h91) h90) h89) h84) h82) (C h19 (T (T h79 h160) h190))) (C h19 h206))) (S h196)) h131)) h102) h180) h176) h174) h113) h38) h97) h96) h55) h95) h94) h64) h93) h91) (C (T (T (T (T (T h74 h135) h130) h197) (C h14 (C h14 (T h100 (C h198 h19))))) (S h200)) h19))))
  have h208 := C h11 h206
  have h209 := C h11 (T (T h114 h160) h190)
  have h210 := C h66 (T (T (T (T (T (T (T h4 h148) h168) h167) h209) h208) h207) h205)
  have h211 := h v142 x y
  have h212 := h (M y v142) x y
  have h213 := h v3 y v2
  have h214 := C h66 (T (T (T h43 (C h14 (C h14 (C (T (T h48 (C h14 (C h14 (C h213 h47)))) (S h212)) h47)))) (S h211)) (C h210 h66))
  have h215 := h v40 v3 v3
  have h216 := S h215
  have h217 := h v2 v1 v1
  have h218 := C (S h217) h19
  have h219 := C h217 h19
  have h220 := h v40 v3 v2
  have h221 := S h220
  have h222 := C h66 h218
  have h223 := C h66 (T (T (T (T (T (T (T h202 h201) h193) h182) h159) h152) h123) h5)
  have h224 := C h66 (T (T (T (C h223 h66) h211) (C h14 (C h14 (C (T (T h212 (C h14 (C h14 (C (S h213) h47)))) h49) h47)))) h44)
  have h225 := C h66 (T h224 h219)
  have h226 := h y v1 x
  have h227 := C (S h226) h19
  let v228 := M x y
  let v229 := M v228 x
  let v230 := M v1 v229
  have h231 := h v230 v3 v1
  have h232 := C h11 (T (T h231 (C h11 (T (C h11 h227) h92))) (C h11 (T h70 (C (T (T (T (T (T (T (T (T (T (T h4 h148) h168) h167) h209) h208) h207) h205) h203) h225) h222) h66))))
  have h233 := h v230 y v1
  have h234 := C h226 h19
  have h235 := h y v3 v2
  have h236 := C h11 (T (T (C (S h235) h11) (C h47 (C h47 h234))) (S h233))
  have h237 := C h11 (T (T (T h236 h232) h221) h219)
  have h238 := h (M v3 v80) v3 v3
  have h239 := C h11 (C h11 (C (T (T h238 h237) (C h11 h218)) h11))
  have h240 := h v80 v3 v3
  have h241 := h v80 x v2
  have h242 := S h241
  have h243 := h v81 v2 v2
  have h244 := S h243
  have h245 := h v2 v3 z
  have h246 := C (S h245) h11
  have h247 := C h66 (T h246 (C h66 h86))
  have h248 := C h245 h11
  have h249 := C h14 (C h14 (C (T (T (C h66 h248) h247) h244) h66))
  have h250 := h v141 x v2
  have h251 := C h66 (T (T (T (T (T (T (T h246 h250) h249) h242) h240) h239) h216) h214)
  have h252 := C h66 (T (C h66 h78) h248)
  have h253 := R z
  let v254 := M (M v0 x) v0
  have h255 := h (M y v254) x y
  have h256 := S h255
  have h257 := h x y v0
  have h258 := h x y v2
  have h259 := C (S h258) h47
  have h260 := C h14 (C h14 (T h259 (C h257 h47)))
  have h261 := C h258 h47
  have h262 := h v2 v3 v1
  have h263 := T (C (S h262) h11) h248
  have h264 := C h66 (T (T (C h66 h263) h247) h244)
  let v265 := M v1 v2
  let v266 := M v265 v1
  let v267 := M v3 v266
  have h268 := h v267 v2 v3
  have h269 := h v267 x v3
  have h270 := S h269
  have h271 := T h246 (C h262 h11)
  have h272 := C h14 (C h14 h271)
  let v273 := M (M z v2) z
  let v274 := M v3 v273
  have h275 := h v274 x v3
  have h276 := h v274 v1 v3
  have h277 := S h276
  have h278 := S h250
  have h279 := C h14 (C h14 (C (T (T h243 h252) (C h66 h246)) h66))
  have h280 := h v81 x v2
  have h281 := h y v2 x
  have h282 := h (M v2 v229) x v2
  have h283 := C h14 (C h14 (C (T (T h282 (C h14 (T (C h14 (C (S h281) h66)) (C h14 h86)))) (S h280)) h66))
  have h284 := h v229 x v2
  have h285 := h v229 x v1
  have h286 := S h285
  have h287 := h v230 v1 v1
  have h288 := h v1 v2 v2
  have h289 := C (S h288) h66
  have h290 := C h288 h66
  have h291 := h v265 x v1
  have h292 := S h240
  have h293 := C h11 (T (T h233 (C h47 (C h47 h227))) (C h235 h11))
  have h294 := C h66 (T h218 h214)
  have h295 := C h66 h219
  have h296 := C h11 (T (T (C h11 (T (C (T (T (T (T (T (T (T (T (T (T h295 h294) h204) h202) h201) h193) h182) h159) h152) h123) h5) h66) h92)) (C h11 (T h70 (C h11 h234)))) (S h231))
  have h297 := C h11 (T (T (T h218 h220) h296) h293)
  have h298 := C h11 (C h11 (C (T (T (C h11 h219) h297) (S h238)) h11))
  have h299 := C h66 (T (T (T (T (T (T (T h224 h215) h298) h292) h241) h279) h278) h248)
  have h300 := T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h4 h148) h168) h167) h209) h208) h207) h205) h203) h299) h247) h244) h83) h125) h124) h73) h72) h65) h63) h62) h56) h54) h53) h39
  have h301 := R (M (M v2 v40) v2)
  have h302 := T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h38 h97) h96) h55) h95) h94) h64) h93) h91) h90) h89) h84) h243) h252) h251) h204) h202) h201) h193) h182) h159) h152) h123) h5
  have h303 := C h19 (T (T (C h302 h301) (C h300 (T (T (T (T (T (T (T (T (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h295 h294) h299) h247) h244) h83) h125) h124) h73) h72) h65) h63) h62) h56) h54) h53) h39) h66) h291) (C h14 (C h14 (C (T (T (C h19 h290) (C h19 (T h289 (C h19 h234)))) (S h287)) h19)))) h286) h284) h283) h279) h278) h210))) (C h19 (T h223 h248)))
  have h304 := h v40 v1 v2
  have h305 := h v230 x v1
  have h306 := h y v1 y
  let v307 := M (M y y) y
  have h308 := h (M v1 v307) x v1
  have h309 := C h14 (C h14 (C (T (T h308 (C h14 (T (C h14 (C (S h306) h19)) (C h14 h234)))) (S h305)) h19))
  have h310 := h v307 x v1
  have h311 := h v307 x z
  have h312 := S h311
  have h313 := h (M z v307) x z
  have h314 := h y z y
  have h315 := h y z z
  let v316 := M (M z y) z
  have h317 := h (M z v316) x z
  have h318 := C h14 (C h14 (C (T (T h317 (C h14 (C h14 (T (C (S h315) h253) (C h314 h253))))) (S h313)) h253))
  have h319 := h v316 x z
  have h320 := h v274 v3 v3
  have h321 := S h320
  have h322 := C h11 (T h297 (C h11 (T (T (T (T (T (T (T (T (T h236 h232) h221) h215) h298) h292) h241) h279) h278) h248)))
  let v323 := M v1 v266
  have h324 := h v323 v3 v1
  have h325 := h v323 x v1
  have h326 := S h325
  have h327 := h v2 v1 z
  have h328 := C h14 (C h14 (T (C (S h327) h19) h219))
  let v329 := M v1 v273
  have h330 := h v329 x v1
  have h331 := C (C h253 (T (T (T (T (T (T (T (T (T (T (T h330 h328) h326) h324) h322) h321) h275) h272) h270) h268) h264) h77)) h253
  have h332 := C h14 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h331 h319) h318) h312) h310) h309) h286) h284) h283) h242) h240) h239) h216) h304) h303) h277) h275) h272) h270) h268) h264) h77)
  have h333 := C h14 (T h332 h261)
  have h334 := h v329 x z
  have h335 := S h330
  have h336 := C h14 (C h14 (T h218 (C h327 h19)))
  have h337 := S h324
  have h338 := C h11 (T (C h11 (T (T (T (T (T (T (T (T (T h246 h250) h249) h242) h240) h239) h216) h220) h296) h293)) h237)
  have h339 := h v228 v3 x
  have h340 := S h339
  have h341 := S h275
  have h342 := C h14 (C h14 h263)
  have h343 := S h268
  have h344 := C h66 (T (T h243 h252) (C h66 h271))
  have h345 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T h76 h344) h343) h269) h342) h341) h320) h338) h337) h325) h336) h335) h334) h333) (C h14 h259)) h14
  have h346 := h y x z
  have h347 := C h302 (C h302 (T (C (S h346) h14) h345))
  let v348 := M x v316
  have h349 := h v348 v1 x
  have h350 := C (T (T h349 h347) h340) h14
  have h351 := C h14 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h350 h284) h283) h242) h240) h239) h216) h304) h303) h277) h320) h338) h337) h325) h336) h335) h334) h333)
  have h352 := S h349
  have h353 := S h334
  have h354 := C (C h253 (T (T (T (T (T (T (T (T (T (T (T h76 h344) h343) h269) h342) h341) h320) h338) h337) h325) h336) h335)) h253
  have h355 := S h319
  have h356 := C h14 (C h14 (C (T (T h313 (C h14 (C h14 (T (C (S h314) h253) (C h315 h253))))) (S h317)) h253))
  have h357 := S h310
  have h358 := C h14 (C h14 (C (T (T h305 (C h14 (T (C h14 h227) (C h14 (C h306 h19))))) (S h308)) h19))
  have h359 := S h284
  have h360 := C h14 (C h14 (C (T (T h280 (C h14 (T (C h14 h78) (C h14 (C h281 h66))))) (S h282)) h66))
  have h361 := S h304
  have h362 := C h19 (T (T (C h19 (T h246 h210)) (C h302 (T (T (T (T (T (T (T (T h223 h250) h249) h360) h359) h285) (C h14 (C h14 (C (T (T h287 (C h19 (T (C h19 h227) h290))) (C h19 h289)) h19)))) (S h291)) (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h38 h97) h96) h55) h95) h94) h64) h93) h91) h90) h89) h84) h243) h252) h251) h225) h222) h66)))) (C h300 h301))
  have h363 := C h14 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h76 h344) h343) h269) h342) h341) h276) h362) h361) h215) h298) h292) h241) h360) h359) h285) h358) h357) h311) h356) h355) h354)
  have h364 := C h14 (T h259 h363)
  have h365 := C h14 h261
  have h366 := C h300 (C h300 (T (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T h365 h364) h353) h330) h328) h326) h324) h322) h321) h275) h272) h270) h268) h264) h77) h14) (C h346 h14)))
  have h367 := C (T (T h339 h366) h352) h14
  have h368 := C h14 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h364 h353) h330) h328) h326) h324) h322) h321) h276) h362) h361) h215) h298) h292) h241) h360) h359) h367)
  have h369 := C h14 (C h14 (T (C (S h257) h47) h261))
  have h370 := h v316 x x
  have h371 := h x x v0
  T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h371 (C h14 (T (T (T (h (M x v254) x x) (C h14 (T (C h14 (C (S h371) h14)) (C h14 (C (h x x y) h14))))) (S (h (M x (M (M y x) y)) x x))) (C h14 (C (T (T (T (T (T (T (T (T (T (T (T h345 (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h365 h364) h353) h330) h328) h326) h324) h322) h321) h276) h362) h361) h215) h298) h292) h241) h360) h359) h285) h358) h357) h311) h356) h355) h370) (C h14 (T (T h351 h260) h256))) h14)) (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (C h14 (T (T h255 h369) h368)) (S h370)) h319) h318) h312) h310) h309) h286) h284) h283) h242) h240) h239) h216) h304) h303) h277) h275) h272) h270) h268) h264) h77) (T h257 (C h47 (T (T h255 h369) (C (T (T h257 (C h47 (T (T (T (T (T h255 h369) h368) (C h14 (T (T (T (T (T (T (T h350 h285) h358) h357) h311) h356) h355) h354))) h332) h261))) (C h47 (T (T (T h259 h339) h366) h352))) (T (T (T (T (T (T (T (T (T (T (T (T (T h364 h353) h330) h328) h326) h324) h322) h321) h275) h272) h270) h268) h264) h77))))))) (S (h v348 y y))) h349) h347) h340) h363) (C h14 (T (T (T (T (T (T (T h331 h319) h318) h312) h310) h309) h286) h367))) h351) h260) h256) h47))))) (S (h v254 x y))) (h v254 x z)) (C h14 (C h14 (C (T (h (M z v254) z z) (C h253 (C h253 (C (S (h x z v0)) h253)))) h253)))) (S (h v1 x z))) h38) h97) h96) h55) h95) h94) h64) h93) h91) h90) h89) h84) h243) h252) h251) h204) h202) h201) h193) h182) h159) h152) h123) h5

