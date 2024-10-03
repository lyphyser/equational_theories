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
theorem Equation1571_implies_Equation4491 (G: Type _) [Magma G] (h: Equation1571 G) : Equation4491 G := fun x y z =>
  have h0 := h z z x
  have h1 := S h0
  let v2 := M y y
  let v3 := M x v2
  let v4 := M z x
  let v5 := M v4 z
  have h6 := h v4 v5 v3
  have h7 := S h6
  let v8 := M v4 v3
  have h9 := h v8 v2 v4
  have h10 := S h9
  have h11 := h v4 v4 (M z (M v4 x))
  have h12 := S h11
  have h13 := h v4 z x
  have h14 := R v4
  have h15 := C h13 (C h14 h13)
  have h16 := h x v3 v3
  have h17 := h x x v2
  let v18 := M v3 v3
  have h19 := R v18
  have h20 := R z
  have h21 := C h14 (C h20 (T (C h19 h17) (S h16)))
  have h22 := h v18 z x
  have h23 := h v3 v3 (M x v3)
  have h24 := S h23
  have h25 := R v3
  have h26 := C h17 (C h25 h17)
  let v27 := M x (M v3 x)
  have h28 := h v27 v5 v5
  have h29 := S h28
  have h30 := R v5
  have h31 := S h17
  have h32 := C h31 (C h25 h31)
  have h33 := T h23 h32
  have h34 := h v5 x v2
  have h35 := S h34
  let v36 := M v5 v2
  have h37 := h v3 v3 (M x v36)
  have h38 := h z v4 v4
  let v39 := M v4 v4
  have h40 := R v39
  have h41 := C h30 (C h14 (T (C h40 h0) (S h38)))
  have h42 := h v39 v4 z
  have h43 := T h42 h41
  have h44 := C h43 (T (T h37 (C h35 (C h25 h35))) (C h30 (C h33 h30)))
  have h45 := T (T (T h44 h29) h26) h24
  have h46 := C h25 h45
  have h47 := T h26 h24
  have h48 := S h42
  have h49 := C h30 (C h14 (T h38 (C h40 h1)))
  have h50 := T h49 h48
  have h51 := C h50 (T (T (C h30 (C h47 h30)) (C h34 (C h25 h34))) (S h37))
  have h52 := T (T (T h23 h32) h28) h51
  have h53 := C h47 h52
  have h54 := T (T (T h53 h46) h22) h21
  have h55 := C h14 h54
  have h56 := R v8
  have h57 := C h56 (T (T h55 h15) h12)
  have h58 := h v27 v4 v3
  let v59 := M v2 v2
  have h60 := h v3 v3 (M x v59)
  have h61 := S h60
  have h62 := h v2 x v2
  have h63 := C h62 (C h25 h62)
  have h64 := R v2
  have h65 := C h64 (C h47 h64)
  have h66 := h y v2 v2
  have h67 := S h66
  have h68 := h y y y
  have h69 := R v59
  have h70 := C h69 h68
  have h71 := C (T h70 h67) (T (C h69 (T (T h70 h67) h68)) h67)
  have h72 := h v59 v59 y
  have h73 := T h72 h71
  have h74 := h v27 v2 v2
  let v75 := M v2 v4
  have h76 := R v75
  have h77 := C h76 (T (T (T h23 h32) h74) (C h73 (T (T (T (T (T (T h65 h63) h61) h23) h32) h58) h57)))
  have h78 := C h30 (T h77 h10)
  let v79 := M v5 v3
  have h80 := R v79
  have h81 := C h80 h78
  have h82 := h v75 v5 v3
  have h83 := h v75 v5 v5
  have h84 := S h83
  have h85 := S h82
  have h86 := S h74
  have h87 := C h64 (C h33 h64)
  have h88 := S h62
  have h89 := C h88 (C h25 h88)
  have h90 := S h58
  have h91 := C h33 h45
  have h92 := C h25 h52
  have h93 := S h22
  have h94 := C h14 (C h20 (T h16 (C h19 h31)))
  have h95 := T (T (T h94 h93) h92) h91
  have h96 := C h14 h95
  have h97 := S h13
  have h98 := C h97 (C h14 h97)
  have h99 := C h56 (T (T h11 h98) h96)
  have h100 := S h72
  have h101 := S h68
  have h102 := C h69 h101
  have h103 := C (T h66 h102) (T h66 (C h69 (T (T h101 h66) h102)))
  have h104 := T h103 h100
  have h105 := C h104 (T (T (T (T (T (T h99 h90) h26) h24) h60) h89) h87)
  have h106 := C h76 (T (T (T h105 h86) h26) h24)
  have h107 := C h30 (T h9 h106)
  have h108 := C h80 h107
  have h109 := T (T h6 h108) h85
  have h110 := C h109 h30
  have h111 := C h30 h110
  have h112 := h v4 v4 z
  have h113 := C h43 (T h112 h111)
  have h114 := T (T (T (T h113 h84) h82) h81) h7
  have h115 := C h20 h114
  have h116 := S h112
  have h117 := T (T h82 h81) h7
  have h118 := C h117 h30
  have h119 := C h30 h118
  have h120 := C h50 (T h119 h116)
  have h121 := h v75 v5 v4
  have h122 := S h121
  have h123 := C h64 h114
  have h124 := C h76 (T (T (T h123 h82) h81) h7)
  have h125 := h v39 v2 v4
  have h126 := C h30 (T (T (T (T (T h53 h46) h22) h21) h125) h124)
  have h127 := C h30 h95
  have h128 := h v5 v4 z
  have h129 := S h128
  have h130 := C h129 (T (T (C h30 h129) h49) h48)
  let v131 := M v5 z
  have h132 := h v5 v5 (M v4 v131)
  let v133 := M v5 v4
  have h134 := R v133
  have h135 := C h134 (T (T (T h132 h130) h127) h126)
  have h136 := T (T (T h135 h122) h83) h120
  have h137 := C h20 h136
  have h138 := h v4 v4 (M z v4)
  have h139 := T (C h0 (C h14 h0)) (S h138)
  have h140 := C h139 (T h137 h115)
  have h141 := h v133 z v5
  have h142 := h v133 v5 z
  have h143 := S h142
  have h144 := C h30 h114
  have h145 := C h134 (T (T (T h144 h141) h140) h1)
  have h146 := h v39 v5 v4
  have h147 := S h125
  have h148 := T (T (T (T h6 h108) h85) h83) h120
  have h149 := C h64 h148
  have h150 := C h76 (T (T (T h6 h108) h85) h149)
  have h151 := C h30 (T (T (T h150 h147) h146) h145)
  have h152 := R v131
  have h153 := C h152 (T (T (T (T h132 h130) h127) h126) h151)
  have h154 := T (T (T (T h153 h143) h141) h140) h1
  have h155 := C h14 h154
  have h156 := S h132
  have h157 := C h128 (T (T h42 h41) (C h30 h128))
  have h158 := C h30 h54
  have h159 := C h30 (T (T (T (T (T h150 h147) h94) h93) h92) h91)
  have h160 := S h146
  have h161 := C h30 h148
  have h162 := S h141
  have h163 := C h134 (T (T (T h159 h158) h157) h156)
  have h164 := T (T (T h113 h84) h121) h163
  have h165 := T h138 (C h1 (C h14 h1))
  have h166 := C h165 (T (C h20 h148) (C h20 h164))
  have h167 := C h134 (T (T (T h0 h166) h162) h161)
  have h168 := C h30 (T (T (T h167 h160) h125) h124)
  have h169 := C h152 (T (T (T (T h168 h159) h158) h157) h156)
  have h170 := h v133 v4 v4
  have h171 := S h170
  have h172 := T (T h0 h166) h162
  have h173 := C h30 h136
  have h174 := C h172 h154
  have h175 := C h139 (T (T (T (T (T (T h174 h167) h160) h94) h93) h92) h91)
  have h176 := h v131 z v5
  have h177 := h v131 v4 v5
  have h178 := S h177
  have h179 := T (T (T (T h0 h166) h162) h142) h169
  have h180 := C h14 h179
  let v181 := M v4 v5
  have h182 := R v181
  have h183 := C h182 h180
  have h184 := C h30 (T (T (T (T (T (T (T (T (T (T (T h183 h178) h176) h175) h55) h15) h12) h6) h108) h85) h121) h163)
  have h185 := C h50 (T (T (T (T h184 h173) h144) h141) (C h139 (C h172 (T (T (T (T h135 h122) h82) h81) h7))))
  have h186 := h v181 v5 v5
  have h187 := C h14 (T (T (T (T (T h118 h186) h185) h171) h142) h169)
  have h188 := C h14 h110
  let v189 := M v4 v181
  have h190 := h v189 v4 v5
  have h191 := S h190
  have h192 := C h14 h118
  have h193 := S h186
  have h194 := C h182 h155
  have h195 := S h176
  have h196 := T (T h141 h140) h1
  have h197 := C h196 h179
  have h198 := C h165 (T (T (T (T (T (T h53 h46) h22) h21) h146) h145) h197)
  have h199 := C h30 (T (T (T (T (T (T (T (T (T (T (T h135 h122) h82) h81) h7) h11) h98) h96) h198) h195) h177) h194)
  have h200 := C h30 h164
  have h201 := C h196 (T (T (T (T h6 h108) h85) h121) h163)
  have h202 := C h43 (T (T (T (T (C h165 h201) h162) h161) h200) h199)
  have h203 := C h14 (T (T (T (T (T h153 h143) h170) h202) h193) h110)
  have h204 := T (T h180 h203) h192
  have h205 := C h204 h30
  have h206 := C h139 (T (T (T (T (T h174 h167) h160) h42) h41) h205)
  have h207 := h v75 v4 v5
  have h208 := S h207
  have h209 := h v189 v5 v5
  have h210 := S h209
  have h211 := C h43 (T (T (T (T (T h132 h130) h127) h126) h151) (C h30 (T (T (T (T h167 h160) h42) h41) h205)))
  have h212 := T (T (T (T (T h0 h166) h162) h170) h202) h193
  have h213 := C h212 (T (T h211 h210) h188)
  have h214 := T (T h188 h187) h155
  have h215 := C h214 h30
  have h216 := C h50 (T (T (T (T (T (C h30 (T (T (T (T h215 h49) h48) h146) h145)) h168) h159) h158) h157) h156)
  have h217 := T (T (T (T h180 h203) h192) h209) h216
  have h218 := h z v5 v3
  have h219 := S h218
  let v220 := M z v3
  have h221 := h v220 v5 z
  have h222 := S h221
  have h223 := h v133 v5 v4
  have h224 := C h165 (T (T (T (T (T h215 h49) h48) h146) h145) h197)
  have h225 := C (T (T h186 h185) h171) (T (T (T (T h224 h175) h55) h15) h12)
  have h226 := C h214 h217
  have h227 := T (T (T (T (C h172 (T (T (T (T (T (T (T (T h53 h46) h22) h21) h42) h41) h205) h226) (C h30 (T (T (T h211 h210) h190) h225)))) (S h223)) h141) h140) h1
  have h228 := R v220
  have h229 := h v27 z v3
  have h230 := h v27 v5 v3
  have h231 := S h230
  have h232 := T (T h132 h130) h127
  have h233 := h v79 z v5
  have h234 := T (T h158 h157) h156
  have h235 := C h80 h234
  have h236 := T (T (T h44 h29) h230) h235
  have h237 := C (T (C h165 (T (C h20 h52) (C h20 h236))) (S h233)) h232
  have h238 := T (T (T h237 h231) h58) h57
  have h239 := C h80 h232
  have h240 := T (T (T h239 h231) h28) h51
  have h241 := T h233 (C h139 (T (C h20 h240) (C h20 h45)))
  have h242 := C h241 h234
  have h243 := T h239 h242
  have h244 := T (T (T (T h11 h98) h96) h198) h195
  have h245 := C h244 (T (T (T (T (C h30 h52) (C h30 h236)) (C h30 h243)) (C h30 h238)) (C h30 (T (T (T h99 h90) h229) (C h228 h227))))
  have h246 := h (M v4 v79) v4 z
  have h247 := S h246
  have h248 := T h237 h235
  have h249 := T (T (T h99 h90) h230) h242
  have h250 := S h229
  have h251 := T (T (T (T h211 h210) h188) h187) h155
  have h252 := C h204 h251
  have h253 := T (T (T (T h0 h166) h162) h223) (C h196 (T (T (T (T (T (T (T (T (C h30 (T (T (T (C (T (T h170 h202) h193) (T (T (T (T h11 h98) h96) h198) h206)) h191) h209) h216)) h252) h215) h49) h48) h94) h93) h92) h91))
  have h254 := T (T (T (T h176 h175) h55) h15) h12
  have h255 := C h254 (T (T (T (T (C h30 (T (T (T (C h228 h253) h250) h58) h57)) (C h30 h249)) (C h30 h248)) (C h30 h240)) (C h30 h45))
  have h256 := C (T h221 h255) h227
  have h257 := C h30 (T (T (T (T (T (T h77 h10) (C h14 h52)) (C h14 h236)) (C h14 h243)) (C h14 h238)) (C h14 (T (T (T h99 h90) h229) h256)))
  have h258 := h (M v5 v8) v2 z
  have h259 := C (T h245 h222) h253
  have h260 := C h30 (T (T (T (T (T (T (C h14 (T (T (T h259 h250) h58) h57)) (C h14 h249)) (C h14 h248)) (C h14 h240)) (C h14 h45)) h9) h106)
  let v261 := M v2 z
  have h262 := R v261
  have h263 := C h80 (C h30 (T (T (T (T (T (T (C h262 (T (T (T h23 h32) h74) (C h73 (T (T (T (T (T (T (T h65 h63) h61) h23) h32) h229) h256) (C (T (T h246 h260) h78) h20))))) (S h258)) h107) h257) h247) h245) h222))
  have h264 := h v261 v5 v3
  have h265 := T (T h264 h263) h219
  have h266 := C h265 h217
  have h267 := C h212 (T (T (T (T (T (T (T (T (T (T h266 h213) h208) h82) h81) h7) h11) h98) h96) h198) h206)
  have h268 := S h264
  have h269 := C h80 (C h30 (T (T (T (T (T (T h221 h255) h246) h260) h78) h258) (C h262 (T (T (T (C h104 (T (T (T (T (T (T (T (C (T (T h107 h257) h247) h20) h259) h250) h26) h24) h60) h89) h87)) h86) h26) h24))))
  have h270 := T (T h218 h269) h268
  have h271 := C h270 h251
  have h272 := T (T (T (T (T h186 h185) h171) h141) h140) h1
  have h273 := C h272 (T (T h192 h209) h216)
  have h274 := h v261 v2 v5
  have h275 := S h274
  have h276 := C h64 (T (T (T (T h113 h84) h207) h273) h271)
  let v277 := M v2 v5
  have h278 := R v277
  have h279 := C h278 (T (T (T (T h6 h108) h85) h149) h276)
  have h280 := C h30 (T (T (T (T (T (T (T (T (T (T (T h279 h275) h264) h263) h219) h0) h166) h162) h170) h202) h193) h110)
  have h281 := C h196 (T (T (T (T (T (T (T (T h280 h119) h116) h6) h108) h85) h207) h273) h271)
  have h282 := h v277 v5 v4
  let v283 := M v4 v220
  have h284 := h z x x
  have h285 := S h284
  let v286 := M x v4
  have h287 := R v286
  let v288 := M x x
  have h289 := h v288 v2 v2
  have h290 := S h289
  have h291 := h v2 v2 (M y (M x y))
  have h292 := h x y y
  have h293 := R v288
  have h294 := C h293 (T (C h292 (C h64 h292)) (S h291))
  have h295 := h v2 x x
  have h296 := T h295 h294
  have h297 := C h64 h296
  have h298 := S h295
  have h299 := S h292
  have h300 := C h299 (C h64 h299)
  have h301 := C h293 (T h291 h300)
  have h302 := C h104 (T (T (T (T h301 h298) h103) h100) h297)
  have h303 := T (T (T (T h103 h100) h297) h302) h290
  have h304 := C h303 h287
  have h305 := h (M v2 v286) v4 v5
  have h306 := S h305
  have h307 := h v277 v3 v5
  have h308 := S h307
  have h309 := C h278 (T (T (T (T (T (T (T (C h64 h251) h282) h281) h267) h191) h188) h187) h155)
  have h310 := h v39 v2 v5
  have h311 := h v3 x v2
  have h312 := S h311
  have h313 := h v3 v3 (M x (M v3 v2))
  have h314 := R (M v3 v5)
  have h315 := C h314 (T (T (T h313 (C h312 (T (T (C h25 h312) h22) h21))) (C h25 h95)) (C h25 (T (T (T (T (T h53 h46) h22) h21) h310) h309)))
  have h316 := T (T (T (T (T (T (T (T h315 h308) h282) h281) h267) h191) h188) h187) h155
  have h317 := T h301 h298
  have h318 := C h64 h317
  have h319 := C h73 (T (T (T (T h318 h72) h71) h295) h294)
  have h320 := T (T (T (T h289 h319) h318) h72) h71
  have h321 := C h320 h287
  have h322 := C (T h284 h321) h316
  have h323 := S h310
  have h324 := S h282
  have h325 := C h64 (T (T (T (T h266 h213) h208) h83) h120)
  have h326 := C h278 (T (T (T (T h325 h123) h82) h81) h7)
  have h327 := C h30 (T (T (T (T (T (T (T (T (T (T (T h118 h186) h185) h171) h141) h140) h1) h218) h269) h268) h274) h326)
  have h328 := C h172 (T (T (T (T (T (T (T (T h266 h213) h208) h82) h81) h7) h112) h111) h327)
  have h329 := C h272 (T (T (T (T (T (T (T (T (T (T h224 h175) h55) h15) h12) h6) h108) h85) h207) h273) h271)
  have h330 := C h278 (T (T (T (T (T (T (T h180 h203) h192) h190) h329) h328) h324) (C h64 h217))
  have h331 := C h314 (T (T (T (C h25 (T (T (T (T (T h330 h323) h94) h93) h92) h91)) (C h25 h54)) (C h311 (T (T h94 h93) (C h25 h311)))) (S h313))
  have h332 := T (T (T (T (T (T (T (T h180 h203) h192) h190) h329) h328) h324) h307) h331
  have h333 := C h265 h332
  have h334 := T (T (T (T (T (T h282 h281) h267) h191) h188) h187) h155
  have h335 := C h334 (T (T (T (T h218 h269) h268) h274) h326)
  have h336 := h v261 v5 v5
  have h337 := S h336
  have h338 := h v39 v5 v5
  have h339 := S h338
  have h340 := T (T (T (T (T (T h180 h203) h192) h190) h329) h328) h324
  have h341 := h v277 x x
  have h342 := R x
  have h343 := h x v4 z
  have h344 := S h343
  have h345 := C h344 (C h30 h344)
  have h346 := h v5 v5 (M v4 (M x z))
  have h347 := R (M v5 v5)
  have h348 := C h347 (T (T (T (T (T (T (T (C h30 (T (T (T (C h293 (T (T h346 h345) (C h342 (C h340 h342)))) (S h341)) h307) h331)) (C h340 h316)) h330) h323) h42) h41) h205) h226)
  have h349 := h v288 v5 v5
  have h350 := C (T (T (T (T h349 h348) h339) h42) h41) (T (T (T (T (T (T h0 h166) h162) h161) h200) h199) (C h30 (T (T (T (T (T (T (T (T (T (T (T (T h183 h178) h176) h175) h55) h15) h12) h6) h108) h85) h207) h273) h271)))
  have h351 := C h340 (T (T (T (T h350 h337) h264) h263) h219)
  have h352 := h v288 v5 z
  have h353 := C h212 (T (T (T (T (T (T (T (T h301 h298) h103) h100) h297) h302) h290) h352) (C h254 (T (T (T (T (T (T (T (T (T (T (T (T h351 h335) h280) h119) h116) h6) h108) h85) h207) h273) h271) h333) h322)))
  have h354 := C h20 h296
  let v355 := M z v2
  have h356 := C h270 h316
  have h357 := C (T h304 h285) h332
  have h358 := C (T (T h354 h353) h306) h30
  have h359 := C h20 h317
  have h360 := S h349
  have h361 := S h346
  have h362 := C h343 (C h30 h343)
  have h363 := C h347 (T (T (T (T (T (T (T h252 h215) h49) h48) h310) h309) (C h334 h332)) (C h30 (T (T (T h315 h308) h341) (C h293 (T (T (C h342 (C h334 h342)) h362) h361)))))
  have h364 := C (T (T (T (T h49 h48) h338) h363) h360) (T (T (T (T (T (T (C h30 (T (T (T (T (T (T (T (T (T (T (T (T h266 h213) h208) h82) h81) h7) h11) h98) h96) h198) h195) h177) h194)) h184) h173) h144) h141) h140) h1)
  have h365 := C h334 (T (T (T (T h218 h269) h268) h336) h364)
  have h366 := C h340 (T (T (T (T h279 h275) h264) h263) h219)
  have h367 := C h272 (T (T (T (T (T (T (T (T (C h244 (T (T (T (T (T (T (T (T (T (T (T (T h357 h356) h266) h213) h208) h82) h81) h7) h112) h111) h327) h366) h365)) (S h352)) h289) h319) h318) h72) h71) h295) h294)
  have h368 := C (T (T (T (T h284 h321) h305) h367) h359) (T (T (T (T (T (T (T (T h358 h357) h356) h266) h213) h208) h82) h81) h7)
  have h369 := C (T (T h305 h367) h359) h30
  have h370 := C h43 (T (T (T (T (T (T h113 h84) h82) h81) h7) h112) h111)
  have h371 := T (T h349 h348) h339
  have h372 := C h371 h148
  have h373 := C h20 (T (T (T (T (T (T (T (T h372 h370) h84) h207) h273) h271) h333) h322) h369)
  have h374 := T (T h338 h363) h360
  have h375 := C h374 h114
  have h376 := C h50 (T (T (T (T (T (T h119 h116) h6) h108) h85) h83) h120)
  have h377 := C h265 (T (T (T (T (T (C h64 (T (T (T (T (T (T (T (T (T h335 h280) h119) h116) h6) h108) h85) h207) h273) h271)) h325) h123) h83) h376) h375)
  have h378 := h v277 v2 z
  have h379 := T (T (T (T h354 h353) h306) h304) h285
  have h380 := h v355 v2 v4
  have h381 := S h380
  have h382 := h v5 x x
  have h383 := h v277 v4 v2
  have h384 := S h383
  have h385 := C h340 h317
  have h386 := h v39 z v2
  have h387 := S h386
  have h388 := C h371 h64
  have h389 := R v355
  have h390 := C h389 (T (T (T (T h284 h321) h305) h367) (C h20 h388))
  have h391 := C h30 (T (T (T (T (T (T (T (T (T (T (T h390 h387) h338) h363) h360) h289) h319) h318) h72) h71) h295) h294)
  have h392 := h v355 v5 z
  let v393 := M v4 v2
  have h394 := R v393
  have h395 := C h394 (T (T (T (T (T (T h284 h321) h305) h367) h359) h392) (C h254 (T h391 h385)))
  have h396 := C h109 (T (T (T (T (T (T (T (T (T (T h395 h384) h282) h281) h267) h191) h188) h187) h155) h382) (C h320 (T (T (T (T (T (T (T (T (T (T (T (T h362 h361) h180) h203) h192) h190) h329) h328) h324) h378) h377) h373) h368)))
  have h397 := C h30 (T (T (T (T (T (T (T (T (T (T (T h396 h381) h354) h353) h306) h304) h285) h218) h269) h268) h336) h364)
  have h398 := h v393 v4 z
  have h399 := h v393 v5 v4
  have h400 := S h399
  have h401 := C h374 h64
  have h402 := C h394 (T (T (T (T (T (T (T (T (C h14 h401) (C h14 h317)) h398) h397) h351) h335) h280) h119) h116)
  have h403 := h v39 v4 v2
  have h404 := C h389 (T (T (T (T (C h20 h401) h353) h306) h304) h285)
  have h405 := C h30 (T (T (T (T (T (T (T (T (T (T (T h301 h298) h103) h100) h297) h302) h290) h349) h348) h339) h386) h404)
  have h406 := C h334 h296
  have h407 := C h172 (T (T h406 h405) (C h30 (T (T (T h390 h387) h403) h402)))
  have h408 := C h20 (C h340 h64)
  let v409 := M z v36
  have h410 := C h20 (C h334 h64)
  have h411 := S h403
  have h412 := S h398
  have h413 := C h394 (T (T (T (T (T (T (C h244 (T h406 h405)) (S h392)) h354) h353) h306) h304) h285)
  have h414 := C h117 (T (T (T (T (T (T (T (T (T (T (C h303 (T (T (T (T (T (T (T (T (T (T (T (T (C h379 (T (T (T (T (T (T (T (T h6 h108) h85) h207) h273) h271) h333) h322) h369)) (C h20 (T (T (T (T (T (T (T (T h358 h357) h356) h266) h213) h208) h83) h376) h375))) (C h270 (T (T (T (T (T h372 h370) h84) h149) h276) (C h64 (T (T (T (T (T (T (T (T (T h266 h213) h208) h82) h81) h7) h112) h111) h327) h366))))) (S h378)) h282) h281) h267) h191) h188) h187) h155) h346) h345)) (S h382)) h180) h203) h192) h190) h329) h328) h324) h383) h413)
  have h415 := C h30 (T (T (T (T (T (T (T (T (T (T (T h350 h337) h264) h263) h219) h284) h321) h305) h367) h359) h380) h414)
  have h416 := C h394 (T (T (T (T (T (T (T (T h112 h111) h327) h366) h365) h415) h412) (C h14 h296)) (C h14 h388))
  have h417 := C h196 (T (T (C h30 (T (T (T h416 h411) h386) h404)) h391) h385)
  have h418 := T (T h399 h417) h410
  have h419 := T (T h408 h407) h400
  T (T (T (T (T (T (T (T (T (T (T h23 h32) h58) (C h56 (T (T (T (T (T (T (T (T (T (T (T (T (T (T h55 h15) h12) h112) h111) h327) h366) h365) h415) h412) h399) h417) h410) (h v409 v2 v4)) (C h117 (T (T (T (T (T (T (T (T (T (C h303 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (C h419 h14) h416) h411) h338) h363) h360) h289) h319) h318) h72) h71) h291) h300) (C h342 (C h303 h342))) (C h342 (C h371 h342)))) (S (h v39 x x))) h386) h404) (C h379 (T (T (T (T (T (T (T h284 h321) h305) h367) h359) h380) h414) (C (T (T (T (T (T (T h112 h111) h327) h366) h365) h415) h412) (T (T (T (T (T (T (T (T h395 h384) h282) h281) h267) h191) h188) h187) h155))))) (C h20 (C h418 h30))) (C h270 (T (T (T (T (T (T (T (T (C h419 h30) (C (T (T (T (T (T (T h398 h397) h351) h335) h280) h119) h116) (T (T (T (T (T (T (T (T h180 h203) h192) h190) h329) h328) h324) h383) h413))) h396) h381) h354) h353) h306) h304) (C h320 (T (h v286 v5 v3) (C h241 (T (T (T (T (T (T (C (T (T (T (T (T (T (T h180 h203) h192) h190) h225) h201) h137) h115) (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (C h287 (C h342 (T (T (T (T (T (T (T (T (T (T h103 h100) h297) h302) h290) h349) h348) h339) h403) h402) (C h418 h14)))) (S (h v409 x v4))) h408) h407) h400) h398) h397) h351) h335) h280) h119) h116) h6) h108) h85) h207) h273) h271) h333) h322) h369) (C h379 (T (T (T (T (T (T (T (T (T (T h180 h203) h192) h190) h329) h328) h324) h378) h377) h373) h368)))) (S (h v355 z v4))) h354) h353) h306) h304) h285))))))) (S (h v283 v2 z))) (h v283 v2 v5)) (C h278 (T (T (T (T (T (C h64 h248) (C h64 (T (T (T h239 h231) h58) h57))) h105) h86) h26) h24))))))) (S (h v277 v4 v3))) h282) h281) h267) h191) h188) h187) h155

