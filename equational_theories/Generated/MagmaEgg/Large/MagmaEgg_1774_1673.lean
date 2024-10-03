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
theorem Equation1774_implies_Equation1673 (G: Type _) [Magma G] (h: Equation1774 G) : Equation1673 G := fun x y z =>
  let v0 := M z z
  let v1 := M v0 y
  let v2 := M x y
  let v3 := M v2 v1
  have h4 := h v3 x v0
  have h5 := S h4
  have h6 := h v0 v0 v0
  have h7 := S h6
  let v8 := M v0 v0
  have h9 := h (M v8 v0) v1 v3
  have h10 := S h9
  have h11 := R v3
  have h12 := R v0
  have h13 := h v0 x y
  have h14 := S h13
  let v15 := M x v0
  let v16 := M v15 y
  have h17 := R v16
  have h18 := h v2 x y
  have h19 := S h18
  let v20 := M (M x v2) y
  have h21 := h v20 v2 v1
  have h22 := S h21
  have h23 := h v1 x v3
  have h24 := h y x v1
  let v25 := M x v3
  have h26 := R v25
  have h27 := T (C h26 h24) (S h23)
  have h28 := h v3 x y
  have h29 := C h11 (T h28 (C h18 h27))
  have h30 := R v2
  have h31 := T (C h30 (T h29 h22)) h19
  have h32 := C h14 (T (C h31 h17) h14)
  let v33 := M v3 v3
  have h34 := h v33 v2 v16
  let v35 := M (M x v1) y
  have h36 := h v33 v2 v35
  have h37 := S h36
  have h38 := R v35
  have h39 := S h28
  have h40 := T h23 (C h26 (S h24))
  have h41 := C h11 (T (C h19 h40) h39)
  have h42 := T h18 (C h30 (T h21 h41))
  have h43 := h v1 x y
  have h44 := h v1 v0 y
  have h45 := S h44
  let v46 := M (M v0 v2) y
  let v47 := M v0 v1
  have h48 := h (M v47 y) v1 v46
  have h49 := R v46
  have h50 := h v2 v0 y
  have h51 := T (C h50 (T h50 (C h44 h49))) (S h48)
  have h52 := R v1
  have h53 := C h52 h51
  have h54 := T h53 h45
  have h55 := C h54 h51
  let v56 := M v2 v2
  have h57 := h v56 v1 v56
  have h58 := S h57
  have h59 := S h50
  have h60 := T h48 (C h59 (T (C h45 h49) h59))
  have h61 := C h52 h60
  have h62 := T h44 h61
  have h63 := C h62 h60
  have h64 := T h44 h63
  have h65 := C h62 h64
  have h66 := h v1 z z
  have h67 := S h66
  have h68 := h z z y
  let v69 := M z v1
  have h70 := R v69
  have h71 := C h70 (S h68)
  have h72 := h y z v1
  have h73 := T h72 h71
  have h74 := h v0 x v3
  have h75 := C h27 (T (C (S h74) h73) h67)
  let v76 := M v15 v3
  have h77 := h v76 v25 y
  have h78 := C h62 (T (T (T h77 h75) h65) h58)
  have h79 := h v76 v1 v1
  have h80 := S h79
  have h81 := T h55 h45
  have h82 := S h77
  have h83 := S h72
  have h84 := C h70 h68
  have h85 := T h84 h83
  have h86 := C h40 (T h66 (C h74 h85))
  have h87 := C h54 h81
  have h88 := C h54 (T (T (T h57 h87) h86) h82)
  have h89 := C (T h57 h87) (T (T (C h19 h30) h57) (C (T (T h53 h63) h88) h81))
  have h90 := h v20 v2 v2
  have h91 := C h52 (T (T (T (T h29 h22) h90) h89) h80)
  have h92 := S h34
  have h93 := C h13 (T h13 (C h42 h17))
  have h94 := C h52 (T h93 h92)
  let v95 := M v2 y
  have h96 := h v33 v2 v95
  have h97 := S h96
  have h98 := R v95
  have h99 := C h42 h98
  have h100 := h y x y
  have h101 := C h100 (T h100 h99)
  have h102 := C h52 (T (T (T h101 h97) h34) h32)
  have h103 := C h43 (T (T (T (T (T (T (T h102 h94) h91) h78) h55) h45) h43) (C h42 h38))
  have h104 := C (T (T (T h103 h37) h34) h32) h12
  have h105 := S h100
  have h106 := C h31 h98
  have h107 := C h105 (T h106 h105)
  have h108 := T (T (T h93 h92) h96) h107
  have h109 := C h52 h108
  have h110 := T h34 h32
  have h111 := C h52 h110
  have h112 := S h90
  have h113 := C (T h65 h58) (T (T (C (T (T h78 h55) h61) h64) h58) (C h18 h30))
  have h114 := T (T (T (T h79 h113) h112) h21) h41
  have h115 := C h52 h114
  have h116 := S h43
  have h117 := C h116 (T (T (T (T (T (T (T (C h31 h38) h116) h44) h63) h88) h115) h111) h109)
  have h118 := h v33 v1 v0
  have h119 := T (T (T h44 h63) h88) h115
  have h120 := C h119 h12
  let v121 := M v1 v0
  have h122 := h v121 y v3
  have h123 := S h122
  have h124 := C (T (T (T h91 h78) h55) h45) h12
  let v125 := M v1 (M y y)
  have h126 := h v125 v0 v1
  have h127 := S h126
  have h128 := R y
  have h129 := h y z z
  have h130 := S h129
  have h131 := C h52 (C h130 h128)
  let v132 := M (M z y) z
  have h133 := h v132 v0 y
  have h134 := T (T (T (T (T (T (T h133 h131) h102) h94) h91) h78) h55) h45
  have h135 := C h12 (T h133 h131)
  have h136 := T h129 h135
  have h137 := S h133
  have h138 := C h52 (C h129 h128)
  have h139 := T (T (T (T (T (T (T h44 h63) h88) h115) h111) h109) h138) h137
  have h140 := C h128 h139
  have h141 := T (T (T (T (T h102 h94) h91) h78) h55) h45
  have h142 := C h12 h141
  have h143 := T (T h129 h135) h142
  have h144 := C h143 (T h140 (C h136 h134))
  have h145 := T (T h144 h127) h102
  have h146 := C h12 (T h138 h137)
  have h147 := T (T (T (T (T h44 h63) h88) h115) h111) h109
  have h148 := C h12 h147
  have h149 := h v47 v69 z
  have h150 := S h149
  have h151 := R z
  have h152 := h z z v1
  have h153 := C h73 (C h152 h151)
  have h154 := C (T (T (T (T h153 h150) h148) h146) h130) (T (T (C h145 h12) (C h94 h12)) h124)
  have h155 := h (M y v1) y v0
  have h156 := C h128 h134
  have h157 := C (T (T h156 h155) h154) h11
  let v158 := M y v3
  have h159 := R v158
  have h160 := C h159 h157
  have h161 := h v132 y v3
  have h162 := T (T (T (T (T (T (T (T (T (T h44 h63) h88) h115) h111) h109) h138) h137) h161) h160) h123
  have h163 := S h161
  have h164 := S h155
  have h165 := T h146 h130
  have h166 := T (T h148 h146) h130
  have h167 := C h166 (T (C h165 h139) h156)
  have h168 := T (T h109 h126) h167
  have h169 := C h85 (C (S h152) h151)
  have h170 := C (T (T (T (T h129 h135) h142) h149) h169) (T (T h120 (C h111 h12)) (C h168 h12))
  have h171 := C (T (T h170 h164) h140) h11
  have h172 := C h159 h171
  have h173 := T (T (T (T (T (T (T (T (T (T h122 h172) h163) h133) h131) h102) h94) h91) h78) h55) h45
  have h174 := C h173 (T (C (T (T (T (C h162 h120) (S h118)) h36) h117) h12) h104)
  have h175 := h v121 v1 v0
  have h176 := C (T (T (T (T (T (T (T (T h144 h127) h138) h137) h161) h160) h123) h175) h174) h11
  have h177 := C h168 h11
  let v178 := M v1 v3
  have h179 := R v178
  have h180 := C h179 (T h177 h176)
  have h181 := h v8 v1 v3
  have h182 := C h30 (T (T (T h93 h92) h29) h22)
  have h183 := T h182 h19
  have h184 := C h30 (T (T (T h21 h41) h34) h32)
  have h185 := h v2 v2 v1
  have h186 := S h185
  have h187 := T (T (T (T (T (T (T (T (T (T h93 h92) h29) h22) h90) h89) h80) h77) h75) h65) h58
  have h188 := C h11 (C h187 h52)
  have h189 := T (T (T h188 h186) h18) h184
  have h190 := T (T (T (T (T (T (T (T (T (T h57 h87) h86) h82) h79) h113) h112) h21) h41) h34) h32
  have h191 := C h11 (C h190 h52)
  have h192 := S h181
  have h193 := C h145 h11
  have h194 := S h175
  have h195 := C (T (T (T h93 h92) h36) h117) h12
  have h196 := C h162 (T h195 (C (T (T (T h103 h37) h118) (C h173 h124)) h12))
  have h197 := C (T (T (T (T (T (T (T (T h196 h194) h122) h172) h163) h133) h131) h126) h167) h11
  have h198 := C h179 (T h197 h193)
  have h199 := C h30 (T (T h9 h198) h192)
  have h200 := T (T (T (T h199 h182) h19) h185) h191
  have h201 := C h190 h12
  have h202 := C h30 h201
  have h203 := C h190 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (C h202 h30) (C h200 h30)) (C h189 h30)) (C h183 h30)) h57) h87) h86) h82) h79) h113) h112) h21) h41) h34) h32) h181) h180) h10)
  let v204 := M v56 v0
  have h205 := h v204 v2 v2
  have h206 := C h187 h12
  have h207 := h v0 v3 v3
  have h208 := S h207
  let v209 := M v3 v0
  let v210 := M v209 v3
  have h211 := R v210
  have h212 := S h205
  have h213 := C h30 h206
  have h214 := C h30 (T (T h181 h180) h10)
  have h215 := T (T (T (T h188 h186) h18) h184) h214
  have h216 := T (T (T h182 h19) h185) h191
  have h217 := T h18 h184
  have h218 := C h187 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h9 h198) h192) h93) h92) h29) h22) h90) h89) h80) h77) h75) h65) h58) (C h217 h30)) (C h216 h30)) (C h215 h30)) (C h213 h30))
  have h219 := C (T (T (T (T (T (T (T (T h6 h218) h212) h201) h9) h198) h192) h93) h92) h211
  have h220 := T h219 h208
  have h221 := C h220 h139
  have h222 := C (T (T (T h148 h146) h130) h100) (T (T (T h221 h130) h100) h99)
  have h223 := h v210 v0 v1
  have h224 := h v210 v0 v3
  have h225 := S h224
  have h226 := C (T (T (T (T (T (T (T (T h34 h32) h181) h180) h10) h206) h205) h203) h7) h211
  have h227 := h v210 v2 v1
  have h228 := S h227
  have h229 := S h223
  have h230 := T h207 h226
  have h231 := C h230 h134
  have h232 := C (T (T (T h105 h129) h135) h142) (T (T (T h106 h105) h129) h231)
  have h233 := T (T (T (T (T (T (T (T (T (T (T h6 h218) h212) h201) h9) h198) h192) h93) h92) h96) h232) h229
  have h234 := T (T (T h202 h199) h182) h19
  have h235 := T (T (T (T (C h217 h12) (C h216 h12)) (C h215 h12)) (C h213 h12)) (C h234 h233)
  have h236 := C h235 h52
  let v237 := M v2 v0
  have h238 := h (M v237 v1) v3 y
  have h239 := S h238
  have h240 := h v0 v2 v1
  let v241 := M v3 y
  have h242 := R v241
  have h243 := C h242 (T h66 (C h240 h85))
  have h244 := C h11 (T (T h243 h239) h236)
  have h245 := T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h244 h228) h223) h222) h97) h34) h32) h181) h180) h10) h206) h205) h203) h7) h207) h226
  have h246 := C h245 h11
  have h247 := C h242 (T (C (S h240) h73) h67)
  have h248 := T (T (T (T (T (T (T (T (T (T (T h223 h222) h97) h34) h32) h181) h180) h10) h206) h205) h203) h7
  have h249 := T (T (T h18 h184) h214) h213
  have h250 := T (T (T (T (C h249 h248) (C h202 h12)) (C h200 h12)) (C h189 h12)) (C h183 h12)
  have h251 := C h250 h52
  have h252 := C h11 (T (T h251 h238) h247)
  let v253 := M v241 v1
  have h254 := h v253 v3 v1
  have h255 := S h254
  have h256 := T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h219 h208) h6) h218) h212) h201) h9) h198) h192) h93) h92) h96) h232) h229) h227) h252
  have h257 := C h11 h141
  have h258 := C h183 h40
  have h259 := C h189 h52
  have h260 := C (T h185 h191) h134
  have h261 := T (T (T h260 h259) h258) h39
  have h262 := C h261 h147
  have h263 := C (T h188 h186) h139
  have h264 := C h216 h52
  have h265 := C h217 h27
  have h266 := T (T (T h28 h265) h264) h263
  have h267 := C h266 h173
  have h268 := C (T (T h267 h262) h257) (T (T h129 h231) (C h256 h52))
  have h269 := C h261 h162
  have h270 := C h266 h141
  have h271 := C (T h270 h269) h128
  have h272 := C h11 h147
  have h273 := C h272 h128
  have h274 := C h11 (T (T (T (T (T (T h273 h271) h268) h255) h243) h239) h236)
  have h275 := T h274 h252
  have h276 := C h275 h11
  let v277 := M v3 v1
  let v278 := M v277 y
  have h279 := h v278 v3 v0
  have h280 := S h279
  have h281 := h v0 z z
  have h282 := h (M (M z v0) z) v0 y
  have h283 := C h257 h128
  have h284 := C (T h267 h262) h128
  have h285 := C (T (T h272 h270) h269) (T (T (C h245 h52) h221) h130)
  have h286 := C h11 (T (T (T (T (T (T h251 h238) h247) h254) h285) h284) h283)
  have h287 := h v210 z z
  have h288 := C h261 h12
  have h289 := C h266 (T (T (T h206 h205) h203) h7)
  have h290 := C h11 (T (T (T (T (T (T (T h223 h222) h97) h34) h32) h181) h180) h10)
  have h291 := T (T h290 h289) h288
  have h292 := C h291 (T (T (T (T (T (T (T (T (T (T (T (T (T h6 h218) h212) h201) h9) h198) h192) h93) h92) h96) h232) h229) h287) (C (T (T (T (T (T (T (T (T (T (T (T (T (T h6 h218) h212) h201) h9) h198) h192) h93) h92) h96) h232) h229) h227) h286) (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (C (C h151 h248) h151) h282) (C h52 (T (C (S h281) h73) h67))) h86) h82) h79) h113) h112) h21) h41) h34) h32) h181) h180) h10) h206) h205) h203) h7)))
  have h293 := C h11 (T (T (T (T (T (T (T h9 h198) h192) h93) h92) h96) h232) h229)
  have h294 := C h261 (T (T (T h6 h218) h212) h201)
  have h295 := C h266 h12
  have h296 := T (T h295 h294) h293
  have h297 := C h296 h12
  have h298 := T (T h297 h292) h280
  have h299 := C h11 h298
  have h300 := C h299 h11
  have h301 := C h291 h12
  have h302 := C h296 (T (T (T (T (T (T (T (T (T (T (T (T (T (C (T (T (T (T (T (T (T (T (T (T (T (T (T h274 h228) h223) h222) h97) h34) h32) h181) h180) h10) h206) h205) h203) h7) (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h6 h218) h212) h201) h9) h198) h192) h93) h92) h29) h22) h90) h89) h80) h77) h75) (C h52 (T h66 (C h281 h85)))) (S h282)) (C (C h151 h233) h151))) (S h287)) h223) h222) h97) h34) h32) h181) h180) h10) h206) h205) h203) h7)
  have h303 := T (T h279 h302) h301
  have h304 := C h11 h303
  have h305 := h v210 v2 v2
  have h306 := S h305
  have h307 := T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h6 h218) h212) h201) h9) h198) h192) h93) h92) h29) h22) h90) h89) h80) h77) h75) h65) h58
  have h308 := C h307 (C h235 h30)
  have h309 := C (T (T (T (T h308 h306) h227) h286) h304) h11
  let v310 := M v0 v3
  have h311 := R v310
  have h312 := C h311 (T (T (T h309 h300) h276) h246)
  let v313 := M v237 v2
  have h314 := h v313 v0 v3
  have h315 := T (T (T (T (T (T (T (T (T (T (T (T (T (T h314 h312) h225) h223) h222) h97) h34) h32) h181) h180) h10) h206) h205) h203) h7
  have h316 := R x
  have h317 := C h316 h315
  have h318 := C h26 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (C h317 h11) h79) h113) h112) h21) h41) h34) h32) h181) h180) h10) h206) h205) h203) h7)
  have h319 := h v313 x v3
  have h320 := S h314
  have h321 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h57 h87) h86) h82) h79) h113) h112) h21) h41) h34) h32) h181) h180) h10) h206) h205) h203) h7) (C h250 h30)
  have h322 := C (T (T (T (T h299 h274) h228) h305) h321) h11
  have h323 := C h304 h11
  have h324 := T h244 h286
  have h325 := C h324 h11
  have h326 := C h256 h11
  have h327 := C h311 (T (T (T h326 h325) h323) h322)
  have h328 := T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h6 h218) h212) h201) h9) h198) h192) h93) h92) h96) h232) h229) h224) h327) h320) h319) h318
  have h329 := S h319
  have h330 := T (T (T (T (T (T (T (T (T (T (T (T (T (T h6 h218) h212) h201) h9) h198) h192) h93) h92) h96) h232) h229) h224) h327) h320
  have h331 := C h316 h330
  have h332 := C h26 (T (T (T (T (T (T (T (T (T (T (T (T (T (T h6 h218) h212) h201) h9) h198) h192) h93) h92) h29) h22) h90) h89) h80) (C h331 h11))
  have h333 := T h332 h329
  have h334 := T (C h316 h333) h317
  have h335 := C h334 h328
  have h336 := T h319 h318
  have h337 := T h331 (C h316 h336)
  have h338 := C h337 h12
  have h339 := h (M v15 v0) v3 v3
  have h340 := S h339
  have h341 := C h334 h12
  have h342 := T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h332 h329) h314) h312) h225) h223) h222) h97) h34) h32) h181) h180) h10) h206) h205) h203) h7
  have h343 := C h337 h342
  have h344 := C h11 (T (T (T (T (T (T (T (T (C h202 h52) (C (T (T h199 h182) h19) h139)) h260) h259) h258) h39) h4) h343) h341)
  have h345 := h v204 v2 v1
  let v346 := M v25 v0
  have h347 := h v346 v1 v1
  have h348 := S h347
  have h349 := h v125 v1 v0
  have h350 := S h349
  have h351 := C h162 (T (T (T (T (T (T (T (T h223 h222) h97) h34) h32) h181) h180) h10) h195)
  have h352 := T (T (T (T (T (T (T h351 h350) h102) h94) h91) h78) h55) h45
  have h353 := C h352 h233
  have h354 := C h173 (T (T (T (T (T (T (T (T h104 h9) h198) h192) h93) h92) h96) h232) h229)
  have h355 := T (T (T (T (T (T (T h44 h63) h88) h115) h111) h109) h349) h354
  have h356 := C h355 h315
  have h357 := T (T (T (T (T (T (T (T (T h356 h353) h351) h350) h102) h94) h91) h78) h55) h45
  have h358 := C h357 h330
  have h359 := C h357 h328
  have h360 := C h352 h330
  have h361 := C h355 h248
  have h362 := T (T (T (T (T (T (T (T (T h44 h63) h88) h115) h111) h109) h349) h354) h361) h360
  have h363 := C h362 h315
  have h364 := h v313 v1 v0
  have h365 := T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h6 h218) h212) h201) h9) h198) h192) h93) h92) h29) h22) h90) h89) h80) h77) h75
  have h366 := C h365 (T (T (T h332 h329) h364) (C (T (T (T (T (T (T (T (T (T (T h122 h172) h163) h133) h131) h349) h354) h361) h360) h363) h359) (T (T (T (T (T (T (T (T (T (T h358 h356) h353) h351) h350) h102) h94) h91) h78) h55) h45)))
  have h367 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h366 h348) h332) h329) h314) h312) h225) h223) h222) h97) h34) h32) h181) h180) h10) h206) h345) h344) h11
  have h368 := C h362 h342
  have h369 := T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h86 h82) h79) h113) h112) h21) h41) h34) h32) h181) h180) h10) h206) h205) h203) h7
  have h370 := C h369 (T (T (T (C (T (T (T (T (T (T (T (T (T (T h368 h358) h356) h353) h351) h350) h138) h137) h161) h160) h123) (T (T (T (T (T (T (T (T (T (T h44 h63) h88) h115) h111) h109) h349) h354) h361) h360) h363)) (S h364)) h319) h318)
  have h371 := C (T (T (T (T (T (T (T (T h308 h306) h224) h327) h320) h319) h318) h347) h370) h11
  have h372 := R v33
  have h373 := C h372 (T (T h322 h371) h367)
  have h374 := h (M v209 v0) v3 v3
  have h375 := C h30 h303
  have h376 := C h30 h298
  have h377 := h v278 v2 v1
  have h378 := S h377
  have h379 := S h374
  have h380 := C (T (T (T (T (T (T (T (T h366 h348) h332) h329) h314) h312) h225) h305) h321) h11
  have h381 := S h345
  have h382 := C h11 (T (T (T (T (T (T (T (T h338 h335) h5) h28) h265) h264) h263) (C (T (T h18 h184) h214) h134)) (C h213 h52))
  have h383 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h382 h381) h201) h9) h198) h192) h93) h92) h96) h232) h229) h224) h327) h320) h319) h318) h347) h370) h11
  have h384 := C h372 (T (T h383 h380) h309)
  have h385 := T (T (T (T (T h4 h343) h341) h339) h384) h379
  have h386 := C (T (T (T (T (T (C h217 h11) (C h216 h11)) (C h215 h11)) (C h213 h11)) (C h234 h385)) h376) h52
  let v387 := M (M v2 x) v1
  have h388 := h (M (M v2 v3) v1) v3 v387
  have h389 := S h388
  have h390 := R v387
  have h391 := h v3 v2 v1
  have h392 := h x v2 v1
  have h393 := C h392 (T h392 (C h391 h390))
  let v394 := M x x
  have h395 := h v394 v3 v253
  have h396 := S h392
  have h397 := C h396 (T (C (S h391) h390) h396)
  have h398 := T (T (T (T (T h374 h373) h340) h338) h335) h5
  have h399 := C (T (T (T (T (T h375 (C h249 h398)) (C h202 h11)) (C h200 h11)) (C h189 h11)) (C h183 h11)) h52
  have h400 := h v278 v0 v1
  have h401 := S h400
  have h402 := C (T (T (T (T h382 h381) h205) h203) h7) h385
  have h403 := C h230 h11
  have h404 := C (T (T (T (T (T (T (T (T h403 h326) h325) h323) h322) h371) h367) h402) (C h12 h298)) h52
  let v405 := M v310 v1
  have h406 := h v405 y v3
  have h407 := S h406
  have h408 := h v278 v1 v0
  have h409 := S h408
  have h410 := T (T (T (T (T (T (T (T (T (T (T h368 h358) h356) h353) h351) h350) h102) h94) h91) h78) h55) h45
  have h411 := T h363 h359
  have h412 := T h361 h360
  have h413 := T (T (T (T (T (T (T (T (T (C (T (T h44 h63) h88) h11) (C h115 h11)) (C h111 h11)) h177) h176) (C (T (T (T (T (T (T (T (T h196 h194) h122) h172) h163) h133) h131) h349) h354) h11)) (C h412 h11)) (C h411 h11)) (C h410 h385)) (C h52 h298)
  have h414 := C h413 h12
  have h415 := h (M v178 v0) v1 z
  have h416 := T (T (T (T (T (T (T (T (T (T (T h44 h63) h88) h115) h111) h109) h349) h354) h361) h360) h363) h359
  have h417 := T (T (T (T (T (T (T (T (T (C h52 h303) (C h416 h398)) (C (T h368 h358) h11)) (C (T h356 h353) h11)) (C (T (T (T (T (T (T (T (T h351 h350) h138) h137) h161) h160) h123) h175) h174) h11)) h197) h193) (C h94 h11)) (C h91 h11)) (C (T (T h78 h55) h45) h11)
  have h418 := C h417 h12
  have h419 := C h173 h418
  have h420 := h v278 v1 v1
  have h421 := S h420
  have h422 := C h413 h52
  have h423 := C h365 h422
  have h424 := T (T (T h423 h421) h408) h419
  have h425 := C h417 h52
  have h426 := C h369 h425
  let v427 := M v178 v1
  have h428 := h v427 v0 v3
  have h429 := C h365 (T (T (C h311 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h6 h218) h212) h201) h9) h198) h192) h93) h92) h96) h232) h229) h227) h286) h304) (C (T (T (T (T (T (T (T (T (T (T h4 h343) h341) h339) h384) h379) h297) h292) h280) h420) h426) h398))) (S h428)) h422)
  have h430 := T h429 h426
  have h431 := C h369 (T (T h425 h428) (C h311 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (C (T (T (T (T (T (T (T (T (T (T h423 h421) h279) h302) h301) h374) h373) h340) h338) h335) h5) h385) h299) h274) h228) h223) h222) h97) h34) h32) h181) h180) h10) h206) h205) h203) h7)))
  have h432 := T (T (T (T (T (T (T (T (T (T (T (T (T (T h260 h259) h258) h39) h4) h343) h341) h339) h384) h379) h297) h292) h280) h420) h431
  have h433 := h v3 v0 y
  have h434 := S h433
  have h435 := R (M v1 z)
  let v436 := M v310 y
  have h437 := h v436 v1 z
  have h438 := C h220 h11
  have h439 := C (T (T (T (T h6 h218) h212) h345) h344) h398
  have h440 := C (T (T (T (T (T (T (T (T (C h12 h303) h439) h383) h380) h309) h300) h276) h246) h438) h52
  have h441 := C h166 h440
  have h442 := C (T (T (T (T (T (T (T (T (T (T (T h434 h4) h343) h341) h339) h384) h379) h297) h292) h280) h400) h441) (T (T (T (T (T (T (T (T (T (T (C (T (T (T (T (T (T (T (T (T (T h53 h63) h88) h115) h111) h109) h138) h137) h161) h160) h123) (T (T (T h437 (C h435 (T (T (T (T (C h434 h151) (C h266 h151)) (C h432 h151)) (C h430 h151)) (C h424 h151)))) (S h415)) h414)) h409) h279) h302) h301) h374) h373) h340) h338) h335) h5)
  have h443 := h v56 v1 v436
  have h444 := C h159 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h6 h218) h212) h201) h9) h198) h192) h93) h92) h29) h22) h90) h89) h80) h77) h75) h65) h58) h443) h442)
  have h445 := C h143 (T (T h444 h407) h404)
  have h446 := S h443
  have h447 := T (T (T (T (T (T (T (T (T (T (T (T (T (T h429 h421) h279) h302) h301) h374) h373) h340) h338) h335) h5) h28) h265) h264) h263
  have h448 := T h423 h431
  have h449 := C h162 h414
  have h450 := T (T (T h449 h409) h420) h426
  have h451 := C h143 h404
  have h452 := C (T (T (T (T (T (T (T (T (T (T (T h451 h401) h279) h302) h301) h374) h373) h340) h338) h335) h5) h433) (T (T (T (T (T (T (T (T (T (T h4 h343) h341) h339) h384) h379) h297) h292) h280) h408) (C (T (T (T (T (T (T (T (T (T (T h122 h172) h163) h133) h131) h102) h94) h91) h78) h55) h61) (T (T (T h418 h415) (C h435 (T (T (T (T (C h450 h151) (C h448 h151)) (C h447 h151)) (C h261 h151)) (C h433 h151)))) (S h437))))
  have h453 := C h159 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h452 h446) h57) h87) h86) h82) h79) h113) h112) h21) h41) h34) h32) h181) h180) h10) h206) h205) h203) h7)
  have h454 := C h166 (T (T h440 h406) h453)
  have h455 := T h451 h454
  have h456 := C h455 h11
  have h457 := h v346 y v0
  have h458 := S h457
  have h459 := C h128 h315
  have h460 := T (T (T (T (T h459 h153) h150) h148) h146) h130
  have h461 := C h460 h328
  have h462 := C h128 h330
  have h463 := T (T (T (T (T h129 h135) h142) h149) h169) h462
  have h464 := C h463 h315
  have h465 := C h460 h330
  have h466 := C h463 h342
  have h467 := T (T h466 h465) h459
  have h468 := C h467 (T (T (T (T (T (T (T (T h129 h135) h142) h149) h169) h462) h464) h461) (C (T (T (T (T (T (T (T h129 h135) h142) h149) h169) h462) h464) h461) h342))
  have h469 := h v346 y y
  have h470 := C (T (T (T (T (T (T (T (T (T (T h451 h401) h279) h302) h301) h374) h373) h340) h338) h335) h5) (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h6 h218) h212) h201) h9) h198) h192) h93) h92) h96) h232) h229) h224) h327) h320) h319) h318) h469) (C (T (T (T (T h101 h232) h229) h227) h252) (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h468 h458) h332) h329) h314) h312) h225) h223) h222) h97) h29) h22) h90) h89) h80) h77) h75) h65) h58) h443) h442) h456) (C (T (T (T h445 h401) h377) (C h11 (T (T h399 h388) h397))) (T (T (T (T (T (T (T (T (T (T (T (T h4 h343) h341) h339) h384) h379) h297) h292) h280) h273) h271) h268) h255))))) (S h395)) h393) h389) h386)
  have h471 := T h445 h441
  have h472 := C h471 h12
  have h473 := T (T (T h449 h409) h400) h454
  have h474 := C h473 h12
  have h475 := C h424 h12
  have h476 := C h430 h12
  have h477 := C (T (T (T (T (T (T (T (T (T (T h4 h343) h341) h339) h384) h379) h297) h292) h280) h420) h431) h342
  have h478 := C h11 h336
  have h479 := C h11 (T (T h224 h327) h320)
  have h480 := h v1 v3 v0
  have h481 := h (M v277 v0) v3 v0
  have h482 := T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h295 h294) h293) h479) h478) h477) h476) h475) h474) h472) h470) h378) h279) h302) h301) h374) h373) h340) h338) h335) h5
  have h483 := h v125 v3 v0
  have h484 := T (T (T (T (T (T (T h368 h358) h356) h353) h351) h350) h483) (C h482 (C h257 h12))
  have h485 := C h11 (T (T h314 h312) h225)
  have h486 := C h11 h333
  have h487 := C (T (T (T (T (T (T (T (T (T (T h429 h421) h279) h302) h301) h374) h373) h340) h338) h335) h5) h328
  have h488 := C h448 h12
  have h489 := C h450 h12
  have h490 := T (T (T h445 h401) h408) h419
  have h491 := C h490 h12
  have h492 := C h455 h12
  have h493 := T (T h462 h464) h461
  have h494 := C h493 (T (T (T (T (T (T (T (T (C (T (T (T (T (T (T (T h466 h465) h459) h153) h150) h148) h146) h130) h328) h466) h465) h459) h153) h150) h148) h146) h130)
  have h495 := C h471 h11
  have h496 := C (T (T (T (T (T (T (T (T (T (T h4 h343) h341) h339) h384) h379) h297) h292) h280) h400) h441) (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h399 h388) h397) h395) (C (T (T (T (T h244 h228) h223) h222) h107) (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (C (T (T (T (C h11 (T (T h393 h389) h386)) h378) h400) h454) (T (T (T (T (T (T (T (T (T (T (T (T h254 h285) h284) h283) h279) h302) h301) h374) h373) h340) h338) h335) h5)) h495) h452) h446) h57) h87) h86) h82) h79) h113) h112) h21) h41) h96) h232) h229) h224) h327) h320) h319) h318) h457) h494))) (S h469)) h332) h329) h314) h312) h225) h223) h222) h97) h34) h32) h181) h180) h10) h206) h205) h203) h7)
  have h497 := h v3 v1 v1
  have h498 := S h497
  have h499 := h v427 v0 y
  have h500 := C h430 h128
  have h501 := C h432 h128
  have h502 := C h266 h128
  have h503 := h v241 v0 v3
  have h504 := S h503
  have h505 := C h261 h128
  have h506 := C h447 h128
  have h507 := C h448 h128
  have h508 := C (T (T (T (T (T (T (T (T (T (T h101 h97) h34) h32) h181) h180) h10) h206) h205) h203) h7) (T (T (T (T (C h490 h128) (C h450 h128)) h507) h506) h505)
  let v509 := M v158 v0
  have h510 := h v509 y y
  have h511 := h v405 y v0
  have h512 := S h511
  have h513 := C h467 (T (T (T (T (T (T (T (T (T (T h4 h343) h341) h339) h384) h379) h297) h292) h280) h377) h496)
  have h514 := C (T h464 h461) h11
  have h515 := C (T (T (T h142 h149) h169) h462) h11
  have h516 := C (T (T h153 h150) h148) h11
  have h517 := h (M (M y v0) v3) v0 v0
  have h518 := S h517
  have h519 := C (T (T h142 h149) h169) h11
  have h520 := C (T (T (T h459 h153) h150) h148) h11
  have h521 := C (T h466 h465) h11
  have h522 := C h493 (T (T (T (T (T (T (T (T (T (T h470 h378) h279) h302) h301) h374) h373) h340) h338) h335) h5)
  have h523 := h v509 y v3
  have h524 := C h165 h11
  have h525 := S h510
  have h526 := C (T (T (T (T (T (T (T (T (T (T h6 h218) h212) h201) h9) h198) h192) h93) h92) h96) h107) (T (T (T (T h502 h501) h500) (C h424 h128)) (C h473 h128))
  have h527 := T (T (T (T (T (T (T (T h526 h525) h444) h407) h511) h522) h521) h520) h524
  have h528 := T (T (T (T (T (T h181 h180) h10) h206) h205) h203) h7
  have h529 := C h528 (T (T (T (T (T (T (T (T (C h527 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h6 h218) h212) h201) h9) h198) h192) h93) h92) h29) h22) h90) h89) h80) h77) h75) h65) h58) h443) h442) h456)) (S h523)) h444) h407) h511) h522) h521) h520) h519)
  have h530 := h v241 v0 v0
  have h531 := h v241 v0 v1
  have h532 := S h531
  have h533 := C h136 h11
  have h534 := T (T (T (T (T (T (T (T h533 h515) h514) h513) h512) h406) h453) h510) h508
  have h535 := C h534 h52
  have h536 := C h143 h535
  have h537 := C h527 h52
  have h538 := C h166 h537
  have h539 := h (M v158 v1) y v1
  have h540 := h v132 z z
  have h541 := C (T h531 h538) (T (T (T (T (T (T (T (T (T (T (T (C h324 h128) (C h304 h128)) (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T h299 h274) h228) h223) h222) h97) h34) h32) h181) h180) h10) h206) h205) h203) h7) (T (T h72 h71) (C (C h151 h139) h151)))) (S h540)) h133) h131) h102) h94) h91) h78) h55) h45)
  have h542 := h v253 v3 y
  have h543 := C h143 (T (T (T (T (C h140 h11) h157) (C (T h170 h164) (T (T (T (T (T (T (T (T (T (T (T (T (T (T h4 h343) h341) h339) h384) h379) h297) h292) h280) h273) h271) h268) h255) h542) h541))) (S h539)) h535)
  have h544 := T h543 h538
  have h545 := S h542
  have h546 := C (T h536 h532) (T (T (T (T (T (T (T (T (T (T (T h44 h63) h88) h115) h111) h109) h138) h137) h540) (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T h6 h218) h212) h201) h9) h198) h192) h93) h92) h96) h232) h229) h227) h286) h304) (T (T (C (C h151 h134) h151) h84) h83))) (C h299 h128)) (C h275 h128))
  have h547 := C h166 (T (T (T (T h537 h539) (C (T h155 h154) (T (T (T (T (T (T (T (T (T (T (T (T (T (T h546 h545) h254) h285) h284) h283) h279) h302) h301) h374) h373) h340) h338) h335) h5))) h171) (C h156 h11))
  have h548 := T (T (T (T (T (T h6 h218) h212) h201) h9) h198) h192
  have h549 := C h548 (T (T (C (T h531 h547) h12) (C h544 h12)) (C (T (T (T h536 h532) h530) h529) h12))
  have h550 := C h311 (C (T (T (T (T (T (T (T (T (T (T h549 h518) h516) h515) h514) h513) h512) h406) h453) h510) h508) h11)
  let v551 := M v241 v0
  have h552 := h v551 v0 v3
  have h553 := S h552
  have h554 := T h536 h547
  have h555 := S h530
  have h556 := C h548 (T (T (T (T (T (T (T (T h516 h515) h514) h513) h512) h406) h453) h523) (C h534 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h495 h452) h446) h57) h87) h86) h82) h79) h113) h112) h21) h41) h34) h32) h181) h180) h10) h206) h205) h203) h7)))
  have h557 := C h528 (T (T (C (T (T (T h556 h555) h531) h538) h12) (C h554 h12)) (C (T h543 h532) h12))
  have h558 := C h311 (C (T (T (T (T (T (T (T (T (T (T h526 h525) h444) h407) h511) h522) h521) h520) h519) h517) h557) h11)
  have h559 := h v241 v3 y
  have h560 := R v551
  have h561 := h y v3 v0
  have h562 := h v551 v0 y
  have h563 := S h562
  have h564 := C (T (T (T h533 h519) h517) h557) h128
  have h565 := h (M v158 y) v1 v1
  have h566 := S h565
  have h567 := C (T (T (T h549 h518) h516) h524) h128
  have h568 := C h365 (T (T (T (T (T (T (T (T (T (T (T h297 h292) h280) h273) h271) h268) h255) h542) h541) (C h554 h52)) (C (T (T (T h543 h532) h530) h529) h52)) (C (T (T (T (T (T (T h556 h555) h503) h558) h553) h562) (C h52 h567)) h52))
  have h569 := h v310 v1 v0
  have h570 := C h369 (T (T (T (T (T (T (T (T (T (T (T (C (T (T (T (T (T (T (C h52 h564) h563) h552) h550) h504) h530) h529) h52) (C (T (T (T h556 h555) h531) h547) h52)) (C h544 h52)) h546) h545) h254) h285) h284) h283) h279) h302) h301)
  have h571 := C h365 (T (T (T (T (T (T (T (T (T (T (T (T (T h565 h570) h439) h383) h380) h309) h300) h276) h246) h438) h569) (C h173 (T (T (T (T (C (T (T (T (T (C h52 (T (T (T (T (T (T (T (T (T (T h403 h326) h325) h323) h322) h371) h367) h402) h568) h566) h564)) h563) h552) h550) h504) (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h6 h218) h212) h201) h9) h198) h192) h93) h92) h96) h232) h229) h224) h327) h320) h319) h318) h457) h494) (C (T (T (T (T (T (T (T (T (T h466 h465) h459) h153) h150) h148) h146) h130) h561) (C h482 h560)) h128)) (C (C h11 (T (T h552 h550) h504)) h128))) (S h559)) h503) h558) h553))) (C h52 (T (T (T (T (T h552 h550) h504) h502) h501) h500))) (S h499))
  have h572 := T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h4 h343) h341) h339) h384) h379) h297) h292) h280) h377) h496) h492) h491) h489) h488) h487) h486) h485) h290) h289) h288
  have h573 := C h369 (T (T (T (T (T (T (T (T (T (T (T (T (T h499 (C h52 (T (T (T (T (T h507 h506) h505) h503) h558) h553))) (C h162 (T (T (T (T h552 h550) h504) h559) (C (T (T (T (T h503 h558) h553) h562) (C h52 (T (T (T (T (T (T (T (T (T (T h567 h565) h570) h439) h383) h380) h309) h300) h276) h246) h438))) (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (C (C h11 (T (T h503 h558) h553)) h128) (C (T (T (T (T (T (T (T (T (T (C h572 h560) (S h561)) h129) h135) h142) h149) h169) h462) h464) h461) h128)) h468) h458) h332) h329) h314) h312) h225) h223) h222) h97) h34) h32) h181) h180) h10) h206) h205) h203) h7))))) (S h569)) h403) h326) h325) h323) h322) h371) h367) h402) h568) h566)
  have h574 := S h483
  have h575 := C h572 (C h272 h12)
  have h576 := h x x v3
  have h577 := h (M v394 v3) v25 y
  have h578 := h x z z
  T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h578 (C h12 (T (T (T (h (M (M z x) z) v0 y) (C h52 (C (S h578) h128))) (C h40 (C h576 h128))) (S h577)))) (C h307 (T (T (T (T (T (T (T (T (T (T (T h577 (C h27 (C (S h576) h128))) (C h119 h30)) (C h111 h30)) (C (T (T h109 h349) h354) h30)) (C h412 h30)) (C h411 h30)) (C h484 h30)) (C (T (T (T (T (T (T (T (T (T h575 h574) h102) h94) h91) h78) h55) h45) h480) (C h482 (T (T (T (T (T h481 (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h295 h294) h293) h479) h478) h477) h476) h475) h474) h472) h470) h378) h279) h302) h301) h374) h373) h340) h338) h335) h5) h497) h573) (T (T (T (T (T (T (T (T (T (T (T (T (T (C (T (T (T (T (T (T (T h575 h574) h349) h354) h361) h360) h363) h359) h12) (C h410 h328)) h368) h358) h356) h353) h351) h350) h102) h94) h91) h78) h55) h45))) (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h571 h498) h4) h343) h341) h339) h384) h379) h297) h292) h280) h377) h496) h492) h491) h489) h488) h487) h52)) (C h486 h52)) (C h485 h52)) (C h291 h52)))) h30)) (C (T (T (T (T (T (T (T (T (T (T (T (T (C h572 (T (T (T (T (T (C h296 h52) (C h479 h52)) (C h478 h52)) (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h477 h476) h475) h474) h472) h470) h378) h279) h302) h301) h374) h373) h340) h338) h335) h5) h497) h573) h52)) (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h571 h498) h4) h343) h341) h339) h384) h379) h297) h292) h280) h377) h496) h492) h491) h489) h488) h487) h486) h485) h290) h289) h288) (T (T (T (T (T (T (T (T (T (T (T (T (T h44 h63) h88) h115) h111) h109) h349) h354) h361) h360) h363) h359) (C h416 h342)) (C h484 h12)))) (S h481))) (S h480)) h44) h63) h88) h115) h111) h109) h138) h137) (h v132 x y)) (C h30 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (C (C h316 h134) h128) (h v35 v2 v1)) (C h11 (T (T (C h116 h52) h86) h82))) (C h11 h114)) (C h11 h110)) (C h11 h108)) (C h11 (T (T (T (T (T (T h101 h97) h34) h32) h181) h180) h10))) h293) h479) h478) h477) h476) h475) h474) h472) h470) h378) h279) h302) h301))) h376) h30)) (C h375 h30)) (C (C h30 (T (T (T (T (T (T h297 h292) h280) h273) h271) h268) h255)) h30)))) (S (h v253 v2 v2))) h254) h285) h284) h283) h279) h302) h301) h374) h373) h340) h338) h335) h5

