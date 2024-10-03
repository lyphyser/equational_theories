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
theorem Equation2113_implies_Equation778 (G: Type _) [Magma G] (h: Equation2113 G) : Equation778 G := fun x y z =>
  let v0 := M z y
  let v1 := M v0 x
  let v2 := M z v1
  let v3 := M y v2
  let v4 := M z z
  have h5 := R v4
  have h6 := S (h z y v2)
  have h7 := R v3
  let v8 := M y v3
  have h9 := R v8
  have h10 := h y z v1
  have h11 := S h10
  have h12 := R v2
  have h13 := R v1
  have h14 := h v0 v1 v1
  have h15 := S h14
  have h16 := h v1 v0 v2
  have h17 := S h16
  let v18 := M v0 v2
  have h19 := R v18
  have h20 := h y v0 v0
  have h21 := S h20
  let v22 := M v0 v0
  have h23 := R v22
  have h24 := h y z y
  have h25 := C h24 h23
  have h26 := C (T (C (T (T h25 h21) h10) h19) h17) (T (C h10 h19) h17)
  have h27 := h v22 y v18
  have h28 := h v1 z y
  have h29 := S h28
  have h30 := R v0
  have h31 := C (C h29 h30) h29
  let v32 := M v2 y
  have h33 := h v0 v32 v0
  have h34 := T h33 h31
  have h35 := C h34 (T h27 h26)
  have h36 := T h35 h15
  have h37 := C h36 h13
  have h38 := S h27
  have h39 := S h24
  have h40 := C h39 h23
  have h41 := C (T h16 (C (T (T h11 h20) h40) h19)) (T h16 (C h11 h19))
  have h42 := S h33
  have h43 := C (C h28 h30) h28
  have h44 := T h43 h42
  have h45 := C h44 (T h41 h38)
  let v46 := M v1 v0
  have h47 := h (M v46 v1) v0 v3
  have h48 := S h47
  let v49 := M v0 v3
  have h50 := R v49
  have h51 := C h36 h34
  have h52 := T h14 h45
  have h53 := C h52 h30
  have h54 := C (T h53 h51) h7
  have h55 := h v3 y v2
  have h56 := S h55
  have h57 := h v22 y v2
  have h58 := S h57
  have h59 := T h20 h40
  have h60 := C (C h59 h12) h7
  have h61 := C (T (T (C h56 h7) h60) h58) h56
  have h62 := h v3 (M v8 v2) v3
  have h63 := T (T h62 h61) h54
  have h64 := C h63 h50
  have h65 := T (T (T (T (T h64 h48) h43) h42) h14) h45
  have h66 := C h65 h13
  have h67 := S h62
  have h68 := T h25 h21
  have h69 := C (C h68 h12) h7
  have h70 := C (T (T h57 h69) (C h55 h7)) h55
  have h71 := C h36 h30
  have h72 := C h52 h44
  have h73 := C (T h72 h71) h7
  have h74 := T (T h73 h70) h67
  have h75 := C h74 h50
  have h76 := h v49 v3 y
  have h77 := S h76
  have h78 := C (C h11 h12) h11
  let v79 := M v0 v1
  have h80 := h v2 v79 v2
  have h81 := T h80 h78
  have h82 := R y
  have h83 := T (T (T (T (T h35 h15) h33) h31) h47) h75
  have h84 := C (T (C h52 h82) (C h83 h82)) h81
  have h85 := C h63 (T h84 h77)
  have h86 := T h85 h75
  have h87 := C h86 h13
  have h88 := S h80
  have h89 := C (C h10 h12) h10
  have h90 := T h89 h88
  have h91 := C (T (C h65 h82) (C h36 h82)) h90
  have h92 := C h74 (T h76 h91)
  have h93 := C h13 h44
  have h94 := C h93 h13
  have h95 := C h13 h34
  have h96 := h v46 v3 v3
  have h97 := S h96
  have h98 := R (M v3 v3)
  have h99 := R v46
  let v100 := M y v0
  have h101 := h v3 (M v100 v2) v3
  have h102 := h v0 y v2
  let v103 := M v0 y
  let v104 := M v103 v2
  have h105 := h v104 v3 x
  have h106 := S h105
  let v107 := M v3 x
  have h108 := R v107
  have h109 := R x
  have h110 := C (T (T (T (T (T h35 h15) h33) h31) h47) h92) h109
  have h111 := C h52 h109
  have h112 := C (T h111 h110) h108
  have h113 := C (T (T (C (T (T (T h112 h106) h84) h77) h30) (C (C h102 h7) h102)) (S h101)) h99
  have h114 := h v107 v1 v0
  have h115 := C (C (T h114 h113) h7) h98
  have h116 := h x v3 v3
  have h117 := C (T (T (T h116 h115) h97) h95) h13
  let v118 := M x v1
  have h119 := h v118 v0 v2
  have h120 := S h119
  have h121 := S h116
  have h122 := S h114
  have h123 := C h36 h109
  have h124 := C (T (T (T (T (T h85 h48) h43) h42) h14) h45) h109
  have h125 := C (T h124 h123) h108
  have h126 := S h102
  have h127 := C (T (T h101 (C (C h126 h7) h126)) (C (T (T (T h76 h91) h105) h125) h30)) h99
  have h128 := C (C (T h127 h122) h7) h98
  have h129 := C (T (T (T h93 h96) h128) h121) h13
  have h130 := C h95 h13
  have h131 := T (T (T h33 h31) h130) h129
  have h132 := C (T (T (T h85 h48) h43) h42) h131
  have h133 := T h64 h92
  have h134 := C h133 h30
  have h135 := C (T (T (T h33 h31) h47) h75) h44
  have h136 := C (T (T (T (T h53 h51) h135) h134) h132) h12
  have h137 := h v2 z v1
  have h138 := S h137
  have h139 := h v22 y v22
  have h140 := S h139
  have h141 := C (T h20 (C (T (T h39 h20) h40) h23)) h59
  have h142 := h y v2 v0
  have h143 := S h142
  let v144 := M v2 v0
  have h145 := R v144
  have h146 := T (C h28 h145) h143
  have h147 := h v1 v2 v2
  have h148 := S h147
  let v149 := M v2 v2
  have h150 := R v149
  have h151 := h v1 z v1
  have h152 := C h151 h150
  have h153 := C (T (C (T (T h152 h148) h28) h145) h143) h146
  have h154 := h v149 v1 v144
  have h155 := C (T (T (T (T (C h138 h12) h154) h153) h141) h140) h138
  let v156 := M z v2
  have h157 := h v2 (M v156 v1) v2
  have h158 := T (T h157 h155) h136
  have h159 := C h158 h19
  have h160 := T (T (T (T (T h159 h120) h117) h94) h47) h92
  have h161 := C h160 h13
  have h162 := S h157
  have h163 := S h154
  have h164 := T h142 (C h29 h145)
  have h165 := C (S h151) h150
  have h166 := C (T h142 (C (T (T h29 h147) h165) h145)) h164
  have h167 := C (T (C (T (T h25 h21) h24) h23) h21) h68
  have h168 := C (T (T (T (T h139 h167) h166) h163) (C h137 h12)) h137
  have h169 := C (T (T (T h64 h48) h43) h42) h34
  have h170 := C h86 h30
  have h171 := T (T (T h117 h94) h43) h42
  have h172 := C (T (T (T h33 h31) h47) h92) h171
  have h173 := C (T (T (T (T h172 h170) h169) h72) h71) h12
  have h174 := T (T h173 h168) h162
  have h175 := C h174 h19
  have h176 := h v18 v2 z
  have h177 := S h176
  have h178 := h z v0 x
  have h179 := S h178
  have h180 := C (C h179 h13) h179
  let v181 := M v0 z
  have h182 := h v1 (M v181 x) v1
  have h183 := R z
  have h184 := T (T (T (T (T h85 h48) h130) h129) h119) h175
  have h185 := C h184 h183
  have h186 := C (T (T (T (C h52 h183) (C h83 h183)) (C h133 h183)) h185) (T h182 h180)
  have h187 := T h186 h177
  have h188 := C h158 h187
  have h189 := T h188 h175
  have h190 := C h189 h13
  have h191 := S h182
  have h192 := C (C h178 h13) h178
  have h193 := C h160 h183
  have h194 := C (T (T (T h193 (C h86 h183)) (C h65 h183)) (C h36 h183)) (T h192 h191)
  have h195 := T h176 h194
  have h196 := C h174 h195
  have h197 := h v118 v1 v0
  have h198 := T (T h116 h115) h97
  have h199 := T h130 h129
  have h200 := C h13 h199
  have h201 := T (T (T (T h116 h115) h97) h95) h200
  let v202 := M x v0
  have h203 := h v202 v2 y
  have h204 := R v32
  have h205 := R v202
  have h206 := h v2 (M (M z v0) v1) v2
  have h207 := S h206
  have h208 := h v0 z v1
  have h209 := C (C h208 h12) h208
  let v210 := M v181 v1
  have h211 := h v210 v2 x
  have h212 := S h211
  let v213 := M v2 x
  have h214 := R v213
  have h215 := C (T (T h111 h110) (C (T (T (T (T (T h85 h48) h130) h129) h119) h196) h109)) h214
  have h216 := C (T (T (T h215 h212) h186) h177) h30
  have h217 := C (T (T (T (T (T h188 h120) h117) h94) h47) h92) h109
  have h218 := C (T (T h217 h124) h123) h214
  have h219 := h v210 y v0
  have h220 := S h219
  have h221 := R v100
  have h222 := C h11 h195
  have h223 := T h16 h222
  have h224 := C (T (T (T (T (T h116 h115) h97) h95) h200) (C h223 h171)) h221
  have h225 := T (T (T h224 h220) h211) h218
  have h226 := C h225 h30
  have h227 := h v100 x v0
  have h228 := h v0 v103 v0
  have h229 := C (T (T (T (C (T (T (C (T (T h228 (C (C h39 h30) h39)) (C (T h227 (C (T (T (T h226 h216) h209) h207) h205)) h82)) h204) (S h203)) (C h201 h30)) h198) (S h197)) h119) h196) h13
  have h230 := h v32 v0 x
  have h231 := C (T (T (T (T (T (T h230 h229) h190) h161) h87) h66) h37) h12
  let v232 := M v32 v2
  have h233 := h v232 v3 v3
  have h234 := S h233
  have h235 := S h230
  have h236 := T (T h96 h128) h121
  have h237 := T h117 h94
  have h238 := C h13 h237
  have h239 := C h10 h187
  have h240 := T h239 h17
  have h241 := C (T (T (T (T (T (C h240 h131) h238) h93) h96) h128) h121) h221
  have h242 := T (T (T h215 h212) h219) h241
  have h243 := C h242 h30
  have h244 := C (T (T (T h176 h194) h211) h218) h30
  have h245 := S h208
  have h246 := C (C h245 h12) h245
  have h247 := T (T (T (T h238 h93) h96) h128) h121
  have h248 := C (T (T (T h188 h120) h197) (C (T (T (C h247 h30) h203) (C (T (T (C (T (C (T (T (T h206 h246) h244) h243) h205) (S h227)) h82) (C (C h24 h30) h24)) (S h228)) h204)) h236)) h13
  have h249 := T h159 h196
  have h250 := C h249 h13
  have h251 := C h184 h13
  have h252 := C h133 h13
  have h253 := C h83 h13
  have h254 := C h52 h13
  have h255 := C (T (T (T (T (T (T h254 h253) h252) h251) h250) h248) h235) h12
  have h256 := C h7 (T h10 h255)
  have h257 := h v210 y v2
  have h258 := S h257
  let v259 := M v1 v2
  have h260 := h v259 v3 v3
  have h261 := S h260
  have h262 := R v259
  have h263 := h v144 v1 v2
  have h264 := C h12 h44
  have h265 := C h12 h237
  have h266 := C h12 h199
  have h267 := C h12 h34
  have h268 := h v144 v1 v3
  have h269 := S h268
  have h270 := R (M v1 v3)
  have h271 := h v232 v3 z
  let v272 := M v3 z
  have h273 := R v272
  have h274 := T (T h80 h78) h256
  have h275 := C (T (C (T (T (T (C (T (T h182 h180) (C h274 h183)) h273) (S h271)) h231) h11) h7) (C h164 h7)) h270
  have h276 := h v272 v1 v3
  have h277 := C (T (T (T (C (T (T (T (T h276 h275) h269) h267) h266) h7) (C h265 h7)) (C h264 h7)) (C (T h263 (C (C h146 h12) h262)) h7)) h98
  have h278 := h z v3 v3
  have h279 := C (T (T (T h278 h277) h261) (C h223 h12)) h7
  have h280 := T (T (T h279 h258) h219) h241
  have h281 := C h280 h30
  let v282 := M z v3
  let v283 := M v282 v0
  have h284 := h v283 v3 v3
  have h285 := S h284
  have h286 := T h57 h69
  have h287 := S h278
  have h288 := S h276
  have h289 := C h7 (T h231 h11)
  have h290 := T (T h289 h89) h88
  have h291 := C (T (C h146 h7) (C (T (T (T h10 h255) h271) (C (T (T (C h290 h183) h192) h191) h273)) h7)) h270
  have h292 := C (T (T (T (C (T (C (C h164 h12) h262) (S h263)) h7) (C h267 h7)) (C h266 h7)) (C (T (T (T (T h265 h264) h268) h291) h288) h7)) h98
  have h293 := C (T (T (T (C h240 h12) h260) h292) h287) h7
  have h294 := T (T (T h224 h220) h257) h293
  have h295 := C h294 h30
  have h296 := T (T (T (T h206 h246) h244) h243) h295
  have h297 := C (C h7 h296) h7
  have h298 := h v2 y v2
  have h299 := C (T h298 h297) h286
  have h300 := T (T (T (T (T (T (T (T (T h299 h285) h281) h226) h216) h209) h207) h80) h78) h256
  have h301 := T h60 h58
  have h302 := S h298
  have h303 := T (T (T (T h281 h226) h216) h209) h207
  have h304 := C (C h7 h303) h7
  have h305 := C (T h304 h302) h301
  have h306 := h v283 v2 v3
  have h307 := S h306
  let v308 := M v2 v3
  have h309 := R v308
  have h310 := T (T (T (T (T (T h299 h285) h281) h226) h216) h209) h207
  have h311 := C h310 h296
  have h312 := C (T (T (T (T (T (T (T (T h299 h285) h281) h226) h216) h209) h207) h298) h297) h286
  have h313 := C (T h312 h305) h310
  have h314 := h v22 v2 v22
  have h315 := C (T (T (T (T (T (T (T h172 h170) h169) h72) h71) h314) h313) h311) h7
  have h316 := C (T (T h135 h134) h132) h7
  have h317 := C (T (T (T (T h62 h61) h54) h316) h315) h309
  have h318 := C (T (C (T (T (T h317 h307) h284) h305) h7) (C h300 h7)) h98
  have h319 := h v308 v3 v3
  have h320 := h v308 v1 v2
  have h321 := S h320
  have h322 := T (T h278 h277) h261
  have h323 := S h319
  have h324 := C (T (T h172 h170) h169) h7
  have h325 := S h314
  have h326 := T (T (T (T (T (T h206 h246) h244) h243) h295) h284) h305
  have h327 := C (T (T (T (T (T (T (T (T h304 h302) h206) h246) h244) h243) h295) h284) h305) h301
  have h328 := C (T h299 h327) h326
  have h329 := C h326 h303
  have h330 := C (T (T (T (T (T (T (T h329 h328) h325) h53) h51) h135) h134) h132) h7
  have h331 := C (T (T (T (T h330 h324) h73) h70) h67) h309
  have h332 := T (T (T (T (T (T (T (T (T h289 h89) h88) h206) h246) h244) h243) h295) h284) h305
  have h333 := C (T (C h332 h7) (C (T (T (T h299 h285) h306) h331) h7)) h98
  have h334 := T (T (T (T h10 h255) h233) h333) h323
  have h335 := T h279 h258
  have h336 := C h82 h335
  have h337 := h v282 v2 v3
  have h338 := S h337
  have h339 := T h257 h293
  have h340 := C h12 h339
  have h341 := C (T (T (T (T (T (C h52 h7) (C h83 h7)) (C h133 h7)) (C h184 h7)) (C h249 h7)) (C h340 h7)) h334
  have h342 := T h341 h338
  have h343 := C h82 h342
  have h344 := C (T (T (T h343 h336) h239) h17) h334
  have h345 := T (T (T (T h319 h318) h234) h231) h11
  have h346 := C h12 h335
  have h347 := C (T (T (T (T (T (C h346 h7) (C h189 h7)) (C h160 h7)) (C h86 h7)) (C h65 h7)) (C h36 h7)) h345
  have h348 := T h337 h347
  have h349 := C h82 h348
  have h350 := C h349 h82
  have h351 := C h82 h339
  have h352 := C (T (T h16 h222) h351) h82
  have h353 := h y v0 v2
  have h354 := S h353
  have h355 := C (T (C (T h354 h10) h19) h17) h354
  have h356 := h v18 v104 v18
  have h357 := h (M v49 y) y v3
  have h358 := S h357
  have h359 := h v1 z x
  have h360 := S h359
  have h361 := h (M z x) v1 x
  have h362 := R (M v1 x)
  have h363 := h y z x
  have h364 := h v144 v1 x
  have h365 := T (T (T (T (T h276 h275) h269) h364) (C (T (C h146 h109) (C h363 h109)) h362)) (S h361)
  have h366 := h v213 v1 v3
  have h367 := S h366
  have h368 := S h356
  have h369 := C (T h16 (C (T h11 h353) h19)) h353
  have h370 := C (T (T h336 h239) h17) h82
  have h371 := C h343 h82
  have h372 := C (T (T (T h16 h222) h351) h349) h345
  have h373 := C (T (T (C (T (T (T (T (T (T (T (T h372 h371) h370) h369) h368) h176) h194) h257) h293) h7) (C h280 h7)) (C h225 h7)) h270
  have h374 := h v308 v1 v3
  have h375 := C (T (T (T (T (T (T (T h10 h255) h233) h333) h323) h374) h373) h367) h365
  have h376 := C (T (T (T (T (T h375 h360) h16) h222) h351) h349) h7
  have h377 := C h376 h9
  have h378 := h v272 y v3
  have h379 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h265 h264) h268) h291) h288) h378) h377) h358) h341) h338) h279) h258) h186) h177) h356) h355) h352) h350) h344) h12
  have h380 := C h266 h12
  have h381 := C h267 h12
  have h382 := h v2 z y
  have h383 := S h382
  have h384 := C (C h383 h30) h383
  have h385 := h v0 (M v156 y) v0
  have h386 := h v0 v0 v1
  have h387 := S h386
  have h388 := R v79
  have h389 := h v22 v3 v1
  have h390 := S h389
  let v391 := M v3 v1
  have h392 := R v391
  have h393 := h v149 v1 v3
  have h394 := T (T (T (T (T h361 (C (T (C (S h363) h109) (C h164 h109)) h362)) (S h364)) h268) h291) h288
  have h395 := S h374
  have h396 := C (T (T (C h242 h7) (C h294 h7)) (C (T (T (T (T (T (T (T (T h279 h258) h186) h177) h356) h355) h352) h350) h344) h7)) h270
  have h397 := T (T (T (T (T (T (T h366 h396) h395) h319) h318) h234) h231) h11
  have h398 := C h397 h394
  have h399 := C h12 h342
  have h400 := C (T (T (T (T (T (T (T (T (T (T (T (T h399 h346) h188) h120) h117) h94) h43) h42) h385) h384) h381) h380) h379) h322
  have h401 := C h12 h348
  have h402 := C h401 h183
  have h403 := C h340 h183
  have h404 := C h249 h183
  have h405 := C (T (T (T (T (T (T (T (T h185 h404) h403) h402) h400) h321) h374) h373) h367) h365
  have h406 := h v104 v3 z
  have h407 := h v107 v1 v3
  have h408 := T (T (T (T (T (C (T (T (T (T (T (T (T (T (T (T (T h127 h122) h407) (C (T (T (T (T (T (C (T (T (T (T h112 h106) h406) h405) h398) h7) h376) (C h343 h7)) (C h336 h7)) (C h240 h7)) (C (T h147 h165) h7)) h270)) (S h393)) h154) h153) h141) h140) h314) h313) h311) h7) h330) h324) h73) h70) h67
  have h409 := C h200 h13
  have h410 := C (T (T (T (T h33 h31) h130) h409) (C (T (T (T h238 h93) h96) (C h408 h301)) h13)) h392
  have h411 := C (C (T h410 h390) h13) h388
  have h412 := h v391 v0 v1
  have h413 := h v391 v0 v2
  have h414 := S h413
  have h415 := C h36 h12
  have h416 := C h65 h12
  have h417 := C h86 h12
  have h418 := C h160 h12
  have h419 := C h189 h12
  have h420 := C h346 h12
  have h421 := C h399 h12
  have h422 := C h238 h13
  have h423 := C h189 h183
  have h424 := C h346 h183
  have h425 := C h399 h183
  have h426 := T (T h260 h292) h287
  have h427 := S h385
  have h428 := C (C h382 h30) h382
  have h429 := C h264 h12
  have h430 := C h265 h12
  have h431 := S h378
  have h432 := C (T (T (T (T (T h343 h336) h239) h17) h359) h398) h7
  have h433 := C h432 h9
  have h434 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h372 h371) h370) h369) h368) h176) h194) h257) h293) h337) h347) h357) h433) h431) h276) h275) h269) h267) h266) h12
  have h435 := C (T (T (T (T (T (T (T (T (T (T (T (T h434 h430) h429) h428) h427) h33) h31) h130) h129) h119) h196) h340) h401) h426
  have h436 := C (T (T (T (T (T (T (T (T h366 h396) h395) h320) h435) h425) h424) h423) h193) h394
  have h437 := T (T (T (T (T h62 h61) h54) h316) h315) (C (T (T (T (T (T (T (T (T (T (T (T h329 h328) h325) h139) h167) h166) h163) h393) (C (T (T (T (T (T (C (T h152 h148) h7) (C h223 h7)) (C h351 h7)) (C h349 h7)) h432) (C (T (T (T (T h375 h436) (S h406)) h105) h125) h7)) h270)) (S h407)) h114) h113) h7)
  have h438 := C (T (T (T (T (C (T (T (T (C h437 h286) h97) h95) h200) h13) h422) h94) h43) h42) h392
  have h439 := T (T (T h157 h155) h136) (C (T (T (T (T (T (T h172 h170) h169) h72) h71) h389) h438) h12)
  have h440 := C h439 (T (T (T (T (T (T (T (T h378 h377) h358) h341) h338) h279) h258) h186) h177)
  have h441 := C (T (T (T (T (T (T (T (T (T (T (T (T h440 h414) h412) h411) h387) h33) h31) h130) h129) h119) h196) h340) h401) h12
  have h442 := T (T (T (C (T (T (T (T (T (T h410 h390) h53) h51) h135) h134) h132) h12) h173) h168) h162
  have h443 := C h442 (T (T (T (T (T (T (T (T h176 h194) h257) h293) h337) h347) h357) h433) h431)
  have h444 := T h413 h443
  have h445 := C h444 h12
  have h446 := C h439 (T (T (T (T (T (T (T (T h445 h441) h421) h420) h419) h418) h417) h416) h415)
  have h447 := C (T (T (T (T (T (T (T (T (T h446 h414) h412) h411) h387) h385) h384) h381) h380) h379) h322
  have h448 := h (M v391 v2) v1 v0
  have h449 := S h448
  have h450 := T h440 h414
  have h451 := C h450 h12
  have h452 := S h412
  have h453 := C (C (T h389 h438) h13) h388
  have h454 := C (T (T (T (T (T (T (T (T (T (T (T (T h399 h346) h188) h120) h117) h94) h43) h42) h386) h453) h452) h413) h443) h12
  have h455 := C h401 h12
  have h456 := C h340 h12
  have h457 := C h249 h12
  have h458 := C h184 h12
  have h459 := C h133 h12
  have h460 := C h83 h12
  have h461 := C h52 h12
  have h462 := h v1 (M v22 x) v1
  have h463 := h v0 v0 x
  have h464 := h v308 v2 v0
  have h465 := C (C (T (T (T (T (T (T h10 h255) h233) h333) h323) h464) (C (T (T (C (T (T (T (T (T (T (T (T (C h326 h345) (C h310 h82)) h230) h229) h190) h161) h87) h66) h37) h30) (C (C h463 h13) h463)) (S h462)) (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h268 h291) h288) h378) h377) h358) h341) h338) h279) h258) h186) h177) h461) h460) h459) h458) h457) h456) h455) h454) h451))) h30) h198
  have h466 := T h465 h449
  have h467 := C h12 h466
  have h468 := C h467 h183
  have h469 := C h310 h334
  have h470 := C h326 h82
  have h471 := S h463
  have h472 := C (C (T (T (T (T (T (T (C (T (T h462 (C (C h471 h13) h471)) (C (T (T (T (T (T (T (T (T h254 h253) h252) h251) h250) h248) h235) h470) h469) h30)) (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h445 h441) h421) h420) h419) h418) h417) h416) h415) h176) h194) h257) h293) h337) h347) h357) h433) h431) h276) h275) h269)) (S h464)) h319) h318) h234) h231) h11) h30) h236
  have h473 := T h448 h472
  have h474 := C h12 h473
  have h475 := C h442 (T (T (T (T (T (T (T (T h461 h460) h459) h458) h457) h456) h455) h454) h451)
  have h476 := h v118 v1 v1
  have h477 := S h476
  have h478 := C (T (T (T (T (T h159 h120) h117) h94) h43) h42) h131
  have h479 := C h189 h30
  have h480 := C h346 h30
  have h481 := C h399 h30
  have h482 := T (T (T (T (T (T (T (T (T (T (T (T h446 h414) h412) h411) h387) h33) h31) h130) h129) h119) h196) h340) h401
  have h483 := C h482 h30
  have h484 := C h467 h30
  have h485 := C (T (T h440 h475) h474) h30
  have h486 := C h444 h30
  let v487 := M v391 v0
  have h488 := h v487 v3 y
  have h489 := S h488
  have h490 := C h450 h30
  have h491 := C (T (T h467 h446) h443) h30
  have h492 := C h474 h30
  have h493 := C (T (T (T (T (T (T (T (T (T (T (T (T h399 h346) h188) h120) h117) h94) h43) h42) h386) h453) h452) h413) h475) h30
  have h494 := C h401 h30
  have h495 := C h340 h30
  have h496 := C h249 h30
  have h497 := C (T (T (T (T (T h33 h31) h130) h129) h119) h175) h171
  have h498 := C h408 (T (T (T (T (T (T (T (T (T (T (T (T (T (T h60 h58) h53) h51) h135) h134) h132) h497) h496) h495) h494) h493) h492) h491) h490)
  have h499 := C (T (C h201 h82) (C (T (T (T h238 h93) h96) h498) h82)) h81
  have h500 := C (T (T (T h33 h31) h130) h409) (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h499 h489) h486) h485) h484) h483) h481) h480) h479) h478) h172) h170) h169) h72) h71) h27) h26)
  have h501 := C (T (T (T (T (T (T (T (T (T (T (T h500 h477) h117) h94) h43) h42) h386) h453) h452) h413) h475) h474) h183
  have h502 := C (T (C (T (T (T (C h437 (T (T (T (T (T (T (T (T (T (T (T (T (T (T h486 h485) h484) h483) h481) h480) h479) h478) h172) h170) h169) h72) h71) h57) h69)) h97) h95) h200) h82) (C h247 h82)) h90
  have h503 := T h488 h502
  have h504 := C h30 h503
  have h505 := C h504 h183
  have h506 := T h499 h489
  have h507 := C h30 h506
  have h508 := C (T (T (T h422 h94) h43) h42) (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h41 h38) h53) h51) h135) h134) h132) h497) h496) h495) h494) h493) h492) h491) h490) h488) h502)
  have h509 := C (T (T (T (T (T (T (T (T (T (T (T h440 h414) h412) h411) h387) h33) h31) h130) h129) h476) h508) h507) h183
  have h510 := C h444 h183
  have h511 := h (M v391 z) v3 v1
  have h512 := S h511
  have h513 := C h450 h183
  have h514 := C (T (T (T (T (T (T (T (T (T (T (T h504 h500) h477) h117) h94) h43) h42) h386) h453) h452) h413) h443) h183
  have h515 := C h507 h183
  have h516 := C (T (T (T (T (T (T (T (T (T (T (T h467 h446) h414) h412) h411) h387) h33) h31) h130) h129) h476) h508) h183
  have h517 := C h474 h183
  have h518 := C (T (T (T (T (T (T (T (T (T h434 h430) h429) h428) h427) h386) h453) h452) h413) h475) h426
  have h519 := C h326 (T (T (T (T (T (T (T (T (T (T (T (T (T (T h499 h489) h486) h485) h484) h483) h481) h480) h479) h478) h172) h170) h169) h72) h71)
  have h520 := C h12 h503
  have h521 := C h12 h506
  have h522 := C h310 (T (T (T (T (T (T (T (T (T (T (T (T (T (T h53 h51) h135) h134) h132) h497) h496) h495) h494) h493) h492) h491) h490) h488) h502)
  have h523 := C (T (T (T (T (C h274 h13) (C h332 h13)) (C (T (T h299 h327) h522) h13)) (C h521 h13)) (C (T (T (T (T (T (T h520 h519) h312) h285) h306) h331) (C h7 (T (T (T (T (T (T h320 h518) h517) h516) h515) h514) h513))) h13)) (T (T h386 h453) h452)
  let v524 := M (M v2 v1) v0
  have h525 := C (T (T (T (T (C (T (T (T (T (T (T (C h7 (T (T (T (T (T (T h510 h509) h505) h501) h468) h447) h321)) h317) h307) h284) h327) h522) h521) h13) (C h520 h13)) (C (T (T h519 h312) h305) h13)) (C h300 h13)) (C h290 h13)) (T (T h412 h411) h387)
  T (T (T (T (T (T h116 h115) h498) (C h7 h503)) (C h7 (T (T (T (T h499 h489) (h v487 y v3)) (C (C (T (T (T (T (T (T (T (T (T (T (T (T (T (C h82 h503) (C (T (T h10 h255) (C (T h470 h469) h12)) (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h499 h489) h486) h485) h484) h483) h481) h480) h479) h478) h172) h170) h169) h72) h71) h139) h167) h166) h163))) (S (h v308 v2 v2))) h320) h518) h517) h516) h515) h514) h513) h511) h525) (h v524 z z)) (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (C (T (T (T (T (T (T (C h183 (T (T (T (T (T (T (T (T (T (T (T (T (T h523 h512) h510) h509) h505) h501) h468) h447) h321) h319) h318) h234) h231) h11)) h385) h384) h381) h380) h379) (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h372 h371) h370) h369) h368) h461) h460) h459) h458) h457) h456) h455) h454) h451) h448) h472) (h (M v100 x) v2 x)) (C (T (T (T (T (T (T (T (T (T (C h467 h109) (C h482 h109)) (C h399 h109)) (C h346 h109)) h217) h124) h123) h359) h436) (C (T (T (T (T (T (T (T (T (T (T h185 h404) h403) h402) h400) h321) h319) h318) h234) h231) h11) (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h378 h377) h358) h341) h338) h279) h258) h186) h177) h461) h460) h459) h458) h457) h456) h455) h454) h451) h448) h472))) h397)) (C (C h82 h466) h82)) (C (T (T (T (C h82 h473) (C (T (T (T (T (T (T (T (T (T (T h10 h255) h233) h333) h323) h320) h435) h425) h424) h423) h193) (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h465 h449) h445) h441) h421) h420) h419) h418) h417) h416) h415) h176) h194) h257) h293) h337) h347) h357) h433) h431))) h405) h360) (T (T (T (T (T (T (T (T (T (T (T (T (T h10 h255) h233) h333) h323) h320) h518) h517) h516) h515) h514) h513) h511) h525))) h12)) h322) (S (h v524 v1 v2))) h523) h512) h510) h509) h505) h501) h468) h447) h321) h319) h318) h234) h231) h11) h5)) h7) h9)) (S (h v4 y v3))))) (C (T (h v3 (M (M y z) v2) v3) (C (C h6 h7) h6)) h5)) (S (h v3 z z))

