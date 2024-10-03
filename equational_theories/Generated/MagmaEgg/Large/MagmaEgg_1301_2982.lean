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
theorem Equation1301_implies_Equation2982 (G: Type _) [Magma G] (h: Equation1301 G) : Equation2982 G := fun x y z =>
  let v0 := M z x
  let v1 := M y v0
  let v2 := M v1 z
  let v3 := M v2 y
  have h4 := h v3 y y
  have h5 := S h4
  have h6 := h y v2 v0
  have h7 := S h6
  let v8 := M (M v1 v2) v0
  have h9 := R v8
  have h10 := h v2 y y
  let v11 := M v3 y
  let v12 := M v11 y
  have h13 := R v12
  have h14 := C h13 (T (C (T (C h7 h13) (S h10)) h9) h7)
  have h15 := h v2 v12 v8
  let v16 := M (M v0 y) x
  let v17 := M v2 v0
  have h18 := h y v17 v16
  have h19 := S h18
  have h20 := R v16
  have h21 := R v17
  have h22 := h z y x
  have h23 := h y z v0
  have h24 := C h21 (T h22 (C (T h23 (C h22 h21)) h20))
  have h25 := R z
  have h26 := R v0
  let v27 := M v2 x
  let v28 := M (M v27 v2) x
  let v29 := M v3 v2
  let v30 := M v29 y
  have h31 := h v2 v30 v28
  have h32 := S h31
  have h33 := R v28
  have h34 := R v30
  have h35 := h v2 v2 x
  have h36 := h v2 v2 y
  have h37 := C h34 (T h35 (C (T h36 (C h35 h34)) h33))
  have h38 := T h37 h32
  have h39 := C h38 h26
  have h40 := C h39 h25
  have h41 := R v2
  have h42 := R y
  have h43 := h v29 v2 y
  have h44 := S h43
  have h45 := S h35
  have h46 := C h34 (T (C (T (C h45 h34) (S h36)) h33) h45)
  have h47 := T h31 h46
  have h48 := C h47 h42
  have h49 := C h38 h48
  have h50 := T h49 h44
  have h51 := R v3
  have h52 := C h47 h51
  have h53 := C (T (C h52 h42) (C h50 h42)) h41
  have h54 := C h38 h51
  have h55 := C h38 h42
  have h56 := C h47 h55
  have h57 := T h43 h56
  have h58 := C (T (C h57 h42) (C h54 h42)) h41
  have h59 := h (M v30 v2) z x
  have h60 := S h59
  have h61 := R x
  have h62 := h x v1 x
  have h63 := S h62
  let v64 := M x x
  let v65 := M (M v64 v1) x
  have h66 := R v65
  have h67 := h v1 x z
  let v68 := M v27 z
  have h69 := R v68
  have h70 := h v1 v68 v65
  let v71 := M v0 z
  let v72 := M v71 x
  have h73 := h z v72 v72
  have h74 := S h73
  have h75 := R v72
  have h76 := h z z x
  have h77 := C h75 (T h76 (C (T h76 (C h76 h75)) h75))
  have h78 := T h77 h74
  have h79 := C h78 (T (T h70 (C h69 (T (C (T (C h63 h69) (S h67)) h66) h63))) (C (C (T (C (T (T h31 h46) h58) h61) (C h53 h61)) h25) h61))
  have h80 := T (T h79 h60) h58
  have h81 := S h76
  have h82 := C h75 (T (C (T (C h81 h75) h81) h75) h81)
  have h83 := T h73 h82
  have h84 := C h83 (T (T (C (C (T (C h58 h61) (C (T (T h53 h37) h32) h61)) h25) h61) (C h69 (T h62 (C (T h67 (C h62 h69)) h66)))) (S h70))
  let v85 := M v3 x
  let v86 := M (M v85 v1) x
  let v87 := M v2 v3
  let v88 := M v87 z
  have h89 := h v1 v88 v86
  have h90 := S h89
  have h91 := R v86
  have h92 := R v88
  have h93 := h v3 v1 x
  have h94 := h v1 v3 z
  have h95 := C h92 (T h93 (C (T h94 (C h93 h92)) h91))
  have h96 := C (C h54 h25) h51
  have h97 := C (C h57 h25) h51
  have h98 := T (T (T h97 h96) h95) h90
  have h99 := C h98 h25
  have h100 := C (C h50 h25) h51
  have h101 := C (C h52 h25) h51
  have h102 := S h93
  have h103 := C h92 (T (C (T (C h102 h92) (S h94)) h91) h102)
  have h104 := C (T (T h40 h24) h19) h26
  have h105 := C h47 h26
  have h106 := C h105 h25
  have h107 := S h22
  have h108 := C h21 (T (C (T (C h107 h21) (S h23)) h20) h107)
  let v109 := M (M v64 y) x
  let v110 := M v1 x
  let v111 := M v110 v0
  have h112 := h y v111 v109
  have h113 := S h112
  have h114 := R v109
  have h115 := R v111
  have h116 := h x y x
  have h117 := h y x v0
  have h118 := C h115 (T h116 (C (T h117 (C h116 h115)) h114))
  have h119 := C (T (T (T (T h118 h113) h18) h108) h106) h26
  have h120 := T (T (T (T (T h119 h104) h89) h103) h101) h100
  have h121 := C h120 h25
  have h122 := S h116
  have h123 := C h115 (T (C (T (C h122 h115) (S h117)) h114) h122)
  have h124 := C (T (T (T (T h40 h24) h19) h112) h123) h26
  have h125 := C (T (T h18 h108) h106) h26
  have h126 := T (T (T (T (T h97 h96) h95) h90) h125) h124
  have h127 := C h126 h25
  have h128 := T (T (T h89 h103) h101) h100
  have h129 := C h128 h25
  have h130 := S h15
  have h131 := C h13 (T h6 (C (T h10 (C h6 h13)) h9))
  have h132 := T (T (T (C (T (T (T h131 h130) h129) h127) h26) (C (T (T (T (T (T h121 h99) h31) h46) h59) h84) h26)) (C h80 h26)) (C h53 h26)
  have h133 := C h132 h25
  have h134 := C h55 h42
  have h135 := h v3 y v2
  have h136 := S h135
  have h137 := T h118 h113
  have h138 := C h137 h47
  have h139 := T (T h138 h136) h48
  have h140 := C h139 h42
  have h141 := T h112 h123
  have h142 := C h141 h38
  have h143 := C h53 h42
  have h144 := C h80 h42
  have h145 := T (T (T (T (T h131 h130) h31) h46) h59) h84
  have h146 := C h145 h42
  have h147 := T (T (T (T (T h146 h144) h143) h55) h135) h142
  have h148 := C h147 h42
  have h149 := T (T (T (T (T h79 h60) h37) h32) h15) h14
  have h150 := C h149 h42
  have h151 := T (T h53 h59) h84
  have h152 := C h151 h42
  have h153 := C h58 h42
  have h154 := T (T (T (T (T h138 h136) h48) h153) h152) h150
  have h155 := C h154 h42
  have h156 := T (T h55 h135) h142
  have h157 := C h156 h42
  have h158 := C h48 h42
  have h159 := h v11 y y
  have h160 := h v110 x v0
  have h161 := S h160
  have h162 := C h61 (T h125 h124)
  have h163 := C (C (T h162 h161) h26) h61
  have h164 := C h61 (T h119 h104)
  have h165 := C (C (T h160 h164) h26) h61
  have h166 := C (T (T (T (C (C h141 h51) h42) (C (T (T (T (T (T (C h165 h51) (C (T (T h163 h118) h113) (T (T (T h48 h153) h152) h150))) (S h159)) h158) h157) h155) h42)) (C (T h148 h140) h42)) (C h134 h42)) h42
  have h167 := C h166 h26
  have h168 := C (T (T (T (C h158 h42) (C (T h157 h155) h42)) (C (T (T (T (T (T h148 h140) h134) h159) (C (T (T h112 h123) h165) (T (T (T h146 h144) h143) h55))) (C h163 h51)) h42)) (C (C h137 h51) h42)) h42
  have h169 := h (M v12 y) z y
  have h170 := S h169
  have h171 := h y v1 v0
  have h172 := S h171
  let v173 := M (M v1 v1) v0
  have h174 := R v173
  have h175 := h v1 y z
  let v176 := M v3 z
  have h177 := R v176
  have h178 := h v1 v176 v173
  let v179 := M v0 v2
  let v180 := M v179 x
  have h181 := h z v180 v1
  have h182 := S h181
  have h183 := R v1
  have h184 := R v180
  have h185 := h v1 v2 z
  have h186 := S h185
  let v187 := M (M v2 v2) z
  have h188 := R v187
  have h189 := C h25 (T (C (C h186 h25) h188) h186)
  have h190 := h v2 z v187
  have h191 := h z v2 x
  have h192 := C h184 (T (T h190 h189) (C (T h191 (C (T h190 h189) h184)) h183))
  have h193 := T h192 h182
  have h194 := C h193 (T (T (T h178 (C h177 (T (C (T (C h172 h177) (S h175)) h174) h172))) (C (C h48 h25) h42)) (C (T (C h156 h25) (C h154 h25)) h42))
  have h195 := T (T h194 h170) h168
  have h196 := C h195 h26
  have h197 := C h78 h61
  have h198 := h v71 z x
  have h199 := S h198
  have h200 := C h83 h61
  have h201 := C h78 h200
  have h202 := C h83 h26
  have h203 := C (T (C h202 h61) (C (T h201 h199) h61)) h25
  have h204 := C h203 h61
  have h205 := C h78 h26
  have h206 := C h83 h197
  have h207 := C (T (C (T h198 h206) h61) (C h205 h61)) h25
  have h208 := T (T (T (T h192 h182) h73) h82) h207
  have h209 := C h208 h61
  have h210 := T (T h209 h204) h197
  have h211 := S h190
  have h212 := C h25 (T h185 (C (C h185 h25) h188))
  have h213 := C h184 (T (T (C (T (C (T h212 h211) h184) (S h191)) h183) h212) h211)
  have h214 := T h181 h213
  have h215 := C h214 (T (T (T (C (T (C h147 h25) (C h139 h25)) h42) (C (C h55 h25) h42)) (C h177 (T h171 (C (T h175 (C h171 h177)) h174)))) (S h178))
  have h216 := C (T (T (T h15 h14) h169) h215) h210
  have h217 := h v179 v2 x
  have h218 := C (T (T (T h217 h216) h196) h167) h25
  have h219 := C (T (T (T (T h218 h133) h40) h24) h19) (T h15 h14)
  have h220 := S h217
  have h221 := T (T (T (T h203 h77) h74) h181) h213
  have h222 := C h221 h61
  have h223 := C h207 h61
  have h224 := T (T h200 h223) h222
  have h225 := C (T (T (T h194 h170) h131) h130) h224
  have h226 := T (T h166 h169) h215
  have h227 := C h226 h26
  have h228 := C h168 h26
  have h229 := C (T (T (T h228 h227) h225) h220) h25
  have h230 := T (T (T (C h58 h26) (C h151 h26)) (C (T (T (T (T (T h79 h60) h37) h32) h129) h127) h26)) (C (T (T (T h121 h99) h15) h14) h26)
  have h231 := C h230 h25
  have h232 := C (T (T (T (T h18 h108) h106) h231) h229) (T h131 h130)
  have h233 := C h166 h42
  have h234 := C h195 h42
  have h235 := C (T (T (T (T (T (T (T h234 h233) h146) h144) h143) h55) h4) h232) h183
  have h236 := C h226 h42
  have h237 := C h168 h42
  have h238 := C (T h237 h236) h183
  have h239 := C h154 h183
  have h240 := C (T (T (T (T h144 h143) h55) h135) h142) h183
  have h241 := C (T h153 h152) h183
  have h242 := C h48 h183
  have h243 := C h163 h26
  have h244 := C (T (T (T (T (T (T h133 h40) h24) h19) h112) h123) h165) h26
  have h245 := C h218 h26
  have h246 := h v179 v0 z
  have h247 := S h246
  have h248 := C h229 h26
  have h249 := C (T (T (T (T (T (T h163 h118) h113) h18) h108) h106) h231) h26
  have h250 := C h165 h26
  have h251 := T (T h250 h249) h248
  have h252 := h v0 z v2
  have h253 := S h252
  have h254 := T h4 h232
  have h255 := C h197 h41
  have h256 := T h209 h204
  have h257 := C h256 h41
  have h258 := C h257 h61
  have h259 := T h223 h222
  have h260 := C h259 h41
  have h261 := C h200 h41
  have h262 := C (T (T (T (T (T h228 h227) h225) h220) h261) h260) h61
  have h263 := C h230 h61
  have h264 := C h105 h61
  have h265 := C (T (T (T (T h264 h263) h262) h258) (C h255 h61)) h41
  have h266 := C (T (T h265 h192) h182) h254
  have h267 := C (T h266 h253) (T (T h129 h127) (C h251 h25))
  have h268 := C h39 h61
  have h269 := C h132 h61
  have h270 := C (T (T (T (T (T h257 h255) h217) h216) h196) h167) h61
  have h271 := C h260 h61
  have h272 := C (T (T (T (T (C h261 h61) h271) h270) h269) h268) h41
  have h273 := C h272 h51
  have h274 := C h273 h41
  have h275 := C h221 h51
  have h276 := C h207 h51
  have h277 := T h276 h275
  have h278 := C h277 h41
  have h279 := C h83 h51
  have h280 := C h279 h41
  have h281 := C (T (T (T (T h280 h278) h274) h267) h247) h25
  have h282 := C h78 h51
  have h283 := C h282 h41
  have h284 := C h203 h51
  have h285 := C h208 h51
  have h286 := T h285 h284
  have h287 := C h286 h41
  have h288 := C h265 h51
  have h289 := C h288 h41
  have h290 := T (T h245 h244) h243
  have h291 := T h219 h5
  have h292 := C (T (T h181 h213) h272) h291
  have h293 := C (T h252 h292) (T (T (C h290 h25) h121) h99)
  have h294 := C (T (T (T (T h246 h293) h289) h287) h283) h25
  let v295 := M v0 x
  let v296 := M (M v295 y) x
  let v297 := M (M v1 v0) v0
  have h298 := h y v297 v296
  have h299 := S h298
  have h300 := R v296
  have h301 := R v297
  have h302 := h v0 y x
  have h303 := h y v0 v0
  have h304 := C h301 (T h302 (C (T h303 (C h302 h301)) h300))
  have h305 := C h98 h26
  have h306 := C h120 h26
  have h307 := C h290 h26
  have h308 := C h265 h61
  have h309 := C (T (T (T (T (C (T (T (T (T (T h280 h278) h274) h267) h247) h261) h61) h271) h270) h269) h268) h41
  have h310 := C h309 h61
  have h311 := C (T (T (T (T h264 h263) h262) h258) (C (T (T (T (T (T h255 h246) h293) h289) h287) h283) h61)) h41
  let v312 := M (M v85 z) x
  let v313 := M (M v0 v3) x
  have h314 := h z v313 v312
  have h315 := S h314
  have h316 := R v312
  have h317 := R v313
  have h318 := h v3 z x
  have h319 := h z v3 x
  have h320 := C h317 (T h318 (C (T h319 (C h318 h317)) h316))
  have h321 := C h197 h51
  have h322 := C h256 h51
  have h323 := T (T (T (T (T h273 h266) h253) h200) h223) h222
  have h324 := C h323 h51
  have h325 := C h277 h51
  have h326 := C h279 h51
  have h327 := C (T (T (C (T (T h326 h325) h324) h61) (C h322 h61)) (C h321 h61)) h51
  have h328 := C (T (T (T (T (T (T h327 h320) h315) h181) h213) h272) h311) h61
  let v329 := M z v3
  have h330 := h (M v329 v3) v3 x
  have h331 := C h282 h51
  have h332 := C h286 h51
  have h333 := T (T (T (T (T h209 h204) h197) h252) h292) h288
  have h334 := C h333 h51
  have h335 := C h259 h51
  have h336 := C h200 h51
  have h337 := C (T (T (C h336 h61) (C h335 h61)) (C (T (T h334 h332) h331) h61)) h51
  have h338 := S h318
  have h339 := C h317 (T (C (T (C h338 h317) (S h319)) h316) h338)
  have h340 := C (T (T (T (T (T (T h309 h265) h192) h182) h314) h339) h337) h61
  have h341 := C h311 h61
  have h342 := C h272 h61
  have h343 := T (C h291 (T (T (T (T (T h200 h223) h222) h342) h341) h340)) (S h330)
  have h344 := T (T (T (T (T h146 h144) h143) h55) h4) h232
  have h345 := C h344 h26
  have h346 := C h154 h26
  have h347 := C h156 h26
  have h348 := C h48 h26
  have h349 := C (T (C (T (T (T h348 h347) h346) h345) h61) (C h343 h61)) h51
  have h350 := C h55 h26
  have h351 := C h139 h26
  have h352 := C h147 h26
  have h353 := T (T (T (T (T h219 h5) h48) h153) h152) h150
  have h354 := C h353 h26
  have h355 := T h330 (C h254 (T (T (T (T (T h328 h310) h308) h209) h204) h197))
  have h356 := C (T (C h355 h61) (C (T (T (T h354 h352) h351) h350) h61)) h51
  let v357 := M (M v2 z) z
  let v358 := M (M v0 v1) x
  have h359 := h z v358 v357
  have h360 := S h359
  have h361 := R v357
  have h362 := R v358
  have h363 := h v1 z z
  have h364 := h z v1 x
  have h365 := C h362 (T h363 (C (T h364 (C h363 h362)) h361))
  have h366 := C h197 h183
  have h367 := C h256 h183
  have h368 := C h323 h183
  have h369 := C h277 h183
  have h370 := C h279 h183
  have h371 := C (T (T (C (T (T h370 h369) h368) h61) (C h367 h61)) (C h366 h61)) h183
  have h372 := C (T (T (T (T h125 h124) h250) h249) h248) (T (T (T (T (T (T (T (C (T (T (T (T (T (T h371 h365) h360) h314) h339) h337) h356) h61) (C h349 h61)) h328) h310) h308) h209) h204) h197)
  have h373 := h (M v329 v1) v1 x
  have h374 := C (T (T (C (T h373 h372) h26) (C h307 h26)) (C (T h306 h305) h26)) h26
  have h375 := C h282 h183
  have h376 := C h286 h183
  have h377 := C h333 h183
  have h378 := C h259 h183
  have h379 := C h200 h183
  have h380 := C (C (T (T (T (T h379 h378) h377) h376) h375) h26) h26
  have h381 := C (C (T (T (T (T h370 h369) h368) h367) h366) h26) h26
  have h382 := S h373
  have h383 := S h363
  have h384 := C (T (T (T (T (T (T h349 h327) h320) h315) h359) (C h362 (T (C (T (C h383 h362) (S h364)) h361) h383))) (C (T (T (C h379 h61) (C h378 h61)) (C (T (T h377 h376) h375) h61)) h183)) h61
  have h385 := C h356 h61
  have h386 := C (T (T (T (T h245 h244) h243) h119) h104) (T (T (T (T (T (T (T h200 h223) h222) h342) h341) h340) h385) h384)
  have h387 := C h251 h26
  have h388 := C h126 h26
  have h389 := C h128 h26
  have h390 := C (T (T (C (T h389 h388) h26) (C h387 h26)) (C (T h386 h382) h26)) h26
  have h391 := S h302
  have h392 := C h301 (T (C (T (C h391 h301) (S h303)) h300) h391)
  let v393 := M (M v85 y) x
  let v394 := M v1 v3
  let v395 := M v394 v0
  have h396 := h y v395 v393
  have h397 := S h396
  have h398 := R v393
  have h399 := R v395
  have h400 := h v3 y x
  have h401 := h y v3 v0
  have h402 := C h399 (T h400 (C (T h401 (C h400 h399)) h398))
  have h403 := C h98 h51
  have h404 := C h120 h51
  have h405 := C h290 h51
  have h406 := h v1 v0 x
  have h407 := S h406
  have h408 := C h210 h141
  have h409 := C (T (T (T (T (T (T (T (C h323 h42) h408) h407) h125) h124) h250) h249) h248) h51
  have h410 := C (C h277 h42) h51
  have h411 := C (C h279 h42) h51
  have h412 := C (T (T (C (T (T h411 h410) h409) h26) (C h405 h26)) (C (T h404 h403) h26)) h51
  let v413 := M v329 y
  have h414 := h (M v413 v3) v3 v0
  have h415 := C h282 h42
  have h416 := C h415 h51
  have h417 := C h286 h42
  have h418 := C h417 h51
  have h419 := C h333 h42
  have h420 := C h224 h137
  have h421 := C (T (T (T (T (T (T (T h245 h244) h243) h119) h104) h406) h420) h419) h51
  have h422 := C h251 h51
  have h423 := C h126 h51
  have h424 := C h128 h51
  have h425 := S h400
  let v426 := M (M v3 v1) y
  have h427 := R v426
  let v428 := M (M v295 v2) x
  let v429 := M (M v3 v0) y
  have h430 := h v2 v429 v428
  have h431 := R v428
  have h432 := R v429
  have h433 := h v0 v2 x
  have h434 := h v2 v0 y
  have h435 := S h433
  have h436 := T h143 h55
  have h437 := h v87 v2 y
  have h438 := h v29 v3 z
  have h439 := T h48 h153
  have h440 := T h204 h197
  have h441 := C h440 h25
  have h442 := C h223 h25
  have h443 := C h204 h25
  have h444 := T h200 h223
  have h445 := C h444 h25
  have h446 := h (M z v0) z x
  have h447 := S h446
  have h448 := C h193 h444
  have h449 := C h214 h440
  let v450 := M (M v0 v0) x
  have h451 := h z v450 x
  have h452 := h z v0 x
  have h453 := R v450
  have h454 := h v1 v0 v173
  have h455 := S h454
  have h456 := C h26 (T h171 (C (C h171 h26) h174))
  have h457 := C h197 h42
  have h458 := C h200 h42
  have h459 := C h26 (T (C (C h172 h26) h174) h172)
  T (T (T (T (h x v0 v1) (C h26 (T (C (T (T (T (C (T (T (T (T (T h162 h161) (C h128 h61)) (C (T (T (T (T (T (T h97 h96) h95) h90) h454) h459) h458) h61)) (C (T (T (T (T (T h457 h456) h455) h125) h124) h250) h61)) (C h243 h61)) h26) (C (T (C (T (T (T h119 h104) h406) h420) h61) (C (T (T (T (T (T (T h408 h407) h125) h124) h250) h249) h248) h61)) h26)) (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (C (T (T (T (T (T (T h245 h244) h243) h119) h104) h406) h420) h61) (C (T (T (T h408 h407) h125) h124) h61)) (C h250 h61)) (C (T (T (T (T (T h243 h119) h104) h454) h459) h458) h61)) (C (T (T (T (T (T (T h457 h456) h455) h89) h103) h101) h100) h61)) (C h98 h61)) h160) h164) (h (M x v1) x v0)) (C h61 (T (T (T (T (T (T (T (T (T h243 h119) h104) h406) h420) h419) h417) h415) (h v413 v0 v3)) (C (T (T (T (T (T (T (T (T (T (T (T h200 h223) h222) h342) h341) h340) h385) h384) (C (C (C (T (T (T (T h373 h372) h307) h306) h305) h61) h183) h61)) (C (T (T (T (T (T (T (C (C (T (T (T (T h389 h388) h387) h386) h382) h61) h183) h371) h365) h360) h451) (C h453 (C (S h452) h61))) (C (T (T (C (C h200 h26) h61) (C (C h259 h26) h61)) (C (T (T (C h333 h26) (C h286 h26)) (C h282 h26)) h61)) h26)) h61)) (C (T (T (T (T (T (C (T (T (C (T (T (C h279 h26) (C h277 h26)) (C h323 h26)) h61) (C (C h256 h26) h61)) (C (C h197 h26) h61)) h26) (C h453 (C h452 h61))) (S h451)) h73) h82) (C (T (T (T (C (T h445 h443) h61) (C (T (T (T (T (T (T h442 h441) h198) h206) h205) h446) h449) h61)) (C (T (T (T (T (T (T (T h448 h447) h202) h201) h199) h445) h443) (C h259 h25)) h61)) (C (T (T (T (C h333 h25) (C h285 h25)) (C h284 h25)) (C h282 h25)) h61)) h25)) h61)) (C (T (T (T (T (T (T (T (C (T (T (T (C (T (T (T (C h279 h25) (C h276 h25)) (C h275 h25)) (C h323 h25)) h61) (C (T (T (T (T (T (T (T (C h256 h25) h442) h441) h198) h206) h205) h446) h449) h61)) (C (T (T (T (T (T (T h448 h447) h202) h201) h199) h445) h443) h61)) (C (T h442 h441) h61)) h25) h77) h74) h181) h213) (h (M v180 v2) v3 v1)) (C h51 (T (C (T (T (T (T (T (T (T (T (T (T (T (T (T (C h195 h51) (C h166 h51)) (C h145 h51)) (C (T (T (T h79 h60) h37) h32) h439)) (S h437)) h52) h49) h44) h438) (C h439 h99)) (C h143 h41)) (C h156 h41)) (C h154 h41)) (C h344 h41)) h183) (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (C h353 h41) (C h147 h41)) (C h139 h41)) (C h153 h41)) (C h436 h129)) (S h438)) h43) h56) h54) h437) (C (T (T (T h31 h46) h59) h84) h436)) (C h149 h51)) (C h168 h51)) (C h226 h51)) (C (T (T (T (T (T (T (T (T h194 h170) h131) h130) h430) (C h432 (T (C (T (C h435 h432) (S h434)) h431) h435))) (C (T (T (C h348 h42) (C (T h347 h346) h42)) (C h345 h42)) h26)) (C (C h343 h42) h26)) (C (C (T (T (T (T h326 h325) h324) h322) h321) h42) h26)) h51)) (C (T (T (T (T (T (T (T (T (T (T (C (C (T (T (T (T h336 h335) h334) h332) h331) h42) h26) (C (C h355 h42) h26)) (C (T (T (C h354 h42) (C (T h352 h351) h42)) (C h350 h42)) h26)) (C h432 (T h433 (C (T h434 (C h433 h432)) h431)))) (S h430)) h15) h14) h169) h215) (C h272 h183)) (C (T (T (T (T (T (T h265 h192) h182) h314) h339) h337) h356) h183)) h51)) (C (T (T (T (T (T (T (T (T (T (C (T (T (T (T (T (T h349 h327) h320) h315) h181) h213) h272) h183) (C h265 h183)) h194) h170) h131) h130) (h v2 v426 v187)) (C h427 (T (C (T (C h186 h427) (S (h v2 v1 y))) h188) h186))) (C (T (T (C h242 h42) (C (T (T h241 h240) h239) h42)) (C (T h238 h235) h42)) h183)) (C (C (T (T (T (T (T (T (T (C h291 (T (T (T (T (T (T (T (T h125 h124) h250) h249) h248) (C h294 h26)) (C (T (T (T (T (T (T (T (T h281 h218) h133) h40) h24) h19) h298) h392) h390) h26)) (C h381 h26)) (C (T (T (T (T (T (T h380 h374) h304) h299) h396) (C h399 (T (C (T (C h425 h399) (S h401)) h398) h425))) (C (T (T (C (T h424 h423) h26) (C h422 h26)) (C (T (T h421 h418) h416) h26)) h51)) h26))) (S h414)) h411) h410) h409) h405) h404) h403) h42) h183)) h51)) h183)))) (S (h (M v394 y) v3 v1))) h61)) (T (T h412 h402) h397))))) (S (h v394 x y))) h424) h423) h422) h421) h418) h416) h414) (C h254 (T (T (T (T (T (T (T (T (C (T (T (T (T (T (T h412 h402) h397) h298) h392) h390) h381) h26) (C h380 h26)) (C (T (T (T (T (T (T (T (T h374 h304) h299) h18) h108) h106) h231) h229) h294) h26)) (C h281 h26)) h245) h244) h243) h119) h104))) h26)) (C (T (T (T (T (T (C (T (T (T (T (T (T (T h219 h5) h48) h153) h152) h150) h237) h236) h183) (C (T h234 h233) h183)) (C h147 h183)) (C (T (T (T (T h138 h136) h48) h153) h152) h183)) (C (T h144 h143) h183)) (C h55 h183)) h26)) h183) (C (C (T (T (T (T (T h242 h241) h240) h239) h238) h235) h26) h183)))) (S (h (M (M v179 z) v2) v0 v1))) h219) h5

