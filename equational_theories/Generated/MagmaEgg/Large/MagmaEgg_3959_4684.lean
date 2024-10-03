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
theorem Equation3959_implies_Equation4684 (G: Type _) [Magma G] (h: Equation3959 G) : Equation4684 G := fun x y z =>
  let v0 := M z y
  let v1 := M v0 x
  have h2 := h v0 x v1
  have h3 := S h2
  let v4 := M v0 v1
  let v5 := M x v4
  have h6 := h v5 v1 v1
  have h7 := S h6
  let v8 := M v1 (M v5 v1)
  have h9 := h v8 v1 x
  have h10 := S h9
  have h11 := R x
  have h12 := R v1
  have h13 := C h12 h2
  have h14 := C h13 h11
  have h15 := h v0 v1 x
  have h16 := T h15 h14
  have h17 := h v1 v4 v1
  have h18 := S h17
  have h19 := R (M v1 v1)
  let v20 := M x y
  let v21 := M v20 z
  have h22 := h v0 v1 v21
  let v23 := M v0 v21
  have h24 := h (M v1 v23) v21 v0
  have h25 := R v0
  have h26 := h v1 v23 y
  have h27 := R y
  have h28 := h v0 x v0
  have h29 := S h28
  let v30 := M v0 v0
  let v31 := M x v30
  have h32 := h v31 v0 v0
  have h33 := S h32
  have h34 := C (C h25 h28) h25
  have h35 := T (T h34 h33) h29
  have h36 := h z v4 y
  have h37 := h z v4 v21
  have h38 := R v21
  have h39 := h z v21 x
  have h40 := S h39
  have h41 := h z x y
  have h42 := S h41
  have h43 := h z y y
  let v44 := M y v0
  have h45 := h v44 x y
  have h46 := C (C h38 (T (T h45 (C (C h11 (S h43)) h27)) h42)) h11
  have h47 := h v44 v21 x
  have h48 := h v44 v21 v21
  have h49 := S h48
  have h50 := S h47
  have h51 := C (C h38 (T (T h41 (C (C h11 h43) h27)) (S h45))) h11
  let v52 := M z v21
  have h53 := h v21 v52 v20
  have h54 := R v20
  have h55 := R z
  have h56 := h x y v21
  have h57 := S h56
  let v58 := M x v21
  let v59 := M y v58
  have h60 := h v20 v59 z
  have h61 := h y v58 v20
  have h62 := S h61
  have h63 := C (T (T (C h54 h62) h60) (C h57 h55)) h54
  let v64 := M y v20
  have h65 := h (M v58 v64) v20 v20
  have h66 := R v52
  have h67 := h v52 v59 z
  have h68 := h v20 z z
  have h69 := R v59
  have h70 := C (T (T (T (T (T h61 h65) h63) (C (T (T (C (T h56 (C h69 h68)) h55) (S h67)) (C h66 (T (T h61 h65) h63))) h54)) (S h53)) (C h38 (T (T h39 h51) h50))) h38
  have h71 := T (T (T (T (T h56 h70) h49) h47) h46) h40
  have h72 := R v4
  have h73 := h v0 x v20
  have h74 := S h73
  let v75 := M v0 v20
  let v76 := M x v75
  have h77 := h v76 v20 v20
  let v78 := M v20 v1
  have h79 := h v78 v0 v20
  have h80 := h x y v0
  have h81 := S h80
  have h82 := h z y v1
  have h83 := S h82
  let v84 := M x v0
  let v85 := M y v84
  have h86 := R v85
  have h87 := C (T (C h86 h83) h81) h12
  let v88 := M z v1
  let v89 := M y v88
  have h90 := h v89 v85 v1
  have h91 := h v89 v85 y
  have h92 := S h91
  have h93 := h v89 y x
  have h94 := h y v88 v0
  have h95 := S h94
  have h96 := h (M v88 v44) v0 v0
  have h97 := S h96
  have h98 := h v0 v89 x
  have h99 := C (T (T (C h82 h11) (S h98)) (C h25 h94)) h83
  have h100 := h z y v20
  have h101 := S h100
  have h102 := h (M y (M z v20)) v20 v20
  have h103 := S h102
  have h104 := h v20 v0 z
  have h105 := h v0 v21 x
  have h106 := S h105
  have h107 := h v0 x v21
  have h108 := S h107
  have h109 := C (C h38 h108) h11
  let v110 := M x v23
  let v111 := M v21 (M v110 v21)
  have h112 := h v111 x v21
  have h113 := h v110 v21 v21
  let v114 := M x v1
  have h115 := h v20 v114 z
  have h116 := h x v1 v20
  have h117 := S h116
  have h118 := C (T (T (T (T (C h54 h117) h115) (C (T (T (T (C (C h11 (T h107 h113)) h38) (S h112)) h109) h106) h55)) (S h104)) (C h54 h100)) h54
  let v119 := M x v20
  have h120 := h (M v1 v119) v20 v20
  have h121 := h x v1 x
  have h122 := S h121
  let v123 := M x x
  have h124 := h (M v1 v123) x x
  have h125 := C (T (T (T (C h12 (T (T (T (T (T (T (T (T (C (C h11 h121) h11) (S h124)) h122) h116) h120) h118) h103) h101) h82)) h99) h97) h95) h11
  let v126 := M x v114
  have h127 := h v126 v1 x
  have h128 := h x x v1
  have h129 := T (T h128 h127) h125
  have h130 := h x y x
  have h131 := h v85 v20 v0
  have h132 := S h131
  have h133 := C (C h54 h80) h25
  have h134 := C (T (T h133 h132) (C h86 (T (T h130 (C (C h27 h129) h11)) (S h93)))) h27
  have h135 := C (C h54 h81) h25
  have h136 := S h65
  have h137 := C (T (T (C h56 h55) (S h60)) (C h54 h61)) h54
  have h138 := C (T (T (T (T (T (C h38 (T (T h47 h46) h40)) h53) (C (T (T (C h66 (T (T h137 h136) h62)) h67) (C (T (C h69 (S h68)) h57) h55)) h54)) h137) h136) h62) h38
  have h139 := h z y v21
  have h140 := S h139
  let v141 := M y v52
  have h142 := h v141 y v21
  have h143 := C (T (T (C h86 (T (T (T (T h142 (C (C h27 h140) h38)) h48) h138) h57)) h131) h135) h27
  have h144 := h v141 v85 y
  have h145 := h v141 v85 v21
  have h146 := S h145
  have h147 := C (T h80 (C h86 h139)) h38
  have h148 := h v20 z v0
  have h149 := S h148
  have h150 := h (M z (M v20 v0)) v0 v0
  have h151 := T (T (C (C h25 h148) h25) (S h150)) h149
  have h152 := h v23 v20 v0
  have h153 := T (T (T (T (T h39 h51) h50) h48) h138) h57
  have h154 := R v23
  have h155 := h z v23 v21
  have h156 := h z v23 y
  have h157 := T (T h148 h150) (C (C h25 h149) h25)
  have h158 := T (T (T (T (T (T (T (C h157 h27) (S h156)) h155) (C (T (T (C h154 h153) h152) (C (T (T (T (T (T (T (T (T (C h54 h151) h147) h146) h144) h143) h134) h92) h90) h87) h25)) h38)) (C (T (T h79 (C (C h25 (T (T (C (C h54 h73) h54) (S h77)) h74)) h54)) (C h72 h71)) h38)) (S h37)) h36) (C h35 h27)
  have h159 := h v21 v23 y
  have h160 := h v0 v21 v0
  have h161 := S h160
  have h162 := h (M v21 v30) v0 v0
  have h163 := h (M v0 v23) v21 v0
  have h164 := h v0 v0 v21
  have h165 := T (T (T h160 (C (C h38 (T (T h164 h163) (C (T (T (T (C h38 (T (T (C (C h25 h160) h25) (S h162)) h161)) h159) (C (C h154 h158) h27)) (S h26)) h25))) h25)) (S h24)) (S h22)
  have h166 := C (C h165 h19) h12
  have h167 := h v1 v23 v1
  have h168 := h v111 x x
  have h169 := C (C h38 h107) h11
  have h170 := C (T (T (T (T (C h12 (T (T (T (C (C h11 (T h105 h169)) h11) (S h168)) h109) h106)) h167) h166) h18) (C h12 h16)) h11
  have h171 := h v110 v1 x
  have h172 := h v31 v0 v21
  have h173 := S h172
  let v174 := M v31 v21
  have h175 := h (M v0 v174) v21 v1
  have h176 := S h175
  have h177 := h v0 v174 v1
  have h178 := h x v30 x
  have h179 := S h178
  have h180 := h (M v30 v123) x v1
  have h181 := S h180
  have h182 := T (T (T (T h171 h170) h10) h7) h3
  have h183 := h v30 v123 v0
  have h184 := h z y v0
  have h185 := S h184
  have h186 := C h25 h185
  have h187 := C h186 h25
  let v188 := M z v0
  let v189 := M y v188
  have h190 := h v189 v0 v0
  have h191 := T (T h184 h190) h187
  have h192 := R v123
  have h193 := h x x y
  have h194 := S h193
  have h195 := h v119 y x
  have h196 := S h195
  have h197 := S h130
  let v198 := M y v123
  have h199 := h v198 x x
  have h200 := C (C h27 (T (T h130 h199) (C (C h11 h197) h11))) h11
  have h201 := h v64 x v1
  have h202 := h x y v1
  have h203 := S h202
  let v204 := M y v114
  have h205 := h v204 y v1
  have h206 := h x v1 y
  have h207 := S h206
  have h208 := C (C h27 h207) h27
  have h209 := h (M v1 v20) y y
  have h210 := S h120
  have h211 := C (T (T (T (T (C h54 h101) h104) (C (T (T (T h105 h169) h112) (C (C h11 (T (S h113) h108)) h38)) h55)) (S h115)) (C h54 h116)) h54
  have h212 := R v84
  have h213 := h v4 v84 v0
  have h214 := h x v4 v0
  have h215 := h x v4 v1
  have h216 := h (M v4 v114) v1 v0
  have h217 := h v4 v114 v21
  have h218 := C (C h25 h108) h38
  have h219 := h v110 v0 v21
  have h220 := T h219 h218
  have h221 := T (T (T (T h100 h102) h211) h210) h117
  have h222 := C h221 h220
  have h223 := S h219
  have h224 := C (C h25 h107) h38
  have h225 := T h224 h223
  have h226 := C h25 h225
  have h227 := C (T h226 h222) h38
  have h228 := h v4 v0 v21
  have h229 := C (C h25 h29) h25
  have h230 := C (T (T (C h25 h95) h98) (C h83 h11)) h82
  have h231 := h y v88 v1
  have h232 := S h231
  have h233 := C h12 h82
  have h234 := h v1 v1 v0
  have h235 := C h12 h3
  have h236 := C (T (T (T (T (T h100 h102) h211) h210) h117) (C h11 (T (T h2 h6) (C (T (T (T (T (T (T (T h235 h234) (C (T (C h12 (T (T (T (T h233 h99) h97) h95) h231)) (C h12 (T (T (T (T h232 h94) h96) h230) (C (T (T (T (T (T h28 h32) h229) h228) h227) (S h217)) h83)))) h25)) (S h216)) (S h215)) h214) (C (T (T h213 (C (T (T (T (T (T (C h212 h35) (C (C h11 (T (T (T (T (T (T (T (T (T h100 h102) h211) h210) h117) h206) h209) h208) h205) (C (C h27 h203) h12))) h12)) (S h201)) h200) h196) h194) h25)) (C h192 h191)) h25)) (S h183)) h12)))) h182
  have h237 := S h167
  have h238 := C (T (C h86 h140) h81) h38
  have h239 := S h144
  have h240 := C (T (T h133 h132) (C h86 (T (T (T (T h56 h70) h49) (C (C h27 h139) h38)) (S h142)))) h27
  have h241 := S h128
  have h242 := S h127
  have h243 := C (T (T (T h94 h96) h230) (C h12 (T (T (T (T (T (T (T (T h83 h100) h102) h211) h210) h117) h121) h124) (C (C h11 h122) h11)))) h11
  have h244 := T (T h243 h242) h241
  have h245 := C (T (T (C h86 (T (T h93 (C (C h27 h244) h11)) h197)) h131) h135) h27
  have h246 := S h90
  have h247 := C (T h80 (C h86 h82)) h12
  have h248 := T (T h28 h32) h229
  have h249 := T (T (T (T (T (T (T (C h248 h27) (S h36)) h37) (C (T (T (C h72 h153) (C (C h25 (T (T h73 h77) (C (C h54 h74) h54))) h54)) (S h79)) h38)) (C (T (T (C (T (T (T (T (T (T (T (T h247 h246) h91) h245) h240) h239) h145) h238) (C h54 h157)) h25) (S h152)) (C h154 h71)) h38)) (S h155)) h156) (C h151 h27)
  have h250 := T (T (T h22 h24) (C (C h38 (T (T (C (T (T (T h26 (C (C h154 h249) h27)) (S h159)) (C h38 (T (T h160 h162) (C (C h25 h161) h25)))) h25) (S h163)) (S h164))) h25)) h161
  have h251 := C (C h250 h19) h12
  have h252 := S h15
  have h253 := C h235 h11
  have h254 := T h253 h252
  have h255 := T (T (T (T h2 h6) h9) (C (T (T (T (T (C h12 h254) h17) h251) h237) (C h12 (T (T (T h105 h169) h168) (C (C h11 (T h109 h106)) h11)))) h11)) (S h171)
  have h256 := C h25 h255
  have h257 := T (T (T h256 h236) h181) h179
  have h258 := h v110 v0 v1
  have h259 := S h258
  have h260 := C h12 h83
  have h261 := S h228
  have h262 := T (T (T (T h116 h120) h118) h103) h101
  have h263 := C (T (C h262 h225) (C h25 h220)) h38
  have h264 := S h209
  have h265 := C (C h27 h206) h27
  have h266 := C (C h27 (T (T (C (C h11 h130) h11) (S h199)) h197)) h11
  have h267 := S h190
  have h268 := C h25 h184
  have h269 := C h268 h25
  have h270 := T (T h269 h267) h185
  have h271 := C (T (T (T (T (T (C h11 (T (T (C (T (T (T (T (T (T (T h183 (C (T (T (C h192 h270) (C (T (T (T (T (T h193 h195) h266) h201) (C (C h11 (T (T (T (T (T (T (T (T (T (C (C h27 h202) h12) (S h205)) h265) h264) h207) h116) h120) h118) h103) h101)) h12)) (C h212 h248)) h25)) (S h213)) h25)) (S h214)) h215) h216) (C (T (C h12 (T (T (T (T (C (T (T (T (T (T h217 h263) h261) h34) h33) h29) h82) h99) h97) h95) h231)) (C h12 (T (T (T (T h232 h94) h96) h230) h260))) h25)) (S h234)) h13) h12) h7) h3)) h116) h120) h118) h103) h101) h255
  have h272 := C (T (T h178 h180) h271) h12
  let v273 := M v31 v1
  have h274 := R v273
  have h275 := h v0 v273 v1
  have h276 := h v31 v1 v1
  have h277 := S h276
  have h278 := C (T (T h236 h181) h179) h12
  have h279 := h v5 v0 v1
  have h280 := C (C h12 (T (T (T h279 (C (C h25 h3) h12)) (C h256 h12)) h278)) h12
  have h281 := C h25 (T h280 h277)
  have h282 := h (M v1 (M v5 v0)) v0 v1
  have h283 := h v5 v1 v0
  have h284 := C (C h38 (T (T (T (T h108 h2) h283) h282) (C (T (T (T h281 h275) (C (T (C h274 h250) (C (T (T (T (T h272 h259) h219) h218) (C h257 h38)) h165)) h12)) (S h177)) h12))) h12
  have h285 := C (C h38 (T h3 h107)) h12
  have h286 := h v5 v21 v1
  have h287 := h v5 v21 x
  have h288 := h v8 x x
  have h289 := h v20 z v21
  have h290 := S h289
  let v291 := M z (M v20 v21)
  have h292 := h x v21 v21
  have h293 := S h292
  have h294 := h (M v21 v58) v21 v0
  have h295 := S h294
  have h296 := h v21 v58 v1
  have h297 := S h296
  have h298 := h v21 v1 y
  have h299 := T (T (T (T (T h286 h285) h284) h176) h173) h29
  let v300 := M v5 v21
  have h301 := h v1 v300 y
  have h302 := h v1 v300 v1
  have h303 := S h286
  have h304 := C (C h38 (T h108 h2)) h12
  have h305 := C h25 h182
  have h306 := C (C h12 (T (T (T h272 (C h305 h12)) (C (C h25 h2) h12)) (S h279))) h12
  have h307 := C h25 (T h276 h306)
  have h308 := T (T (T h178 h180) h271) h305
  have h309 := C (C h38 (T (T (T (T (C (T (T (T h177 (C (T (C (T (T (T (T (C h308 h38) h224) h223) h258) h278) h250) (C h274 h165)) h12)) (S h275)) h307) h12) (S h282)) (S h283)) h3) h107)) h12
  have h310 := T (T (T (T (T h28 h172) h175) h309) h304) h303
  have h311 := h v1 v1 v1
  have h312 := T (T (T (T (T h311 (C (C h310 h19) h12)) (S h302)) h301) (C (C h299 h249) h27)) (S h298)
  have h313 := R v58
  have h314 := h v1 v58 v1
  have h315 := T (T h314 (C (C h313 h312) h12)) h297
  have h316 := C (C h38 (C h315 h25)) h25
  have h317 := h (M v1 v58) v21 v0
  have h318 := h x v1 v21
  have h319 := T (T (T (T (T (T (T (T (T h100 h102) h211) h210) h117) h318) h317) h316) h295) h293
  have h320 := h v20 z v1
  have h321 := S h320
  have h322 := T h321 h289
  have h323 := C h12 h320
  have h324 := h v1 v21 v1
  have h325 := h v20 z y
  have h326 := S h325
  let v327 := M v20 y
  let v328 := M z v327
  have h329 := h v328 y v21
  let v330 := M v328 v21
  have h331 := h (M y v330) v21 v1
  have h332 := h y v330 v1
  have h333 := R (M y v1)
  have h334 := h v328 v21 z
  have h335 := h v328 z y
  have h336 := h v328 y y
  have h337 := h (M y v21) z y
  have h338 := h v20 y z
  have h339 := T (T (T (T h338 h337) (C (C h55 (T (T (C (C h27 h325) h27) (S h336)) h326)) h27)) (C (C h55 h325) h27)) (S h335)
  have h340 := h v21 v327 v20
  have h341 := h v21 v20 v21
  have h342 := R (M v21 v21)
  have h343 := h v85 v0 v1
  have h344 := h (M v0 (M v85 v1)) v1 v21
  have h345 := h v85 v1 v21
  have h346 := h x v0 x
  have h347 := h v89 v0 x
  have h348 := h v1 v0 v1
  have h349 := T (T (T (T (T h298 (C (C h310 h158) h27)) (S h301)) h302) (C (C h299 h19) h12)) (S h311)
  have h350 := S h318
  have h351 := S h317
  have h352 := T (T h296 (C (C h313 h349) h12)) (S h314)
  have h353 := C (C h38 (C h352 h25)) h25
  have h354 := T (T (T (T (T (T (T (T (T h292 h294) h353) h351) h350) h116) h120) h118) h103) h101
  have h355 := h x v21 v1
  have h356 := S h355
  have h357 := h (M v21 v114) v1 v1
  have h358 := S h357
  have h359 := C (C h12 h355) h12
  have h360 := C h352 h12
  have h361 := C h315 h12
  have h362 := C (C h12 h356) h12
  have h363 := h v189 v21 v0
  have h364 := h v189 y v21
  have h365 := h z v0 y
  have h366 := S h365
  have h367 := h v30 y y
  have h368 := T (T (T (T h365 h367) (C (C h27 h366) h27)) h364) (C (C h27 (T (T (T (T (T (T h363 (C (C h38 (T h185 h139)) h25)) (C (T (C h38 (T (T (T (T (T (T (T (T (T (T (T (T (T (T h140 h100) h102) h211) h210) h117) h318) h317) h316) h295) h293) h355) h357) h362) h361)) (C h38 (T (T (T h360 h359) h358) h356))) h25)) (C (T (T (T (T (T (T h296 (C (C h354 h349) h12)) (S h348)) h233) h99) h97) h95) h25)) h347) (C (C h25 h244) h11)) (S h346))) h38)
  have h369 := h (M v1 v188) v0 v21
  have h370 := h z v1 v0
  have h371 := h z v1 x
  let v372 := M z x
  have h373 := h (M v1 v372) x v0
  have h374 := h v1 v372 v1
  have h375 := h z x x
  have h376 := h (M x v372) x v1
  have h377 := h z x v0
  have h378 := S h377
  have h379 := h (M x v188) v0 v21
  have h380 := S h379
  have h381 := T (T (T (T (C (C h27 (T (T (T (T (T (T h346 (C (C h25 h129) h11)) (S h347)) (C (T (T (T (T (T (T h94 h96) h230) h260) h348) (C (C h319 h312) h12)) h297) h25)) (C (T (C h38 (T (T (T h355 h357) h362) h361)) (C h38 (T (T (T (T (T (T (T (T (T (T (T (T (T (T h360 h359) h358) h356) h292) h294) h353) h351) h350) h116) h120) h118) h103) h101) h139))) h25)) (C (C h38 (T h140 h184)) h25)) (S h363))) h38) (S h364)) (C (C h27 h365) h27)) (S h367)) h366
  have h382 := h v85 x v21
  have h383 := C (C h25 (T h382 (C (C h11 h381) h38))) h38
  have h384 := C (C h25 (T (C (C h11 h368) h38) (S h382))) h38
  have h385 := h x v0 y
  have h386 := S h385
  have h387 := h v75 y y
  have h388 := S h387
  have h389 := C (C h27 h385) h27
  have h390 := h v85 y v21
  have h391 := S h390
  have h392 := C h27 h368
  have h393 := h y v188 z
  have h394 := S h393
  have h395 := h (M v188 (M y z)) z z
  have h396 := S h395
  have h397 := h z v189 y
  have h398 := C (T (T (C h184 h27) (S h397)) (C h55 h393)) h55
  have h399 := h z v30 y
  have h400 := h v0 v0 z
  have h401 := S h400
  have h402 := C (T (T (C h55 h401) h399) (C h270 h27)) h55
  have h403 := h (M v0 (M v0 z)) z z
  have h404 := h v0 v0 v20
  have h405 := S h404
  have h406 := h (M v0 v75) v20 v20
  have h407 := h v20 v30 z
  have h408 := S h403
  have h409 := C (T (T (C h191 h27) (S h399)) (C h55 h400)) h55
  have h410 := C (T (T (C h55 h394) h397) (C h185 h27)) h55
  have h411 := C h27 h381
  have h412 := C (T (T (T (T (T (T h411 h393) h395) h410) h409) h408) h401) h38
  have h413 := C (C h27 h386) h27
  have h414 := h z y z
  let v415 := M y (M z z)
  have h416 := h v415 x z
  have h417 := h z (M v415 x) v21
  have h418 := C (T (T (T (T (T h417 (C (T (T (T (T (T (T (T (T (T (T (C (T (T (T h416 (C (C h11 (S h414)) h55)) (C (T (T (T (T h385 h387) h413) h390) h412) h55)) (S h407)) h153) (C (C h54 h404) h54)) (S h406)) h405) h400) h403) h402) h398) h396) h394) h392) h38)) h391) h389) h388) h386) h27
  have h419 := C (T (T (T (T (T (T h400 h403) h402) h398) h396) h394) h392) h38
  have h420 := C (T (T (T (T (T h385 h387) h413) h390) (C (T (T (T (T (T (T (T (T (T (T h411 h393) h395) h410) h409) h408) h401) h404) h406) (C (C h54 h405) h54)) (C (T (T (T h407 (C (T (T (T (T h419 h391) h389) h388) h386) h55)) (C (C h11 h414) h55)) (S h416)) h71)) h38)) (S h417)) h27
  have h421 := h v84 y y
  have h422 := S h421
  have h423 := C (C h27 h41) h27
  let v424 := M y v372
  have h425 := h v424 y v1
  have h426 := S h425
  have h427 := h v424 v1 x
  have h428 := h z y x
  have h429 := T (T (T (T h128 h127) h125) (C (T (T (T h94 h96) h230) (C h12 (T h83 h428))) h11)) (S h427)
  have h430 := C (C h27 h429) h12
  have h431 := h v198 v1 y
  have h432 := S h431
  have h433 := h v198 y x
  have h434 := C (C h12 (T (T (T (T h193 h195) h266) (C (C h27 h130) h11)) (S h433))) h27
  have h435 := h v1 v123 v1
  have h436 := h x x v0
  have h437 := C (C h25 h140) h38
  have h438 := h v141 v0 v21
  have h439 := h v141 x v0
  have h440 := T (T h439 (C (C h11 (T (T (T (T (T (T h438 h437) h419) h391) h389) h388) h386)) h25)) (S h436)
  let v441 := M v141 x
  have h442 := h v21 v441 v1
  have h443 := T (T h442 (C (C h440 h349) h12)) (S h435)
  have h444 := C h443 h27
  have h445 := S h438
  have h446 := C (C h25 h139) h38
  have h447 := T (T h436 (C (C h11 (T (T (T (T (T (T h385 h387) h413) h390) h412) h446) h445)) h25)) (S h439)
  have h448 := T (T h435 (C (C h447 h312) h12)) (S h442)
  have h449 := C h448 h27
  have h450 := C (C h12 (T (T (T (T h433 (C (C h27 h197) h11)) h200) h196) h194)) h27
  have h451 := S h428
  have h452 := T (T (T (T h427 (C (T (T (T (C h12 (T h451 h82)) h99) h97) h95) h11)) h243) h242) h241
  have h453 := C (C h27 h452) h12
  have h454 := h v424 y v21
  have h455 := h v424 v21 x
  have h456 := S h455
  have h457 := C (C h38 (T h140 h428)) h11
  have h458 := C (C h38 (T h451 h139)) h11
  have h459 := h v424 v21 v1
  have h460 := h v21 v123 v21
  have h461 := h v21 v441 v21
  have h462 := h v126 v1 v1
  have h463 := h v198 v21 v1
  have h464 := C (C h27 h42) h27
  have h465 := h (M v21 v372) x v1
  have h466 := h v204 x v1
  let v467 := M v204 x
  have h468 := h v1 v467 v1
  have h469 := h (M v1 v467) x v0
  have h470 := h v204 v1 x
  have h471 := h v59 v1 v21
  have h472 := T (T (T (T (T h471 (C (C h12 h57) h38)) (C (C h12 (T (T (T (T (T (T (T (T h202 h470) h469) (C (C h11 (C (T (T h468 (C (C (T (T (T (T h466 (C (C h11 h203) h248)) (C (C h11 (T (T (T (T (T (T h56 h70) h49) h47) h46) h465) (C (T (T (T (C h11 (T (T (T (T (T (T (T (T (C (C h38 (T (T (T (T h41 h421) h464) h425) h453)) h12) (S h463)) (C (T (C h27 (T (T (T (T (T (T (T (T h128 h462) (C (C h12 h241) h12)) (C h448 h12)) (C (T (T h461 (C (C h440 h342) h38)) (S h460)) h12)) (C (C h38 h429) h12)) (S h459)) h455) h458)) (C h27 (T h457 h456))) h38)) (S h454)) h425) h453) h431) h450) h449)) (C h11 (T (T (T (T (T (T (T h444 h434) h432) h430) h426) h423) h422) h420))) (C h11 (T (T (T (T h418 h42) h377) h379) h384))) (C h11 (T (T h383 h380) h378))) h12))) h35)) (S h376)) (S h375)) h19) h12)) (S h374)) h25)) h25)) (S h373)) (S h371)) h370) h369) (C (C h25 (T (C (C h12 h368) h38) (S h345))) h38))) h38)) (S h344)) (S h343)) h81
  let v473 := M v59 v1
  have h474 := h v21 v473 v21
  have h475 := h v21 v473 v1
  have h476 := T (T (T (T (T h80 h343) h344) (C (C h12 (T (T (T (T (T (T (T (T (C (C h25 (T h345 (C (C h12 h381) h38))) h38) (S h369)) (S h370)) h371) h373) (C (C h11 (C (T (T h374 (C (C (T (T (T (T h375 h376) (C (C h11 (T (T (T (T (T (T (C (T (T (T (C h11 (T (T h377 h379) h384)) (C h11 (T (T (T (T h383 h380) h378) h41) h420))) (C h11 (T (T (T (T (T (T (T h418 h421) h464) h425) h453) h431) h450) h449))) (C h11 (T (T (T (T (T (T (T (T h444 h434) h432) h430) h426) h454) (C (T (C h27 (T h455 h458)) (C h27 (T (T (T (T (T (T (T (T h457 h456) h459) (C (C h38 h452) h12)) (C (T (T h460 (C (C h447 h342) h38)) (S h461)) h12)) (C h443 h12)) (C (C h12 h128) h12)) (S h462)) h241))) h38)) h463) (C (C h38 (T (T (T (T h430 h426) h423) h422) h42)) h12)))) h12) (S h465)) h51) h50) h48) h138) h57)) h248)) (C (C h11 h202) h35)) (S h466)) h19) h12)) (S h468)) h25)) h25)) (S h469)) (S h470)) h203)) h38)) (C (C h12 h56) h38)) (S h471)
  have h477 := h v1 v20 v1
  have h478 := R v327
  have h479 := h v1 v327 v20
  have h480 := T (T (T (T h335 (C (C h55 h326) h27)) (C (C h55 (T (T h325 h336) (C (C h27 h326) h27))) h27)) (S h337)) (S h338)
  have h481 := h v328 v1 z
  have h482 := h y (M v328 v1) v1
  have h483 := h v328 y v1
  let v484 := M z v78
  have h485 := h v484 v1 v1
  have h486 := S h485
  have h487 := h (M v1 (M v484 v1)) v1 z
  have h488 := S h487
  have h489 := h v20 v1 z
  have h490 := h v1 v78 v0
  have h491 := T (T (T h94 h96) h230) h260
  have h492 := h v20 v1 v1
  have h493 := h v1 v78 y
  have h494 := R v78
  have h495 := h v21 v78 y
  have h496 := h x y v20
  have h497 := S h496
  let v498 := M y v119
  have h499 := R v498
  have h500 := h v59 v498 v21
  have h501 := h v59 v498 v1
  have h502 := h v85 v0 v21
  have h503 := S h502
  have h504 := h v0 (M v85 v21) v1
  have h505 := h v0 v188 v1
  have h506 := h v204 v0 y
  have h507 := h v204 v0 v1
  have h508 := R v89
  have h509 := h v31 v89 v0
  have h510 := T (T (T h233 h99) h97) h95
  have h511 := C (T (T (T (C h257 h510) h509) (C (T (C h508 h29) h83) h25)) h268) h25
  have h512 := h v1 v4 v0
  have h513 := C (C h250 h349) h12
  have h514 := h v21 v4 v1
  have h515 := S h514
  have h516 := C (C h165 h312) h12
  have h517 := S h512
  have h518 := C (T (T (T h186 (C (T h82 (C h508 h28)) h25)) (S h509)) (C h308 h491)) h25
  have h519 := h v30 v0 v21
  have h520 := S h519
  have h521 := T h438 h437
  have h522 := T h446 h445
  have h523 := C (T (C h354 h522) (C h25 h521)) h38
  have h524 := h v30 v58 v21
  have h525 := S h524
  have h526 := C (T (C h25 h522) (C h319 h521)) h38
  have h527 := h v59 v0 v1
  have h528 := h v59 v0 v21
  have h529 := C (T (T (T (C h354 (T (T (T (T (T (T (T (T (C (C h25 h56) h38) (S h528)) h527) (C (T (T (T (T (C (T (T (T (T (T h184 h190) h187) h519) h526) h525) h472) (C (T (T (T (T (T (T (T (T (T h524 h523) h520) h269) h518) h517) h17) h251) h516) h515) h54)) (C (T (T h514 h513) h237) h54)) (C (T (T h167 h166) h18) h54)) (C (T (T (T h512 h511) h267) h185) h54)) h12)) (C (C h25 h202) h12)) (S h507)) h506) (C (C h25 (T (T (T (T (T (T (T h265 h264) h207) h116) h120) h118) h103) h101)) h27)) h366)) h505) (C (C h368 h72) h12)) (S h504)) h38
  have h530 := h v75 v58 v21
  have h531 := h (M v75 v58) v21 v1
  have h532 := h x v75 v21
  have h533 := h v76 v89 v20
  have h534 := h v85 v0 v0
  have h535 := C (T (T (T (T (T (T h530 h529) h503) h534) (C (T (T (T (C h25 h81) (C (T h82 (C h508 h73)) h54)) (S h533)) (C (T (T (T h532 h531) (C (T (T (T (C h38 (T (T (T (T (T (T (T (T (T (T (T (C (T (T (T (T (T h530 h529) h503) h81) h496) (C h499 h476)) h12) (S h501)) h500) (C (T (C h499 h57) h497) h38)) h147) h146) h144) h143) h134) h92) h90) h87)) h495) (C (C h494 h158) h27)) (S h493)) h12)) (S h492)) h491)) h25)) (S h490)) (C h12 (T h489 (C h323 h55)))) h55
  have h536 := S h530
  have h537 := C (T (T (T h504 (C (C h381 h72) h12)) (S h505)) (C h319 (T (T (T (T (T (T (T (T h365 (C (C h25 (T (T (T (T (T (T (T h100 h102) h211) h210) h117) h206) h209) h208)) h27)) (S h506)) h507) (C (C h25 h203) h12)) (C (T (T (T (T (C (T (T (T h184 h190) h518) h517) h54) (C (T (T h17 h251) h237) h54)) (C (T (T h167 h516) h515) h54)) (C (T (T (T (T (T (T (T (T (T h514 h513) h166) h18) h512) h511) h187) h519) h526) h525) h54)) (C (T (T (T (T (T h524 h523) h520) h269) h267) h185) h476)) h12)) (S h527)) h528) (C (C h25 h57) h38)))) h38
  have h538 := C h12 h321
  have h539 := C (T (T (T (T (T (T (C h12 (T (C h538 h55) (S h489))) h490) (C (T (T (T (C (T (T (T h492 (C (T (T (T h493 (C (C h494 h249) h27)) (S h495)) (C h38 (T (T (T (T (T (T (T (T (T (T (T h247 h246) h91) h245) h240) h239) h145) h238) (C (T h496 (C h499 h56)) h38)) (S h500)) h501) (C (T (T (T (T (T (C h499 h472) h497) h80) h502) h537) h536) h12)))) h12)) (S h531)) (S h532)) h510) h533) (C (T (C h508 h74) h83) h54)) (C h25 h80)) h25)) (S h534)) h502) h537) h536) h55
  have h540 := h v484 v21 v1
  have h541 := T (T (T (T h540 (C (T (T (C h38 h322) (C h38 (T (T (T (T h290 h320) h485) h487) h539))) (C h38 (T (T (T (T (T (T h535 h488) h486) h321) h325) h483) (C (T (T h482 (C (C (T (T (T (T h481 (C (C h12 h480) h55)) (C (T (T h479 (C (C h478 (T (T (T (T (T h477 (C (C h476 h312) h12)) (S h475)) h474) (C (C h472 h342) h38)) (S h341))) h54)) (S h340)) h55)) (C (C h38 h339) h55)) (S h334)) h333) h12)) (S h332)) h12)))) h12)) (S h331)) (S h329)) h326
  have h542 := h v1 (M v484 v21) v1
  have h543 := R v141
  have h544 := C h262 (T (T (T (T (T h224 h223) h258) h278) h276) h306)
  T (T (T (T (T (T (T (T h320 h485) (C (T (T (T h538 h324) (C (C (T (T (T (T h325 h329) h331) (C (T (T (C h38 (T (T (T (T (T (T (C (T (T h332 (C (C (T (T (T (T h334 (C (C h38 h480) h55)) (C (T (T h340 (C (C h478 (T (T (T (T (T h341 (C (C h476 h342) h38)) (S h474)) h475) (C (C h472 h349) h12)) (S h477))) h54)) (S h479)) h55)) (C (C h12 h339) h55)) (S h481)) h333) h12)) (S h482)) h12) (S h483)) h326) h320) h485) h487) h539)) (C h38 (T (T (T (T h535 h488) h486) h321) h289))) (C h38 (T h290 h320))) h12)) (S h540)) h19) h12)) (S h542)) h12)) (C (T (T (T h542 (C (C h541 (T (T (T h13 (C h12 (T (T (T (T (T (T h3 h28) h32) h229) h228) h227) (C (T h544 h281) h38)))) (C h12 (T (T (T (T (T (T (T (T (T (T (T (C (T h307 (C h221 (T (T (T (T (T h280 h277) h272) h259) h219) h218))) h38) h263) h261) h34) h33) h172) h175) h309) h304) h303) h287) (C (C h38 (T (T (T (C (C h11 h16) h11) (S h288)) h253) h252)) h11)))) (C (T (T (T (T (T h28 h32) h229) h228) (C (T (T (T (T (T h226 h222) h544) h281) (C h25 (T (C (T (T (T (T (T (T (T h178 h180) h271) h305) (C (T h139 (C h543 h320)) h12)) (S (h v484 v141 v1))) (h v484 v141 v21)) (C (T (C h543 h541) h140) (T (T (T (T h320 (h v484 v1 v21)) (C (T (T (T h542 (C (C h541 h19) h12)) (S h324)) h323) h38)) (C (C h12 h322) h38)) (S (h v291 v1 v21))))) h12) (S (h v291 v0 v1))))) (C h319 (T (h v291 v0 v21) (C (C h25 h290) h38)))) h38)) (S (h v23 v58 v21))) (T (T (T (T (T (T (T (C (C h38 (T (T (T h15 h14) h288) (C (C h11 h254) h11))) h11) (S h287)) h286) h285) h284) h176) h173) h29)))) h12)) (S (h (M v23 v58) v21 v1))) (S (h x v23 v21))) h12)) h171) h170) h10) h7) h3

