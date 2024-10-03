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
theorem Equation2519_implies_Equation1320 (G: Type _) [Magma G] (h: Equation2519 G) : Equation1320 G := fun x y z =>
  let v0 := M y x
  let v1 := M v0 z
  let v2 := M v1 z
  let v3 := M y v2
  have h4 := h v3 x x
  have h5 := S h4
  have h6 := R x
  let v7 := M v3 x
  let v8 := M v7 x
  have h9 := R v2
  have h10 := h v2 v0 y
  have h11 := S h10
  have h12 := R y
  let v13 := M v2 y
  let v14 := M v0 (M v13 v0)
  have h15 := h v14 x x
  have h16 := S h15
  have h17 := R v0
  have h18 := h v2 v0 z
  have h19 := S h18
  have h20 := h z x v1
  have h21 := R v1
  have h22 := h y z x
  have h23 := T (C (C h6 h22) h21) (S h20)
  have h24 := h z z v2
  have h25 := S h24
  have h26 := h v0 z z
  have h27 := R z
  have h28 := C h27 h26
  have h29 := T (C h28 h9) h25
  have h30 := C (C h9 h29) h17
  have h31 := h z v2 v0
  have h32 := T h31 h30
  have h33 := C h17 h32
  have h34 := C h33 h23
  have h35 := T h34 h19
  have h36 := C h35 h12
  have h37 := h x v1 y
  have h38 := T h37 h36
  have h39 := C h38 h17
  have h40 := h x v3 x
  have h41 := S h40
  let v42 := M x x
  let v43 := M v3 (M v42 v3)
  have h44 := h v43 v0 x
  have h45 := C (C h6 (T h40 (C (T h44 (C (C h17 (T (C h41 h17) h39)) h6)) h6))) h6
  have h46 := h v42 y x
  have h47 := h v43 z x
  have h48 := S h37
  have h49 := T h20 (C (C h6 (S h22)) h21)
  have h50 := S h31
  have h51 := C h27 (S h26)
  have h52 := T h24 (C h51 h9)
  have h53 := C (C h9 h52) h17
  have h54 := T h53 h50
  have h55 := C h17 h54
  have h56 := C h55 h49
  have h57 := T h18 h56
  have h58 := C h57 h12
  have h59 := T h58 h48
  have h60 := C h59 h27
  have h61 := h (M z (M v13 z)) x x
  have h62 := C h38 h27
  have h63 := h v0 y z
  have h64 := S h63
  let v65 := M y (M v1 y)
  have h66 := h v65 v2 v2
  have h67 := S h66
  have h68 := h v1 y v2
  have h69 := S h68
  let v70 := M v1 v2
  let v71 := M y (M v70 y)
  have h72 := h v71 y v2
  have h73 := T h72 (C (C h12 (C h69 h12)) h9)
  have h74 := C (C h9 (T h68 (C h73 h9))) h9
  have h75 := C (T (C h27 (T (C (T h74 h67) h27) h64)) h28) h9
  let v76 := M v2 v1
  have h77 := h v76 z v2
  have h78 := h v76 x v2
  have h79 := S h78
  have h80 := T (C (C h12 (C h68 h12)) h9) (S h72)
  have h81 := C (C h9 (T (C h80 h9) h69)) h9
  have h82 := h v1 y x
  have h83 := S h82
  have h84 := C h12 (C h83 h12)
  have h85 := C h12 (C h82 h12)
  have h86 := h v65 v3 v0
  have h87 := S h86
  have h88 := R v3
  let v89 := M v65 v0
  have h90 := h v89 v2 v2
  have h91 := S h90
  have h92 := h v1 v3 v0
  have h93 := C (C h12 (C (S h92) h12)) h17
  have h94 := h (M v3 (M (M v1 v0) v3)) y v0
  let v95 := M z v0
  let v96 := M v95 v1
  have h97 := h v1 v0 v96
  have h98 := S h97
  have h99 := R v96
  have h100 := h z v1 v0
  have h101 := C (T h33 (C h17 (T (T h53 h50) h100))) h99
  have h102 := T h101 h98
  have h103 := C h102 h17
  have h104 := C (T h100 h103) h88
  have h105 := h z z z
  have h106 := S h105
  have h107 := C h106 h88
  have h108 := C h88 (T h107 h104)
  have h109 := C h105 h88
  have h110 := h z v0 v2
  have h111 := S h110
  have h112 := C h88 (T (C h111 h88) h109)
  have h113 := C (T (T (T h112 h108) h94) h93) h9
  let v114 := M z v2
  let v115 := M v0 (M v114 v0)
  have h116 := h v115 v3 v2
  have h117 := T h116 h113
  have h118 := C h117 h9
  have h119 := C h9 (T h110 h118)
  have h120 := h (M v2 z) x v0
  have h121 := S h120
  have h122 := C h106 h6
  have h123 := C h105 h6
  have h124 := h z z v0
  have h125 := C h6 (T (C (S h124) h6) h123)
  have h126 := C (T h125 (C h6 (T h122 (C h32 h6)))) h17
  have h127 := C h6 (T h122 (C h124 h6))
  have h128 := S h100
  have h129 := C (T (C h6 (T (C h128 h6) h123)) h127) h17
  let v130 := M v1 v96
  have h131 := h v130 x v0
  have h132 := C (T (C h17 (T (T h128 h31) h30)) h55) h99
  have h133 := C (T (T (T (T (T (T h97 h132) h131) h129) h126) h121) h119) h9
  have h134 := C h88 (C (T h133 h91) h88)
  have h135 := h (M v3 (M v70 v3)) x v2
  have h136 := S h135
  have h137 := h v1 v3 v2
  have h138 := C (T (C h6 (C h69 h6)) (C h6 (C h137 h6))) h9
  have h139 := h v71 x v2
  have h140 := C (T (T (T h139 h138) h136) h134) h17
  have h141 := C (T (T h140 h87) h85) h6
  have h142 := S h139
  have h143 := C (T (C h6 (C (S h137) h6)) (C h6 (C h68 h6))) h9
  have h144 := S h131
  have h145 := C (T h125 (C h6 (T h122 (C h100 h6)))) h17
  have h146 := C (T (C h6 (T (C h54 h6) h123)) h127) h17
  have h147 := S h116
  have h148 := C h88 (T h107 (C h110 h88))
  have h149 := T h97 h132
  have h150 := C h149 h17
  have h151 := C (T h150 h128) h88
  have h152 := C h88 (T h151 h109)
  have h153 := S h94
  have h154 := C (C h12 (C h92 h12)) h17
  have h155 := C (T (T (T h154 h153) h152) h148) h9
  have h156 := T h155 h147
  have h157 := C h156 h9
  have h158 := C h9 (T h157 h111)
  have h159 := C (T (T (T (T (T (T h158 h120) h146) h145) h144) h101) h98) h9
  have h160 := C h88 (C (T h90 h159) h88)
  have h161 := C (T (T (T h160 h135) h143) h142) h17
  have h162 := C (T (T h84 h86) h161) h6
  let v163 := M v1 x
  let v164 := M y (M v163 y)
  have h165 := h v164 y x
  have h166 := h v164 x x
  have h167 := S h166
  have h168 := h v1 x x
  have h169 := C (T (C h6 (C (S h168) h6)) (C h6 (C h82 h6))) h6
  let v170 := M v163 x
  have h171 := h (M x v170) x x
  have h172 := C h102 h6
  have h173 := C h172 h6
  have h174 := C h6 h173
  have h175 := C h149 h6
  have h176 := C h175 h6
  have h177 := h v170 v1 x
  have h178 := S h177
  have h179 := C (T (T (T (T (T h133 h91) h154) h153) h152) h148) h9
  have h180 := h (M v70 v2) v2 v3
  have h181 := S h180
  have h182 := C (T (T (T (T (T h112 h108) h94) h93) h90) h159) h9
  have h183 := C (T h155 h182) h88
  have h184 := C h117 h88
  have h185 := h v115 x v2
  have h186 := S h185
  have h187 := C (T (C h6 (T (C h29 h6) h123)) (C h6 (T h122 (C h110 h6)))) h9
  have h188 := h v95 x v2
  have h189 := h v65 v3 v3
  have h190 := h v1 x v3
  have h191 := S h190
  let v192 := M v1 v3
  have h193 := h (M x (M v192 x)) y v3
  have h194 := C (T (T (T (C h27 (T (C (T (C (C h88 (T h190 (C (T h193 (C (C h12 (C h191 h12)) h88)) h88))) h88) (S h189)) h27) h64)) h188) h187) h186) h88
  let v195 := M v3 v1
  have h196 := h v195 z v3
  have h197 := C h9 (C (T (T (T h196 h194) h184) h183) h9)
  have h198 := h (M v2 (M v195 v2)) x v1
  have h199 := S h198
  have h200 := h v3 v2 v1
  have h201 := h (M x v7) x x
  have h202 := S h201
  let v203 := M x v8
  have h204 := h v203 x x
  have h205 := C (C h6 (T h4 (C (T h204 (C (C h6 (C h5 h6)) h6)) h6))) h6
  have h206 := C (T (T h205 h202) (C h6 (C h200 h6))) h21
  have h207 := C (T (T h206 h199) h197) h88
  have h208 := C (T (T (T h207 h181) h179) h113) h9
  have h209 := C h9 h208
  have h210 := C (C h6 (T (C (T (C (C h6 (C h4 h6)) h6) (S h204)) h6) h5)) h6
  have h211 := C (T (T (C h6 (C (S h200) h6)) h201) h210) h21
  have h212 := S h196
  have h213 := S h188
  have h214 := C (T (C h6 (T (C h111 h6) h123)) (C h6 (T h122 (C h52 h6)))) h9
  have h215 := C (T (T (T h185 h214) h213) (C h27 (T h63 (C (T h189 (C (C h88 (T (C (T (C (C h12 (C h190 h12)) h88) (S h193)) h88) h191)) h88)) h27)))) h88
  have h216 := C h156 h88
  have h217 := C (T h179 h113) h88
  have h218 := C h9 (C (T (T (T h217 h216) h215) h212) h9)
  have h219 := C (T (T h218 h198) h211) h88
  have h220 := h v115 v1 x
  have h221 := S h220
  have h222 := h v65 x x
  have h223 := S h222
  have h224 := C (C h6 (T h82 (C (T h165 (C h84 h6)) h6))) h6
  have h225 := C (T (T (T (C h27 (T (C (T h224 h223) h27) h64)) h188) h187) h186) h6
  have h226 := h (M x v1) z x
  have h227 := h x v2 v7
  have h228 := R v7
  have h229 := h y x v2
  have h230 := h v203 v1 x
  have h231 := h (M v1 v195) x x
  have h232 := h v3 v1 v1
  have h233 := S h232
  let v234 := M v1 (M v195 v1)
  have h235 := h v234 v3 v3
  have h236 := S h235
  let v237 := M x v3
  let v238 := M v237 x
  let v239 := M v238 v1
  have h240 := h v239 v2 v3
  have h241 := S h240
  have h242 := C (T (T (T h155 h182) h180) h219) h9
  have h243 := C h9 h242
  have h244 := T (T (T (T (T (T (T h97 h132) h131) h129) h126) h121) h119) h243
  have h245 := C (T (C (T (T (T (T (C h244 h88) h241) h206) h199) h197) h88) h219) h88
  have h246 := h (M v192 v3) v1 v3
  have h247 := T (T (T (T (T (T (T h209 h158) h120) h146) h145) h144) h101) h98
  have h248 := C (T h207 (C (T (T (T (T h218 h198) h211) h240) (C h247 h88)) h88)) h88
  have h249 := C (C h88 (T h248 (C (T h246 (C (C h21 (C (T (T (T (T (T h245 (C (T h207 h181) h88)) h217) h216) h215) h212) h21)) h88)) h88))) h88
  have h250 := h v239 v3 v3
  have h251 := T (T (T (T (T (T (C h21 (C (T (C (T (T h250 h249) h236) h21) h233) h21)) h231) (C (C h6 (T (C (T (C (C h21 (C h4 h21)) h6) (S h230)) h6) h5)) h6)) h205) h202) (C (T h37 (C h35 h229)) h228)) (S h227)
  have h252 := C h251 h21
  have h253 := h v239 v1 v1
  have h254 := S h250
  have h255 := C (C h88 (T (C (T (C (C h21 (C (T (T (T (T (T h196 h194) h184) h183) (C (T h180 h219) h88)) h248) h21)) h88) (S h246)) h88) h245)) h88
  have h256 := C h247 (T h232 (C (T (T (T (T (T (T h235 h255) h254) h253) h252) h226) h225) h21))
  have h257 := C (T (T (T (T h235 h255) h254) h240) h256) h6
  have h258 := C (T (T (T (T (T h257 h221) h116) h182) h180) h219) h9
  have h259 := C h9 h258
  have h260 := C (T (T (T (T (T (T h259 h209) h158) h120) h146) h145) h144) h6
  have h261 := h v234 v2 x
  have h262 := S h253
  have h263 := C (T (C h57 (S h229)) h48) h228
  have h264 := T (T (T (T (T (T h227 h263) h201) h210) (C (C h6 (T h4 (C (T h230 (C (C h21 (C h5 h21)) h6)) h6))) h6)) (S h231)) (C h21 (C (T h232 (C (T (T h235 h255) h254) h21)) h21))
  have h265 := C h264 h21
  have h266 := S h226
  have h267 := S h165
  have h268 := C (C h6 (T (C (T (C h85 h6) h267) h6) h83)) h6
  have h269 := C (T (T (T h185 h214) h213) (C h27 (T h63 (C (T h222 h268) h27)))) h6
  have h270 := C h244 (T (C (T (T (T (T (T (T h269 h266) h265) h262) h250) h249) h236) h21) h233)
  have h271 := C (T (T (T (T (T (T h270 h241) h250) h249) h236) h261) h260) h6
  have h272 := C (T (T (T (T h155 h147) h220) h271) h173) h6
  have h273 := C h117 h6
  have h274 := C h156 h6
  have h275 := S h261
  have h276 := C (T (T (T (T h270 h241) h250) h249) h236) h6
  have h277 := C (T (T (T (T (T h207 h181) h179) h147) h220) h276) h9
  have h278 := C h9 h277
  have h279 := C (T (T (T (T (T (T h131 h129) h126) h121) h119) h243) h278) h6
  have h280 := C (T (T (T (T (T (T h279 h275) h235) h255) h254) h240) h256) h6
  have h281 := C (T (T (T (T h176 h280) h221) h116) h113) h6
  have h282 := C (T (T (T (T (T (T (T (T h281 h274) h269) h266) h265) h262) h240) h256) (C h21 (C (T h273 h272) h21))) h6
  have h283 := C h6 (T (T h282 h178) h176)
  have h284 := C (T (T (T (T (T (T (T (T (C h21 (C (T h281 h274) h21)) h270) h241) h253) h252) h226) h225) h273) h272) h6
  have h285 := h v170 x x
  have h286 := S h285
  have h287 := C h6 (T (T h173 h177) h284)
  have h288 := C h287 h6
  have h289 := h v130 x x
  have h290 := C h251 (T (T (T (T (T (T h97 h132) h289) h288) h286) h177) h284)
  have h291 := C (T (C h6 (T (T (T (T (T (T (T (T (T (T (T h274 h269) h266) h265) h290) h283) h174) h171) h169) h167) h165) h162)) (C h6 (T h141 (C (T (T h84 h66) h81) h6)))) h9
  have h292 := h v89 x v2
  have h293 := S h289
  have h294 := C h283 h6
  have h295 := h v170 v0 v0
  have h296 := S h295
  have h297 := C h27 (T (C (T h140 h87) h27) h64)
  have h298 := C (T (T (T (T (T (T h297 h188) h187) h186) h220) h271) h173) h17
  have h299 := C h27 (T h63 (C (T h86 h161) h27))
  have h300 := C (T (T (T h185 h214) h213) h299) h17
  have h301 := T h300 h298
  have h302 := C h301 h17
  have h303 := C (T (T (T h297 h188) h187) h186) h17
  have h304 := h v71 z v0
  have h305 := C (T (T (T (T (T h160 h135) h143) h142) h304) h303) h17
  have h306 := h v164 z x
  have h307 := C (C h6 (T (C (T (C (C h27 (T (T h18 h56) (C h82 h23))) h6) (S h306)) h6) h83)) h6
  have h308 := h v114 x x
  have h309 := C (T (T h176 h280) h276) h9
  have h310 := T (T (T (T h309 h258) h208) h157) h111
  have h311 := C h310 h9
  have h312 := C (T (T h257 h271) h173) h9
  have h313 := C (T (T (T (T (T (T h309 h258) h208) h157) h111) h100) h103) h88
  have h314 := C h88 h313
  have h315 := C (T (T (T (T (T (T (T (T (T (T (T (T (T h314 h94) h93) h292) h291) h79) h77) h75) h25) h110) h118) h242) h277) h312) h9
  have h316 := h v170 v3 v2
  have h317 := C h17 (T (T (T (T (T (T (T (T (T (T (T (T (T (T h97 h132) h289) h288) h286) h316) h315) h311) h308) h307) h224) h223) h86) h305) h302)
  have h318 := C h317 h17
  have h319 := C (T (T (T (T (T (T (T (T (T h318 h296) h285) h294) h293) h131) h129) h126) h121) h119) h9
  let v320 := M v0 v1
  have h321 := h (M v320 v0) v0 v2
  have h322 := S h321
  have h323 := S h316
  have h324 := C (T (T (T (T (T (T h150 h128) h110) h118) h242) h277) h312) h88
  have h325 := C h88 h324
  have h326 := S h292
  have h327 := C h264 (T (T (T (T (T (T h282 h178) h285) h294) h293) h101) h98)
  have h328 := C h6 h176
  have h329 := S h171
  have h330 := C (T (C h6 (C h83 h6)) (C h6 (C h168 h6))) h6
  have h331 := C (T (C h6 (T (C (T (T h74 h67) h85) h6) h162)) (C h6 (T (T (T (T (T (T (T (T (T (T (T h141 h267) h166) h330) h329) h328) h287) h327) h252) h226) h225) h273))) h9
  have h332 := S h77
  have h333 := C (T h51 (C h27 (T h63 (C (T h66 h81) h27)))) h9
  have h334 := C (T (T (T (T (T (T (T (T (T (T (T (T (T h309 h258) h208) h157) h111) h24) h333) h332) h78) h331) h326) h154) h153) h325) h9
  have h335 := T (T (T (T h110 h118) h242) h277) h312
  have h336 := C h335 h9
  have h337 := S h308
  have h338 := C (C h6 (T h82 (C (T h306 (C (C h27 (T (T (C h83 h49) h34) h19)) h6)) h6))) h6
  have h339 := S h304
  have h340 := C (T (T (T (T (T h300 h339) h139) h138) h136) h134) h17
  have h341 := C (T (T (T (T (T (T h176 h280) h221) h185) h214) h213) h299) h17
  have h342 := T h341 h303
  have h343 := C h342 h17
  have h344 := C h17 (T (T (T (T (T (T (T (T (T (T (T (T (T (T h343 h340) h87) h222) h268) h338) h337) h336) h334) h323) h285) h294) h293) h101) h98)
  have h345 := C h344 h17
  have h346 := C (T (T (T (T (T (T (T (T (T h158 h120) h146) h145) h144) h289) h288) h286) h295) h345) h9
  have h347 := T h300 h339
  have h348 := C (T (T (T (T (T (T (C h9 (C h342 h9)) (C h9 (T (C h347 h9) h69))) h78) h331) h326) h90) h346) h17
  have h349 := h v170 v2 v0
  have h350 := C h17 (T (T (T (T (T (T (T (T (T (T (T h343 h340) h87) h222) h268) h338) h337) h336) h334) h323) h349) h348)
  have h351 := C (T h317 h350) h9
  have h352 := C (T h351 h322) h9
  have h353 := S h349
  have h354 := T h304 h303
  have h355 := C (T (T (T (T (T (T h319 h91) h292) h291) h79) (C h9 (T h68 (C h354 h9)))) (C h9 (C h301 h9))) h17
  have h356 := C h17 (T (T (T (T (T (T (T (T (T (T (T h355 h353) h316) h315) h311) h308) h307) h224) h223) h86) h305) h302)
  have h357 := C (T h356 h344) h9
  have h358 := C h9 h309
  have h359 := T (T (T (T (T (T (T (T (T (T (T (T (T h352 h319) h91) h292) h291) h79) h77) h75) h25) h110) h118) h242) h277) h312
  have h360 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (C h9 h359) h358) h259) h209) h158) h120) h146) h145) h144) h289) h288) h286) h295) h345) h321) h357) h9
  have h361 := h v320 v2 v2
  have h362 := h v0 x x
  have h363 := h v2 v0 x
  have h364 := S h363
  let v365 := M v2 x
  let v366 := M v0 (M v365 v0)
  have h367 := h v366 y x
  have h368 := h v366 x x
  have h369 := h (M x v365) x x
  have h370 := h v2 v0 v1
  have h371 := C (T (T (T (C h6 (C (S h370) h6)) h369) (C (C h6 (C (T (T (T (C (C h6 (C h363 h6)) h6) (S h368)) h367) (C (T (C h12 (T (C (T (T h364 h18) h56) h12) h36)) (C h12 h59)) h6)) h6)) h6)) (S h362)) h21
  let v372 := M v0 (M v76 v0)
  have h373 := h v372 x v1
  have h374 := h v372 x v0
  have h375 := S h374
  have h376 := S h373
  have h377 := C (T (T (T h362 (C (C h6 (C (T (T (T (C (T (C h12 h38) (C h12 (T h58 (C (T (T h34 h19) h363) h12)))) h6) (S h367)) h368) (C (C h6 (C h364 h6)) h6)) h6)) h6)) (S h369)) (C h6 (C h370 h6))) h21
  have h378 := h v115 v0 v0
  have h379 := h v163 v2 x
  have h380 := C (C h6 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h141 h267) h166) h330) h329) h328) h287) h327) h262) h250) h249) h236) h261) h260) h172) h379) (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h358 h259) h209) h158) h120) h146) h145) h144) h289) h288) h286) h176) h280) h221) h378) (C (T (T (T (C h17 h302) h344) h377) h376) h17)) h6))) h17
  have h381 := h v71 x v0
  have h382 := h v71 z x
  have h383 := C h347 h6
  have h384 := C h342 h6
  have h385 := S h381
  have h386 := C h9 h312
  have h387 := C (C h6 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (C (T (T (T h373 h371) h317) (C h17 h343)) h17) (S h378)) h220) h271) h173) h285) h294) h293) h131) h129) h126) h121) h119) h243) h278) h386) h6) (S h379)) h175) h279) h275) h235) h255) h254) h253) h290) h283) h174) h171) h169) h167) h165) h162)) h17
  have h388 := S h361
  have h389 := C (T h321 h357) h9
  have h390 := T (T (T (T (T (T (T (T (T (T (T (T (T h309 h258) h208) h157) h111) h24) h333) h332) h78) h331) h326) h90) h346) h389
  have h391 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h351 h322) h318) h296) h285) h294) h293) h131) h129) h126) h121) h119) h243) h278) h386) (C h9 h390)) h9
  have h392 := T (T (T (T (T (T (T (T h391 h388) h377) h376) h374) h387) h385) h304) h298
  have h393 := C h392 h6
  have h394 := C h390 h6
  have h395 := C h335 h6
  have h396 := T (T (T (T h395 h394) h393) h384) h383
  have h397 := C h396 h27
  have h398 := h x y z
  have h399 := S h398
  let v400 := M x z
  have h401 := h (M y (M v400 y)) v0 z
  have h402 := C h59 h17
  have h403 := C (C h27 (T (C (T (C (C h17 (T h402 (C h398 h17))) h27) (S h401)) h27) h399)) h27
  have h404 := h v14 z z
  have h405 := h v43 v3 x
  have h406 := C h59 h88
  have h407 := C (C h6 (T (C (T (C (C h88 (T h406 (C h40 h88))) h6) (S h405)) h6) h41)) h6
  have h408 := h (M v3 (M v13 v3)) x x
  have h409 := C h38 h88
  have h410 := C (C h12 (T (C (T (T (T (T (C h88 h409) h408) h407) h45) h16) h12) h11)) h409
  have h411 := h v3 y v237
  have h412 := T (T (T (T (T (T (T (T h411 h410) h408) h407) h45) h16) h404) h403) h397
  have h413 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h341 h339) h381) h380) h375) h373) h371) h361) h360) h352) h319) h91) h292) h291) h79) h77) h75) h25) h412
  have h414 := C h301 h88
  have h415 := C h354 h88
  have h416 := C h6 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (C (T (T h415 h414) h413) h6) (S h382)) h381) h380) h375) h373) h371) h361) h360) h352) h319) h91) h292) h291) h79) h77) h75) h25)
  have h417 := C h347 h88
  have h418 := C h342 h88
  have h419 := C h392 h88
  have h420 := C h389 h88
  have h421 := C (T (T (T (T (T (T (T (T (T (T (T (T h309 h258) h208) h157) h111) h24) h333) h332) h78) h331) h326) h90) h346) h88
  have h422 := C h6 (C (T (T (T (T (T h324 h421) h420) h419) h418) h417) h6)
  have h423 := C h6 (C h104 h6)
  let v424 := M z v3
  have h425 := h (M x (M v424 x)) x v3
  have h426 := S h425
  have h427 := h z x v3
  have h428 := h z z v3
  have h429 := C (T (C h6 (T (C (S h428) h6) h123)) (C h6 (T h122 (C h427 h6)))) h88
  let v430 := M z (M v424 z)
  have h431 := h v430 x v3
  have h432 := h v430 v3 x
  have h433 := S h432
  have h434 := S h411
  have h435 := S h408
  have h436 := C (C h6 (T h40 (C (T h405 (C (C h88 (T (C h41 h88) h409)) h6)) h6))) h6
  have h437 := C (C h6 (T (C (T (C (C h17 (T h402 (C h40 h17))) h6) (S h44)) h6) h41)) h6
  have h438 := C (C h12 (T h10 (C (T (T (T (T h15 h437) h436) h435) (C h88 h406)) h12))) h406
  have h439 := S h404
  have h440 := C (C h27 (T h398 (C (T h401 (C (C h17 (T (C h399 h17) h39)) h27)) h27))) h27
  have h441 := C h310 h6
  have h442 := C h359 h6
  have h443 := T (T (T (T (T (T (T (T h341 h339) h381) h380) h375) h373) h371) h361) h360
  have h444 := C h443 h6
  have h445 := C h301 h6
  have h446 := C h354 h6
  have h447 := T (T (T (T h446 h445) h444) h442) h441
  have h448 := C h447 h27
  let v449 := M z x
  have h450 := h v449 v0 x
  have h451 := S h450
  have h452 := h v449 y z
  have h453 := S h452
  have h454 := C (C h12 (T h10 (C (T h404 h403) h12))) h27
  have h455 := h v71 x v3
  have h456 := S h455
  have h457 := T (T (T (T (T (T (T (T h448 h440) h439) h15) h437) h436) h435) h438) h434
  have h458 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h24 h333) h332) h78) h331) h326) h90) h346) h389) h391) h388) h377) h376) h374) h387) h385) h304) h298) h457
  have h459 := C h6 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h24 h333) h332) h78) h331) h326) h90) h346) h389) h391) h388) h377) h376) h374) h387) h385) h382) (C (T (T h458 h418) h417) h6))
  have h460 := C h459 h88
  have h461 := h v400 v3 v3
  have h462 := S h461
  have h463 := C h416 h88
  have h464 := C h80 h88
  have h465 := C h88 (T (T (T (T h464 h415) h414) h413) (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h24 h333) h332) h78) h331) h326) h90) h346) h389) h391) h388) h377) h376) h374) h387) h385) h455) h463) h457))
  have h466 := C h73 h88
  have h467 := C h88 (T h417 h466)
  have h468 := C h88 h418
  have h469 := C h88 h419
  have h470 := C h88 h420
  have h471 := C h88 h421
  have h472 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h460 h456) h381) h380) h375) h373) h371) h361) h360) h352) h319) h91) h154) h153) h325) h471) h470) h469) h468) h467) h465) h88
  have h473 := C (T h472 h462) h88
  have h474 := C h88 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h473 h460) h456) h381) h380) h375) h373) h371) h361) h360) h352) h319) h91) h292) h291) h79) h77) h75) h25)
  have h475 := C (T (T (T (T (T (T (T (T (T (T (T (T h319 h91) h292) h291) h79) h77) h75) h25) h110) h118) h242) h277) h312) h88
  have h476 := C h88 h475
  have h477 := C h352 h88
  have h478 := C h88 h477
  have h479 := C h443 h88
  have h480 := C h88 h479
  have h481 := C h88 h414
  have h482 := C h88 (T h464 h415)
  have h483 := C h88 (T (T (T (T (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h460 h456) h381) h380) h375) h373) h371) h361) h360) h352) h319) h91) h292) h291) h79) h77) h75) h25) h412) h458) h418) h417) h466)
  have h484 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h483 h482) h481) h480) h478) h476) h314) h94) h93) h90) h346) h389) h391) h388) h377) h376) h374) h387) h385) h455) h463) h88
  have h485 := C (T h461 h484) h88
  have h486 := h (M v400 v3) v3 v3
  have h487 := S h486
  have h488 := C h88 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h24 h333) h332) h78) h331) h326) h90) h346) h389) h391) h388) h377) h376) h374) h387) h385) h455) h463) h485)
  have h489 := C (C h12 (T (C (T h440 h439) h12) h11)) h27
  have h490 := C (T (T (T (T (T (T (T h446 h445) h444) h442) h441) h452) h489) h488) h88
  have h491 := C h88 (T (T h490 h487) h485)
  have h492 := h (M v3 (M v449 v3)) x x
  have h493 := h z v3 x
  have h494 := h z y x
  have h495 := C h6 (T (C (S h494) h6) h123)
  have h496 := C h6 (T h122 (C h494 h6))
  have h497 := h z v1 x
  have h498 := h (M v1 (M v449 v1)) x x
  have h499 := C (T (T (T (T (T (T (T (T (T (C h21 (C h447 h21)) h498) (C (T (C h6 (T (C (S h497) h6) h123)) h496) h6)) (C (T h495 (C h6 (T h122 (C h493 h6)))) h6)) (S h492)) (C h88 (C h396 h88))) h491) h474) h454) h453) h6
  have h500 := h v71 v1 x
  have h501 := C h352 h17
  have h502 := C h389 h17
  have h503 := S h500
  have h504 := C (T (T (T (T (T (T (T h474 h454) h453) h395) h394) h393) h384) h383) h88
  have h505 := C h88 (T (T h473 h486) h504)
  have h506 := C (T (T (T (T (T (T (T (T (T h452 h489) h488) h505) (C h88 (C h447 h88))) h492) (C (T (C h6 (T (C (S h493) h6) h123)) h496) h6)) (C (T h495 (C h6 (T h122 (C h497 h6)))) h6)) (S h498)) (C h21 (C h396 h21))) h6
  have h507 := C (T (T (T (T (T (T (T (T (T (T h506 h503) h381) h380) h375) h373) h371) h317) h350) (C h17 h502)) (C h17 (T (T (T (T (T (T (T (T (T (T (T (T (T h501 h355) h353) h316) h315) h311) h308) h307) h224) h223) h86) h305) h302) (C (T (T (T h341 h339) h500) h499) h17)))) h6
  have h508 := C (T (T (T (T (T (T h507 h451) h395) h394) h393) h384) h383) h27
  have h509 := T (T (T (T (T (T (T (T (T h508 h448) h440) h439) h15) h437) h436) h435) h438) h434
  have h510 := S h431
  have h511 := C (T (C h6 (T (C (S h427) h6) h123)) (C h6 (T h122 (C h428 h6)))) h88
  have h512 := C h6 (C h151 h6)
  have h513 := C h6 (C (T (T (T (T (T h415 h414) h479) h477) h475) h313) h6)
  have h514 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h506 h503) h381) h380) h375) h373) h371) h361) h360) h352) h319) h91) h154) h153) h325) h471) h470) h469) h468) h467) h465) h88
  have h515 := T (T (T (T (T (T (T h514 h462) h459) h513) h512) h425) h511) h510
  have h516 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h24 h333) h332) h78) h331) h326) h90) h346) h389) h391) h388) h377) h376) h374) h387) h385) h500) h499) h509
  let v517 := M v449 x
  have h518 := h v517 z x
  have h519 := C (T (T (T (T (T (T (T (T (T (T (C h17 (T (T (T (T (T (T (T (T (T (T (T (T (T (C (T (T (T h506 h503) h304) h298) h17) h343) h340) h87) h222) h268) h338) h337) h336) h334) h323) h349) h348) h502)) (C h17 h501)) h356) h344) h377) h376) h374) h387) h385) h500) h499) h6
  have h520 := C (T (T (T (T (T (T h446 h445) h444) h442) h441) h450) h519) h27
  have h521 := T (T (T (T (T (T (T (T (T h411 h410) h408) h407) h45) h16) h404) h403) h397) h520
  have h522 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h506 h503) h381) h380) h375) h373) h371) h361) h360) h352) h319) h91) h292) h291) h79) h77) h75) h25) h521
  have h523 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h483 h482) h481) h480) h478) h476) h314) h94) h93) h90) h346) h389) h391) h388) h377) h376) h374) h387) h385) h500) h499) h88
  have h524 := T h472 h523
  have h525 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h506 h503) h381) h380) h375) h373) h371) h361) h360) h352) h319) h91) h154) h153) h325) h471) h470) h469) h468) h467) h465) (C h88 h524)) (C h88 (T h522 (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h24 h333) h332) h78) h331) h326) h90) h346) h389) h391) h388) h377) h376) h374) h387) h385) h500) h499) h518) (C h516 h6)) (C h515 h6)) h509)))) h6
  have h526 := T h514 h484
  have h527 := C h526 h88
  have h528 := C h88 (T (T (T h527 h473) h486) h504)
  have h529 := C h524 h88
  have h530 := h v517 v3 v3
  have h531 := S h530
  have h532 := C h88 (T (T (T h490 h487) h485) h529)
  have h533 := C (T (T (T (T (T (T h507 h451) h452) h489) h488) h505) h532) h88
  have h534 := C (T (T (T (T (T (T h528 h491) h474) h454) h453) h450) h519) h88
  have h535 := T (T (T (T (T (T (T h431 h429) h426) h423) h422) h416) h461) h523
  have h536 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (C h88 (T (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (C h535 h6) (C h522 h6)) (S h518)) h506) h503) h381) h380) h375) h373) h371) h361) h360) h352) h319) h91) h292) h291) h79) h77) h75) h25) h521) h516)) (C h88 h526)) h483) h482) h481) h480) h478) h476) h314) h94) h93) h90) h346) h389) h391) h388) h377) h376) h374) h387) h385) h500) h499) h6
  have h537 := C (T (T (T (T (T (T (T (T (T (T (T h411 h410) h408) h407) h45) h16) h404) h403) h397) h520) (C (T (T (T (T (T (T (T (T (T h525 h433) h431) h429) h426) h423) h422) h416) h461) h523) h27)) (C h515 h27)) (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h533 h531) h506) h503) h381) h380) h375) h373) h371) h361) h360) h352) h319) h91) h292) h291) h79) h77) h75) h25)
  have h538 := C h88 (T (T (T (T (T (T (T h527 h473) h460) h456) h500) h499) h530) h534)
  T (T (T (T (T (T h227 h263) h201) h210) (h v238 x x)) (C (C h6 (T (C (T (T (C (T (T h205 h202) (C h6 (C (h v3 v2 x) h6))) h6) (S (h (M v2 (M v7 v2)) x x))) (C h9 (C (T (h v7 z x) (C (T (T (T (C h27 (T (T (T (T (T (T (T (T (T (T (T (T (C (T (T (C (T (T (C (C h12 (T h10 (C (T h15 h437) h12))) h6) (S h46)) (C h6 (T h40 (C (T h47 (C (C h27 (T (C h41 h27) h62)) h6)) h6)))) h6) (S h61)) (C h27 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h60 h459) h513) h512) h425) h511) h510) h432) h536) h507) h451) h452) h489) h488) h505) h532) h538) h537))) h27) (S (h v430 z z))) h432) h536) h507) h451) h452) h489) h488) h505) h532) h538) h537)) (C h27 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (C (T (T (T (T (T (T (T (T (T (T (T (C h535 h27) (C (T (T (T (T (T (T (T (T (T h514 h462) h459) h513) h512) h425) h511) h510) h432) h536) h27)) h508) h448) h440) h439) h15) h437) h436) h435) h438) h434) (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h24 h333) h332) h78) h331) h326) h90) h346) h389) h391) h388) h377) h376) h374) h387) h385) h500) h499) h530) h534)) (C h88 (T (T (T (T (T (T (T h533 h531) h506) h503) h455) h463) h485) h529))) h528) h491) h474) h454) h453) h450) h519) h525) h433) h431) h429) h426) h423) h422) h416) h62))) h61) (C (T (T (C h6 (T (C (T (C (C h27 (T h60 (C h40 h27))) h6) (S h47)) h6) h41)) h46) (C (C h12 (T (C (T h45 h16) h12) h11)) h6)) h6)) h6)) h9))) h6) (S (h v8 v2 x)))) h6)) h5

