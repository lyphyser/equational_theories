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
theorem Equation2308_implies_Equation4673 (G: Type _) [Magma G] (h: Equation2308 G) : Equation4673 G := fun x y z =>
  have h0 := R y
  let v1 := M x y
  let v2 := M v1 z
  have h3 := h z v2 v1
  have h4 := R x
  have h5 := C (C h4 (S h3)) h0
  let v6 := M v2 v1
  have h7 := h (M v2 (M z v6)) x y
  have h8 := R v6
  have h9 := h z v1 v1
  have h10 := S h9
  have h11 := R v1
  let v12 := M v1 v1
  have h13 := h (M v1 (M z v12)) x y
  have h14 := T (C (C h4 h9) h0) (S h13)
  have h15 := C h14 h11
  have h16 := T h15 h10
  have h17 := R v2
  have h18 := C h17 (C h16 h8)
  have h19 := h v6 v1 z
  have h20 := S h19
  have h21 := R z
  let v22 := M x z
  let v23 := M v22 y
  let v24 := M v23 v1
  have h25 := h v24 v23 v2
  have h26 := S h25
  let v27 := M v23 v2
  have h28 := R v27
  have h29 := T h13 (C (C h4 h10) h0)
  have h30 := C h29 h11
  have h31 := T h9 h30
  have h32 := R v23
  have h33 := h (M v23 (M z v27)) v1 z
  have h34 := h z v23 v2
  have h35 := C (T (T (C (C h11 h34) h21) (S h33)) (C h32 (C h31 h28))) h17
  have h36 := C h11 (T (T (T h35 h26) h15) h10)
  have h37 := C (T (T (C h32 (C h16 h28)) h33) (C (C h11 (S h34)) h21)) h17
  have h38 := h v24 x v2
  have h39 := S h38
  let v40 := M x v2
  have h41 := R v40
  have h42 := h (M x (M z v40)) v1 z
  have h43 := h z x v2
  let v44 := M v2 z
  have h45 := h v44 v1 z
  have h46 := C h11 (T (T (T h9 h30) h25) h37)
  have h47 := C (T (T (T (T (C h46 h16) (S h45)) (C (C h11 h43) h21)) (S h42)) (C h4 (C h31 h41))) h17
  have h48 := C h11 (T (T (T h47 h39) h25) h37)
  have h49 := C (T (T (T (T (C h4 (C h16 h41)) h42) (C (C h11 (S h43)) h21)) h45) (C h36 h31)) h17
  have h50 := C h11 (T h38 h49)
  have h51 := T (T h50 h48) h36
  have h52 := h v1 z v1
  have h53 := S h52
  let v54 := M z v1
  let v55 := M v1 v54
  have h56 := h (M z v55) x y
  have h57 := S h56
  have h58 := h v1 y v1
  have h59 := C h4 (S h58)
  have h60 := C (T h59 (C h4 h52)) h0
  have h61 := C h4 h58
  have h62 := h v1 v23 v1
  have h63 := C (T (C h4 (S h62)) h61) h0
  have h64 := h (M v23 (M v1 v24)) x y
  have h65 := C h11 (T h47 h39)
  have h66 := C h11 (T (T (T h35 h26) h38) h49)
  have h67 := h v2 y z
  have h68 := S h67
  let v69 := M y z
  let v70 := M y (M v2 v69)
  have h71 := R v70
  have h72 := C h71 h16
  have h73 := C h32 (T (T (T (T h72 h68) h46) h66) h65)
  have h74 := C (T (T (T (T h73 h64) h63) h60) h57) h11
  have h75 := C h71 h31
  have h76 := h v2 x z
  have h77 := S h76
  have h78 := R (M x (M v2 v22))
  have h79 := C h78 h16
  have h80 := C h32 (T (T (T h79 h77) h67) h75)
  have h81 := C h80 h11
  have h82 := C h78 h31
  have h83 := h v2 v23 z
  have h84 := S h83
  let v85 := M v23 z
  have h86 := R (M v23 (M v2 v85))
  have h87 := C h86 h16
  have h88 := C h32 (T (T (T h87 h84) h76) h82)
  have h89 := C h88 h11
  have h90 := C h86 h31
  have h91 := h v2 v2 z
  have h92 := S h91
  have h93 := R (M v2 (M v2 v44))
  have h94 := C h93 h16
  have h95 := C h32 (T (T (T h94 h92) h83) h90)
  have h96 := C h95 h11
  have h97 := C h93 h31
  have h98 := h y v1 v23
  have h99 := S h98
  have h100 := h (M v1 (M y (M v1 v23))) v22 y
  have h101 := R v22
  have h102 := T (C (T (C (C h101 h98) h0) (S h100)) h32) h99
  have h103 := C h101 h102
  have h104 := T h98 (C (T h100 (C (C h101 h99) h0)) h32)
  have h105 := h v24 v23 v22
  have h106 := S h105
  let v107 := M v23 v22
  have h108 := R v107
  have h109 := h (M v23 (M z v107)) x z
  have h110 := h z v23 v22
  have h111 := C (T (T (C (C h4 h110) h21) (S h109)) (C h32 (C h31 h108))) h101
  have h112 := C (T (T (C h32 (C h16 h108)) h109) (C (C h4 (S h110)) h21)) h101
  have h113 := h v24 v23 v1
  have h114 := C h31 h31
  have h115 := C h32 h114
  have h116 := C (T (C h4 (T (T (T (C h115 h11) (S h113)) h105) h112)) (C h4 (T (T (T h111 h106) h15) h10))) h104
  let v117 := M z z
  let v118 := M v23 v117
  have h119 := h v118 x y
  have h120 := T (T h119 h116) h103
  have h121 := C h120 (T h91 h97)
  have h122 := h v2 v1 z
  have h123 := S h122
  let v124 := M v1 (M v2 v2)
  have h125 := R v124
  have h126 := C h125 h16
  have h127 := S h119
  have h128 := C h16 h16
  have h129 := C h32 h128
  have h130 := C (T (C h4 (T (T (T h9 h30) h105) h112)) (C h4 (T (T (T h111 h106) h113) (C h129 h11)))) h102
  have h131 := C h101 h104
  have h132 := T (T h131 h130) h127
  have h133 := C h132 (T h126 h123)
  have h134 := C (T h133 h121) h11
  have h135 := h v124 v23 v1
  have h136 := C h51 h17
  have h137 := C h11 h136
  have h138 := T (T h46 h66) h65
  have h139 := C h138 h17
  have h140 := h v70 v23 v1
  have h141 := C (T (T h140 h74) h53) h139
  have h142 := h v70 v2 v2
  have h143 := S h140
  have h144 := C h32 (T (T (T (T h50 h48) h36) h67) h75)
  have h145 := S h64
  have h146 := C (T h59 (C h4 h62)) h0
  have h147 := C (T (C h4 h53) h61) h0
  have h148 := C (T (T (T (T h56 h147) h146) h145) h144) h11
  have h149 := h v1 v22 v2
  have h150 := S h149
  let v151 := M v1 (M v22 v2)
  let v152 := M v22 v151
  have h153 := h v152 v1 z
  have h154 := S h153
  have h155 := C h11 h149
  have h156 := h v1 v23 v2
  have h157 := C (T (C h11 (S h156)) h155) h21
  let v158 := M v1 v27
  have h159 := h (M v23 v158) v1 z
  have h160 := h v158 v23 v1
  have h161 := R v158
  have h162 := h v23 v1 z
  have h163 := h v23 v23 z
  have h164 := S h163
  let v165 := M v23 v85
  let v166 := M v23 v165
  have h167 := R v166
  have h168 := C h167 h16
  have h169 := C h167 h31
  have h170 := h v118 z z
  have h171 := S h170
  have h172 := C h132 h128
  have h173 := C h21 (T h115 h172)
  have h174 := C h173 h16
  have h175 := h (M z v118) v23 v1
  have h176 := C h120 h114
  have h177 := C h21 (T h176 h129)
  have h178 := C h21 (T (T (T (T h131 h130) h127) h115) h172)
  have h179 := C h120 (T (T (T (T (T h178 h177) h175) (C (T (C h132 (T (T (T (T h174 h171) h119) h116) h103)) (C h120 (T h163 h169))) h11)) (C (C h32 (T (T (T h168 h164) h162) (C h161 h31))) h11)) (S h160))
  let v180 := M z v23
  have h181 := R v180
  have h182 := C h132 h181
  have h183 := T (T (T (T h182 h179) h159) h157) h154
  have h184 := C h183 h17
  have h185 := C h120 h181
  have h186 := C h21 (T (T (T (T h176 h129) h119) h116) h103)
  have h187 := S h175
  have h188 := C (T (C h132 (T h168 h164)) (C h120 (T (T (T (T h131 h130) h127) h170) (C h177 h31)))) h11
  have h189 := C h132 (T (T (T (T (T h160 (C (C h32 (T (T (T (C h161 h16) (S h162)) h163) h169)) h11)) h188) h187) h173) h186)
  have h190 := S h159
  have h191 := C h11 h150
  have h192 := C (T h191 (C h11 h156)) h21
  have h193 := h v1 x v2
  have h194 := C (T (C h11 (S h193)) h155) h21
  let v195 := M v1 v40
  have h196 := h (M x v195) v1 z
  have h197 := h v195 v23 v1
  have h198 := R v195
  have h199 := h x v1 z
  have h200 := h x v23 z
  have h201 := S h200
  have h202 := R (M v23 (M x v85))
  have h203 := C h202 h16
  have h204 := C h202 h31
  have h205 := h x z z
  have h206 := S h205
  have h207 := R (M z (M x v117))
  have h208 := C h207 h16
  have h209 := C h207 h31
  have h210 := h x v2 z
  have h211 := S h210
  have h212 := R (M v2 (M x v44))
  have h213 := C h212 h16
  have h214 := C h212 h31
  have h215 := h x y z
  have h216 := S h215
  have h217 := R (M y (M x v69))
  have h218 := C h217 h16
  have h219 := C h217 h31
  have h220 := h x x z
  have h221 := S h220
  let v222 := M x (M x v22)
  have h223 := R v222
  have h224 := C h223 h16
  have h225 := C h223 h31
  have h226 := C (C h32 (T h220 h225)) h11
  have h227 := C h4 (T (T (T (T (T (T h226 (C (C h32 (T (T (T h224 h221) h215) h219)) h11)) (C (C h32 (T (T (T h218 h216) h210) h214)) h11)) (C (C h32 (T (T (T h213 h211) h205) h209)) h11)) (C (C h32 (T (T (T h208 h206) h200) h204)) h11)) (C (C h32 (T (T (T h203 h201) h199) (C h198 h31))) h11)) (S h197))
  have h228 := C (C h32 (T h224 h221)) h11
  have h229 := h v222 v23 v1
  have h230 := C h4 (T h229 h228)
  have h231 := h (M x v222) x z
  have h232 := S h231
  have h233 := h x x v22
  have h234 := h x v22 v22
  have h235 := S h234
  have h236 := C h4 h235
  have h237 := C (T h236 (C h4 h233)) h21
  let v238 := M x (M v22 v22)
  have h239 := h (M v22 v238) x z
  have h240 := C (T (T (T (T (T (T (T (T (T (T h239 h237) h232) h230) h227) h196) h194) h192) h190) h189) h185) h17
  have h241 := S h239
  have h242 := C h4 h234
  have h243 := h x v1 v22
  have h244 := C (T (C h4 (S h243)) h242) h21
  let v245 := M x (M v1 v22)
  have h246 := h (M v1 v245) x z
  have h247 := h v245 v23 v1
  have h248 := R v245
  have h249 := h v1 x z
  have h250 := h v1 y z
  have h251 := S h250
  have h252 := R (M y (M v1 v69))
  have h253 := C h252 h16
  have h254 := C h252 h31
  have h255 := h v1 v2 z
  have h256 := S h255
  have h257 := R (M v2 (M v1 v44))
  have h258 := C h257 h16
  have h259 := C h257 h31
  have h260 := h v1 v23 z
  have h261 := S h260
  have h262 := R (M v23 (M v1 v85))
  have h263 := C h262 h16
  have h264 := C h262 h31
  have h265 := h z x v1
  let v266 := M x v1
  have h267 := h (M x (M z v266)) x y
  have h268 := R v266
  have h269 := h v24 x v1
  have h270 := h v1 z z
  have h271 := S h270
  let v272 := M z (M v1 v117)
  have h273 := R v272
  have h274 := C h273 h16
  have h275 := C h14 (T h274 h271)
  have h276 := C h273 h31
  have h277 := h v272 v23 v1
  have h278 := C h29 (T h270 h276)
  have h279 := C (T (C (T h9 h278) h11) (S h277)) h16
  have h280 := C (T h277 (C (T h275 h10) h11)) h31
  have h281 := h v1 v22 z
  let v282 := M v22 z
  have h283 := R (M v22 (M v1 v282))
  have h284 := C h32 (T (T (T (C h283 h16) (S h281)) h270) h280)
  have h285 := C h32 (T (T (T h279 h271) h281) (C h283 h31))
  have h286 := h v54 v23 v1
  have h287 := C h11 (T (T (T (T (T (T (T h286 (C h285 h11)) (C (T (T (T h284 (C h32 (T h279 h276))) h275) h30) h11)) (C (T h269 (C (T (T (C h4 (C h16 h268)) h267) (C (C h4 (S h265)) h0)) (T h260 h264))) h11)) (C (C h32 (T (T (T h263 h261) h255) h259)) h11)) (C (C h32 (T (T (T h258 h256) h250) h254)) h11)) (C (C h32 (T (T (T h253 h251) h249) (C h248 h31))) h11)) (S h247))
  have h288 := T (T (T h287 h246) h244) h241
  have h289 := C h288 h17
  have h290 := C h11 (T (T (T (T (T (T (T h247 (C (C h32 (T (T (T (C h248 h16) (S h249)) h250) h254)) h11)) (C (C h32 (T (T (T h253 h251) h255) h259)) h11)) (C (C h32 (T (T (T h258 h256) h260) h264)) h11)) (C (T (C (T (T (C (C h4 h265) h0) (S h267)) (C h4 (C h31 h268))) (T h263 h261)) (S h269)) h11)) (C (T (T (T h15 h278) (C h32 (T h274 h280))) h285) h11)) (C h284 h11)) (S h286))
  have h291 := S h246
  have h292 := C (T h236 (C h4 h243)) h21
  have h293 := T (T (T h239 h292) h291) h290
  have h294 := C h293 h17
  have h295 := C (T (C h4 (S h233)) h242) h21
  have h296 := C h4 (T h226 (S h229))
  have h297 := C h4 (T (T (T (T (T (T h197 (C (C h32 (T (T (T (C h198 h16) (S h199)) h200) h204)) h11)) (C (C h32 (T (T (T h203 h201) h205) h209)) h11)) (C (C h32 (T (T (T h208 h206) h210) h214)) h11)) (C (C h32 (T (T (T h213 h211) h215) h219)) h11)) (C (C h32 (T (T (T h218 h216) h220) h225)) h11)) h228)
  have h298 := S h196
  have h299 := C (T h191 (C h11 h193)) h21
  have h300 := C (T (T (T (T (T (T (T (T (T (T h182 h179) h159) h157) h299) h298) h297) h296) h231) h295) h241) h17
  have h301 := T (T (T (T h153 h192) h190) h189) h185
  have h302 := C h301 h17
  have h303 := h v12 v23 v1
  have h304 := h v152 x z
  have h305 := S h304
  have h306 := C h183 h101
  have h307 := C h4 h306
  have h308 := h x y v22
  have h309 := S h308
  have h310 := h (M y (M x (M y v22))) x z
  have h311 := C (T (T (T (T (T (T (T (T (T (T (T h310 (C (T (C h4 h309) h242) h21)) h237) h232) h230) h227) h196) h194) h192) h190) h189) h185) h101
  have h312 := C h4 (T h308 h311)
  have h313 := C (T h312 h307) h16
  have h314 := h (M x x) v23 v1
  have h315 := C (T (T (T (T (T (T (T (T (T (T (T h182 h179) h159) h157) h299) h298) h297) h296) h231) h295) (C (T h236 (C h4 h308)) h21)) (S h310)) h101
  have h316 := C h4 (T h315 h309)
  have h317 := C h301 h101
  have h318 := C h4 h317
  have h319 := C (T (T (T (T (T (T (T (T (T (C h4 (T (T (T (T (C h288 h101) h235) h308) h311) h306)) h318) h316) h314) (C (C h32 (T (T (T h313 h305) h153) (C h191 h31))) h11)) (S h303)) (C h11 (T h149 h302))) (C h11 h300)) (C h11 h294)) (C h11 (T (T (T (T (T (T (T (T h289 h240) h184) h150) h52) h148) h143) h142) (C (T (C h138 (T (T (T (T (T (T (T (T h141 h137) h135) h134) h96) h89) h81) h74) h53)) (C h51 h11)) h17)))) h21
  have h320 := h v55 x z
  have h321 := C h125 h31
  have h322 := h v2 v22 z
  have h323 := S h322
  have h324 := R (M v22 (M v2 v282))
  have h325 := C h324 h16
  have h326 := C h324 h31
  have h327 := h v2 z z
  have h328 := S h327
  have h329 := R (M z (M v2 v117))
  have h330 := C h329 h16
  have h331 := C h329 h31
  have h332 := C h51 (T (T (T (T (T (T (T (T (T (T (T (T (T (C h32 (T h327 h331)) (C h32 (T (T (T h330 h328) h322) h326))) (C h32 (T (T (T h325 h323) h122) h321))) h133) h121) h95) h88) h80) h73) h64) h63) h60) h57) (C h31 (T (T h320 h319) h20)))
  have h333 := C h138 h28
  have h334 := h v22 v23 z
  have h335 := R (M v23 (M v22 v85))
  have h336 := C h51 h28
  have h337 := C h120 (T h122 h321)
  have h338 := C h132 (T h94 h92)
  have h339 := C h32 (T (T (T h87 h84) h91) h97)
  have h340 := C h32 (T (T (T h79 h77) h83) h90)
  have h341 := C h32 (T (T (T h72 h68) h76) h82)
  have h342 := S h320
  have h343 := C (T h318 h316) h31
  have h344 := C (C h32 (T (T (T (C h155 h16) h154) h304) h343)) h11
  have h345 := C h51 (T (T (T (T (T (T (T (T h52 h148) (C h341 h11)) (C h340 h11)) (C h339 h11)) (C (T h338 h337) h11)) (S h135)) (C h11 h139)) (C (T (T h52 h148) h143) h136))
  have h346 := C h138 h11
  have h347 := C (T (T (T (T (T (T (T (T (T (C h11 (T (T (T (T (T (T (T (T (C (T h346 h345) h17) (S h142)) h140) h74) h53) h149) h302) h300) h294)) (C h11 h289)) (C h11 h240)) (C h11 (T h184 h150))) h303) h344) (S h314)) h312) h307) (C h4 (T (T (T (T h317 h315) h309) h234) (C h293 h101)))) h21
  have h348 := C h138 (T (T (T (T (T (T (T (T (T (T (T (T (T (C h16 (T (T h19 h347) h342)) h56) h147) h146) h145) h144) h341) h340) h339) h338) h337) (C h32 (T (T (T h126 h123) h322) h326))) (C h32 (T (T (T h325 h323) h327) h331))) (C h32 (T h330 h328)))
  have h349 := C h17 (C h31 h8)
  have h350 := S h7
  have h351 := C (C h4 h3) h0
  have h352 := T (T (T (T h351 h350) h349) h348) h336
  have h353 := h v22 v1 z
  have h354 := R v151
  have h355 := h v22 v22 z
  have h356 := R (M v22 (M v22 v282))
  have h357 := h v22 y z
  have h358 := R (M y (M v22 v69))
  have h359 := h v22 v2 z
  have h360 := R (M v2 (M v22 v44))
  have h361 := h v22 z z
  have h362 := S h361
  have h363 := R (M z (M v22 v117))
  have h364 := C h363 h16
  have h365 := C h363 h31
  have h366 := h v22 x z
  have h367 := S h366
  have h368 := R v238
  have h369 := C h368 h16
  have h370 := C h368 h31
  have h371 := h v118 y z
  have h372 := R v69
  have h373 := R v85
  have h374 := h z v22 z
  have h375 := S h374
  have h376 := R (M v22 (M z v282))
  have h377 := C h376 h16
  have h378 := C h32 (T h377 h375)
  have h379 := C h376 h31
  have h380 := h z v2 z
  have h381 := S h380
  have h382 := R (M v2 (M z v44))
  have h383 := C h382 h16
  have h384 := C h32 (T (T (T h383 h381) h374) h379)
  have h385 := C h382 h31
  have h386 := C h120 (T (T (T h15 h10) h380) h385)
  have h387 := h v23 v2 v1
  have h388 := C h4 (S h387)
  have h389 := h v23 v23 v1
  have h390 := h (M v23 (M v23 v24)) x y
  have h391 := h v24 x z
  have h392 := S h391
  have h393 := C (C h4 (C h31 h101)) h16
  have h394 := C (C h4 (C h16 h101)) h31
  have h395 := h v24 z z
  have h396 := S h395
  have h397 := R v117
  have h398 := C (C h21 (C h31 h397)) h16
  have h399 := C (C h21 (C h16 h397)) h31
  have h400 := h v24 v1 z
  have h401 := S h400
  have h402 := C (C h11 (C h31 h17)) h16
  have h403 := C (C h11 (C h16 h17)) h31
  have h404 := h v24 y z
  have h405 := S h404
  have h406 := C (C h0 (C h31 h372)) h16
  have h407 := C (C h0 (C h16 h372)) h31
  have h408 := h v24 v23 z
  have h409 := S h408
  have h410 := C (C h32 (C h31 h373)) h16
  have h411 := C (C h32 (C h16 h373)) h31
  have h412 := T (T (T (T h333 h332) h18) h7) h5
  let v413 := M v23 v6
  have h414 := C h120 h8
  have h415 := C (T (T (T (T (T (T (T h333 h332) h18) h7) h5) h131) h130) h127) h8
  have h416 := C (T (T (T (T (T (T (T h119 h116) h103) h351) h350) h349) h348) h336) h8
  have h417 := C h132 h8
  have h418 := S (h v413 x y)
  have h419 := C (C h4 (T (T h303 h344) (C (T (T (C h352 (T (T (T (T (T (T (T (T (T (T (T (T (T (T h313 h305) h153) h299) h298) h297) h296) h231) h295) h292) h291) h290) h320) h319) h20)) h415) h414) h11))) h0
  have h420 := h v1 x y
  T (T (T (T (T (T (T (T h67 h75) (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h140 h74) h53) h420) h419) h418) h417) h416) (C h412 (T (T (T (T (T (T (T (T (T (T (T (T (T (T h19 h347) h342) h287) h246) h244) h237) h232) h230) h227) h196) h194) h154) h304) h343))) (C h32 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h313 h305) h153) h299) h298) h297) h296) h231) h295) h292) h291) h290) h320) h319) h20) h346) h345) (C h17 (T (T (T (T (T (T (T (T (T (T (T (T (T h141 h137) h135) h134) h96) h89) h81) h74) h53) h420) h419) h418) h417) h416))) (C h17 h415)) (C h17 h414)) (h (M v2 v413) x y)) (C (T h388 (C h4 h389)) h0)) (S h390)) (C h352 (T (T (T (T (T (T (T (T (C h32 (T h391 h394)) (C h32 (T (T (T h393 h392) h395) h399))) (C h32 (T (T (T h398 h396) h400) h403))) (C h32 (T (T (T h402 h401) h404) h407))) (C h32 (T (T (T h406 h405) h408) h411))) (C h132 (T h410 h409))) h386) h384) h378))))) (C h32 (T (T (T (T (C h412 (T (T (T (T (T (T (T (T (C h32 (T h374 h379)) (C h32 (T (T (T h377 h375) h380) h385))) (C h132 (T (T (T h383 h381) h9) h30))) (C h120 (T h408 h411))) (C h32 (T (T (T h410 h409) h404) h407))) (C h32 (T (T (T h406 h405) h400) h403))) (C h32 (T (T (T h402 h401) h395) h399))) (C h32 (T (T (T h398 h396) h391) h394))) (C h32 (T h393 h392)))) h390) (C (T (C h4 (S h389)) (C h4 h387)) h0)) (C (T h388 (C h4 (T (T (T (T h131 h130) h127) (h v118 v23 v1)) (C (T (C h132 (T (T h386 h384) h378)) (C h120 h373)) h11)))) h0)) (S (h v165 x y))))) (h v166 v23 v1)) h188) h187) h173) h186) (h v180 v23 v1)) (C (C h32 (T (T (T (T (T (T (C (T (T (T (T (T h178 h177) h175) (C (C h32 (T (T (T h174 h171) h371) (C (C h0 (C h120 h372)) h31))) h11)) (C (C h32 (T (T (T (C (C h0 (C h132 h372)) h16) (S h371)) (h v118 v22 z)) (C (C h101 (C h120 (R v282))) h31))) h11)) (S (h (M v22 (M v23 v282)) v23 v1))) h16) (S (h v23 v22 z))) h131) h130) h127) (h v118 x z)) (C (C h4 (T (T (C h120 (T h361 h365)) (C h32 (T (T (T h364 h362) h366) h370))) (C h32 (T h369 h367)))) h31))) h11)) (S (h (M x v107) v23 v1))) (C h4 (T (T (C h32 (T h366 h370)) (C h32 (T (T (T h369 h367) h361) h365))) (C h132 (T h364 h362))))) (C h4 (T (T (T (T (T (C h120 (T h359 (C h360 h31))) (C h32 (T (T (T (C h360 h16) (S h359)) h357) (C h358 h31)))) (C h32 (T (T (T (C h358 h16) (S h357)) h355) (C h356 h31)))) (C h32 (T (T (T (C h356 h16) (S h355)) h353) (C h354 h31)))) (C h32 (T (T (T (C h354 h16) (S h353)) h334) (C h335 h31)))) (C h352 (T (C h335 h16) (S h334)))))) h16)) (S (h (M v2 v27) x z))) h333) h332) h18) h7) h5

