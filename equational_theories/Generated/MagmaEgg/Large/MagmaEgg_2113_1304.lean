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
theorem Equation2113_implies_Equation1304 (G: Type _) [Magma G] (h: Equation2113 G) : Equation1304 G := fun x y z =>
  let v0 := M x z
  let v1 := M v0 z
  let v2 := M v1 y
  have h3 := R v2
  let v4 := M y v2
  have h5 := h y y v4
  have h6 := S h5
  have h7 := R (M y v4)
  have h8 := R v4
  let v9 := M y y
  have h10 := h v9 v0 z
  have h11 := S h10
  let v12 := M (M v0 v1) z
  have h13 := h v1 v12 v1
  have h14 := S h13
  have h15 := h v1 v0 z
  have h16 := R v1
  have h17 := C (C h15 h16) h15
  let v18 := M z v2
  let v19 := M v1 v1
  have h20 := h v19 v0 v18
  have h21 := S h20
  have h22 := R v18
  have h23 := h v0 v1 y
  have h24 := S h23
  have h25 := R y
  have h26 := h z x z
  have h27 := C (C h26 h25) h3
  have h28 := h y z v2
  have h29 := R z
  have h30 := h v0 z z
  let v31 := M z z
  have h32 := R v31
  have h33 := S h26
  have h34 := R v0
  have h35 := h v0 v1 v0
  have h36 := C (C (T (C (T h35 (C (C h33 h34) h33)) h32) (S h30)) h29) h16
  have h37 := h v31 v0 z
  let v38 := M v0 v2
  have h39 := h v1 (M v38 z) v1
  have h40 := S h39
  have h41 := h v2 v0 z
  have h42 := C (C h41 h16) h41
  let v43 := M (M v2 v1) v2
  have h44 := h v43 v4 v4
  have h45 := S h44
  let v46 := M v4 v4
  have h47 := R v46
  have h48 := S h41
  have h49 := C (C h48 h16) h48
  have h50 := h v4 v0 z
  have h51 := S h50
  have h52 := h v1 (M (M v0 v4) z) v1
  have h53 := T (T h52 (C (C h51 h16) h51)) (C (C h8 (T h39 h49)) h8)
  have h54 := C h53 h47
  have h55 := T (T (T h54 h45) h42) h40
  have h56 := C h55 h34
  have h57 := C (T h56 h33) h33
  have h58 := h v46 v1 v0
  have h59 := h y v2 v2
  let v60 := M v2 v2
  have h61 := R v60
  have h62 := h y v1 y
  have h63 := C (C (T (C h62 h61) (S h59)) h3) h8
  have h64 := h v60 y v2
  have h65 := T (T (T (T (T h64 h63) h58) h57) h37) h36
  let v66 := M x v2
  have h67 := h v0 (M v66 z) v0
  have h68 := S h67
  have h69 := h v2 x z
  have h70 := C (C h69 h34) h69
  have h71 := C (T h70 h68) h65
  have h72 := h v0 v2 v2
  have h73 := C (T (T (T h27 h24) h72) h71) h22
  have h74 := C (T h28 h73) (T h28 (C (T h27 h24) h22))
  have h75 := T h74 h21
  have h76 := C h75 h16
  have h77 := T (T h76 h17) h14
  have h78 := S h28
  have h79 := C (C h33 h25) h3
  have h80 := S h72
  have h81 := S h64
  have h82 := S h62
  have h83 := C (C (T h59 (C h82 h61)) h3) h8
  have h84 := S h58
  have h85 := T (T (C (C h8 (T h42 h40)) h8) (C (C h50 h16) h50)) (S h52)
  have h86 := C h85 h47
  have h87 := T (T (T h39 h49) h44) h86
  have h88 := C h87 h34
  have h89 := C (T h26 h88) h26
  have h90 := S h37
  have h91 := C (C (T h30 (C (T (C (C h26 h34) h26) (S h35)) h32)) h29) h16
  have h92 := T (T (T (T (T h91 h90) h89) h84) h83) h81
  have h93 := S h69
  have h94 := C (C h93 h34) h93
  have h95 := C (T h67 h94) h92
  have h96 := C (T (T (T h95 h80) h23) h79) h22
  have h97 := C (T h96 h78) (T (C (T h23 h79) h22) h78)
  have h98 := T h20 h97
  have h99 := C (T h95 h80) h98
  have h100 := C (T (T (T h70 h68) h72) h71) h65
  have h101 := T (T h72 h100) h99
  have h102 := C (C h101 h29) h77
  have h103 := C h98 h16
  have h104 := S h15
  have h105 := C (C h104 h16) h104
  have h106 := T (T h13 h105) h103
  have h107 := C (T (T (T h95 h80) h67) h94) h92
  have h108 := C (T h72 h71) h75
  have h109 := T (T h108 h107) h80
  have h110 := C (C h109 h29) h106
  have h111 := h v9 z v0
  have h112 := S h111
  let v113 := M z v0
  have h114 := R v113
  let v115 := M x v0
  have h116 := h v0 (M v115 z) v0
  have h117 := S h116
  have h118 := h v0 x z
  let v119 := M v0 v0
  have h120 := h v119 z x
  let v121 := M z x
  have h122 := R v121
  have h123 := R x
  have h124 := R v119
  have h125 := h z v0 v0
  have h126 := h z v1 v1
  have h127 := S h126
  have h128 := R v19
  have h129 := h z v0 z
  have h130 := h v19 z x
  have h131 := C (T (T (T h130 (C (T (C (T (C h129 h128) h127) h123) (C (T h125 (C h33 h124)) h123)) h122)) (S h120)) (C h118 h34)) h118
  have h132 := T (T (T h102 h11) h74) h21
  have h133 := C h132 h34
  have h134 := h v0 (M (M x v1) z) v0
  have h135 := S h134
  have h136 := h v1 x z
  have h137 := C (T h26 (C h136 h34)) h136
  have h138 := T h137 h135
  have h139 := h (M v9 v1) v1 z
  have h140 := S h139
  let v141 := M v1 z
  have h142 := R v141
  have h143 := T (T (T h20 h97) h10) h110
  have h144 := C h143 h29
  have h145 := h z v1 v0
  let v146 := M v141 v0
  have h147 := R v146
  have h148 := T (C h147 h26) (S h145)
  have h149 := C (T (T (C h148 h29) h37) h36) h148
  have h150 := h z v146 z
  have h151 := C (T (T h150 h149) h144) h142
  have h152 := C (C (T (T (T (T h151 h140) h76) h17) h14) h106) h138
  have h153 := h v141 z v1
  have h154 := T (T (T (T h153 h152) h133) h131) h117
  have h155 := S h129
  have h156 := C h155 h98
  have h157 := S h150
  have h158 := T h145 (C h147 h33)
  have h159 := C (T (T h91 h90) (C h158 h29)) h158
  have h160 := C h132 h29
  have h161 := C (T (T (T (T h160 h159) h157) h126) h156) h154
  have h162 := C (T (T (T (T h13 h105) h103) h139) h161) h114
  have h163 := C h129 h75
  have h164 := T h163 h127
  have h165 := C h164 h34
  have h166 := S h153
  have h167 := S h136
  have h168 := C (T (C h167 h34) h33) h167
  have h169 := T h134 h168
  have h170 := C (T (T h160 h159) h157) h142
  have h171 := C (C (T (T (T (T h13 h105) h103) h139) h170) h77) h169
  have h172 := C h143 h34
  have h173 := S h118
  have h174 := C (T (T (T (C h173 h34) h120) (C (T (C (T (C h26 h124) (S h125)) h123) (C (T h126 (C h155 h128)) h123)) h122)) (S h130)) h173
  have h175 := T (T (T (T h116 h174) h172) h171) h166
  have h176 := C (T (T (T (T h163 h127) h150) h149) h144) h175
  have h177 := T h126 h156
  have h178 := C h177 h34
  have h179 := h v113 v2 v4
  have h180 := S h179
  have h181 := R (M v2 v4)
  have h182 := T (T (T (T (T h13 h105) h103) h139) h161) h165
  have h183 := h v2 (M v141 y) v2
  have h184 := h z v1 y
  have h185 := h v2 v0 y
  have h186 := S h185
  have h187 := h z v0 y
  have h188 := S h187
  let v189 := M v0 y
  have h190 := R v189
  have h191 := h v189 (M v38 y) v189
  have h192 := h v189 v2 v0
  have h193 := S h192
  let v194 := M v2 v0
  have h195 := R v194
  have h196 := C (T (T (T (T (T (T h13 h105) h103) h139) h161) h165) (C h187 h34)) h195
  have h197 := C (T (T (T (T (T (T (C h188 h34) h178) h176) h140) h76) h17) h14) h195
  have h198 := h v189 v2 x
  have h199 := S h198
  let v200 := M v2 x
  have h201 := R v200
  have h202 := h v121 z v4
  have h203 := R (M z v4)
  let v204 := M (M v1 x) v0
  have h205 := h z v204 z
  have h206 := S h205
  have h207 := R v204
  have h208 := h x v1 v0
  have h209 := T h208 (C h207 h33)
  have h210 := C (C h209 h29) h209
  have h211 := C h164 h16
  have h212 := T (T (T (T (T h178 h176) h140) h76) h17) h14
  have h213 := C h177 h212
  have h214 := T (T (T (T (T (T h213 h211) h137) h135) h72) h100) h99
  have h215 := C (T (T (T (C h214 h123) (C h109 h123)) h210) h206) h122
  have h216 := h v113 z x
  have h217 := C (T (T (T (T h151 h161) h165) h216) h215) h8
  have h218 := h v141 z v4
  have h219 := T (T (T (T (T (T (T (T h116 h174) h172) h171) h166) h218) (C h217 h203)) (S h202)) (C h187 h123)
  have h220 := C h219 h201
  have h221 := T (T (T h220 h199) h192) h197
  have h222 := C (T (T (T (C h221 h29) (C (T (T (T h196 h193) h191) (C (T (C h186 h190) h188) h186)) h29)) (C (C h184 h3) h184)) (S h183)) h182
  have h223 := h v200 v0 z
  have h224 := C (C (T h223 h222) h8) h181
  have h225 := h x v2 v4
  have h226 := T (T (T (T (T (T (T (T h225 h224) h180) h178) h176) h140) h76) h17) h14
  have h227 := C h226 (T (T (T (T (T (T (T h42 h40) h13) h105) h103) h139) h161) h165)
  have h228 := S h223
  have h229 := S h216
  have h230 := C h164 h182
  have h231 := C h177 h16
  have h232 := T (T (T (T (T (T h108 h107) h80) h134) h168) h231) h230
  have h233 := T (C h207 h26) (S h208)
  have h234 := C (C h233 h29) h233
  have h235 := C (T (T (T h205 h234) (C h101 h123)) (C h232 h123)) h122
  have h236 := C (T (T (T (T h235 h229) h178) h176) h170) h8
  have h237 := T (T (T (T (T (T (T (T (C h188 h123) h202) (C h236 h203)) (S h218)) h153) h152) h133) h131) h117
  have h238 := C h237 h201
  have h239 := T (T (T h196 h193) h198) h238
  have h240 := S h184
  have h241 := C (T (T (T h183 (C (C h240 h3) h240)) (C (T (T (T (C (T h187 (C h185 h190)) h185) (S h191)) h192) h197) h29)) (C h239 h29)) h212
  have h242 := T (T (T (T (T (T (T (T h13 h105) h103) h139) h161) h165) h179) (C (C (T h241 h228) h8) h181)) (S h225)
  have h243 := C h242 (T (T (T (T (T (T (T h178 h176) h140) h76) h17) h14) h39) h49)
  have h244 := C (T (T (T (T h176 h140) h76) h17) h14) h114
  have h245 := h v9 v1 v4
  have h246 := S h245
  have h247 := R (M v1 v4)
  have h248 := C h85 (T (T (T (T (T h58 h57) h37) h36) h20) h97)
  have h249 := T (T (T (T (T (T (T (T h151 h140) h76) h17) h14) h39) h49) h44) h248
  have h250 := h v43 x x
  have h251 := S h250
  let v252 := M x x
  have h253 := R v252
  have h254 := R (M x v43)
  have h255 := h v19 v1 z
  have h256 := C h85 (T (T (T h58 h57) h37) h36)
  have h257 := T (T (T h39 h49) h44) h256
  have h258 := C h257 h29
  have h259 := h v113 z v0
  have h260 := C (T (T (T (T (T (T (T (T h13 h105) h103) h139) h161) h165) h259) (C (T (T (T (T (T (T (C (T (T (T (T (T (T (T (T (T h213 h211) h137) h135) h116) h174) h172) h171) h166) h258) h175) (S h255)) h20) h97) h111) h244) h243) h212)) (C h254 h242)) h253
  have h261 := C (T (T (C (T (T (T (T (T (T (T (T (T (T (T h260 h251) h42) h40) h13) h105) h103) h139) h161) h165) h216) h215) h8) h236) (C h249 h8)) h247
  have h262 := h v252 v1 v4
  have h263 := h v252 v0 x
  have h264 := S h263
  have h265 := R (M v0 v252)
  have h266 := S h262
  have h267 := C h53 (T (T (T h91 h90) h89) h84)
  have h268 := T (T (T h267 h45) h42) h40
  have h269 := C h268 h29
  have h270 := C (T (T (T (T (T (T (T (T (C h254 h226) (C (T (T (T (T (T (T h227 h162) h112) h74) h21) h255) (C (T (T (T (T (T (T (T (T (T h269 h153) h152) h133) h131) h117) h134) h168) h231) h230) h154)) h182)) (S h259)) h178) h176) h140) h76) h17) h14) h253
  have h271 := C h53 (T (T (T (T (T h74 h21) h91) h90) h89) h84)
  have h272 := T (T (T (T (T (T (T (T h271 h45) h42) h40) h13) h105) h103) h139) h170
  have h273 := C (T (T (C h272 h8) h217) (C (T (T (T (T (T (T (T (T (T (T (T h235 h229) h178) h176) h140) h76) h17) h14) h39) h49) h250) h270) h8)) h247
  have h274 := T (T h245 h273) h266
  have h275 := h v0 (M (M x y) z) v0
  have h276 := h y x z
  have h277 := C (T (C (C h276 h34) h276) (S h275)) h274
  have h278 := h v0 y y
  have h279 := T (T (T (T (T h213 h211) h137) h135) h278) h277
  have h280 := C (T (T (C (T (T (T h134 h168) h231) h230) h212) (C h279 h16)) (C h265 h242)) (T h205 h234)
  have h281 := C (T (C h101 h16) (C h109 h182)) h29
  have h282 := h v12 x v0
  have h283 := S h282
  have h284 := R v115
  have h285 := R v12
  have h286 := C h242 h285
  have h287 := C h286 h34
  have h288 := C (T (C h101 h212) (C h109 h16)) h29
  have h289 := S h278
  have h290 := T (T h262 h261) h246
  have h291 := S h276
  have h292 := C (T h275 (C (C h291 h34) h291)) h290
  have h293 := T (T (T (T (T h292 h289) h134) h168) h231) h230
  have h294 := C (T (T (C h265 h226) (C h293 h16)) (C (T (T (T h213 h211) h137) h135) h182)) (T h210 h206)
  have h295 := T (T h263 h294) h288
  have h296 := C h16 h295
  have h297 := T (T (T (T h271 h45) h250) h270) h296
  have h298 := C h297 h34
  have h299 := T h267 h248
  have h300 := C h299 h34
  have h301 := T h54 h256
  have h302 := C h301 h34
  have h303 := C (T (T (T (T (T h26 h88) h302) h300) h298) h287) h284
  have h304 := T h267 h86
  have h305 := C h304 h34
  have h306 := T h271 h256
  have h307 := C h306 h34
  have h308 := T (T h281 h280) h264
  have h309 := C h16 h308
  have h310 := T (T (T (T h309 h260) h251) h44) h248
  have h311 := C h310 h34
  have h312 := C h226 h285
  have h313 := C h312 h34
  have h314 := C (T (T (T (T (T h313 h311) h307) h305) h56) h33) h284
  have h315 := h v12 x v2
  have h316 := R v66
  let v317 := M v1 v2
  have h318 := h v317 z v2
  have h319 := S h318
  have h320 := R v317
  have h321 := h v113 v0 z
  have h322 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (C (T (T h303 h283) h281) h16) (S h321)) h178) h176) h140) h76) h17) h14) h39) h49) h250) h270) h296) h286) h138
  have h323 := h v115 z v1
  have h324 := h v115 v1 y
  have h325 := S h323
  have h326 := C (T (T (T (T (T (T (T (T (T (T (T (T (T h312 h309) h260) h251) h42) h40) h13) h105) h103) h139) h161) h165) h321) (C (T (T h288 h282) h314) h16)) h169
  have h327 := T (T (T (T (T (T (T h26 h88) h302) h300) h298) h287) h326) h325
  have h328 := T (T (T (T h309 h260) h251) h42) h40
  have h329 := C h34 h308
  have h330 := C h34 h295
  have h331 := h y v2 z
  have h332 := S h331
  have h333 := h v0 v2 z
  let v334 := M v2 z
  have h335 := R v334
  have h336 := h y v1 v0
  have h337 := C (T (C (T (T h332 h336) (C h195 h33)) h335) (S h333)) h332
  let v338 := M v2 y
  have h339 := h v334 (M v338 z) v334
  have h340 := T (T (T (T (T (T (T h323 h322) h313) h311) h307) h305) h56) h33
  have h341 := C h3 h340
  have h342 := C h3 h327
  have h343 := S h339
  have h344 := C (T h333 (C (T (T (C h195 h26) (S h336)) h331) h335)) h331
  have h345 := C h219 (T (T (T (C h3 h106) (C h3 (T (T h139 h161) h165))) h241) h228)
  have h346 := C h237 (T (T (T h223 h222) (C h3 (T (T h178 h176) h140))) (C h3 h77))
  have h347 := h v194 v1 v2
  have h348 := C (T (T (T (T h95 h80) h67) h94) (C (T h347 (C (T (T (T (T (T (T (T (T (T (T (T (T (C h239 h3) (C (T h220 h346) h3)) (C (T (T (T (T h345 h199) h344) h343) h342) h3)) (C (T (T (T (T (T (T (T h341 h339) h337) (C h101 h25)) (C h232 h25)) (C h279 h25)) (C h330 h25)) (C (T (T (T (T (T (T (T (T (T (T (T h329 h292) h289) h116) h174) h172) h171) h166) h258) (C h299 h29)) (C h297 h29)) (C h328 h327)) h25)) h3)) (S h324)) h323) h322) h313) h311) h307) h305) h56) h33) h320)) h3)) h22
  have h349 := C (T (T (T (T (C (T (T (T (C (T (T (T (T (T (T (T (T (T h28 h73) h348) h319) (C h87 h3)) (C h301 h3)) (C h299 h3)) (C h272 h3)) (C (T (T (T (T (T (T (T (T (T h151 h140) h76) h17) h14) h39) h49) h250) h270) h296) h3)) (C h286 h3)) h316) (S h315)) h282) h314) h8) (C (T (T (T (T (T (T (T (T (T (T h303 h283) h281) h280) h264) h262) h261) h246) h111) h244) h243) h8)) (C h227 h8)) (C (T (T (T h162 h112) h10) h110) h8)) (C (T h102 h11) h8)) h7
  have h350 := h v66 y v4
  have h351 := h v66 v2 v2
  have h352 := h v2 v338 v2
  have h353 := S h352
  have h354 := C (C h62 h3) h62
  have h355 := S h350
  have h356 := C (T (T (T (T (C (T h10 h110) h8) (C (T (T (T h102 h11) h111) h244) h8)) (C h243 h8)) (C (T (T (T (T (T (T (T (T (T (T h227 h162) h112) h245) h273) h266) h263) h294) h288) h282) h314) h8)) (C (T (T (T h303 h283) h315) (C (T (T (T (T (T (T (T (T (T (C h312 h3) (C (T (T (T (T (T (T (T (T (T h309 h260) h251) h42) h40) h13) h105) h103) h139) h170) h3)) (C h249 h3)) (C h306 h3)) (C h304 h3)) (C h55 h3)) h318) (C (T (T (T (T (C (T (C (T (T (T (T (T (T (T (T (T (T (T (T h26 h88) h302) h300) h298) h287) h326) h325) h324) (C (T (T (T (T (T (T (T (C (T (T (T (T (T (T (T (T (T (T (T (C (T (T (T (T h39 h49) h250) h270) h296) h340) (C h310 h29)) (C h306 h29)) h269) h153) h152) h133) h131) h117) h278) h277) h330) h25) (C h329 h25)) (C h293 h25)) (C h214 h25)) (C h109 h25)) h344) h343) h342) h3)) (C (T (T (T (T h341 h339) h337) h198) h346) h3)) (C (T h345 h238) h3)) (C h221 h3)) h320) (S h347)) h3) h70) h68) h72) h71) h22)) h96) h78) h316)) h8)) h7
  have h357 := T (T h5 h356) h355
  have h358 := h v4 y y
  have h359 := S h358
  have h360 := R v9
  have h361 := h y y v2
  have h362 := S h361
  have h363 := h v4 (M v9 v2) v4
  have h364 := T h363 (C (C h362 h8) h362)
  have h365 := C h364 h360
  have h366 := C (T h365 h359) h25
  have h367 := C h8 h98
  have h368 := C h367 h25
  have h369 := C h8 h75
  have h370 := T (C (C h361 h8) h361) (S h363)
  have h371 := C h370 h360
  have h372 := C h364 h290
  have h373 := C (T (T h372 h371) h369) h25
  have h374 := C h8 h308
  have h375 := C h374 h25
  have h376 := T (T h350 h349) h6
  have h377 := C h8 h295
  have h378 := C h370 h274
  have h379 := C (T (T h358 h378) h377) h376
  have h380 := h v66 v4 y
  have h381 := C (C h82 h3) h82
  have h382 := C (T (T h374 h372) h359) h357
  have h383 := C h377 h25
  have h384 := C (T (T h367 h365) h378) h25
  have h385 := C h369 h25
  have h386 := C (T h358 h371) h25
  T (T (T (T (T (T (T h225 h224) h180) (h v113 v1 y)) (C (T (T (T (T (T (C (T (T (T (T (T (T (T (T (T (T h162 h112) h245) h273) h266) h263) h294) h288) (h v12 v1 y)) (C (T (T (T (T (T (T (T (T (T (C h310 h25) (C h306 h25)) (C h268 h25)) h352) h381) h386) h385) h384) h383) h382) h3)) (C (T (T (T (T (T (T (T (T (T (T h379 h375) h373) h368) h366) h354) h353) (C h257 h25)) (C h299 h25)) (C h297 h25)) (C h328 h357)) h3)) (T (T (T h28 h73) h348) h319)) (S (h v66 v1 v2))) h351) (C (T (T (T (T (C (C (T (T (T (T (T (T h352 h381) h386) h385) h384) h383) h382) h376) (T h352 h381)) (S h380)) h350) h349) h6) (T (T (T (T (T (T (T (T (T (T (T (T (T h64 h63) h58) h57) h37) h36) h20) h97) h245) h273) h266) h263) h294) h288))) (C h25 (T (T (T (T (T h281 h280) h264) h262) h261) h246))) (C h25 h75)) h3)) (C (C h25 h98) h3)) (C (C h25 (T (T (T (T (T h245 h273) h266) h263) h294) h288)) h3)) (C (T (T (T (T (C (T (T (T (T h5 h356) h355) h380) (C (C (T (T (T (T (T (T h379 h375) h373) h368) h366) h354) h353) h357) (T h354 h353))) (T (T (T (T (T (T (T (T (T (T (T (T (T h281 h280) h264) h262) h261) h246) h74) h21) h91) h90) h89) h84) h83) h81)) (S h351)) h350) h349) h6) h3)

