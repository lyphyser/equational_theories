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
theorem Equation928_implies_Equation1929 (G: Type _) [Magma G] (h: Equation928 G) : Equation1929 G := fun x y z =>
  let v0 := M y x
  let v1 := M y v0
  have h2 := h z v1 x
  have h3 := S h2
  have h4 := R v1
  have h5 := C h4 (C h3 h3)
  let v6 := M z x
  let v7 := M v1 x
  have h8 := h v1 v1 (M v7 v6)
  let v9 := M z z
  let v10 := M v9 v0
  let v11 := M v1 v9
  let v12 := M v11 v0
  have h13 := R v10
  have h14 := h v12 v11 v9
  have h15 := S h14
  let v16 := M v9 x
  have h17 := h v9 v9 (M v16 v6)
  have h18 := S h17
  have h19 := h z v9 x
  have h20 := R v9
  have h21 := C h20 (C h19 h19)
  have h22 := h v9 v1 x
  have h23 := S h22
  have h24 := R v16
  have h25 := h v7 y v0
  have h26 := S h25
  have h27 := h y v1 x
  have h28 := R y
  have h29 := C h28 h27
  have h30 := h y y (M v0 v6)
  have h31 := S h30
  have h32 := h z y x
  have h33 := C h28 (C h32 h32)
  have h34 := T h33 h31
  have h35 := C h34 h20
  have h36 := T (T h35 h33) h31
  have h37 := C h34 h36
  have h38 := S h32
  have h39 := C h28 (C h38 h38)
  have h40 := T h30 h39
  have h41 := C h40 h20
  have h42 := T (T h30 h39) h41
  let v43 := M y v9
  have h44 := R v43
  have h45 := C h44 h42
  have h46 := h v43 v11 x
  have h47 := S h46
  have h48 := R x
  have h49 := C h40 h48
  let v50 := M v11 x
  have h51 := R v50
  have h52 := T h8 h5
  have h53 := C h40 (T (T (T (C h52 (C h51 h49)) h47) h33) h31)
  have h54 := h v50 y v0
  have h55 := T (T (T (T (T h54 h53) h45) h37) h29) h26
  have h56 := C h4 (C h55 h24)
  have h57 := T h56 h23
  have h58 := C h57 h57
  have h59 := S h54
  have h60 := C h34 h48
  have h61 := S h8
  have h62 := C h4 (C h2 h2)
  have h63 := T h62 h61
  have h64 := C h34 (T (T (T h30 h39) h46) (C h63 (C h51 h60)))
  have h65 := C h44 h36
  have h66 := C h40 h42
  have h67 := C h28 (S h27)
  have h68 := T (T (T (T (T h25 h67) h66) h65) h64) h59
  have h69 := C h4 (C h68 h24)
  have h70 := h v9 v1 v11
  have h71 := S h70
  have h72 := R (M v9 v11)
  let v73 := M v1 v11
  have h74 := h v73 y v0
  have h75 := S h74
  have h76 := h v0 y v9
  have h77 := S h76
  have h78 := h z v0 x
  have h79 := S h78
  have h80 := R v0
  have h81 := C h80 (C h79 h79)
  let v82 := M v0 x
  have h83 := h v0 v0 (M v82 v6)
  have h84 := T h83 h81
  have h85 := C h44 h84
  have h86 := C h40 h80
  have h87 := h v1 v1 (M v50 v16)
  have h88 := S h87
  have h89 := T h22 h69
  have h90 := C h89 h89
  have h91 := S h19
  have h92 := C h20 (C h91 h91)
  have h93 := C h34 h80
  have h94 := S h83
  have h95 := C h80 (C h78 h78)
  have h96 := T h95 h94
  have h97 := C h44 h96
  have h98 := T h97 h93
  have h99 := C h98 (T (T h17 h92) h90)
  have h100 := C h34 (T (T (T h99 h88) h86) h85)
  have h101 := T h86 h85
  have h102 := C h101 (T (T h58 h21) h18)
  have h103 := C h44 (T (T (T h62 h61) h87) h102)
  have h104 := T (T h103 h100) h77
  have h105 := R v73
  have h106 := C h4 (C h105 h104)
  have h107 := h v43 v1 v11
  have h108 := h v43 v11 v11
  have h109 := S h108
  have h110 := C h44 (T (T (T h99 h88) h8) h5)
  have h111 := C h40 (T (T (T h97 h93) h87) h102)
  have h112 := T (T h76 h111) h110
  let v113 := M v11 v11
  have h114 := R v113
  have h115 := C h52 (C h114 h112)
  have h116 := C h28 (T (T (T h115 h109) h107) h106)
  have h117 := h v113 y v0
  have h118 := T (T h117 h116) h75
  have h119 := C h4 (C h118 h72)
  have h120 := T (T (T h119 h71) h22) h69
  have h121 := C h120 h120
  have h122 := S h117
  have h123 := C h63 (C h114 h104)
  have h124 := S h107
  have h125 := C h4 (C h105 h112)
  have h126 := C h28 (T (T (T h125 h124) h108) h123)
  have h127 := T (T h74 h126) h122
  have h128 := C h4 (C h127 h72)
  have h129 := h v9 v1 y
  have h130 := S h129
  have h131 := R (M v9 y)
  have h132 := R v11
  let v133 := M v43 (M v0 v9)
  have h134 := h v133 y v9
  have h135 := S h134
  have h136 := h (M v43 v11) v11 v9
  have h137 := S h136
  have h138 := C h112 h20
  let v139 := M v11 v9
  have h140 := R v139
  have h141 := C h140 (T (T h83 h81) h138)
  have h142 := C h28 (T (T (C h52 h141) h137) h103)
  have h143 := h v139 y v0
  have h144 := T (T h143 h142) h135
  have h145 := S h143
  have h146 := C h104 h20
  have h147 := C h140 (T (T h146 h95) h94)
  have h148 := C h28 (T (T h110 h136) (C h63 h147))
  let v149 := M v139 (M z v9)
  have h150 := h v1 v1 v149
  have h151 := S h150
  have h152 := R v149
  have h153 := h z v11 v9
  have h154 := h z v1 v11
  have h155 := S h154
  have h156 := R (M z v11)
  have h157 := C h4 (C h118 h156)
  have h158 := T (T (T h157 h155) h153) (C h63 h152)
  have h159 := C h4 (C h127 h156)
  have h160 := R v6
  have h161 := C h4 (C h55 h160)
  have h162 := T (T (T h161 h3) h154) h159
  have h163 := C h4 (C h68 h160)
  have h164 := T h2 h163
  have h165 := T (T (T (T h143 h142) h135) h97) h93
  have h166 := C h165 (T (T (T (T h21 h18) (C h164 h164)) (C h162 h162)) (C h158 h158))
  have h167 := T (T (T (T (T (T h166 h151) h86) h85) h134) h148) h145
  have h168 := h v43 v11 v1
  have h169 := S h168
  have h170 := C h44 h63
  have h171 := T (T h134 h148) h145
  have h172 := C h171 h80
  have h173 := C h52 (T h172 h141)
  have h174 := C h101 h80
  have h175 := C h4 h174
  have h176 := C (T (T h175 h173) h137) h20
  have h177 := h (M v1 (M v1 v0)) y v0
  have h178 := S h177
  have h179 := T (T (T h176 h146) h95) h94
  have h180 := C h98 h80
  have h181 := C h4 h180
  have h182 := C h144 h80
  have h183 := C h63 (T h147 h182)
  have h184 := T (T (T (T (T (T (T h95 h94) h76) h111) h110) h136) h183) h181
  have h185 := C h184 h179
  have h186 := C (T (T h136 h183) h181) h20
  have h187 := C h84 (T (T (T (T h60 h83) h81) h138) h186)
  have h188 := C h80 h49
  have h189 := T (T h188 h187) h185
  have h190 := C h4 h189
  have h191 := h v0 v1 x
  have h192 := S h191
  have h193 := C h4 (C h192 h192)
  have h194 := h v1 v1 (M v7 v82)
  have h195 := C h34 (T (T (T (T (T (T (T h143 h142) h135) h97) h93) h194) h193) h190)
  have h196 := C (T h195 h178) h20
  let v197 := M v11 v1
  have h198 := h v197 v11 v9
  have h199 := h v9 v11 v9
  have h200 := S h199
  have h201 := T h161 h3
  have h202 := T (T (T h157 h155) h2) h163
  have h203 := T (T (T (C h52 h152) (S h153)) h154) h159
  have h204 := C (T (T (T (T h86 h85) h134) h148) h145) (T (T (T (T (C h203 h203) (C h202 h202)) (C h201 h201)) h17) h92)
  have h205 := T (T (T h166 h151) h8) h5
  have h206 := R v197
  have h207 := T (T (T (T (T (T h62 h61) h86) h85) h134) h148) h145
  let v208 := M v9 v9
  let v209 := M v139 v208
  have h210 := h v209 v11 v1
  have h211 := S h194
  have h212 := C h4 (C h191 h191)
  have h213 := C h80 h60
  have h214 := C h96 (T (T (T (T h176 h146) h95) h94) h49)
  have h215 := T (T (T h83 h81) h138) h186
  have h216 := T (T (T (T (T (T (T h175 h173) h137) h103) h100) h77) h83) h81
  have h217 := C h216 h215
  have h218 := T (T h217 h214) h213
  have h219 := C h4 h218
  have h220 := C h40 (T (T (T (T (T (T (T h219 h212) h211) h86) h85) h134) h148) h145)
  have h221 := C (T h177 h220) h20
  have h222 := R v208
  have h223 := T h17 h92
  have h224 := C h52 (T (T (C h223 h215) (C h222 h221)) (C (T (T (T (T h21 h18) h199) (C h132 (T h210 (C h207 (C h206 (T (C h205 (T h150 h204)) h200)))))) (S h198)) (T (T (T (T (T (T (T (T h196 h176) h146) h95) h94) h76) h111) h110) h170)))
  have h225 := T h224 h169
  have h226 := C h225 h20
  have h227 := T (T (T h226 h35) h33) h31
  have h228 := T (T (T (T (T (T h143 h142) h135) h97) h93) h150) h204
  let v229 := M v1 v10
  have h230 := R (M v229 v9)
  have h231 := T h21 h18
  have h232 := C h44 h52
  have h233 := T (T (T h62 h61) h150) h204
  have h234 := T (T (T (T (T (T h143 h142) h135) h97) h93) h8) h5
  have h235 := C h63 (T (T (C (T (T (T (T h198 (C h132 (T (C h234 (C h206 (T h199 (C h233 (T h166 h151))))) (S h210)))) h200) h17) h92) (T (T (T (T (T (T (T (T h232 h103) h100) h77) h83) h81) h138) h186) h221)) (C h222 h196)) (C h231 h179))
  have h236 := T h168 h235
  have h237 := C h236 h20
  have h238 := h v229 v11 y
  have h239 := T (T (T h224 h169) h33) h31
  have h240 := T (T (T h30 h39) h168) h235
  have h241 := C h240 h239
  have h242 := h v9 y v0
  have h243 := T h242 h241
  let v244 := M v11 y
  have h245 := R v244
  have h246 := h v244 v11 v9
  have h247 := C h4 (C (T (T (T (T (T (T (T (T (T h246 (C h132 (T (T (T (T (T (C h234 (C h245 h243)) (S h238)) h224) h169) h41) h237))) (C h207 h230)) (C h228 h227)) (C h167 h40)) (C h140 h41)) (C h144 h36)) (C (T (T (T h97 h93) h8) h5) h40)) (C h132 h41)) (C h63 h36)) h131)
  have h248 := T (T (T h247 h130) h70) h128
  have h249 := C h248 h248
  have h250 := S h242
  have h251 := C h239 h240
  have h252 := T h251 h250
  have h253 := T (T (T h30 h39) h41) h237
  have h254 := C h4 (C (T (T (T (T (T (T (T (T (T (C h52 h42) (C h132 h35)) (C (T (T (T h62 h61) h86) h85) h34)) (C h171 h42)) (C h140 h35)) (C h228 h34)) (C h167 h253)) (C h234 h230)) (C h132 (T (T (T (T (T h226 h35) h168) h235) h238) (C h207 (C h245 h252))))) (S h246)) h131)
  have h255 := C h236 h227
  have h256 := C h40 (T (T (T h125 h124) h41) h237)
  have h257 := C h34 (T h108 h123)
  have h258 := C h40 (T (C h52 (C (T (T (T h66 h65) h64) h59) h49)) h47)
  have h259 := h (M y y) y v0
  have h260 := C (T (T (T (T (T (T (T (T (T h259 h258) h257) h116) h256) h255) h251) h250) h129) h254) (T (T (T h251 h250) h129) h254)
  have h261 := C h98 h48
  have h262 := C h144 h48
  have h263 := C h167 h48
  have h264 := C (T h25 h67) (T (T (T (T (T (T (T (T (T (T h263 h262) h261) h25) h67) h259) h258) h257) h116) h256) h255)
  have h265 := R (M v209 x)
  have h266 := C h55 h265
  have h267 := C h228 h48
  have h268 := C h68 h267
  have h269 := R (M v139 x)
  have h270 := C h55 h269
  have h271 := C h171 h48
  have h272 := C h101 h48
  have h273 := S h259
  have h274 := C h34 (T h46 (C h63 (C (T (T (T h54 h53) h45) h37) h60)))
  have h275 := C h40 (T h115 h109)
  have h276 := C (T (T (T (T (T (T (T (T h74 h126) h275) h274) h273) h66) h65) h64) h59) (T (T (T (T (T (T (T h117 h275) h274) h273) h29) h26) h272) h271)
  have h277 := h (M v73 v113) v0 v9
  have h278 := S h277
  have h279 := C (T (T (T (T (T (T (T (T h54 h53) h45) h37) h259) h258) h257) h116) h75) (T (T (T (T (T (T (T h262 h261) h25) h67) h259) h258) h257) h122)
  have h280 := C h68 h269
  have h281 := C h55 h263
  have h282 := C h68 h265
  have h283 := C h34 (T (T (T h226 h35) h107) h106)
  have h284 := C h225 h253
  have h285 := C (T h29 h26) (T (T (T (T (T (T (T (T (T (T h284 h283) h126) h275) h274) h273) h29) h26) h272) h271) h267)
  have h286 := C (T (T (T (T (T (T (T (T (T h247 h130) h242) h241) h284) h283) h126) h275) h274) h273) (T (T (T h247 h130) h242) h241)
  have h287 := T (T (T h119 h71) h129) h254
  have h288 := C h287 h287
  have h289 := T (T (T h56 h23) h70) h128
  have h290 := C h289 h289
  have h291 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h259 h258) h257) h116) h256) h255) h251) h250) h17) h92) h90) h290) h288) h286) h285) h282) h281) h280) h279) h252
  have h292 := T (T (T (T (T (T h17 h92) h90) h290) h288) h286) h291
  have h293 := T (T (T (T (T (T (T (T (T h195 h178) h175) h173) h137) h103) h100) h77) h83) h81
  have h294 := C h293 h292
  have h295 := C h225 h48
  have h296 := C h80 (T (T (T (T (T (T (T h295 h60) h83) h81) h138) h186) h221) h294)
  have h297 := C h236 h48
  let v298 := M v43 v139
  have h299 := h v298 y v0
  have h300 := S h299
  have h301 := T (T (T (T h196 h176) h146) h95) h94
  have h302 := T (T (T (T (T (T (T (T (T h95 h94) h76) h111) h110) h136) h183) h181) h177) h220
  have h303 := C h302 h301
  have h304 := T (T (T (T h83 h81) h138) h186) h221
  have h305 := C h216 h304
  have h306 := T h305 h303
  have h307 := C h167 h223
  have h308 := C h34 (T (T (T (T (T (T h307 h166) h151) h194) h193) h190) (C h4 h306))
  have h309 := C h228 h231
  have h310 := C h225 (T (T (T (T h62 h61) h150) h204) h309)
  have h311 := R v229
  have h312 := C h311 h52
  have h313 := C h40 h4
  have h314 := C (T (T (T (T h313 h232) h103) h100) h77) (T (T (T (T (T (T (T (T (T (T (T (T (T h312 h310) h308) h300) h195) h178) h175) h173) h137) h103) h100) h77) h49) h297)
  have h315 := C h311 h63
  have h316 := C h236 (T (T (T (T h307 h166) h151) h8) h5)
  have h317 := C h184 h301
  have h318 := C h293 h304
  have h319 := T h318 h317
  have h320 := C h40 (T (T (T (T (T (T (C h4 h319) h219) h212) h211) h150) h204) h309)
  have h321 := C h34 h4
  have h322 := C (T (T (T (T (T (T h195 h178) h175) h173) h137) h170) h321) (T (T (T (T (T (T (T (T (T (T (T h76 h111) h110) h136) h183) h181) h177) h220) h299) h320) h316) h315)
  have h323 := T (T (T (T (T (T (T (T (T (T (T (T (T (T h322 h314) h296) h278) h276) h270) h268) h266) h264) h260) h249) h121) h58) h21) h18
  have h324 := R v12
  have h325 := h v298 v11 v0
  have h326 := C h205 (T (T (T (T (T (T (T (T (T h76 h111) h110) h136) h183) h181) h177) h220) h325) (C h207 (C h324 h323)))
  have h327 := C h228 h96
  have h328 := R (M v298 v9)
  have h329 := C (T h313 h232) h20
  have h330 := C (T h170 h321) h20
  have h331 := C h4 (C (T (T (T (T (T (T (T (T (T h174 h172) h141) (C h140 h330)) (C h140 (T (T h329 h186) h221))) (C h234 h328)) (C h207 (T (T h196 h176) h146))) h327) h326) h15) h13)
  have h332 := h v9 v1 v0
  have h333 := T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h188 h187) h185) h305) h303) h322) h314) h296) h278) h276) h270) h268) h266) h264) h260) h249) h121) h58) h21) h18) h332) h331
  have h334 := C h333 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h322 h314) h296) h278) h276) h270) h268) h266) h264) h260) h249) h121) h58) h21) h18) h332) h331)
  have h335 := C (T (T (T (T (T (T h313 h232) h136) h183) h181) h177) h220) (T (T (T (T (T (T (T (T (T (T (T h312 h310) h308) h300) h195) h178) h175) h173) h137) h103) h100) h77)
  have h336 := C (T (T (T (T h76 h111) h110) h170) h321) (T (T (T (T (T (T (T (T (T (T (T (T (T h295 h60) h76) h111) h110) h136) h183) h181) h177) h220) h299) h320) h316) h315)
  have h337 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h276 h270) h268) h266) h264) h260) h249) h121) h58) h21) h18) h242) h241) h284) h283) h126) h275) h274) h273) h243
  have h338 := T (T (T (T (T (T h337 h260) h249) h121) h58) h21) h18
  have h339 := C h302 h338
  have h340 := C h80 (T (T (T (T (T (T (T h339 h196) h176) h146) h95) h94) h49) h297)
  have h341 := T (T (T (T (T (T (T (T (T (T (T (T (T (T h17 h92) h90) h290) h288) h286) h285) h282) h281) h280) h279) h277) h340) h336) h335
  have h342 := C h105 h127
  have h343 := C h118 h105
  have h344 := C h114 h118
  have h345 := C (T (T (T (T (T h25 h67) h259) h258) h257) h122) (T (T (T (T (T (T h261 h25) h67) h259) h258) h257) h122)
  have h346 := R (M v133 x)
  have h347 := C h55 h346
  have h348 := C h68 (T (T (T (T (T (T h54 h53) h45) h37) h29) h26) h272)
  have h349 := C h55 h51
  have h350 := C h51 h68
  have h351 := h (M v50 v7) v9 v9
  have h352 := S h351
  have h353 := C h51 h55
  have h354 := C h68 h51
  have h355 := C h55 (T (T (T (T (T (T h261 h25) h67) h66) h65) h64) h59)
  have h356 := C h68 h346
  have h357 := C (T (T (T (T (T h117 h275) h274) h273) h29) h26) (T (T (T (T (T (T h117 h275) h274) h273) h29) h26) h272)
  have h358 := C h114 h127
  have h359 := C h127 h105
  have h360 := C h105 h118
  have h361 := h v0 v11 v9
  have h362 := C h167 h84
  have h363 := C h233 (T (T (T (T (T (T (T (T (T (C h234 (C h324 h341)) (S h325)) h195) h178) h175) h173) h137) h103) h100) h77)
  have h364 := T (T (T (T (C h4 (T h14 h363)) (C h52 h362)) (S h361)) h83) h81
  have h365 := C h364 h292
  have h366 := C h96 h365
  have h367 := T (T (T (T h95 h94) h361) (C h63 h327)) (C h4 (T h326 h15))
  have h368 := C h367 h338
  have h369 := C h364 (T (T (T (T (T (T h83 h81) h138) h186) h221) h294) h368)
  have h370 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h188 h187) h185) h305) h303) h322) h314) h296) h278) h276) h270) h268) h266) h264) h260) h249) h121) h58) h21) h18) (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h369 h366) h278) h276) h270) h268) h266) h264) h291) (C (T (T (T (T (T (T (T (T h276 h270) h268) h266) h264) h260) h249) h121) h58) h292)) (C h222 (C h360 h20))) (C h222 (C h359 h20))) (C h222 (C h358 h20))) (C h222 (C (T (T h357 h356) h355) h20))) (C h222 (C h354 h20))) (C h222 (C h353 h20)))
  have h371 := C h367 (T (T (T (T (T (T h365 h339) h196) h176) h146) h95) h94)
  have h372 := C h84 h368
  have h373 := S h332
  have h374 := C h4 (C (T (T (T (T (T (T (T (T (T h14 h363) h362) (C h234 (T (T h138 h186) h221))) (C h207 h328)) (C h140 (T (T h196 h176) h330))) (C h140 h329)) h147) h182) h180) h13)
  have h375 := T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h374 h373) h17) h92) h90) h290) h288) h286) h285) h282) h281) h280) h279) h277) h340) h336) h335) h318) h317) h217) h214) h213
  have h376 := C h375 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h374 h373) h17) h92) h90) h290) h288) h286) h285) h282) h281) h280) h279) h277) h372) h371)
  let v377 := M v0 v0
  have h378 := R v377
  have h379 := C h378 h306
  have h380 := C h378 h189
  let v381 := M v377 v377
  have h382 := C h375 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h374 h373) h17) h92) h90) h290) h288) h286) h285) h282) h281) h280) h279) h277) h340) h336) h335)
  have h383 := C h333 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h369 h366) h278) h276) h270) h268) h266) h264) h260) h249) h121) h58) h21) h18) h332) h331)
  have h384 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h17 h92) h90) h290) h288) h286) h285) h282) h281) h280) h279) h277) h340) h336) h335) h318) h317) h217) h214) h213) (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (C h222 (C h350 h20)) (C h222 (C h349 h20))) (C h222 (C (T (T h348 h347) h345) h20))) (C h222 (C h344 h20))) (C h222 (C h343 h20))) (C h222 (C h342 h20))) (C (T (T (T (T (T (T (T (T h90 h290) h288) h286) h285) h282) h281) h280) h279) h338)) h337) h285) h282) h281) h280) h279) h277) h372) h371)
  have h385 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h188 h187) h185) h305) h303) h322) h314) h296) h278) h360) h359) h358) h357) h356) h355) h354) h353) h351) h384) h383) h382) (C h378 h319)) (C h378 h218)) h323
  have h386 := T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h17 h92) h90) h290) h288) h286) h285) h282) h281) h280) h279) h360) h359) h358) h357) h356) h355) h354) h353) h351) h384) h383) h382) h385
  have h387 := S (h z x x)
  have h388 := C h48 (C h387 h387)
  have h389 := h x x (M (M x x) v6)
  T (T (T (T (T (T (h x v1 x) (C h52 (T (T (T (T (C (T (T (T (T (T (T (T (T (T h25 h67) h259) h258) h257) h116) h256) h255) h251) h250) (T (T (T (T (T (C h48 (T (T h389 h388) (C (T h389 h388) h386))) (S (h v381 x v9))) h380) h379) h385) (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h380 h379) h334) h376) h370) h352) h350) h349) h348) h347) h345) h344) h343) h342) h276) h270) h268) h266) h264) h260) h249) h121) h58) h386))) (S (h v381 v9 v9))) h380) h379) h385))) (C h207 (R (M v381 v9)))) (C h165 (T (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h380 h379) h334) h376) h370) h352) h350) h349) h348) h347) h345) h344) h343) h342) h277) h340) h336) h335) h318) h317) h217) h214) h213) h341) h334))) (S (h v1 v1 (M v12 v10)))) h8) h5

