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
theorem Equation1571_implies_Equation2573 (G: Type _) [Magma G] (h: Equation1571 G) : Equation2573 G := fun x y z =>
  let v0 := M z x
  let v1 := M v0 y
  let v2 := M y v1
  let v3 := M v2 z
  let v4 := M v3 x
  have h5 := S (h v4 v3 v2)
  have h6 := h v2 v2 (M y (M v2 v1))
  have h7 := S h6
  have h8 := h v2 y v1
  have h9 := R v2
  have h10 := C h8 (C h9 h8)
  have h11 := h v1 v1 (M v0 (M v3 y))
  have h12 := S h11
  have h13 := h v3 v0 y
  have h14 := R v1
  have h15 := C h13 (C h14 h13)
  let v16 := M v1 v3
  have h17 := h (M v3 v16) v3 v3
  have h18 := S h17
  have h19 := R v3
  have h20 := S h13
  have h21 := C h20 (C h14 h20)
  have h22 := h z v0 v0
  have h23 := S h22
  have h24 := h z z x
  let v25 := M v0 v0
  have h26 := R v25
  have h27 := C h26 h24
  have h28 := T h27 h23
  have h29 := h v25 v2 z
  have h30 := C (T h29 (C h19 (C h9 h28))) (T (T h11 h21) (C h19 (C (T h11 h21) h19)))
  have h31 := R y
  have h32 := C h31 (T (T (T h30 h18) h15) h12)
  have h33 := C h9 h32
  have h34 := h v25 y v1
  have h35 := h v25 v25 z
  have h36 := S h35
  have h37 := S h24
  have h38 := C h26 h37
  have h39 := T h22 h38
  have h40 := C h39 (T h22 (C h26 (T (T h37 h22) h38)))
  have h41 := T (T (T h40 h36) h34) h33
  have h42 := C h9 h41
  have h43 := C h28 (T (C h26 (T (T h27 h23) h24)) h23)
  have h44 := S h34
  have h45 := S h29
  have h46 := C h19 (C h9 h39)
  have h47 := C (T h46 h45) (T (T (C h19 (C (T h15 h12) h19)) h15) h12)
  have h48 := C h31 (T (T (T h11 h21) h17) h47)
  have h49 := C h9 h48
  let v50 := M v2 v2
  have h51 := h v50 y v1
  have h52 := S h51
  have h53 := C h41 h14
  let v54 := M z z
  have h55 := h v54 v0 y
  have h56 := S h55
  have h57 := R (M v54 y)
  have h58 := h v0 v0 (M z (M y x))
  have h59 := S h58
  have h60 := h y z x
  have h61 := R v0
  have h62 := C h60 (C h61 h60)
  have h63 := T h62 h59
  have h64 := C h63 h57
  have h65 := h y y v1
  have h66 := S h65
  have h67 := T (T (T h49 h44) h35) h43
  have h68 := C h67 h66
  have h69 := h y v2 v2
  have h70 := T h69 h68
  have h71 := C h9 h70
  have h72 := C h14 (T h71 h64)
  have h73 := T h72 h56
  have h74 := C h73 h14
  have h75 := h v1 v1 (M v0 (M z y))
  have h76 := h z v0 y
  have h77 := S h69
  have h78 := C h41 h65
  have h79 := T h78 h77
  have h80 := C h9 h79
  have h81 := S h60
  have h82 := C h81 (C h61 h81)
  have h83 := T h58 h82
  have h84 := C h83 h57
  have h85 := C h14 (T h84 h80)
  have h86 := T h55 h85
  have h87 := C h86 (T (C h76 (C h14 h76)) (S h75))
  have h88 := h v1 z z
  have h89 := T (T h42 h10) h7
  have h90 := C h89 (T (T (T h48 (C h31 (T (T (T (T (T h30 h18) h15) h12) h88) h87))) (C h31 h74)) (C h31 h53))
  have h91 := T (T (T (T (T h90 h52) h49) h44) h35) h43
  have h92 := C h9 h91
  have h93 := S h88
  have h94 := S h76
  have h95 := C h73 (T h75 (C h94 (C h14 h94)))
  have h96 := C h86 h14
  have h97 := C h67 h14
  have h98 := C h9 h67
  have h99 := S h8
  have h100 := C h99 (C h9 h99)
  have h101 := T (T h6 h100) h98
  have h102 := C h101 (T (T (T (C h31 h97) (C h31 h96)) (C h31 (T (T (T (T (T h95 h93) h11) h21) h17) h47))) h32)
  let v103 := M v2 y
  let v104 := M v1 v103
  have h105 := h v104 v1 v0
  have h106 := S h105
  have h107 := R v104
  have h108 := C h107 h63
  have h109 := C h14 h108
  have h110 := C h86 h83
  have h111 := C h14 h110
  have h112 := R v54
  have h113 := C h112 h63
  have h114 := C h14 h113
  have h115 := h v2 z z
  have h116 := S h115
  have h117 := h z y v1
  have h118 := S h117
  have h119 := C h118 (C h9 h118)
  have h120 := h v2 v2 (M y (M z v1))
  have h121 := T h120 h119
  have h122 := C h67 h121
  have h123 := T h122 h116
  have h124 := C h67 h123
  have h125 := S h120
  have h126 := C h117 (C h9 h117)
  have h127 := T h126 h125
  have h128 := C h41 h127
  have h129 := C h41 (T (T (T h126 h125) h115) h128)
  have h130 := T (T h122 h129) h124
  have h131 := C h14 h130
  have h132 := T h115 h128
  have h133 := C h14 h132
  let v134 := M v1 v2
  have h135 := h v134 v3 v1
  have h136 := S h135
  let v137 := M v1 y
  have h138 := h v1 v1 (M v0 v137)
  have h139 := S h138
  have h140 := h v1 v0 y
  have h141 := R v50
  have h142 := h v50 v0 y
  have h143 := C h140 (T (T h142 (C h14 (C h61 (T (C h141 h65) h77)))) (C h14 h140))
  have h144 := C h14 (T h90 h52)
  have h145 := R v134
  let v146 := M v2 v54
  have h147 := h v146 v1 v2
  have h148 := C h67 (T (T (T h122 h116) h120) h119)
  have h149 := C h41 h132
  have h150 := C h112 h83
  have h151 := C h73 h63
  have h152 := C h107 h83
  have h153 := R (M v3 v1)
  have h154 := C h153 (T (T (T (T (T (C h19 h132) (C h19 h130)) (C h19 h113)) (C h19 h110)) (C h19 h108)) (C h19 (T (T (T (T (T (T (T (T (T (T h152 h151) h150) h149) h148) h116) h6) h100) h98) h147) (C h145 (T (T h144 h143) h139)))))
  have h155 := h y v3 v1
  let v156 := M v1 v0
  have h157 := R v156
  have h158 := C h157 (T (T (T (T (T (T (T h155 h154) h136) h133) h131) h114) h111) h109)
  have h159 := T (T (T (T (T (T (T (T (T h158 h106) h72) h56) h40) h36) h34) h33) h51) h102
  have h160 := C h9 h159
  have h161 := R (M v156 y)
  have h162 := C h83 h161
  have h163 := S h155
  have h164 := T (T h149 h148) h128
  have h165 := C h14 (T h51 h102)
  have h166 := S h140
  have h167 := C h166 (T (T (C h14 h166) (C h14 (C h61 (T h69 (C h141 h66))))) (S h142))
  have h168 := C h153 (T (T (T (T (T (C h19 (T (T (T (T (T (T (T (T (T (T (C h145 (T (T h138 h167) h165)) (S h147)) h42) h10) h7) h115) h129) h124) h113) h110) h108)) (C h19 h152)) (C h19 h151)) (C h19 h150)) (C h19 h164)) (C h19 h123))
  have h169 := C h14 h123
  have h170 := C h14 h164
  have h171 := C h14 h150
  have h172 := C h14 h151
  have h173 := C h14 h152
  have h174 := C h157 (T (T (T (T (T (T (T h173 h172) h171) h170) h169) h135) h168) h163)
  have h175 := h v50 v3 v1
  have h176 := S h175
  have h177 := h v1 v1 (M v0 (M y y))
  have h178 := S h177
  have h179 := h y v0 y
  have h180 := C h179 (C h14 h179)
  have h181 := C h73 h31
  have h182 := C h86 h31
  have h183 := C h14 (T (T (T (T (T (T (T (T (T (T (T h162 h160) h92) h42) h10) h7) h115) h129) h124) h113) h110) h108)
  have h184 := h v156 v0 y
  have h185 := h v156 v2 y
  have h186 := S h185
  have h187 := T (T (T (T (T (T (T (T (T h90 h52) h49) h44) h35) h43) h55) h85) h105) h174
  have h188 := C h9 h187
  have h189 := T (T (T (T (T h40 h36) h34) h33) h51) h102
  have h190 := C h9 h189
  have h191 := T (T (T (T h6 h100) h98) h190) h188
  have h192 := C h63 h181
  have h193 := R (M v104 y)
  have h194 := C h83 h193
  have h195 := h v156 v1 y
  have h196 := S h195
  have h197 := C h14 h187
  have h198 := R v137
  have h199 := C h198 (T (T (T h138 h167) h165) h197)
  have h200 := C h63 (T (T (T (T (T (T (T (T (T (T (T (T (T (T h199 h196) h184) h183) h173) h172) h171) h170) h169) h135) h168) h163) h69) h68) h182)
  have h201 := C h14 h159
  have h202 := C h198 (T (T (T h201 h144) h143) h139)
  have h203 := R v103
  have h204 := C h203 h191
  have h205 := C h83 (T (T (T h204 h186) h195) h202)
  have h206 := R (M v103 v2)
  have h207 := C h63 h206
  have h208 := T (T (T (T h160 h92) h42) h10) h7
  have h209 := C h203 h208
  have h210 := C h9 (T h185 h209)
  have h211 := C (T (T (T (T (T (T (T h210 h207) h205) h200) h194) h192) h84) h80) h191
  have h212 := T (T h135 h168) h163
  have h213 := C h212 (T (T (C h14 (T (T (T (T (T (T (T (T (T (T (T (T (T (T h211 h186) h184) h183) h173) h172) h171) h170) h169) h135) h168) h163) h69) h68) h182)) (C h14 h181)) (C h14 h79))
  have h214 := h (M v2 v156) v1 v2
  have h215 := C h9 (T h204 h186)
  have h216 := C h83 h206
  have h217 := C h63 (T (T (T h199 h196) h185) h209)
  have h218 := S h184
  have h219 := C h63 h161
  have h220 := C h14 (T (T (T (T (T (T (T (T (T (T (T h152 h151) h150) h149) h148) h116) h6) h100) h98) h190) h188) h219)
  have h221 := C h83 (T (T (T (T (T (T (T (T (T (T (T (T (T (T h181 h78) h77) h155) h154) h136) h133) h131) h114) h111) h109) h220) h218) h195) h202)
  have h222 := C h63 h193
  have h223 := C h83 h182
  have h224 := h v103 v0 v2
  have h225 := S h224
  have h226 := S h214
  have h227 := C (T (T (T (T (T (T (T h71 h64) h223) h222) h221) h217) h216) h215) h208
  have h228 := T (T h155 h154) h136
  have h229 := C h228 (T (T (C h14 h70) (C h14 h182)) (C h14 (T (T (T (T (T (T (T (T (T (T (T (T (T (T h181 h78) h77) h155) h154) h136) h133) h131) h114) h111) h109) h220) h218) h185) h227)))
  have h230 := S h179
  have h231 := C h230 (C h14 h230)
  have h232 := T (T (T (T (T h177 h231) h229) h226) h210) h207
  let v233 := M v0 v2
  have h234 := R v233
  have h235 := C h153 (C h19 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (C h234 h232) h225) h71) h64) h223) h222) h221) h217) h216) h215) h214) h213) h180) h178) h88) h87) h74) h53))
  have h236 := h v233 v3 v1
  have h237 := T (T (T (T (T (T (T (T (T (T h236 h235) h176) h49) h44) h35) h43) h55) h85) h105) h174
  have h238 := C h63 h237
  have h239 := h v233 z v3
  have h240 := S h239
  have h241 := h v3 v3 v146
  have h242 := h z v2 z
  have h243 := T (C h242 (C h19 h242)) (S h241)
  have h244 := S h236
  have h245 := T (T (T (T (T h216 h215) h214) h213) h180) h178
  have h246 := C h153 (C h19 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h97 h96) h95) h93) h177) h231) h229) h226) h210) h207) h205) h200) h194) h192) h84) h80) h224) (C h234 h245)))
  have h247 := C (T (T (T (T (T (T h40 h36) h34) h33) h175) h246) h244) h243
  have h248 := S h242
  have h249 := T h241 (C h248 (C h19 h248))
  have h250 := C h73 h249
  have h251 := C h86 h19
  have h252 := C h67 h19
  have h253 := R z
  have h254 := C h253 (T (T (T h252 h251) h250) h247)
  have h255 := C h41 h19
  have h256 := C h253 h255
  have h257 := C h73 h19
  have h258 := C h253 h257
  have h259 := C h86 h243
  have h260 := h v3 z z
  have h261 := T h260 h259
  have h262 := C h253 h261
  have h263 := h v146 v2 v2
  have h264 := S h263
  have h265 := C (T (T h236 h235) h176) (T (T (T h6 h100) h98) h190)
  have h266 := C h121 (T (T (T (T (T (T (T (T (T (T h265 h264) h42) h10) h7) h120) h119) h262) h258) h256) h254)
  have h267 := R (M v233 v2)
  have h268 := C h83 h267
  have h269 := C h234 h83
  have h270 := C h63 h269
  have h271 := R (M v233 v0)
  have h272 := C h83 h271
  have h273 := C h234 h63
  have h274 := C (T (T h175 h246) h244) (T (T (T h92 h42) h10) h7)
  have h275 := T (T (T (T (T (T (T (T h238 h162) h160) h92) h42) h10) h7) h62) h59
  have h276 := C h275 (T (T (T (T (T h6 h100) h98) h263) h274) h273)
  have h277 := T (T (T (T (T h276 h272) h270) h268) h266) h240
  have h278 := C h9 h277
  let v279 := M v2 v233
  have h280 := R (M v279 v2)
  have h281 := C h83 h280
  have h282 := R v279
  have h283 := C h282 h83
  have h284 := C h63 h283
  have h285 := C h282 h63
  have h286 := T (T (T (T (T (T (T (T (T (T h158 h106) h72) h56) h40) h36) h34) h33) h175) h246) h244
  have h287 := C h83 h286
  have h288 := T (T (T (T (T (T (T (T h58 h82) h6) h100) h98) h190) h188) h219) h287
  have h289 := C h288 (T (T (T (T (T h269 h265) h264) h42) h10) h7)
  have h290 := C h63 h271
  have h291 := C h83 h273
  have h292 := C h63 h267
  have h293 := S h260
  have h294 := T h250 h293
  have h295 := C h253 h294
  have h296 := C h253 h251
  have h297 := C h253 h252
  have h298 := C (T (T (T (T (T (T h236 h235) h176) h49) h44) h35) h43) h249
  have h299 := C h253 (T (T (T h298 h259) h257) h255)
  have h300 := C h127 (T (T (T (T (T (T (T (T (T (T h299 h297) h296) h295) h126) h125) h6) h100) h98) h263) h274)
  have h301 := h v233 v3 v2
  have h302 := S h301
  have h303 := h v279 v2 v0
  have h304 := S h303
  have h305 := C h83 h285
  have h306 := C h63 h280
  have h307 := T (T (T (T (T h239 h300) h292) h291) h290) h289
  have h308 := C h9 h307
  let v309 := M v2 v0
  have h310 := R v309
  have h311 := C h310 (T (T (T (T (T (T (T (T (T h6 h100) h98) h190) h188) h219) h287) h308) h306) h305)
  have h312 := R (M v3 v2)
  have h313 := C h312 (T (C h19 (T (T (T (T (T (T (T (T h311 h304) h238) h162) h160) h92) h263) h274) h273)) (C h19 h269))
  have h314 := h v309 v3 v2
  have h315 := T (T (T (T (T (T (T (T (T h314 h313) h302) h239) h300) h292) h291) h290) h289) h285
  have h316 := C h9 h315
  have h317 := h v309 y v1
  have h318 := S h317
  have h319 := S h314
  have h320 := C h310 (T (T (T (T (T (T (T (T (T h284 h281) h278) h238) h162) h160) h92) h42) h10) h7)
  have h321 := C h312 (T (C h19 h273) (C h19 (T (T (T (T (T (T (T (T h269 h265) h264) h190) h188) h219) h287) h303) h320)))
  have h322 := T (T h301 h321) h319
  have h323 := C h14 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h276 h272) h270) h268) h266) h240) h236) h235) h176) h49) h44) h35) h43) h55) h85) h105) h174)
  have h324 := h v279 v1 v2
  have h325 := C h310 h83
  have h326 := C h9 (T (T (T (T h325 h311) h304) h324) (C h212 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h323 h201) h144) h143) h139) h177) h231) h229) h226) h210) h207) h205) h200) h194) h192) h84) h80) h224) (C h322 h245))))
  have h327 := R (M v309 v0)
  have h328 := C h83 h327
  have h329 := C h310 h63
  have h330 := T (T (T (T (T (T (T (T (T (T (T (T h316 h284) h281) h278) h238) h162) h160) h92) h42) h10) h7) h62) h59
  have h331 := C h330 (T (T (T (T (T (T (T (T (T h6 h100) h98) h190) h188) h219) h287) h303) h320) h329)
  have h332 := T (T (T h331 h328) h326) h318
  have h333 := C h9 h332
  let v334 := M v2 v309
  have h335 := R (M v334 v2)
  have h336 := C h83 h335
  have h337 := R v334
  have h338 := C h337 h83
  have h339 := C h63 h338
  have h340 := R (M v334 v0)
  have h341 := C h83 h340
  have h342 := C h337 h63
  have h343 := T (T (T (T (T (T (T (T (T h283 h276) h272) h270) h268) h266) h240) h301) h321) h319
  have h344 := C h9 h343
  have h345 := T (T (T (T (T (T (T (T (T (T (T (T h58 h82) h6) h100) h98) h190) h188) h219) h287) h308) h306) h305) h344
  have h346 := C h345 (T (T (T (T (T (T (T (T (T h325 h311) h304) h238) h162) h160) h92) h42) h10) h7)
  have h347 := C h63 h327
  have h348 := C h14 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h158 h106) h72) h56) h40) h36) h34) h33) h175) h246) h244) h239) h300) h292) h291) h290) h289)
  have h349 := T (T h314 h313) h302
  have h350 := C h9 (T (T (T (T (C h228 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (C h349 h232) h225) h71) h64) h223) h222) h221) h217) h216) h215) h214) h213) h180) h178) h138) h167) h165) h197) h348)) (S h324)) h303) h320) h329)
  have h351 := h v334 x x
  have h352 := S h351
  have h353 := R x
  have h354 := T (T (T (T (T (T (T (T (T (T h6 h100) h98) h190) h188) h219) h287) h308) h306) h305) h344
  have h355 := C h354 h353
  have h356 := C h353 h355
  have h357 := h x y v1
  have h358 := S h357
  have h359 := C h358 (C h9 h358)
  have h360 := h v2 v2 (M y (M x v1))
  let v361 := M x x
  have h362 := R v361
  have h363 := C h362 (T (T h360 h359) h356)
  have h364 := C h312 (T (C h19 (T (T (T (T (T (T (T (T h363 h352) h316) h284) h281) h278) h303) h320) h329)) (C h19 h325))
  have h365 := h v361 v3 v2
  have h366 := T (T (T (T (T (T (T h365 h364) h319) h317) h350) h347) h346) h342
  have h367 := C h63 h366
  let v368 := M v2 v361
  have h369 := h v368 v2 z
  have h370 := S h369
  have h371 := S h365
  have h372 := S h360
  have h373 := C h357 (C h9 h357)
  have h374 := T (T (T (T (T (T (T (T (T (T h316 h284) h281) h278) h238) h162) h160) h92) h42) h10) h7
  have h375 := C h374 h353
  have h376 := C h353 h375
  have h377 := C h362 (T (T h376 h373) h372)
  have h378 := C h312 (T (C h19 h329) (C h19 (T (T (T (T (T (T (T (T h325 h311) h304) h308) h306) h305) h344) h351) h377)))
  have h379 := T (T (T (T (T (T (T h338 h331) h328) h326) h318) h314) h378) h371
  have h380 := C h83 h379
  have h381 := C h63 h340
  have h382 := C h83 h342
  have h383 := C h63 h335
  have h384 := T (T (T h317 h350) h347) h346
  have h385 := C h9 h384
  have h386 := T (T (T (T h385 h383) h382) h381) h380
  have h387 := C h386 h253
  have h388 := C h354 h253
  have h389 := T h388 h387
  have h390 := T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h367 h341) h339) h336) h333) h316) h284) h281) h278) h238) h162) h160) h92) h42) h10) h7
  have h391 := C h390 h389
  have h392 := C h349 h19
  have h393 := T (T h365 h364) h319
  have h394 := C h393 h19
  have h395 := T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h58 h82) h6) h100) h98) h190) h188) h219) h287) h308) h306) h305) h344) h385) h383) h382) h381) h380
  have h396 := C h395 (T (T (T h394 h392) h298) h293)
  have h397 := R (M v361 v3)
  have h398 := C h63 h397
  have h399 := T (T h314 h378) h371
  have h400 := C h399 h19
  have h401 := C h322 h19
  have h402 := C h374 h253
  have h403 := T (T (T (T h402 h260) h247) h401) h400
  have h404 := C h83 h403
  have h405 := R (M v334 z)
  have h406 := C h63 h405
  have h407 := C h374 h388
  have h408 := T (T h392 h298) h293
  have h409 := C h345 h408
  have h410 := R (M v309 v3)
  have h411 := C h63 h410
  have h412 := T (T h260 h247) h401
  have h413 := C (T (T (T (T (T (T h238 h162) h160) h92) h42) h10) h7) h412
  have h414 := T h298 h293
  have h415 := C h288 h414
  have h416 := R (M v233 v3)
  have h417 := C h63 h416
  have h418 := T h260 h247
  have h419 := C h89 h418
  have h420 := C (T (T (T (T h58 h82) h6) h100) h98) (T (T (T h252 h251) h250) h293)
  have h421 := R (M v50 v3)
  have h422 := C h63 h421
  have h423 := C h9 h255
  have h424 := R (M v54 v3)
  have h425 := C h83 h424
  have h426 := C h63 h257
  have h427 := C h9 h261
  let v428 := M v2 v3
  have h429 := h v428 v3 v2
  have h430 := S h429
  have h431 := h v361 y v1
  have h432 := S h431
  have h433 := h v1 v2 v0
  have h434 := C h9 (T (T (T h211 h186) h195) h202)
  have h435 := C (T (T (T (T (T (T (T (T h236 h235) h176) h49) h44) h35) h43) h55) h85) h31
  have h436 := C h9 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h435 h181) h78) h77) h155) h154) h136) h133) h131) h114) h111) h109) h220) h218) h185) h227)
  have h437 := R (M v233 y)
  have h438 := C h83 h437
  have h439 := C h349 h31
  have h440 := C h63 h439
  have h441 := R (M v309 y)
  have h442 := C h83 h441
  have h443 := C h322 h31
  have h444 := C (T (T (T (T (T (T (T (T h72 h56) h40) h36) h34) h33) h175) h246) h244) h31
  have h445 := C h330 (T (T (T (T h69 h68) h182) h444) h443)
  have h446 := C h345 (T (T (T (T h439 h435) h181) h78) h77)
  have h447 := C h63 h441
  have h448 := C h83 h443
  have h449 := C h63 h437
  have h450 := C h9 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h211 h186) h184) h183) h173) h172) h171) h170) h169) h135) h168) h163) h69) h68) h182) h444)
  have h451 := C h9 (T (T (T h199 h196) h185) h227)
  have h452 := C h14 (T (T (T (T (T (T (T (T (T (T (T (T h331 h328) h326) h318) h314) h313) h302) h239) h300) h292) h291) h290) h289)
  have h453 := C h14 h338
  have h454 := T (T (T (T (T (T (T (T (T h184 h183) h173) h172) h171) h170) h169) h135) h168) h163
  have h455 := h v334 v1 v0
  have h456 := C h362 h83
  have h457 := C h9 (T (T (T (T (T h456 h363) h352) h455) (C h454 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h453 h452) h323) h201) h144) h143) h139) h177) h231) h229) h226) h210) h207) h205) h451) h450) h449) h448) h447) h446))) (C h31 (T (T (T (T (T (T (T (T (T (T (T (T (T (T h445 h442) h440) h438) h436) h434) h217) h216) h215) h214) h213) h180) h178) h433) (C h399 (T (T (T h214 h213) h180) h178)))))
  have h458 := R (M v361 v0)
  have h459 := C h83 h458
  have h460 := C h362 h63
  have h461 := T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h367 h341) h339) h336) h333) h316) h284) h281) h278) h238) h162) h160) h92) h42) h10) h7) h62) h59
  have h462 := C h461 (T (T (T (T (T (T (T (T (T (T (T (T (T h6 h100) h98) h190) h188) h219) h287) h308) h306) h305) h344) h351) h377) h460)
  have h463 := T (T (T h462 h459) h457) h432
  have h464 := C h9 h463
  have h465 := R (M v368 v2)
  have h466 := C h83 h465
  have h467 := R v368
  have h468 := C h467 h83
  have h469 := C h63 h468
  have h470 := R (M v368 v0)
  have h471 := C h83 h470
  have h472 := C h467 h63
  have h473 := C h395 (T (T (T (T (T (T (T (T (T (T (T (T (T h456 h363) h352) h316) h284) h281) h278) h238) h162) h160) h92) h42) h10) h7)
  have h474 := C h63 h458
  have h475 := C h14 h342
  have h476 := C h14 (T (T (T (T (T (T (T (T (T (T (T (T h276 h272) h270) h268) h266) h240) h301) h321) h319) h317) h350) h347) h346)
  have h477 := T (T (T (T (T (T (T (T (T h155 h154) h136) h133) h131) h114) h111) h109) h220) h218
  have h478 := C h9 (T (T (T (T (T (C h31 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (C h393 (T (T (T h177 h231) h229) h226)) (S h433)) h177) h231) h229) h226) h210) h207) h205) h451) h450) h449) h448) h447) h446)) (C h477 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h445 h442) h440) h438) h436) h434) h217) h216) h215) h214) h213) h180) h178) h138) h167) h165) h197) h348) h476) h475))) (S h455)) h351) h377) h460)
  have h479 := h v361 v0 z
  have h480 := R (M v361 z)
  have h481 := h v25 v3 z
  have h482 := S h481
  have h483 := h z v3 z
  have h484 := S h483
  have h485 := h v361 x v0
  have h486 := T (T (T (T (T (T (T (T (T h325 h311) h304) h308) h306) h305) h344) h351) h377) h460
  have h487 := C h353 h486
  have h488 := T (T (T (T (T (T (T (T (T h269 h265) h264) h190) h188) h219) h287) h303) h320) h329
  have h489 := C h353 h488
  have h490 := C h353 h273
  have h491 := T (T (T (T (T (T (T (T (T (T h152 h151) h150) h149) h148) h116) h6) h100) h98) h263) h274
  have h492 := C h353 h491
  have h493 := C h353 h108
  have h494 := C h353 h110
  have h495 := C h353 h113
  have h496 := C h353 h130
  have h497 := C h353 h132
  let v498 := M x v2
  have h499 := h v498 v3 v2
  have h500 := S h499
  have h501 := T (T (T (T h367 h341) h339) h336) h333
  have h502 := C h501 h353
  have h503 := C h353 h502
  have h504 := C h386 h353
  let v505 := M v2 x
  have h506 := h v505 v1 v2
  have h507 := S h506
  have h508 := R v505
  have h509 := C h508 h390
  have h510 := h x v2 x
  have h511 := C h228 (C h14 (T h510 h509))
  let v512 := M y (M v1 x)
  have h513 := h v512 z v2
  have h514 := S h510
  have h515 := T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h6 h100) h98) h190) h188) h219) h287) h308) h306) h305) h344) h385) h383) h382) h381) h380
  have h516 := T (C h508 h515) h514
  have h517 := C h212 (C h14 h516)
  have h518 := T h510 (C (T h506 h517) h390)
  let v519 := M z v2
  have h520 := R v519
  have h521 := R v498
  have h522 := h v519 x v2
  have h523 := C h312 (C h19 (T h522 (C h521 (T (T (T (T (C h353 (T (T (T (T (T (C h520 (T (T h62 h59) (C h253 h518))) (S h513)) h511) h507) h355) h504)) h503) h376) h373) h372))))
  have h524 := h z v3 v2
  let v525 := M x v0
  have h526 := R v525
  have h527 := R (M v3 z)
  have h528 := C h527 (T (T (T (T (T (T (T (T (T (T (T (C h19 (T (T (T (T (T (T (C h526 (T (T (T (T (T (T (T (T (T (T (T h524 h523) h500) h497) h496) h495) h494) h493) h492) h490) h489) h487)) (S h485)) h431) h478) h474) h473) h472)) (C h19 h468)) (C h19 h463)) (C h19 h366)) (C h19 h338)) (C h19 h332)) (C h19 h315)) (C h19 h283)) (C h19 h277)) (C h19 h237)) (C h19 h159)) (C h19 h91))
  have h529 := h v525 v3 z
  have h530 := h v525 v1 v3
  have h531 := S h530
  have h532 := C h501 h253
  have h533 := T h532 h402
  have h534 := S h529
  have h535 := S h524
  have h536 := C (T h511 h507) h515
  have h537 := C h353 h504
  have h538 := C h312 (C h19 (T (C h521 (T (T (T (T h360 h359) h356) h537) (C h353 (T (T (T (T (T h502 h375) h506) h517) h513) (C h520 (T (T (C h253 (T h536 h514)) h58) h82)))))) (S h522)))
  have h539 := C h353 h123
  have h540 := C h353 h164
  have h541 := C h353 h150
  have h542 := C h353 h151
  have h543 := C h353 h152
  have h544 := T (T (T (T (T (T (T (T (T (T h265 h264) h42) h10) h7) h115) h129) h124) h113) h110) h108
  have h545 := C h353 h544
  have h546 := C h353 h269
  have h547 := T (T (T (T (T (T (T (T (T h325 h311) h304) h238) h162) h160) h92) h263) h274) h273
  have h548 := C h353 h547
  have h549 := T (T (T (T (T (T (T (T (T h456 h363) h352) h316) h284) h281) h278) h303) h320) h329
  have h550 := C h353 h549
  have h551 := T (T (T h431 h478) h474) h473
  have h552 := C h527 (T (T (T (T (T (T (T (T (T (T (T (C h19 h189) (C h19 h187)) (C h19 h286)) (C h19 h307)) (C h19 h285)) (C h19 h343)) (C h19 h384)) (C h19 h342)) (C h19 h379)) (C h19 h551)) (C h19 h472)) (C h19 (T (T (T (T (T (T h468 h462) h459) h457) h432) h485) (C h526 (T (T (T (T (T (T (T (T (T (T (T h550 h548) h546) h545) h543) h542) h541) h540) h539) h499) h538) h535)))))
  have h553 := C (T (T h483 h552) h534) h533
  have h554 := C h253 (T (T (T (T (T h394 h392) h298) h293) h388) h387)
  have h555 := C h253 h403
  have h556 := C h253 (T (T (T h392 h298) h293) h388)
  have h557 := C h253 h401
  have h558 := T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h456 h363) h352) h316) h284) h281) h278) h238) h162) h160) h92) h42) h10) h7) h120) h119) h262) h258) h256) h254) h557) h556) h555) h554) h553
  have h559 := R v16
  have h560 := C h559 (T (T (T (T (T (T (T (T (T (T (T (T (T h155 h154) h136) h133) h131) h114) h111) h109) h220) (C h14 (T (T (T (T h162 h160) h92) h263) h274))) (C h14 h273)) (C h14 h488)) (C h14 h486)) (C h14 h558))
  have h561 := T (T (T (T h560 h531) h529) h528) h484
  have h562 := C h253 h392
  have h563 := C h253 (T (T (T h402 h260) h247) h401)
  have h564 := T (T (T (T h394 h392) h298) h293) h388
  have h565 := C h253 h564
  have h566 := C h253 (T (T (T (T (T h532 h402) h260) h247) h401) h400)
  have h567 := C (T (T h529 h528) h484) h389
  have h568 := T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h567 h566) h565) h563) h562) h299) h297) h296) h295) h126) h125) h6) h100) h98) h190) h188) h219) h287) h308) h306) h305) h344) h351) h377) h460
  have h569 := C h559 (T (T (T (T (T (T (T (T (T (T (T (T (T (C h14 h568) (C h14 h549)) (C h14 h547)) (C h14 h269)) (C h14 (T (T (T (T h265 h264) h190) h188) h219))) h183) h173) h172) h171) h170) h169) h135) h168) h163)
  have h570 := h v525 z v3
  have h571 := S h570
  have h572 := C h121 (T (T (T (T (T (T (T (T (T (C h253 h132) (C h253 h130)) (C h253 h113)) (C h253 h110)) (C h253 h108)) (C h253 h491)) (C h253 h273)) (C h253 h488)) (C h253 h486)) (C h253 h558))
  have h573 := h (M v2 v519) x v3
  have h574 := S h573
  have h575 := C h127 (T (T (T (T (T (T (T (T (T (C h253 h568) (C h253 h549)) (C h253 h547)) (C h253 h269)) (C h253 h544)) (C h253 h152)) (C h253 h151)) (C h253 h150)) (C h253 h164)) (C h253 h123))
  let v576 := M x v3
  have h577 := R v576
  have h578 := C h577 (T (T (T (T (T (T (T (T (T (T (T (T h524 h523) h500) h497) h496) h495) h494) h493) h492) h490) h489) h487) (C h353 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h456 h363) h352) h316) h284) h281) h278) h238) h162) h160) h92) h42) h10) h7) h120) h119) h262) h258) h256) h254) h557) h556) h555) h554) h553) (C (T h570 h575) h19))))
  have h579 := C h527 (T (T (C h19 (T (T (T (T (T h578 h574) h572) h571) h530) h569)) (C h19 h561)) (C h19 h39))
  have h580 := h v576 v3 z
  have h581 := T (T (T (T (T (T (T (T (T (T (T h580 h579) h482) h34) h33) h175) h246) h244) h301) h321) h378) h371
  have h582 := C h577 (T (T (T (T (T (T (T (T (T (T (T (T (C h353 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (C (T h572 h571) h19) h567) h566) h565) h563) h562) h299) h297) h296) h295) h126) h125) h6) h100) h98) h190) h188) h219) h287) h308) h306) h305) h344) h351) h377) h460)) h550) h548) h546) h545) h543) h542) h541) h540) h539) h499) h538) h535)
  have h583 := C h83 (T (T (T (T (T (T h560 h531) h570) h575) h573) h582) (C h581 h253))
  have h584 := R (M v16 y)
  have h585 := C h63 h584
  have h586 := T (T (T (T h483 h552) h534) h530) h569
  have h587 := C h390 h586
  let v588 := M v0 z
  have h589 := R v588
  have h590 := T (T (T (T (T (T (C h589 (T (T (T (T (T h388 h387) h587) h585) h583) (C h63 h480))) (S h479)) h431) h478) h474) h473) h472
  have h591 := C h63 h590
  have h592 := R v428
  have h593 := h v588 v2 v3
  have h594 := h v588 v1 v3
  have h595 := S h594
  have h596 := S h580
  have h597 := C h527 (T (T (C h19 h28) (C h19 h586)) (C h19 (T (T (T (T (T h560 h531) h570) h575) h573) h582)))
  have h598 := T (T (T (T (T (T (T (T (T (T (T h365 h364) h313) h302) h236) h235) h176) h49) h44) h481) h597) h596
  have h599 := C h598 h253
  have h600 := C h589 (T (T (T (T (T (C h83 h480) (C h63 (T (T (T (T (T (T h599 h578) h574) h572) h571) h530) h569))) (C h83 h584)) (C h515 h561)) h532) h402)
  have h601 := T (T (T (T (T (T h468 h462) h459) h457) h432) h479) h600
  have h602 := C h14 h472
  have h603 := C h14 (T (T (T (T (T (T (T (T (T (T (T h338 h331) h328) h326) h318) h314) h378) h371) h431) h478) h474) h473)
  have h604 := C h559 (T (T (T (T (T (T (T (T (T h138 h167) h165) h197) h348) h476) h475) h603) h602) (C h14 h601))
  have h605 := C h14 (T (T (T (T (T (T (T (T (T (T (T h462 h459) h457) h432) h365) h364) h319) h317) h350) h347) h346) h342)
  have h606 := C h14 h468
  have h607 := C h559 (T (T (T (T (T (T (T (T (T (C h14 h590) h606) h605) h453) h452) h323) h201) h144) h143) h139)
  have h608 := h v588 v0 v3
  have h609 := R (M v588 v3)
  have h610 := C h83 h601
  have h611 := C h63 h470
  have h612 := C h83 h472
  have h613 := C h63 h465
  have h614 := C h9 h551
  let v615 := M v0 v3
  have h616 := R v615
  have h617 := C h312 (T (C h19 (T (T (T (C h616 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h6 h100) h98) h190) h188) h219) h287) h308) h306) h305) h344) h385) h383) h382) h381) h380) h614) h613) h612) h611) h610) (C h63 h609))) (S h608)) h594) h607)) (C h19 (T (T (T h604 h595) h593) (C h592 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h591 h471) h469) h466) h464) h367) h341) h339) h336) h333) h316) h284) h281) h278) h238) h162) h160) h92) h42) h10) h7)))))
  have h618 := h v615 v3 v2
  have h619 := C h19 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h618 h617) h430) h427) h426) h425) h423) h422) h420) h419) h417) h415) h413) h411) h409) h407) h406) h404) h398) h396) h391)
  let v620 := M v3 v615
  have h621 := C h616 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (C h83 h609) h591) h471) h469) h466) h464) h367) h341) h339) h336) h333) h316) h284) h281) h278) h238) h162) h160) h92) h42) h10) h7)
  have h622 := C h19 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (C h515 h533) (C h461 (T (T (T h260 h247) h401) h400))) (C h83 h397)) (C h63 h564)) (C h83 h405)) (C h354 h402)) (C h330 h412)) (C h83 h410)) (C (T (T (T (T (T (T h6 h100) h98) h190) h188) h219) h287) h408)) (C h275 h418)) (C h83 h416)) (C h101 h414)) (C (T (T (T (T h42 h10) h7) h62) h59) (T (T (T h260 h259) h257) h255))) (C h83 h421)) (C h9 h252)) (C h63 h424)) (C h83 h251)) (C h9 h294)) h429) (C h312 (T (C h19 (T (T (T (C h592 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h6 h100) h98) h190) h188) h219) h287) h308) h306) h305) h344) h385) h383) h382) h381) h380) h614) h613) h612) h611) h610)) (S h593)) h594) h607)) (C h19 (T (T (T h604 h595) h608) h621))))) (S h618))
  have h623 := h v3 x x
  have h624 := h x v2 z
  have h625 := S h624
  have h626 := h v3 v3 (M v2 (M x z))
  have h627 := T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h58 h82) h6) h100) h98) h190) h188) h219) h287) h308) h306) h305) h344) h385) h383) h382) h381) h380) h369) h622
  have h628 := h v576 y v1
  have h629 := h v1 v1 (M v0 (M x y))
  have h630 := h x v0 y
  have h631 := h v1 x x
  have h632 := T (T (T (T (T (C h393 h31) h439) h435) h181) h78) h77
  have h633 := C h354 h632
  have h634 := R (M v361 y)
  have h635 := C h83 h634
  have h636 := T (T (T (T (T h69 h68) h182) h444) h443) (C h399 h31)
  have h637 := C h461 h636
  have h638 := C h395 h632
  have h639 := C h63 h634
  have h640 := C h374 h636
  have h641 := h v368 v1 v0
  have h642 := h v368 x x
  have h643 := S h642
  have h644 := C h581 (T (T (T h360 h359) h356) h537)
  have h645 := C h577 h83
  have h646 := R (M v576 v0)
  have h647 := C h577 h63
  have h648 := C h598 (T (T (T h503 h376) h373) h372)
  have h649 := T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h619 h370) h367) h341) h339) h336) h333) h316) h284) h281) h278) h238) h162) h160) h92) h42) h10) h7) h62) h59
  have h650 := R v620
  have h651 := S h630
  have h652 := h x v3 v3
  have h653 := C h312 (T (C h19 h647) (C h19 (T (T (T (T (T (T h645 h644) h643) h369) h622) (h v620 v3 x)) (C (R v4) (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (C h19 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (C h649 h518) (C h83 (R (M v512 v2)))) (C h9 (T h536 h509))) (C h515 h516)) h502) h375) h506) h517) (h v512 v3 v2)) (C h312 (T (C h19 (T (T (T (T (T (T (T h536 h514) h652) (C (R (M v3 v3)) (T (T (C h19 (T (T (T (T h628 (C h9 (T (T (T (T (T (C h31 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (C h581 (T h629 (C h651 (C h14 h651)))) (S h631)) h177) h231) h229) h226) h210) h207) h205) h451) h450) h449) h448) h447) h446) h640) h639) h638)) (C h477 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h637 h635) h633) h445) h442) h440) h438) h436) h434) h217) h216) h215) h214) h213) h180) h178) h138) h167) h165) h197) h348) h476) h475) h603) h602))) (S h641)) h642) h648) h647))) (C h63 h646)) (C h627 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h645 h644) h643) h367) h341) h339) h336) h333) h316) h284) h281) h278) h238) h162) h160) h92) h42) h10) h7))) (C h650 h63))) (C h19 (C h650 h83))) (C h19 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (C h649 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h6 h100) h98) h190) h188) h219) h287) h308) h306) h305) h344) h385) h383) h382) h381) h380) h642) h648) h647)) (C h83 h646)) (C h9 (T (T (T (T (T h645 h644) h643) h641) (C h454 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h606 h605) h453) h452) h323) h201) h144) h143) h139) h177) h231) h229) h226) h210) h207) h205) h451) h450) h449) h448) h447) h446) h640) h639) h638))) (C h31 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h637 h635) h633) h445) h442) h440) h438) h436) h434) h217) h216) h215) h214) h213) h180) h178) h631) (C h598 (T (C h630 (C h14 h630)) (S h629)))))))) (S h628)) h580) h579) h482) h34) h33) h175) h246) h244) h301) h321) h378) h371) h479) h600))))) (S (h v588 v3 v3))) h608) h621) (C h616 h63))) (C h19 (C h616 h83))))) h617) h430) h427) h426) h425) h423) h422) h420) h419) h417) h415) h413) h411) h409) h407) h406) h404) h398) h396) h391) (C h63 (R (M v368 z)))) (C h83 (T (T (T h532 h402) h623) (C h598 (T (C h624 (C h19 h624)) (S h626)))))) (C h63 (R (M v576 v3)))) (C h627 (T (C h581 (T h626 (C h625 (C h19 h625)))) (S h623)))) (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h619 h370) h367) h341) h339) h336) h333) h316) h284) h281) h278) h238) h162) h160) h92) h42) h10) h7) (T (T (T (T (T h388 h387) h587) h585) h583) (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h6 h100) h98) h190) h188) h219) h287) h308) h306) h305) h344) h385) h383) h382) h381) h380) h369) h622) (T (T (T (T (T (T (T h599 h578) h574) h572) h571) h529) h528) h484)))))) (S (h v620 v2 z))) h619) h370) h367) h341) h339) h336) h333) h316) h284) h281) h278) h238) h162) h160) h92) h42) h10) h7)))))
  have h654 := h v576 v3 v2
  T (T h652 (C (T (T (T (T (T (T (T h46 h45) h481) h597) h596) h654) h653) h5) (C h19 (T (T h654 h653) h5)))) (S (h v3 v3 x))

