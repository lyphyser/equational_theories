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
theorem Equation2113_implies_Equation4512 (G: Type _) [Magma G] (h: Equation2113 G) : Equation4512 G := fun x y z =>
  let v0 := M x y
  let v1 := M y z
  let v2 := M v0 z
  have h3 := R v0
  let v4 := M v1 v2
  have h5 := R v4
  have h6 := h z v1 v2
  have h7 := S h6
  have h8 := R v2
  let v9 := M v1 z
  have h10 := h v9 v2 v0
  have h11 := S h10
  let v12 := M v2 v0
  have h13 := R v12
  have h14 := R v9
  have h15 := R z
  have h16 := h v0 v2 v2
  have h17 := S h16
  let v18 := M v2 v2
  have h19 := h v18 z v18
  have h20 := S h19
  have h21 := R v18
  have h22 := h z v0 z
  have h23 := S h22
  have h24 := C h23 h21
  have h25 := h z v2 v2
  have h26 := C (T h25 (C (T (T h23 h25) h24) h21)) (T h25 h24)
  let v27 := M x v1
  have h28 := h (M z z) v27 v0
  have h29 := S h28
  let v30 := M v27 v0
  let v31 := M v27 v1
  have h32 := h v30 (M v31 v0) v30
  have h33 := S h32
  have h34 := h v1 v27 v0
  have h35 := R v30
  have h36 := h v1 x y
  have h37 := S h36
  have h38 := h y v27 v0
  have h39 := C (T h38 (C (T h37 h34) h35)) h34
  have h40 := T h39 h33
  have h41 := S h25
  have h42 := C h22 h21
  have h43 := C (T (C (T (T h42 h41) h22) h21) h41) (T h42 h41)
  let v44 := M x v2
  have h45 := h v27 (M v44 v1) v27
  have h46 := S h45
  have h47 := h v2 x v1
  have h48 := R v27
  have h49 := C (C h47 h48) h47
  have h50 := T h49 h46
  have h51 := C h8 h50
  have h52 := T (T (C h51 h8) h49) h46
  let v53 := M v2 v27
  have h54 := h (M v53 v2) v2 v2
  have h55 := S h47
  have h56 := C (C h55 h48) h55
  have h57 := R v1
  have h58 := h y v0 v0
  let v59 := M v0 v0
  have h60 := R v59
  have h61 := h y x y
  have h62 := T (C h61 h60) (S h58)
  have h63 := C (T (T (T (C h62 h57) h39) h33) (C (T (T (T h45 h56) h54) (C h52 (T h19 h43))) h3)) h40
  have h64 := h v59 y v1
  have h65 := T (T (T (T h64 h63) h29) h26) h20
  have h66 := h v2 x y
  have h67 := S h66
  have h68 := C (C h67 h3) h67
  have h69 := h v0 (M v44 y) v0
  have h70 := T h69 h68
  have h71 := C h70 h65
  have h72 := T h71 h17
  have h73 := C h72 h15
  have h74 := S h64
  have h75 := S h34
  have h76 := C (T (C (T h75 h36) h35) (S h38)) h75
  have h77 := T h32 h76
  have h78 := T h58 (C (S h61) h60)
  have h79 := S h54
  have h80 := T h45 h56
  have h81 := C h8 h80
  have h82 := C h81 h8
  have h83 := T (T h45 h56) h82
  have h84 := C (T (T (T (C (T (T (T (C h83 (T h26 h20)) h79) h49) h46) h3) h32) h76) (C h78 h57)) h77
  have h85 := T (T (T (T h19 h43) h28) h84) h74
  have h86 := S h69
  have h87 := C (C h66 h3) h66
  have h88 := T h87 h86
  have h89 := C h88 h85
  have h90 := C h70 h21
  have h91 := T h90 h89
  have h92 := C h91 h15
  have h93 := C h88 h21
  let v94 := M x v0
  have h95 := h v0 (M v94 y) v0
  have h96 := S h95
  have h97 := h v0 x y
  have h98 := C (C h97 h3) h97
  have h99 := C h85 h3
  have h100 := h (M v18 v0) v0 v1
  have h101 := S h100
  let v102 := M v0 v1
  have h103 := R v102
  have h104 := C h65 h3
  have h105 := S h97
  have h106 := C (C h105 h3) h105
  let v107 := M x z
  have h108 := h v0 (M v107 y) v0
  have h109 := S h108
  have h110 := h z x y
  have h111 := h v0 x v1
  have h112 := S h111
  have h113 := h z y x
  have h114 := S h113
  let v115 := M y x
  have h116 := R v115
  have h117 := R x
  have h118 := h v1 v0 v27
  let v119 := M v0 v27
  have h120 := R v119
  have h121 := h y x v1
  have h122 := C (C (T (C h121 h120) (S h118)) h117) h116
  have h123 := h v119 y x
  have h124 := h v27 (M v94 v1) v27
  have h125 := C (T (T h124 (C (T (T (T (C h112 h48) h123) h122) h114) h112)) (C h110 h3)) h110
  have h126 := C h83 h65
  have h127 := T (T (T h126 h79) h49) h46
  have h128 := C h52 h85
  have h129 := C h83 h21
  have h130 := T h129 h128
  have h131 := C (T (T (T (C h130 h15) (C h127 h15)) h125) h109) (T (T (T (T h125 h109) h95) h106) h104)
  have h132 := h v18 v27 z
  have h133 := T (T (T (T (T (T h64 h63) h29) h26) h20) h132) h131
  have h134 := h v1 y z
  have h135 := S h134
  have h136 := h v59 y z
  have h137 := S h136
  have h138 := C (C h78 h15) h57
  let v139 := M y v1
  have h140 := h v1 (M v139 z) v1
  have h141 := C (T (T h140 (C (T (T (C h135 h57) h138) h137) h135)) (C h133 h57)) h103
  have h142 := T (T (T (T (T (T h141 h101) h99) h98) h96) h16) h93
  have h143 := C h142 h15
  have h144 := C (T (T h143 h92) h73) h14
  have h145 := h v102 v1 z
  have h146 := h v102 v1 v27
  have h147 := S h146
  let v148 := M v1 v27
  have h149 := R v148
  have h150 := C (C h62 h15) h57
  have h151 := S h132
  have h152 := S h110
  have h153 := S h123
  have h154 := S h121
  have h155 := C (C (T h118 (C h154 h120)) h117) h116
  have h156 := C (T (T (C h152 h3) (C (T (T (T h113 h155) h153) (C h111 h48)) h111)) (S h124)) h152
  have h157 := C h52 h21
  have h158 := T h126 h157
  have h159 := T (T (T h45 h56) h54) h128
  have h160 := C (T (T (T h108 h156) (C h159 h15)) (C h158 h15)) (T (T (T (T h99 h98) h96) h108) h156)
  have h161 := T (T (T (T (T (T h160 h151) h19) h43) h28) h84) h74
  have h162 := C (T (T (C h161 h57) (C (T (T h136 h150) (C h134 h57)) h134)) (S h140)) h103
  have h163 := T (T (T (T (T (T h90 h17) h95) h106) h104) h100) h162
  have h164 := T h71 h93
  have h165 := T h16 h89
  have h166 := C (T (T (T (T (T h113 h155) h153) (C h165 h48)) (C h164 h48)) (C h163 h48)) h149
  have h167 := C (T (T (T (T (T (C h142 h48) (C h91 h48)) (C h72 h48)) h123) h122) h114) h149
  have h168 := T h146 h167
  have h169 := h v0 y z
  have h170 := S h169
  have h171 := h v1 (M (M y v0) z) v1
  have h172 := C (T (T (T h171 (C (C h170 h57) h170)) (C h168 h3)) (C (T (T (T h166 h147) h145) h144) h3)) h13
  have h173 := C (C (T h172 h11) h8) h5
  have h174 := S h171
  have h175 := C (C h169 h57) h169
  have h176 := T h166 h147
  have h177 := C h176 h3
  have h178 := S h145
  have h179 := C h163 h15
  have h180 := C h164 h15
  have h181 := C h165 h15
  have h182 := C (T (T h181 h180) h179) h14
  have h183 := C (T (T (T (C (T (T (T h182 h178) h146) h167) h3) h177) h175) h174) h13
  have h184 := h v9 v2 v2
  have h185 := h v18 v0 v2
  have h186 := S h185
  let v187 := M v0 v2
  have h188 := R v187
  have h189 := C h142 h8
  have h190 := T (T h99 h98) h96
  have h191 := C h8 h190
  have h192 := C h191 h8
  have h193 := T (T h95 h106) h104
  have h194 := C h8 h193
  have h195 := h v12 v1 v2
  have h196 := S h195
  have h197 := C (C (T h10 h183) h8) h5
  have h198 := C (T (T (T h6 h197) h196) h194) h8
  let v199 := M z v2
  have h200 := h v199 v27 y
  have h201 := S h200
  let v202 := M v27 y
  have h203 := R v202
  have h204 := R y
  have h205 := C (T (T (T h191 h195) h173) h7) h8
  have h206 := C h194 h8
  have h207 := h v27 (M v107 v1) v27
  have h208 := h z x v1
  let v209 := M z v27
  have h210 := h v209 y v1
  have h211 := R v139
  have h212 := R v209
  have h213 := C h176 h48
  have h214 := h v148 z v27
  have h215 := T h214 (C (T h213 h154) h212)
  have h216 := h v1 x v1
  have h217 := S h216
  have h218 := h v27 v31 v27
  have h219 := C (T (T (C (T (C (T (T h218 (C (C h217 h48) h217)) (C h215 h57)) h211) (S h210)) h15) (C (C h208 h48) h208)) (S h207)) (T (T (T (T (T h125 h109) h69) h68) h206) h205)
  have h220 := h v139 v27 z
  have h221 := h y y z
  have h222 := S h221
  have h223 := h v1 (M (M y y) z) v1
  have h224 := C (T (T h223 (C (C h222 h57) h222)) (C (T h220 h219) h204)) h203
  have h225 := C (T (T (T (T (T (T (T (T (T (T h224 h201) h198) h192) h87) h86) h95) h106) h104) h100) h162) h8
  have h226 := S h220
  have h227 := S h214
  have h228 := C h168 h48
  have h229 := C (T h121 h228) h212
  have h230 := S h208
  have h231 := C (T (T h207 (C (C h230 h48) h230)) (C (T h210 (C (T (T (C (T h229 h227) h57) (C (C h216 h48) h216)) (S h218)) h211)) h15)) (T (T (T (T (T h198 h192) h87) h86) h108) h156)
  have h232 := C (T (T (C (T h231 h226) h204) (C (C h221 h57) h221)) (S h223)) h203
  have h233 := h v199 v27 v2
  have h234 := S h233
  let v235 := M v27 v2
  have h236 := R v235
  have h237 := h v139 v1 y
  have h238 := S h237
  have h239 := h y v0 v27
  have h240 := T (T h113 h155) h153
  let v241 := M (M v0 y) v27
  have h242 := R v241
  have h243 := T (C h242 h240) (S h239)
  have h244 := h z v241 z
  have h245 := h v102 v1 v2
  have h246 := S h245
  have h247 := C h225 h5
  have h248 := h v202 v1 v2
  have h249 := C (T (T (T (T h248 h247) h246) h146) h167) h48
  let v250 := M v202 v27
  have h251 := h v250 v27 v0
  have h252 := S h251
  have h253 := S h248
  have h254 := C (T (T (T (T (T (T (T (T (T (T h141 h101) h99) h98) h96) h69) h68) h206) h205) h200) h232) h8
  have h255 := C h254 h5
  have h256 := C (T (T (T (T h166 h147) h245) h255) h253) h48
  have h257 := T (T (C h159 h204) (C h158 h204)) (C (T (T (T h129 h79) h49) h46) (T (T h121 h228) h256))
  have h258 := C h257 h3
  have h259 := h v1 v2 v2
  have h260 := S h259
  have h261 := h v2 y z
  have h262 := S h261
  have h263 := h v1 (M (M y v2) z) v1
  have h264 := C (T h263 (C (C h262 h57) h262)) h21
  have h265 := C h57 h65
  have h266 := C (T (T (T (T h265 h264) h260) h36) h258) h40
  have h267 := C h57 h85
  have h268 := C (T (C (C h261 h57) h261) (S h263)) h21
  have h269 := C (T (T h259 h268) h267) h211
  have h270 := C (T (T h265 h264) h260) h211
  have h271 := h v59 v1 v139
  have h272 := T (T (T (T h141 h101) h99) h98) h96
  have h273 := C h272 h193
  have h274 := T (T (T (T h95 h106) h104) h100) h162
  have h275 := C h274 (T (T (T h198 h192) h87) h86)
  have h276 := C (T (T (T (T (T (T (T (T (T (T h275 h273) h160) h151) h19) h43) h28) h84) h74) h271) (C h270 (T (T (T (T (T h269 h266) h252) h249) h213) h154))) (T h244 (C (C h243 h15) h243))
  have h277 := C (T (T (T h276 h238) h220) h219) h8
  have h278 := h v199 v0 z
  have h279 := C (T (T (C (T (T (T (C (T (T (T (T (T h69 h68) h206) h205) h278) h277) h236) h234) h200) h232) h8) h225) h189) h188
  have h280 := h v235 v0 v2
  have h281 := C h127 h204
  have h282 := C h130 h204
  have h283 := C (T (T (T h45 h56) h54) h157) (T (T h249 h213) h154)
  have h284 := T (T h283 h282) h281
  have h285 := h v250 v27 v2
  have h286 := C (C (T (T (T (T (T (T (T h269 h266) h252) h285) (C (T (C h284 h8) (C (T (T (T (T h248 h247) h246) h145) h144) h8)) (T (T h280 h279) h186))) (S h184)) h10) h183) h8) h5
  have h287 := h v139 v1 v2
  have h288 := C h272 (T (T (T h69 h68) h206) h205)
  have h289 := C h274 h190
  have h290 := C (T (T (T (T (T (T (T (T h64 h63) h29) h26) h20) h132) h131) h289) h288) h15
  let v291 := M v59 z
  have h292 := h v291 v0 v27
  have h293 := S h292
  have h294 := C (T (T (T (T (T (T (T (T h275 h273) h160) h151) h19) h43) h28) h84) h74) h15
  have h295 := T (T h123 h122) h114
  have h296 := T h239 (C h242 h295)
  have h297 := C (T (T (T (T (C h284 h3) h37) h259) h268) h267) h77
  have h298 := C (T (T (T (T (T (T (T (T (T (T (C h269 (T (T (T (T (T h121 h228) h256) h251) h297) h270)) (S h271)) h64) h63) h29) h26) h20) h132) h131) h289) h288) (T (C (C h296 h15) h296) (S h244))
  have h299 := S h287
  have h300 := C (T (T (T h231 h226) h237) h298) h8
  have h301 := C (T (T (T (T (T h300 (S h278)) h198) h192) h87) h86) h236
  have h302 := C (C (T (T (T (T (T (T (T h172 h11) h184) (C (T (C (T (T (T (T h182 h178) h245) h255) h253) h8) (C h257 h8)) (T (T h185 (C (T (T (C h163 h8) h254) (C (T (T (T h224 h201) h233) h301) h8)) h188)) (S h280)))) (S h285)) h251) h297) h270) h8) h5
  have h303 := T (T (T (T (T (T h6 h197) h302) h299) h237) h298) h294
  have h304 := C (T h81 (C (T (T (T h181 h180) h179) (C h272 h303)) h50)) h240
  have h305 := h (M v53 z) v27 x
  have h306 := S h305
  have h307 := h x y z
  have h308 := S h307
  have h309 := h v1 (M v115 z) v1
  have h310 := T (T (T (T (T (T h290 h276) h238) h287) h286) h173) h7
  have h311 := C (T (C (T (T (T (C h274 h310) h143) h92) h73) h80) h51) h295
  have h312 := h v27 (M (M x v27) v1) v27
  have h313 := S h312
  have h314 := h v27 x v1
  let v315 := M v27 v27
  have h316 := h v315 v1 v315
  have h317 := R v315
  have h318 := C h217 h317
  have h319 := h v1 v27 v27
  have h320 := C (T (T (T (T h136 h150) (C (T h319 (C (T (T h217 h319) h318) h317)) (T h319 h318))) (S h316)) (C h314 h48)) h314
  have h321 := C h161 h48
  have h322 := C (T h275 h273) h48
  have h323 := C (T (T (T h322 h321) h320) h313) (T (T (T (T (T (T (T (T (T (T (T h123 h122) h114) h6) h197) h302) h299) h237) h298) h294) h292) h311)
  have h324 := h v199 v0 v27
  have h325 := C (T (T (C h165 h117) (C h164 h117)) (C (T (T (T (T (T (T (T h90 h17) h69) h68) h206) h205) h324) h323) h117)) (T h309 (C (C h308 h57) h308))
  let v326 := M (M v0 x) v1
  have h327 := S h324
  have h328 := C (T h289 h288) h48
  have h329 := C h133 h48
  have h330 := S h314
  have h331 := S h319
  have h332 := C h216 h317
  have h333 := C (T (T (T (T (C h330 h48) h316) (C (T (C (T (T h332 h331) h216) h317) h331) (T h332 h331))) h138) h137) h330
  have h334 := C (T (T (T h312 h333) h329) h328) (T (T (T (T (T (T (T (T (T (T (T h304 h293) h290) h276) h238) h287) h286) h173) h7) h113) h155) h153)
  have h335 := C (T (T (C (T (T (T (T (T (T (T h334 h327) h198) h192) h87) h86) h16) h93) h117) (C h91 h117)) (C h72 h117)) (T (C (C h307 h57) h307) (S h309))
  have h336 := h v199 v2 v27
  have h337 := R v53
  have h338 := h v209 v27 v2
  have h339 := h v59 z v59
  have h340 := C (C h8 h310) h8
  have h341 := C (T h340 h23) h85
  have h342 := h v291 v2 v2
  have h343 := T (T (T (T (T (T (T (T h6 h197) h302) h299) h237) h298) h294) h342) h341
  have h344 := R (M z v59)
  have h345 := C (C h8 h303) h8
  have h346 := C (T h22 h345) h65
  have h347 := T (T (T (T (T (T (T (T (T (T (T (C h343 (T (T (T (T (T (T (T (T (T (T h325 h306) h304) h293) h290) h276) h238) h287) h286) h173) h7)) (C (T (T h346 (C (T (T (T (T (T (T (T (T (T (T h340 h23) h6) h197) h302) h299) h237) h298) h294) h342) h341) h21)) (C h344 h85)) h343)) (S h339)) h64) h63) h29) h26) h20) h132) h131) h289) h288
  have h348 := h v326 z v27
  have h349 := S h342
  have h350 := C (T (T (T (T (C (T (T (T (T (T (T (T h69 h68) h206) h205) h233) (C (T (T h300 (C (T (T h294 h342) h341) h8)) (C (T (T (T (T (T (T (T h346 h349) h292) h311) h305) h335) h348) (C (T (T (T (T (C h347 h48) h322) h321) h320) h313) h212)) h8)) h236)) (S h338)) (C (T (T (T (T h6 h197) h196) h194) (C h8 (T (T (T (T (T (T h99 h98) h96) h69) h68) h206) h205))) h48)) h337) (S h336)) h324) h323) (C h48 (T h305 h335))) h8
  have h351 := T (T (T (T (T (T (T (T h346 h349) h290) h276) h238) h287) h286) h173) h7
  have h352 := C h351 (T (T (T (T (T (T (T (T (T (T h6 h197) h302) h299) h237) h298) h294) h292) h311) h305) h335)
  have h353 := C (T (T (C h344 h65) (C (T (T (T (T (T (T (T (T (T (T h346 h349) h290) h276) h238) h287) h286) h173) h7) h22) h345) h21)) h341) h351
  T (T (h v27 v1 v0) (C (T (C h215 h3) (C (T (T (T (T h229 h227) (h v148 z v0)) (C (T (T (T (T (T h177 h175) h174) h36) h258) (C (T (T (T (T h283 h282) h281) h248) (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h225 h189) (C h91 h8)) (C h72 h8)) (h v187 v27 v2)) (C (T (C (T (T (T (C (T (T (T (T h45 h56) h82) (C (T (T (T (T (T (T (T (T (T (T (T (T h51 (h v53 v0 v2)) (C (T (T h350 (C (C h48 (T h325 h306)) h8)) (C (T (T (T h334 h327) h233) h301) h8)) h188)) h279) h186) h19) h43) h28) h84) h74) h339) h353) h352) h8)) (C h347 h8)) h188) (S (h v199 v0 v2))) h336) (C (T (T (T (T (T (T (T (C (T (T (T (T (C h8 (T (T (T (T (T (T h198 h192) h87) h86) h95) h106) h104)) h191) h195) h173) h7) h48) h338) (C (T (T (C (T (T (T (T (T (T (T (C (T (T (T (T h312 h333) h329) h328) (C (T (T (T (T (T (T (T (T (T (T (T h275 h273) h160) h151) h19) h43) h28) h84) h74) h339) h353) h352) h48)) h212) (S h348)) h325) h306) h304) h293) h342) h341) h8) (C (T (T h346 h349) h290) h8)) h277) h236)) h234) h198) h192) h87) h86) h337)) h8) h350) h236)) (S (h v326 v27 v2))) h325) h306) h304) h293) h290) h276) h238) h287) h286) h173) h7) h5)) h3)) (R (M z v0)))) (S (h v4 z v0))) h3)) (R (M v1 v0)))) (S (h v2 v1 v0))

