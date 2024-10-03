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
theorem Equation2308_implies_Equation3388 (G: Type _) [Magma G] (h: Equation2308 G) : Equation3388 G := fun x y z =>
  let v0 := M z y
  let v1 := M x v0
  let v2 := M z v1
  have h3 := h v2 v2 y
  have h4 := S h3
  have h5 := R y
  have h6 := h x z y
  have h7 := R v2
  have h8 := C h7 (C h7 h6)
  let v9 := M x y
  have h10 := h (M v2 x) v9 x
  have h11 := S h6
  have h12 := R x
  have h13 := h y x x
  have h14 := S h13
  let v15 := M x x
  let v16 := M x (M y v15)
  have h17 := R v16
  have h18 := C (T (C h7 (T (C h17 h11) h14)) h11) h5
  have h19 := h v16 v2 y
  have h20 := T h19 h18
  have h21 := C h20 h12
  have h22 := T h13 h21
  have h23 := h v1 y v0
  have h24 := R z
  have h25 := C (C h24 (S h23)) h5
  let v26 := M y (M v1 (M y v0))
  have h27 := h v26 z y
  have h28 := h v26 v9 x
  have h29 := S h28
  have h30 := S h27
  have h31 := C (C h24 h23) h5
  have h32 := S h19
  have h33 := C (T h6 (C h7 (T h13 (C h17 h6)))) h5
  have h34 := T h33 h32
  have h35 := C h34 h12
  let v36 := M v9 x
  have h37 := h v36 v9 x
  have h38 := S h37
  have h39 := C h22 h22
  have h40 := C h20 h39
  let v41 := M y y
  have h42 := R v41
  have h43 := C h34 h42
  have h44 := C (T h43 h40) h11
  have h45 := C h7 (T (T (T h44 h38) h35) h14)
  have h46 := C (T (T h45 h31) h30) h22
  have h47 := h v36 v1 v1
  have h48 := S h47
  have h49 := R v1
  let v50 := M v1 v1
  have h51 := R v50
  have h52 := h (M v1 (M y v50)) x v0
  have h53 := R v0
  have h54 := h y v1 v1
  have h55 := C (T (T (C (C h12 h54) h53) (S h52)) (C h49 (C h22 h51))) h49
  have h56 := C h20 h42
  have h57 := T h35 h14
  have h58 := C h57 h57
  have h59 := C h34 h58
  have h60 := C (T h59 h56) h6
  have h61 := C h7 (T (T (T h13 h21) h37) h60)
  have h62 := C (T h6 h61) (T (T (T h55 h48) h35) h14)
  have h63 := C (T (T (C h49 (C h57 h51)) h52) (C (C h12 (S h54)) h53)) h49
  have h64 := h v36 v2 v9
  have h65 := S h64
  have h66 := R v9
  let v67 := M v2 v9
  have h68 := R v67
  have h69 := h (M v2 (M y v67)) x y
  have h70 := h y v2 v9
  have h71 := C h20 h57
  have h72 := R v36
  have h73 := C h34 h72
  have h74 := C (T (T (T (T h73 h71) (C (C h12 h70) h5)) (S h69)) (C h7 (C h22 h68))) h66
  have h75 := C h20 h72
  have h76 := C h34 h22
  have h77 := C (T h76 h75) h66
  have h78 := C h12 (T (T (T (T h77 h74) h65) h47) h63)
  have h79 := C (T h73 h71) h66
  have h80 := C h12 h79
  have h81 := C (T (T (T (T (C h7 (C h57 h68)) h69) (C (C h12 (S h70)) h5)) h76) h75) h66
  have h82 := C h12 (T (T (T h13 h21) h64) h81)
  have h83 := C h12 (T (T (T h74 h65) h35) h14)
  have h84 := C h12 h77
  have h85 := C h12 (T (T (T (T h55 h48) h64) h81) h79)
  have h86 := C (T h45 h11) (T (T (T h13 h21) h47) h63)
  let v87 := M v9 v41
  have h88 := h v87 v2 y
  have h89 := T (T (T (T h88 h86) h85) h84) h83
  have h90 := C h89 (T (T (T (T h82 h80) h78) h62) h46)
  have h91 := h v16 v1 y
  have h92 := S h91
  let v93 := M v1 y
  have h94 := R v93
  have h95 := C h49 (C h34 h94)
  have h96 := h (M v1 (M v9 v93)) v9 x
  have h97 := C h49 (C h20 h94)
  have h98 := C h97 h22
  have h99 := h v16 y y
  have h100 := S h99
  have h101 := C h5 h43
  have h102 := C h101 h57
  have h103 := C h66 (T (T (T h102 h100) h91) h98)
  have h104 := h (M y v87) v9 x
  have h105 := C h5 h56
  have h106 := S h88
  have h107 := C h5 (T (T (T (T (T h82 h80) h78) h62) h106) h43)
  have h108 := C (T (T (T (T (T h107 h105) h104) (C h103 h12)) (S h96)) h95) h57
  have h109 := T (T (T (T h82 h80) h78) h62) h106
  have h110 := C h109 (T (T (T h108 h92) h19) h18)
  have h111 := C h5 (T (T (T (T (T h56 h88) h86) h85) h84) h83)
  have h112 := C h105 h22
  have h113 := C h95 h57
  have h114 := C h66 (T (T (T h113 h92) h99) h112)
  have h115 := C (T (T (T (T (T h97 h96) (C h114 h12)) (S h104)) h101) h111) h22
  have h116 := C h66 (T h113 h115)
  have h117 := C h20 (T (T (T h33 h32) h99) h112)
  have h118 := C h34 h66
  let v119 := M v9 v9
  have h120 := h v119 v9 x
  have h121 := S h120
  have h122 := C h20 h66
  have h123 := C h34 (T (T (T h102 h100) h19) h18)
  have h124 := C h66 (T h108 h98)
  have h125 := C h89 (T (T (T h33 h32) h91) h115)
  have h126 := C (T (T h27 h25) h61) h57
  have h127 := C h109 (T (T (T (T h126 h86) h85) h84) h83)
  have h128 := h y y x
  let v129 := M y x
  let v130 := M y v129
  let v131 := M y v130
  have h132 := R v131
  have h133 := C (T (C h7 (T (C h132 h11) (S h128))) h11) h5
  have h134 := h v131 v2 y
  have h135 := R v129
  have h136 := C h57 h135
  have h137 := C h22 h135
  have h138 := h v130 x y
  have h139 := S h138
  have h140 := h v129 v9 x
  have h141 := S h140
  have h142 := h v36 x x
  have h143 := S h142
  have h144 := h x x y
  have h145 := S h144
  let v146 := M x v9
  let v147 := M x v146
  have h148 := R v147
  have h149 := C h148 h57
  have h150 := R v15
  have h151 := C (T (T h33 h32) (C h12 (C h22 h150))) (T h149 h145)
  have h152 := h v147 v9 x
  have h153 := T (T h152 (C (T h151 h143) h6)) (C h57 h11)
  have h154 := C h153 h22
  have h155 := h x v9 y
  have h156 := S h155
  let v157 := M v9 y
  have h158 := R (M v9 (M x v157))
  have h159 := C h158 h57
  have h160 := C h66 (T (T (T h159 h156) h144) h154)
  have h161 := C h160 h12
  have h162 := C h158 h22
  have h163 := h x v1 y
  have h164 := R (M v1 (M x v93))
  have h165 := C h66 (T (T (T (C h164 h57) (S h163)) h155) h162)
  have h166 := C h165 h12
  have h167 := C h66 (T (T (T h159 h156) h163) (C h164 h22))
  have h168 := C h148 h22
  have h169 := C (T (T (C h12 (C h57 h150)) h19) h18) (T h144 h168)
  have h170 := T (T (C h22 h6) (C (T h142 h169) h11)) (S h152)
  have h171 := C h170 h57
  have h172 := C h66 (T (T (T h171 h145) h155) h162)
  have h173 := h v36 x y
  have h174 := S h173
  have h175 := C h22 h89
  let v176 := M y v9
  have h177 := h v176 v9 x
  have h178 := S h177
  have h179 := C (T h127 h125) h12
  have h180 := h x x v9
  have h181 := S h180
  have h182 := C h12 h170
  have h183 := C h182 h66
  have h184 := C h12 (T (T (T (T (T (T (T (T (T (T h183 h181) h6) h31) h30) h28) h179) h178) h107) h105) h175)
  have h185 := C h184 h5
  let v186 := M x v129
  have h187 := h v186 x y
  have h188 := C (T (T (T (T (T (T (T h187 h185) h174) h142) h169) (C h66 (T h149 h154))) h172) h167) h11
  have h189 := C (T h110 h90) h12
  have h190 := T (T (T (T h177 h189) h29) h27) h25
  have h191 := R v186
  have h192 := C h191 h190
  have h193 := C h22 (T (T (T (T h192 h188) h166) h161) h141)
  have h194 := C (T h193 h136) h66
  have h195 := h v186 y v9
  have h196 := S h187
  have h197 := C h12 h153
  have h198 := C h197 h66
  have h199 := C h57 h109
  have h200 := C h12 (T (T (T (T (T (T (T (T (T (T h199 h101) h111) h177) h189) h29) h27) h25) h11) h180) h198)
  have h201 := C h200 h5
  have h202 := C (T (T h27 h25) h11) (T (T (T (T h173 h201) h196) h195) h194)
  have h203 := C (T (T h88 h46) h202) h57
  have h204 := C (T (T h78 h62) h106) h22
  have h205 := h v157 x y
  have h206 := T (T (T (T h187 h185) h174) h35) h14
  have h207 := C h66 (T (T (T (T (T (T (T (T (C h206 (T (T (T (T h205 h204) h203) h139) h137)) (C h5 h136)) h134) h133) h82) h80) h78) h62) h46)
  have h208 := h v186 v9 y
  have h209 := S h195
  have h210 := T (T (T (T h31 h30) h28) h179) h178
  have h211 := C h191 h210
  have h212 := C (T (T (T (T (T (T (T h165 h160) (C h66 (T h171 h168))) h151) h143) h173) h201) h196) h6
  have h213 := C h167 h12
  have h214 := C h172 h12
  have h215 := C h57 (T (T (T (T h140 h214) h213) h212) h211)
  have h216 := C (T h137 h215) h66
  have h217 := C (T (T h6 h31) h30) (T (T (T (T h216 h209) h187) h185) h174)
  have h218 := C (T (T (T (T (T h217 h126) h86) h85) h84) h83) (T (T (T (T (T (T h13 h21) h173) h201) h196) h208) (C (T (T (T (T (T (T h207 h127) h125) h124) h114) h123) h122) h22))
  have h219 := C (T (T (T h134 h133) h33) h32) h72
  have h220 := h y y y
  have h221 := R (M y (M y v41))
  have h222 := T (T (T (C h221 h57) (S h220)) h13) h21
  have h223 := S h134
  have h224 := C (T h6 (C h7 (T h128 (C h132 h6)))) h5
  have h225 := C (T h224 h223) h222
  have h226 := T (T (T h35 h14) h220) (C h221 h22)
  have h227 := h y v1 x
  let v228 := M v1 x
  let v229 := M v1 (M y v228)
  have h230 := R v229
  have h231 := h v229 v2 y
  have h232 := T h231 (C (T (C h7 (T (C h230 h11) (S h227))) h11) h5)
  have h233 := C h232 h226
  have h234 := h y v1 y
  let v235 := M v1 (M y v93)
  have h236 := R v235
  have h237 := T (C (T h6 (C h7 (T h227 (C h230 h6)))) h5) (S h231)
  have h238 := C (T (T (T (T (T (T (T (T (C h237 (T (T (T (C h236 h57) (S h234)) h13) h21)) h233) h225) h219) h71) h205) h204) h203) h218) h12
  have h239 := h v235 v9 x
  have h240 := C (C h7 (T (T (T (T (C (T (T (T (T (T (T (T (T h239 h238) h121) h118) h117) h103) h116) h110) h90) h11) h29) h27) h25) h11)) h22
  have h241 := h v235 v2 y
  have h242 := S h239
  have h243 := C h237 h222
  have h244 := C (T h134 h133) h226
  have h245 := C (T (T (T h19 h18) h224) h223) h72
  have h246 := S h205
  have h247 := C (T (T h88 h86) h85) h57
  have h248 := C (T (T h217 h126) h106) h22
  have h249 := T (T (T (T h13 h21) h173) h201) h196
  have h250 := C h249 (T (T (T (T h136 h138) h248) h247) h246)
  have h251 := C h5 h137
  have h252 := C (T (T (T (T (T h82 h80) h78) h62) h46) h202) (T (T (T (T (T (T (C (T (T (T (T (T (T h118 h117) h103) h116) h110) h90) (C h66 (T (T (T (T (T (T (T (T h126 h86) h85) h84) h83) h224) h223) h251) h250))) h57) (S h208)) h187) h185) h174) h35) h14)
  have h253 := C (T (T (T (T (T (T (T (T h252 h248) h247) h246) h76) h245) h244) h243) (C h232 (T (T (T h35 h14) h234) (C h236 h22)))) h12
  have h254 := R v119
  have h255 := T (T (T (T (T (T h19 h18) h82) h80) h78) h62) h106
  have h256 := C h255 h254
  have h257 := C h34 h254
  have h258 := C (T (C h7 (T (C (T (T h257 h256) (C h89 (T (T (T (T h120 h253) h242) h241) h240))) h11) (S h10))) h8) h5
  let v259 := M v9 v119
  have h260 := h v259 v2 y
  have h261 := C h20 h254
  have h262 := T (T (T (T (T (T h88 h86) h85) h84) h83) h33) h32
  have h263 := C h262 h254
  have h264 := S h241
  have h265 := C (C h7 (T (T (T (T h6 h31) h30) h28) (C (T (T (T (T (T (T (T (T h127 h125) h124) h114) h123) h122) h120) h253) h242) h6))) h57
  have h266 := C h109 (T (T (T (T h265 h264) h239) h238) h121)
  have h267 := h x v0 x
  have h268 := R (M v0 (M x (M v0 x)))
  have h269 := C h7 (T (C h268 h11) (S h267))
  have h270 := C h269 h22
  have h271 := C h7 (T h267 (C h268 h6))
  have h272 := h x x x
  let v273 := M x v15
  let v274 := M x v273
  have h275 := R v274
  have h276 := C (T (C h7 (T (C h275 h11) (S h272))) h271) h5
  have h277 := h v274 v2 y
  have h278 := h v273 y v9
  have h279 := S h278
  have h280 := R v273
  have h281 := h v87 x x
  have h282 := S h281
  let v283 := M x (M v9 v15)
  have h284 := h v283 v2 y
  have h285 := R v283
  have h286 := h v9 x x
  have h287 := h v9 z x
  have h288 := R (M z (M v9 (M z x)))
  have h289 := C h7 (T (C h288 h11) (S h287))
  have h290 := C h7 (T h287 (C h288 h6))
  have h291 := h v9 v9 x
  let v292 := M v9 (M v9 v36)
  have h293 := R v292
  have h294 := h v292 v2 y
  have h295 := h v186 v9 x
  have h296 := C (T (T h260 h258) h4) (T h37 h60)
  have h297 := T (T h173 h201) h196
  have h298 := C h89 (T h39 (C h297 h72))
  have h299 := C h109 h58
  have h300 := C (T (C (T (T (T (T (T (T (T (T h82 h80) h78) h62) h106) h43) h40) h299) h298) (T (T h296 h45) h11)) (S h295)) (T (T (T (T (T h6 h31) h30) h28) h179) h178)
  have h301 := h v259 v9 x
  have h302 := S h260
  have h303 := C h7 (C h7 h11)
  have h304 := C (T h303 (C h7 (T h10 (C (T (T h266 h263) h261) h6)))) h5
  have h305 := C h206 (T (T (T (T h3 h304) h302) h301) h300)
  have h306 := C h297 h7
  have h307 := C h22 h7
  let v308 := M y v2
  have h309 := R v308
  have h310 := C h34 h309
  have h311 := C (T (T (T (T (T (T (T (T (T (T (T h310 (C h20 (T (T (T (T (T (T h307 h306) h305) h193) h136) h138) h248))) (C h109 (T h247 h246))) (C h89 (T (T (T h76 h245) h244) h243))) (C h66 (T h233 h225))) (C h66 (T h219 h75))) h294) (C (T (C h7 (T (C h293 h11) (S h291))) h290) h5)) (C (T h289 (C h7 (T h286 (C h285 h6)))) h5)) (S h284)) (C h12 (C h34 h150))) (C h12 (C h255 h150))) h11
  let v312 := M v9 v308
  have h313 := R v312
  have h314 := C h313 h190
  have h315 := C h22 (T (T (T (T (T (T (T h314 h311) h282) h88) h86) h85) h84) h83)
  have h316 := C h313 h210
  have h317 := C h20 h309
  have h318 := C h57 h7
  have h319 := T (T h187 h185) h174
  have h320 := C h319 h7
  have h321 := S h301
  have h322 := C (T (T (T (T (T (T (T (T (C h109 (T (C h319 h72) h58)) (C h89 h39)) h59) h56) h88) h86) h85) h84) h83) (T (T h6 h61) (C (T (T h3 h304) h302) (T h44 h38)))
  have h323 := C (T h295 h322) (T (T (T (T (T h177 h189) h29) h27) h25) h11)
  have h324 := C h249 (T (T (T (T h323 h321) h260) h258) h4)
  have h325 := C (T (T (T (T (T (T (T (T (T (T (T (C h12 (C h262 h150)) (C h12 (C h20 h150))) h284) (C (T (C h7 (T (C h285 h11) (S h286))) h290) h5)) (C (T h289 (C h7 (T h291 (C h293 h6)))) h5)) (S h294)) (C h66 (T h73 h245))) (C h66 (T h244 h243))) (C h109 (T (T (T h233 h225) h219) h71))) (C h89 (T h205 h204))) (C h34 (T (T (T (T (T (T h203 h139) h137) h215) h324) h320) h318))) h317) h6
  have h326 := h v87 x v2
  have h327 := S h326
  let v328 := M x v2
  have h329 := R v328
  have h330 := h (M x (M v9 v328)) z v1
  have h331 := h v9 x v2
  have h332 := h v9 v2 v2
  have h333 := C h24 (S h332)
  have h334 := C h24 h332
  have h335 := h v9 y v2
  have h336 := h (M y v312) z v1
  have h337 := C h262 h309
  have h338 := C h255 h309
  have h339 := h v312 y v9
  have h340 := h v87 x v9
  have h341 := R v146
  have h342 := h (M x (M v9 v146)) x y
  have h343 := h v9 x v9
  have h344 := h v9 v0 v9
  have h345 := C h12 (S h344)
  have h346 := C h12 h344
  have h347 := h v9 v9 v9
  have h348 := h (M v9 v259) x y
  have h349 := C h8 h57
  have h350 := C h303 h22
  have h351 := h v2 v1 y
  have h352 := S h351
  have h353 := R (M v1 (M v2 v93))
  have h354 := C h353 h57
  have h355 := C h353 h22
  have h356 := h v2 y y
  have h357 := S h356
  have h358 := R (M y (M v2 v41))
  have h359 := C h358 h57
  have h360 := C h358 h22
  have h361 := T (T (T (T (T (T (C (T (T (T (T (T (T (T (T (T (T (T (T (T (C h34 h7) (C h20 (T h356 h360))) (C h66 (T (T (T h359 h357) h351) h355))) (C h66 (T (T (T h354 h352) h3) h350))) (C h109 (T h349 h4))) (C h89 (T (T (T (T h3 h304) h302) h257) h256))) (C h66 h263)) (C h66 h261)) h348) (C (T (C h12 (S h347)) h346) h5)) (C (T h345 (C h12 h343)) h5)) (S h342)) (C h12 (C h34 h341))) (C h12 (C h255 h341))) h66) (S h340)) h88) h86) h85) h84) h83
  have h362 := C h57 (T (T (T (T (T (T (T h82 h80) h78) h62) h106) h281) h325) h316)
  have h363 := T (T (T (T (T (T h82 h80) h78) h62) h106) h340) (C (T (T (T (T (T (T (T (T (T (T (T (T (T (C h12 (C h262 h341)) (C h12 (C h20 h341))) h342) (C (T (C h12 (S h343)) h346) h5)) (C (T h345 (C h12 h347)) h5)) (S h348)) (C h66 h257)) (C h66 h256)) (C h109 (T (T (T (T h263 h261) h260) h258) h4))) (C h89 (T h3 h350))) (C h66 (T (T (T h349 h4) h351) h355))) (C h66 (T (T (T h354 h352) h356) h360))) (C h34 (T h359 h357))) (C h20 h7)) h66)
  have h364 := C h22 h341
  have h365 := C (T (T (T (T (T (T (T (T (T h364 (C h57 (T (T (T (T (C h12 h363) (C (T (T (T (T (T (T (T (T (T h6 h31) h30) h28) h179) h178) h107) h105) h175) h362) h361)) (S h339)) h310) h338))) (C h5 h337)) (C h5 h317)) h336) (C (T (C h24 (S h335)) h334) h49)) (C (T h333 (C h24 h331)) h49)) (S h330)) (C h12 (C h34 h329))) (C h12 (C h255 h329))) h7
  let v366 := M y v146
  have h367 := R v366
  have h368 := C h367 (T (T (T (T (T (T (T (T (T h140 h214) h213) h212) h211) h323) h321) h260) h258) h4)
  have h369 := C h5 (T (T (T (T (T h368 h365) h327) h281) h325) h316)
  have h370 := T (T (T (T (T (T (T (T (T (T h369 h315) h199) h101) h111) h177) h189) h29) h27) h25) h11
  have h371 := h v366 y x
  have h372 := C h57 h341
  have h373 := C h12 (T (T (T (T h372 h371) (C h370 (T (T (T (T (T (T (T (T h6 h31) h30) h28) h179) h178) h107) h105) h175))) h200) (C h12 (T h183 h181)))
  have h374 := C h12 h364
  have h375 := h (M x v366) x y
  have h376 := S h375
  have h377 := h y x v9
  have h378 := C (C h12 h377) h5
  have h379 := C h206 (T (T h120 (C (T (T (T (T (T (T (T h252 h248) h247) h246) h378) h376) h374) h373) h6)) (C h280 h210))
  have h380 := C h297 h254
  have h381 := C h22 h254
  have h382 := C (T (T h381 h380) h379) h66
  have h383 := C h12 (T h382 h279)
  have h384 := C h57 h254
  have h385 := C h319 h254
  have h386 := C (C h12 (S h377)) h5
  have h387 := C h12 h372
  have h388 := S h371
  have h389 := C h367 (T (T (T (T (T (T (T (T (T h3 h304) h302) h301) h300) h192) h188) h166) h161) h141)
  have h390 := C (T (T (T (T (T (T (T (T (T (C h12 (C h262 h329)) (C h12 (C h20 h329))) h330) (C (T (C h24 (S h331)) h334) h49)) (C (T h333 (C h24 h335)) h49)) (S h336)) (C h5 h310)) (C h5 h338)) (C h22 (T (T (T (T h337 h317) h339) (C (T (T (T (T (T (T (T (T (T h315 h199) h101) h111) h177) h189) h29) h27) h25) h11) h363)) (C h12 h361)))) h372) h7
  have h391 := C h5 (T (T (T (T (T h314 h311) h282) h326) h390) h389)
  have h392 := T (T (T (T (T (T (T (T (T (T h6 h31) h30) h28) h179) h178) h107) h105) h175) h362) h391
  have h393 := C h12 (T (T (T (T (C h12 (T h180 h198)) h184) (C h392 (T (T (T (T (T (T (T (T h199 h101) h111) h177) h189) h29) h27) h25) h11))) h388) h364)
  have h394 := C h249 (T (T (C h280 h190) (C (T (T (T (T (T (T (T h393 h387) h375) h386) h205) h204) h203) h218) h11)) h121)
  have h395 := C (T (T h394 h385) h384) h66
  have h396 := h (M y v119) x y
  have h397 := C h12 (T h278 h395)
  have h398 := S h277
  have h399 := C (T h269 (C h7 (T h272 (C h275 h6)))) h5
  have h400 := C h271 h57
  have h401 := h v36 v1 y
  have h402 := C (T (T (T (T (T (T (T h13 h21) h401) (C (T (T (T (T (T (T (C h49 (C h57 h94)) h241) h240) h400) h399) h398) h397) h5)) (S h396)) h381) h380) h379) (T (T (T (T (T (T (T h368 h365) h327) h88) h86) h85) h84) h83)
  have h403 := C (T (T (T (T (T (T (T h394 h385) h384) h396) (C (T (T (T (T (T (T h383 h277) h276) h270) h265) h264) (C h49 (C h22 h94))) h5)) (S h401)) h35) h14) (T (T (T (T (T (T (T h82 h80) h78) h62) h106) h326) h390) h389)
  have h404 := C h392 (T (T (T (T (T (T (T (T (T (T (T (T h382 h403) h369) h315) h199) h101) h111) h177) h189) h29) h27) h25) h11)
  have h405 := C h12 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h125 h124) h114) h123) h122) h120) h253) h242) h241) h240) h400) h399) h398) h397) h404) h388) h364)
  have h406 := C h12 (T (T (T h117 h103) h116) h110)
  have h407 := C h12 h118
  have h408 := T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h407 h406) h405) h373) h278) h403) h369) h315) h199) h101) h111) h177) h189) h29) h27) h25) h11
  let v409 := M x v119
  have h410 := h v409 v1 v1
  have h411 := S h410
  have h412 := C h12 h122
  have h413 := C h12 (T (T (T h125 h124) h114) h123)
  have h414 := C h370 (T (T (T (T (T (T (T (T (T (T (T (T h6 h31) h30) h28) h179) h178) h107) h105) h175) h362) h391) h402) h395)
  have h415 := C h12 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h372 h371) h414) h383) h277) h276) h270) h265) h264) h239) h238) h121) h118) h117) h103) h116) h110)
  have h416 := T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h6 h31) h30) h28) h179) h178) h107) h105) h175) h362) h391) h402) h279) h393) h415) h413) h412
  have h417 := h (M x v50) z y
  have h418 := h v1 x v0
  have h419 := C (C h49 (T (T (T h6 (C (C h24 h418) h5)) (S h417)) (C h416 h51))) h49
  have h420 := C (C h49 (T (T (T (C h408 h51) h417) (C (C h24 (S h418)) h5)) h11)) h49
  have h421 := C h408 (T (T (T (T (T (T (T h378 h376) h374) h415) h413) h412) h410) h420)
  have h422 := R v409
  have h423 := C h422 (T (T (T (T (T (T (T (T h307 h306) h305) h193) h136) h138) h248) h247) h246)
  have h424 := h v409 y v1
  have h425 := S h424
  have h426 := C h57 h49
  have h427 := C h22 h49
  let v428 := M y v1
  have h429 := h (M x v428) z y
  have h430 := h y x v0
  let v431 := M v0 y
  have h432 := R v431
  have h433 := C h297 h432
  have h434 := C h22 h432
  have h435 := C (T (T h434 h433) (C h206 (T (T (T (C (C h24 h430) h5) (S h429)) (C h12 h427)) (C h416 h426)))) h49
  have h436 := C h416 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h435 h425) h407) h406) h405) h387) h375) h386) h205) h204) h203) h139) h137) h215) h324) h320) h318)
  have h437 := C h57 h432
  have h438 := C h319 h432
  have h439 := C (T (T (C h249 (T (T (T (C h408 h427) (C h12 h426)) h429) (C (C h24 (S h430)) h5))) h438) h437) h49
  have h440 := h v273 x y
  let v441 := M x v147
  have h442 := h v441 v0 y
  have h443 := h (M y v431) x v0
  have h444 := C h408 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h307 h306) h305) h193) h136) h138) h248) h247) h246) h378) h376) h374) h415) h413) h412) h424) h439)
  have h445 := C h422 (T (T (T (T (T (T (T (T h205 h204) h203) h139) h137) h215) h324) h320) h318)
  have h446 := C h416 (T (T (T (T (T (T (T h419 h411) h407) h406) h405) h387) h375) h386)
  have h447 := h v228 x v0
  have h448 := R v176
  have h449 := h v441 y v9
  have h450 := h v441 y v1
  have h451 := S h450
  have h452 := R v428
  have h453 := h (M y (M y v428)) x v0
  have h454 := h y y v1
  have h455 := h y z v1
  have h456 := h (M z v308) x v0
  have h457 := C (T (T (T (T (T (T (T (T (T (C h24 (T (T (T (T (T (T h205 h204) h203) h139) h137) h215) h324)) (C h24 h320)) (C h24 h318)) h456) (C (C h12 (S h455)) h53)) (C (C h12 h454) h53)) (S h453)) (C h5 (C h22 h452))) (C h5 (C h297 h452))) (C h5 (C h182 h452))) h49
  have h458 := C (T (T (T (T (T (T (T (T (T (C h5 (C h197 h452)) (C h5 (C h319 h452))) (C h5 (C h57 h452))) h453) (C (C h12 (S h454)) h53)) (C (C h12 h455) h53)) (S h456)) (C h24 h307)) (C h24 h306)) (C h24 (T (T (T (T (T (T h305 h193) h136) h138) h248) h247) h246))) h49
  let v459 := M v0 v228
  have h460 := h v459 v9 x
  T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h82 h80) h78) h62) h106) h43) h40) h299) h298) (C h66 (T (T (T (T (T (C (T (T (T h295 h322) (C h66 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h296 h45) h31) h30) h28) h179) h178) h107) h105) h175) h362) h391) h402) h279) h393) (C h416 (T (T (T (T (T (T (T (T (T (T (T h372 h371) h414) h383) h277) h276) h270) h265) h264) h239) h238) h121))))) (C h66 (T (T (T (T (T (T (C h408 (T (T (T (T (T (T (T (T (T (T (T h120 h253) h242) h241) h240) h400) h399) h398) h397) h404) h388) h364)) h415) h413) h412) (h v409 v9 x)) (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (C h66 (T (T (T (T (T (T (T (C h407 h57) (S (h v16 x y))) h19) h18) h224) h223) h251) h250)) h207) h127) h125) h124) h114) h123) h122) h120) h253) h242) h241) h240) h400) h399) h398) h397) (C h416 (T (T (T (T (T (T (T (T (T (T (T h382 h403) h369) h315) h199) h101) h111) h177) h189) h29) h27) h25))) (C h408 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h31 h30) h28) h179) h178) h107) h105) h175) h362) h391) h402) h279) h393) h415) h413) h412) h410) h420))) h446) h445) h444) (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T h6 h31) h30) h28) h179) h178) h107) h105) h175) h362) h391) h402) h279) h440) (C (T (T (T (T (T (T (T (C h12 (T (T (T (C (T (T (T (T (T (T (T (T (T (T h393 h387) h375) h386) h205) h204) h203) h139) h137) h215) (C h5 (C h182 h448))) h66) (S h449)) h450) h458)) (C h12 (T (T (T (T h457 h451) h197) h195) h194))) h217) h126) h86) h85) h84) h83) (T (T (T (T (T (T (T h13 h21) h173) h201) h196) h182) h442) (C (T (C h53 (C h197 h432)) (C h53 (T (T (T (T h438 h437) h443) (C (T (T h436 h423) h421) h53)) (S h447)))) h22)))) (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h435 h425) h407) h406) h405) h373) h278) h403) h369) h315) h199) h101) h111) h177) h189) h29) h27) h25) h11))) (S h460)) h6)) (C (R v459) (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h31 h30) h28) h179) h178) h107) h105) h175) h362) h391) h402) h279) h393) h387) h375) h386))))) h57) (S (h v459 v9 y))) h460) (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (C (T (T (T (T (T (T (T h82 h80) h78) h62) h46) h202) (C h12 (T (T (T (T h216 h209) h182) h450) h458))) (C h12 (T (T (T h457 h451) h449) (C (T (T (T (T (T (T (T (T (T (T (C h5 (C h197 h448)) h193) h136) h138) h248) h247) h246) h378) h376) h374) h373) h66)))) (T (T (T (T (T (T (T (C (T (C h53 (T (T (T (T h447 (C (T (T h446 h445) h444) h53)) (S h443)) h434) h433)) (C h53 (C h182 h432))) h57) (S h442)) h197) h187) h185) h174) h35) h14)) (S h440)) h278) h403) h369) h315) h199) h101) h111) h177) h189) h29) h27) h25) h11) (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h6 h31) h30) h28) h179) h178) h107) h105) h175) h362) h391) h402) h279) h393) h415) h413) h412) h424) h439))) h436) h423))) (C h66 (T (T (T (T (T (T h421 (C h416 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h419 h411) h407) h406) h405) h373) h278) h403) h369) h315) h199) h101) h111) h177) h189) h29) h27) h25))) (C h408 (T (T (T (T (T (T (T (T (T (T (T h31 h30) h28) h179) h178) h107) h105) h175) h362) h391) h402) h395))) h383) h277) h276) h270))) h266) h263) h261) h260) h258) h4

