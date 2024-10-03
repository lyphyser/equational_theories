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
theorem Equation2370_implies_Equation1117 (G: Type _) [Magma G] (h: Equation2370 G) : Equation1117 G := fun x y z =>
  let v0 := M x z
  have h1 := h z z v0
  have h2 := S h1
  have h3 := R v0
  let v4 := M z z
  have h5 := h (M z (M v0 v4)) v0 x
  have h6 := R x
  have h7 := C (T (C (C h3 (C h6 h1)) h6) (S h5)) h3
  have h8 := T h7 h2
  let v9 := M y v0
  have h10 := R v9
  have h11 := C h10 h8
  have h12 := C (T h5 (C (C h3 (C h6 h2)) h6)) h3
  let v13 := M v9 z
  let v14 := M y v13
  have h15 := h z v14 y
  have h16 := S h15
  have h17 := R y
  let v18 := M z v14
  have h19 := h (M v14 (M y v18)) y x
  have h20 := S h19
  have h21 := C (C h17 (C h6 h15)) h6
  have h22 := C (T h21 h20) h17
  have h23 := T (T (T h22 h16) h1) h12
  have h24 := C h10 h23
  have h25 := C h17 (T h24 h11)
  have h26 := C (C h17 (C h6 h16)) h6
  have h27 := C (T h19 h26) h17
  let v28 := M v9 x
  have h29 := h v28 y v9
  have h30 := h v9 x v9
  have h31 := S h30
  have h32 := h (M x (M v9 v28)) v9 x
  have h33 := T (C (T (C (C h10 (C h6 h30)) h6) (S h32)) h10) h31
  have h34 := T (T (T h7 h2) h15) h27
  have h35 := C h10 h34
  have h36 := T h1 h12
  have h37 := C h10 h36
  have h38 := C h17 (T h37 h35)
  have h39 := T h30 (C (T h32 (C (C h10 (C h6 h31)) h6)) h10)
  have h40 := R v14
  have h41 := C (T (T (T (T (C h40 h39) (C h38 h33)) (S h29)) h21) h20) h17
  have h42 := h v0 x v14
  have h43 := S h42
  have h44 := C (C h40 (C h17 h43)) h17
  let v45 := M v0 x
  let v46 := M x (M v14 v45)
  have h47 := h v46 v14 y
  have h48 := h v46 v14 x
  have h49 := S h48
  have h50 := C h40 (C h6 h42)
  have h51 := h v0 z v14
  have h52 := C (T (C h40 (C h6 (S h51))) h50) h6
  let v53 := M v0 z
  let v54 := M z (M v14 v53)
  have h55 := h v54 v14 x
  have h56 := h v54 v13 v13
  have h57 := S h56
  have h58 := R v13
  have h59 := S h55
  have h60 := C h40 (C h6 h43)
  have h61 := C (T h60 (C h40 (C h6 h51))) h6
  have h62 := S h47
  have h63 := C (C h40 (C h17 h42)) h17
  have h64 := C (T (T (T (T h19 h26) h29) (C h25 h39)) (C h40 h33)) h17
  have h65 := T (T (T (T (T (T h15 h64) h63) h62) h48) h61) h59
  have h66 := C h65 h58
  let v67 := M z v13
  have h68 := h (M v13 (M v13 v67)) v13 x
  have h69 := h z v13 v13
  have h70 := h z v9 v13
  have h71 := S h70
  let v72 := M z v9
  let v73 := M v9 (M v13 v72)
  have h74 := h v73 v13 x
  have h75 := h v73 v13 z
  have h76 := R z
  have h77 := C (T (T (T (T (T (C (C h58 (C h76 h70)) h76) (S h75)) h74) (C (T (C h58 (C h6 h71)) (C h58 (C h6 h69))) h6)) (S h68)) (C h58 (C h58 h66))) h58
  have h78 := T (T (T (T (T (T (T (T h77 h57) h55) h52) h49) h47) h44) h41) h27
  have h79 := C h10 h78
  have h80 := C (C h58 (C h76 h71)) h76
  have h81 := S h74
  have h82 := C h58 (C h6 h70)
  have h83 := T (T (T (T (T (T h55 h52) h49) h47) h44) h41) h16
  have h84 := C h83 h58
  have h85 := C (T (T (T (T (T (C h58 (C h58 h84)) h68) (C (T (C h58 (C h6 (S h69))) h82) h6)) h81) h75) h80) h58
  have h86 := h v54 v13 v9
  have h87 := S h86
  have h88 := h (M v13 (M v9 v67)) v9 x
  have h89 := h z v13 v9
  have h90 := C (T (T (C (C h10 (C h6 h89)) h6) (S h88)) (C h58 (C h10 h66))) h10
  have h91 := T (T (T h90 h87) h56) h85
  have h92 := C h10 h91
  have h93 := C (T (T (C h58 (C h10 h84)) h88) (C (C h10 (C h6 (S h89))) h6)) h10
  have h94 := h v54 v9 v14
  have h95 := S h94
  have h96 := h v72 y x
  have h97 := h x z y
  let v98 := M x x
  let v99 := M (M y v98) x
  have h100 := h v99 y y
  have h101 := S h100
  have h102 := h x v9 y
  have h103 := S h102
  let v104 := M x v9
  have h105 := h (M v9 (M y v104)) y x
  have h106 := C (T h105 (C (C h17 (C h6 h103)) h6)) h17
  have h107 := T h102 h106
  have h108 := C (C h17 (C h17 h107)) h17
  have h109 := C (T (C (C h17 (C h6 h102)) h6) (S h105)) h17
  have h110 := T h109 h103
  have h111 := C (C h17 (C h17 h110)) h17
  have h112 := h v99 y z
  have h113 := S h112
  have h114 := C h17 (C h76 h107)
  have h115 := C h114 h76
  have h116 := C h76 h110
  have h117 := C h17 h116
  have h118 := C h117 h76
  have h119 := h v99 y v0
  have h120 := S h119
  have h121 := C (C h17 (C h3 h107)) h3
  have h122 := C (C h17 (C h3 h110)) h3
  have h123 := h v99 y v9
  have h124 := S h123
  have h125 := C h10 h107
  have h126 := C h17 h125
  have h127 := C (C h10 (T (T (T (C h40 (T (T (T (C h126 h10) h124) h119) h122)) (C h40 (T (T (T h121 h120) h112) h118))) (C h40 (T (T (T h115 h113) h100) h111))) (C h40 (T (T (T (T (T h108 h101) (C (C h17 (C h6 h97)) h6)) (S h96)) (C h76 h39)) (C h65 h33))))) h40
  let v128 := M y v28
  have h129 := h v128 v9 v14
  have h130 := h v128 v14 v14
  have h131 := S h130
  have h132 := S h129
  have h133 := C h10 h110
  have h134 := C h17 h133
  have h135 := C (C h10 (T (T (T (C h40 (T (T (T (T (T (C h83 h39) (C h76 h33)) h96) (C (C h17 (C h6 (S h97))) h6)) h100) h111)) (C h40 (T (T (T h108 h101) h112) h118))) (C h40 (T (T (T h115 h113) h119) h122))) (C h40 (T (T (T h121 h120) h123) (C h134 h10))))) h40
  have h136 := C (T (T (T (T (T (T (T (T (T h15 h64) h63) h62) h48) h61) h59) h94) h135) h132) h40
  have h137 := h v18 y x
  have h138 := S h137
  have h139 := h v9 z y
  have h140 := h v9 x y
  have h141 := S h140
  have h142 := C (T (C h17 (C h6 h141)) (C h17 (C h6 h139))) h6
  let v143 := M x v128
  have h144 := h v143 y x
  have h145 := h v143 y v9
  have h146 := S h145
  have h147 := C (C h17 (C h10 h140)) h10
  have h148 := C h40 (T (T (T (T (T h147 h146) h144) h142) h138) h136)
  have h149 := C (C h17 (C h10 h141)) h10
  have h150 := h v143 y v14
  have h151 := S h150
  have h152 := C h17 (C h40 h140)
  have h153 := C (C h40 (T (C h40 (T (T (T (C h152 h40) h151) h145) h149)) h148)) h40
  let v154 := M y (M v14 v9)
  have h155 := h v154 v14 v14
  have h156 := C h10 (T (T (T (T (T (T (T h155 h153) h131) h129) h127) h95) h86) h93)
  have h157 := h (M v9 v154) y x
  have h158 := S h157
  have h159 := h v14 v9 y
  have h160 := h v14 v14 y
  have h161 := S h160
  have h162 := C h17 (C h6 h161)
  have h163 := C (T h162 (C h17 (C h6 h159))) h6
  have h164 := C h17 (C h6 h160)
  have h165 := h v14 z y
  have h166 := C (T (C h17 (C h6 (S h165))) h164) h6
  let v167 := M v14 z
  let v168 := M y v167
  have h169 := h (M z v168) y x
  have h170 := h v168 v14 y
  have h171 := C h40 h8
  have h172 := C h40 h23
  have h173 := C (C h17 (T h172 h171)) h40
  have h174 := h v28 y v14
  have h175 := C h17 (T (T h133 h174) h173)
  have h176 := T (T (T h77 h57) h86) h93
  have h177 := T (T (T (T (T (T (T (T h22 h64) h63) h62) h48) h61) h59) h56) h85
  have h178 := C h40 h34
  have h179 := C h40 h36
  have h180 := C h76 (T (C (T (T (T (T h179 h178) (C h40 h177)) (C h40 h176)) (C h40 (T (T (T (T (T (T h90 h87) h94) h135) h132) h126) h175))) h17) (S h170))
  have h181 := C h17 (T (T (T (T (T (T (T h180 h169) h166) h163) h158) h156) h92) h79)
  have h182 := C h40 h78
  have h183 := S h174
  have h184 := C (C h17 (T h179 h178)) h40
  have h185 := C h17 (T (T h184 h183) h125)
  have h186 := C h76 (T h170 (C (T (T (T (T (C h40 (T (T (T (T (T (T h185 h134) h129) h127) h95) h86) h93)) (C h40 h91)) h182) h172) h171) h17))
  have h187 := S h169
  have h188 := C (T h162 (C h17 (C h6 h165))) h6
  let v189 := M y (M v14 v14)
  let v190 := M v14 v189
  have h191 := h v190 y x
  have h192 := h v190 y v0
  have h193 := S h192
  have h194 := C h17 (C h3 h160)
  let v195 := M v0 v14
  have h196 := h (M y v195) v0 y
  have h197 := C h17 (C h3 h161)
  have h198 := h v190 y y
  have h199 := S h198
  have h200 := C (C h17 (C h17 h160)) h17
  have h201 := C (C h17 (C h17 h161)) h17
  have h202 := S h191
  have h203 := C h17 (T (T (T (T (T h180 h169) h166) h202) h198) h201)
  have h204 := C (T (C h17 (C h6 (S h159))) h164) h6
  have h205 := S h155
  have h206 := C h17 (C h40 h141)
  have h207 := S h144
  have h208 := C (T (C h17 (C h6 (S h139))) (C h17 (C h6 h140))) h6
  have h209 := C (T (T (T (T (T (T (T (T (T h129 h127) h95) h55) h52) h49) h47) h44) h41) h16) h40
  have h210 := C h40 (T (T (T (T (T h209 h137) h208) h207) h145) h149)
  have h211 := C (C h40 (T h210 (C h40 (T (T (T h147 h146) h150) (C h206 h40))))) h40
  have h212 := C h10 (T (T (T (T (T (T (T h90 h87) h94) h135) h132) h130) h211) h205)
  have h213 := C h10 h176
  have h214 := C h10 h177
  have h215 := C h17 (T (T (T (T (T (T (T h214 h213) h212) h157) h204) h188) h187) h186)
  have h216 := C (T (T (C (C h3 (T (T (T h38 h215) h203) (C h17 (T (T (T h200 h199) h192) (C h197 h3))))) h17) (S h196)) h194) h3
  have h217 := C h17 (T (T (T (T (T h200 h199) h191) h188) h187) h186)
  have h218 := C (T (T h197 h196) (C (C h3 (T (T (T (C h17 (T (T (T (C h194 h3) h193) h198) h201)) h217) h181) h25)) h17)) h3
  have h219 := h v154 x y
  have h220 := S h219
  have h221 := h x y x
  have h222 := S h221
  let v223 := M x y
  have h224 := h (M y (M x v223)) x x
  have h225 := h x z x
  have h226 := h (M z (M x v0)) x x
  have h227 := h v0 z z
  have h228 := S h227
  have h229 := C (T (T (T (C h76 (C h6 h228)) h226) (C (T (C h6 (C h6 (S h225))) (C h6 (C h6 h221))) h6)) (S h224)) h6
  let v230 := M z (M z v53)
  have h231 := h v230 z x
  have h232 := h v230 y z
  have h233 := S h232
  have h234 := S h231
  have h235 := C (T (T (T h224 (C (T (C h6 (C h6 h222)) (C h6 (C h6 h225))) h6)) (S h226)) (C h76 (C h6 h227))) h6
  have h236 := T (T h221 h235) h234
  have h237 := h (M y (M z v223)) z x
  have h238 := h x y z
  have h239 := C (T (T (C (C h76 (C h6 h238)) h6) (S h237)) (C h17 (C h76 (C h236 h17)))) h76
  have h240 := T (T (T (T (T (T (T (T (T (T (T (T h15 h64) h63) h62) h48) h61) h59) h94) h135) h132) h130) h211) h205
  have h241 := T (T h231 h229) h222
  have h242 := C (T (T (C h17 (C h76 (C h241 h17))) h237) (C (C h76 (C h6 (S h238))) h6)) h76
  let v243 := M z x
  have h244 := h (M x (M y v243)) y x
  have h245 := h z x y
  have h246 := h z v9 y
  have h247 := C (C h17 (C h6 (S h246))) h6
  let v248 := M y v72
  have h249 := h (M v9 v248) y x
  have h250 := h v248 z v14
  have h251 := h v143 y z
  have h252 := h v143 v13 v13
  have h253 := S h252
  have h254 := h v0 v13 v14
  have h255 := C (T (C h40 (C h6 (S h254))) h50) h6
  let v256 := M v0 v13
  let v257 := M v14 v256
  have h258 := h (M v13 v257) v14 x
  have h259 := h v257 v0 v14
  have h260 := S h259
  have h261 := h v13 v14 v14
  have h262 := S h261
  let v263 := M v14 (M v14 (M v13 v14))
  have h264 := h v263 v14 v0
  have h265 := h v263 v14 x
  have h266 := S h265
  have h267 := C h40 (C h6 h261)
  have h268 := C h267 h6
  have h269 := T (T (T h268 h266) h264) (C (C h40 (C h3 h262)) h3)
  have h270 := C h40 (C h6 h262)
  have h271 := C h270 h6
  have h272 := h v263 v14 y
  have h273 := S h272
  have h274 := h v190 y v14
  have h275 := S h274
  have h276 := C h17 (C h40 h160)
  have h277 := C (T (C h40 (T (T (T (C h17 (T (T (T (C h276 h40) h275) h198) h201)) h217) h181) h25)) (C h40 (C h17 h261))) h17
  have h278 := h v189 v14 y
  have h279 := C h40 (T (T (T (T h278 h277) h273) h265) h271)
  have h280 := C h3 (T (T (T (T (T (T (T (T h35 h214) h213) h212) h157) h204) h202) h192) h218)
  have h281 := C h3 h37
  have h282 := C (T (T h281 h280) (C h3 (T (T (T h216 h193) h279) (C h40 h269)))) h40
  have h283 := C h58 (T h282 h260)
  have h284 := C h3 h11
  have h285 := C h3 (T (T (T (T (T (T (T (T h216 h193) h191) h163) h158) h156) h92) h79) h24)
  have h286 := S h278
  have h287 := C h17 (C h40 h161)
  have h288 := C (T (C h40 (C h17 h262)) (C h40 (T (T (T h38 h215) h203) (C h17 (T (T (T h200 h199) h274) (C h287 h40)))))) h17
  have h289 := C h40 (T (T (T (T h268 h266) h272) h288) h286)
  have h290 := T (T (T (C (C h40 (C h3 h261)) h3) (S h264)) h265) h271
  have h291 := C (T (T (C h3 (T (T (T (C h40 h290) h289) h192) h218)) h285) h284) h40
  have h292 := h v256 v14 v13
  have h293 := S h292
  have h294 := C h58 (T h259 h291)
  have h295 := S h258
  have h296 := C (T h60 (C h40 (C h6 h254))) h6
  have h297 := C (T h181 h25) (T (T (T (T (T (T (T h15 h64) h63) h62) h48) h296) h295) h294)
  have h298 := h v167 y z
  have h299 := C (T h298 h297) h58
  have h300 := C h40 (T h299 h293)
  have h301 := C h58 (T (T h300 h259) h291)
  have h302 := h v167 v13 v14
  have h303 := S h298
  have h304 := C (T h38 h215) (T (T (T (T (T (T (T h283 h258) h255) h49) h47) h44) h41) h16)
  have h305 := C (T (T (T (T h304 h303) h302) (C (T (T (T (T (T (T (T (T (T (T (T (T h301 h283) h258) h255) h61) h59) h94) h135) h132) h130) h211) h205) h152) h40)) h151) h58
  have h306 := T h292 h305
  have h307 := h (M v13 (M v13 v256)) v13 x
  have h308 := h v0 v13 v13
  have h309 := h v0 x v13
  have h310 := S h309
  let v311 := M x (M v13 v45)
  have h312 := h v311 v13 x
  have h313 := h v311 v13 z
  have h314 := C (T (T (T (T (T (C (C h58 (C h76 h309)) h76) (S h313)) h312) (C (T (C h58 (C h6 h310)) (C h58 (C h6 h308))) h6)) (S h307)) (C h58 (C h58 h306))) h58
  have h315 := C (T h304 h303) h58
  have h316 := C h40 (T h292 h315)
  have h317 := C h58 (T (T h282 h260) h316)
  have h318 := C (T (T (T (T h150 (C (T (T (T (T (T (T (T (T (T (T (T (T h206 h155) h153) h131) h129) h127) h95) h55) h52) h296) h295) h294) h317) h40)) (S h302)) h298) h297) h58
  have h319 := T h318 h293
  have h320 := C (T (T (T (T (T (C h58 (C h58 h319)) h307) (C (T (C h58 (C h6 (S h308))) (C h58 (C h6 h309))) h6)) (S h312)) h313) (C (C h58 (C h76 h310)) h76)) h58
  have h321 := h v143 v13 v9
  have h322 := S h321
  have h323 := h (M v13 (M v9 v256)) v9 x
  have h324 := h v0 v13 v9
  have h325 := h v0 v14 v9
  have h326 := S h325
  let v327 := M v14 (M v9 v195)
  have h328 := h v327 v9 x
  have h329 := h v327 v9 v0
  have h330 := C (T (T (T (T (T (C (C h10 (C h3 h325)) h3) (S h329)) h328) (C (T (C h10 (C h6 h326)) (C h10 (C h6 h324))) h6)) (S h323)) (C h58 (C h10 h306))) h10
  have h331 := C (T (T (T (T (T (C h58 (C h10 h319)) h323) (C (T (C h10 (C h6 (S h324))) (C h10 (C h6 h325))) h6)) (S h328)) h329) (C (C h10 (C h3 h326)) h3)) h10
  have h332 := h v143 v13 v0
  have h333 := S h332
  have h334 := h (M v13 (M v0 v256)) v0 x
  have h335 := h v0 v13 v0
  have h336 := h v0 v14 v0
  have h337 := S h336
  let v338 := M v14 (M v0 v195)
  have h339 := h v338 v0 x
  have h340 := h v338 v0 v0
  have h341 := C (T (T (T (T (T (C (C h3 (C h3 h336)) h3) (S h340)) h339) (C (T (C h3 (C h6 h337)) (C h3 (C h6 h335))) h6)) (S h334)) (C h58 (T (C h3 (T h281 h280)) (C h3 (T (T (T h285 h284) h292) h305))))) h3
  have h342 := C (T (T (T (T (T (C h58 (T (C h3 (T (T (T h318 h293) h281) h280)) (C h3 (T h285 h284)))) h334) (C (T (C h3 (C h6 (S h335))) (C h3 (C h6 h336))) h6)) (S h339)) h340) (C (C h3 (C h3 h337)) h3)) h3
  have h343 := h v143 v13 z
  have h344 := h (M z v256) v0 x
  have h345 := h v9 z v0
  let v346 := M v0 v104
  have h347 := h v346 x v13
  have h348 := S h347
  have h349 := h y v0 x
  have h350 := C (C h6 (C h58 h349)) h58
  have h351 := C (C h6 (C h58 (S h349))) h58
  have h352 := h v9 y v0
  have h353 := S h352
  let v354 := M y (M v0 (M v9 y))
  have h355 := h v354 v0 x
  have h356 := h v354 v0 y
  have h357 := h y v0 y
  have h358 := h y x v9
  have h359 := S h358
  have h360 := h (M x (M v9 (M y x))) v9 x
  have h361 := h y v13 v9
  have h362 := S h361
  let v363 := M v13 (M v9 v14)
  have h364 := h v363 v9 x
  have h365 := h v363 v9 z
  have h366 := C (T (T (T (T (C (C h10 (C h76 h361)) h76) (S h365)) h364) (C (T (C h10 (C h6 h362)) (C h10 (C h6 h358))) h6)) (S h360)) h10
  have h367 := C (T (T (T (T h360 (C (T (C h10 (C h6 h359)) (C h10 (C h6 h361))) h6)) (S h364)) h365) (C (C h10 (C h76 h362)) h76)) h10
  have h368 := C h58 (T h358 h367)
  let v369 := M v13 y
  have h370 := h v369 z v14
  have h371 := C h58 (T h366 h359)
  have h372 := C h10 (T (T (T h371 h370) (C (C h76 (T (T (T (T (T (C h40 (T (T (T (C (T h368 (C h58 (T (T (T (T (T (T (T (T (T h366 h359) h357) (C (C h3 (C h17 h352)) h17)) (S h356)) h355) (C (T (T (C h3 (C h6 h353)) h347) h351) h6)) (C (T (T h350 h348) (C h3 (C h6 h345))) h6)) (S h344)) (C h76 h306)))) h76) (S h343)) h332) h342)) (C h40 (T (T (T h341 h333) h321) h331))) (C h40 (T (T (T h330 h322) h252) h320))) (C h40 (T (T (T (T (T h314 h253) h144) h142) h138) h136))) h210) (C h40 (T (T (T h147 h146) h251) (C (C h17 (C h76 h141)) h76))))) h40)) (S h250))
  have h373 := C h10 h368
  have h374 := C (T (T (T (T (T (T h373 h372) h249) h247) (C (C h17 (C h6 h245)) h6)) (S h244)) (C h6 (T h114 (C h17 (T (C h76 (T (T (T (T (T (T h109 h103) h221) h235) h234) h232) h242)) (C h240 (T (T (T (T h239 h233) h231) h229) h222))))))) h17
  have h375 := C h10 h371
  have h376 := S h357
  have h377 := C (C h3 (C h17 h353)) h17
  have h378 := S h355
  have h379 := C (T (T h350 h348) (C h3 (C h6 h352))) h6
  have h380 := C h10 (T (T (T h250 (C (C h76 (T (T (T (T (T (C h40 (T (T (T (C (C h17 (C h76 h140)) h76) (S h251)) h145) h149)) h148) (C h40 (T (T (T (T (T h209 h137) h208) h207) h252) h320))) (C h40 (T (T (T h314 h253) h321) h331))) (C h40 (T (T (T h330 h322) h332) h342))) (C h40 (T (T (T h341 h333) h343) (C (T (C h58 (T (T (T (T (T (T (T (T (T (C h76 h319) h344) (C (T (T (C h3 (C h6 (S h345))) h347) h351) h6)) h379) h378) h356) h377) h376) h358) h367)) h371) h76))))) h40)) (S h370)) h368)
  have h381 := S h249
  have h382 := C (C h17 (C h6 h246)) h6
  have h383 := C h76 (T (T (T (T (T (T h239 h233) h231) h229) h222) h102) h106)
  have h384 := T (T (T (T (T (T (T (T (T (T (T (T h155 h153) h131) h129) h127) h95) h55) h52) h49) h47) h44) h41) h16
  have h385 := C h384 (T (T (T (T h221 h235) h234) h232) h242)
  have h386 := C (T (T (T (T (T (T (C h6 (T (C h17 (T h385 h383)) h117)) h244) (C (C h17 (C h6 (S h245))) h6)) h382) h381) h380) h375) h17
  have h387 := h v263 v14 v9
  have h388 := S h387
  have h389 := C h40 (C h10 h261)
  let v390 := M v9 v13
  have h391 := h (M v14 v390) v9 v14
  have h392 := C h40 (C h10 h262)
  have h393 := h v13 v9 v9
  have h394 := S h393
  let v395 := M v9 (M v9 (M v13 v9))
  have h396 := h v395 v9 x
  have h397 := S h396
  have h398 := h v13 v13 v9
  have h399 := C h10 (C h6 (S h398))
  have h400 := C (T h399 (C h10 (C h6 h393))) h6
  have h401 := C h10 (C h6 h398)
  have h402 := h v13 y v9
  have h403 := C (T (C h10 (C h6 (S h402))) h401) h6
  let v404 := M v9 v369
  have h405 := h (M y v404) v9 x
  have h406 := h v404 y y
  have h407 := S h406
  have h408 := T (T (T (T (T (T (T (T (T h90 h87) h94) h135) h132) h130) h211) h205) h219) h386
  have h409 := T (T (T (T (T (T (T (T (T (T h7 h2) h15) h64) h63) h62) h48) h61) h59) h56) h85
  have h410 := C (C h17 (T (T (T (C h17 h36) (C h17 h409)) (C h17 h176)) (C h17 h408))) h17
  have h411 := C h17 (T h410 h407)
  have h412 := T (T (T (T (T (T (T (T (T (T h77 h57) h55) h52) h49) h47) h44) h41) h16) h1) h12
  have h413 := T (T (T (T (T (T (T (T (T h374 h220) h155) h153) h131) h129) h127) h95) h86) h93
  have h414 := C (C h17 (T (T (T (C h17 h413) (C h17 h91)) (C h17 h412)) (C h17 h8))) h17
  have h415 := h z z y
  have h416 := C (C h17 (C h6 (S h415))) h6
  let v417 := M y v4
  have h418 := h (M z v417) y x
  have h419 := C h76 h8
  have h420 := C h76 h412
  have h421 := C h76 h91
  have h422 := C h384 (T (T (T (T (T (T (T (T h15 h64) h63) h62) h48) h61) h59) h86) h93)
  have h423 := C h17 (T (T (T h422 h421) h420) h419)
  have h424 := C h76 h423
  have h425 := C h240 (T (T (T (T (T (T (T (T h90 h87) h55) h52) h49) h47) h44) h41) h16)
  have h426 := C h76 h176
  have h427 := C h76 h409
  have h428 := C h76 h36
  have h429 := C h17 (T (T (T h428 h427) h426) h425)
  have h430 := h v417 z y
  have h431 := C h240 (T (T (T (T (T (T (T (T (T (T (T (T (T (T h374 h220) h155) h153) h131) h129) h127) h95) h55) h52) h49) h47) h44) h41) h16)
  have h432 := C (T (C h17 h431) h423) h76
  have h433 := h v404 y z
  have h434 := h v404 y v0
  have h435 := S h434
  have h436 := C h3 h409
  have h437 := C h3 h36
  have h438 := C (C h17 (T (T (T h437 h436) (C h3 h176)) (C h3 h408))) h3
  have h439 := C h17 (T (T (T h438 h435) h433) h432)
  have h440 := C h3 h8
  have h441 := C h3 h412
  have h442 := C (C h17 (T (T (T (C h3 h413) (C h3 h91)) h441) h440)) h3
  have h443 := h v28 y v13
  have h444 := S h443
  have h445 := C h58 h34
  have h446 := C h58 h36
  have h447 := C (C h17 (T h446 h445)) h58
  have h448 := C h17 (T (T (T (T (T (T (T h447 h444) h382) h381) h380) h375) h434) h442)
  have h449 := C h58 h8
  have h450 := C h58 h23
  have h451 := C (C h17 (T h450 h449)) h58
  have h452 := C h17 (T (T (T h184 h183) h443) h451)
  have h453 := C h384 (T (T (T (T (T (T (T (T (T (T (T (T (T (T h15 h64) h63) h62) h48) h61) h59) h94) h135) h132) h130) h211) h205) h219) h386)
  have h454 := C h76 (T (T (C (T (T (T (T (T h428 h427) h426) h425) h453) (C h76 (T (T (T (T (T (T (T (T (T h374 h220) h155) h153) h131) h126) h175) h452) h448) h439))) h17) (S h430)) h429)
  have h455 := C h17 (T (T (T (T (T (T (T (T (T h454 h424) h418) h416) h382) h381) h380) h375) h406) h414)
  have h456 := C h17 (T (T (T h447 h444) h174) h173)
  have h457 := C h17 (T (T (T (T (T (T (T h438 h435) h373) h372) h249) h247) h443) h451)
  have h458 := S h433
  have h459 := C (T h429 (C h17 h453)) h76
  have h460 := C h17 (T (T (T h459 h458) h434) h442)
  have h461 := C h76 (T (T h423 h430) (C (T (T (T (T (T (C h76 (T (T (T (T (T (T (T (T (T h460 h457) h456) h185) h134) h130) h211) h205) h219) h386)) h431) h422) h421) h420) h419) h17))
  have h462 := C h76 h429
  have h463 := S h418
  have h464 := C (C h17 (C h6 h415)) h6
  have h465 := C h17 (T (T (T (T (T (T (T (T (T h459 h458) h373) h372) h249) h247) h464) h463) h462) h461)
  have h466 := h x v14 y
  let v467 := M x v14
  let v468 := M y v467
  have h469 := h (M v14 v468) y x
  have h470 := h v468 x y
  have h471 := S h470
  have h472 := h v13 z x
  have h473 := S h472
  have h474 := C h6 (C h17 h473)
  have h475 := C (T h474 (C h6 (T (T (T h38 h215) h203) (C h17 (T (T (T h200 h199) h191) (C h162 h6)))))) h17
  have h476 := C h6 (C h17 h472)
  have h477 := C h476 h17
  have h478 := C h474 h17
  let v479 := M z (M x (M v13 z))
  have h480 := h v479 x y
  have h481 := h v479 x v9
  have h482 := S h481
  have h483 := C h6 (C h10 h472)
  have h484 := h (M x v390) v9 v14
  have h485 := C h6 (C h10 h473)
  have h486 := C (T (T (T (T h485 h484) (C (C h10 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (C h40 (T (T (T (C h483 h10) h482) h480) h478)) (C h40 (T (T h477 h475) h471))) h469) (C (C h17 (C h6 (S h466))) h6)) h123) (C (T (T (T h134 h130) h211) h205) h10)) (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T h155 h153) h131) h126) h175) h452) h448) h439) h465) h455) h411) h405) h403) h400) h397) h10)) h394) h37) h35) h214) h213) h212) h157) h204) h202) h279) (C h40 (T (T (T h268 h266) h387) (C h392 h10))))) h40)) (S h391)) h389) h10
  have h487 := S h480
  have h488 := C (T (C h6 (T (T (T (C h17 (T (T (T (C h164 h6) h202) h198) h201)) h217) h181) h25)) h476) h17
  have h489 := C h40 (T (T h470 h488) h478)
  have h490 := S h469
  have h491 := C (C h17 (C h6 h466)) h6
  have h492 := C (T (T (T h155 h153) h131) h126) h10
  have h493 := C h17 (T (T (T (T (T (T (T (T (T h454 h424) h418) h416) h382) h381) h380) h375) h433) h432)
  have h494 := C h17 (T (T (T (T (T (T (T (T (T h410 h407) h373) h372) h249) h247) h464) h463) h462) h461)
  have h495 := C h17 (T h406 h414)
  have h496 := S h405
  have h497 := C (T h399 (C h10 (C h6 h402))) h6
  have h498 := C (T (C h10 (C h6 h394)) h401) h6
  have h499 := T (T (T (T (T (T (T (T (T (T (T (T (T (T h396 h498) h497) h496) h495) h494) h493) h460) h457) h456) h185) h134) h130) h211) h205
  have h500 := C h499 h10
  have h501 := C (T (T (T (T h392 h391) (C (C h10 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (C h40 (T (T (T (C h389 h10) h388) h265) h271)) h289) h191) h163) h158) h156) h92) h79) h24) h11) h393) h500) h492) h124) h491) h490) h489) (C h40 (T (T (T h477 h487) h481) (C h485 h10))))) h40)) (S h484)) h483) h10
  have h502 := h v13 v13 v14
  have h503 := C (T (C h40 (C h6 (S h502))) h267) h6
  have h504 := h (M v13 (M v14 (M v13 v13))) v14 x
  have h505 := S h504
  have h506 := C (T h270 (C h40 (C h6 h502))) h6
  let v507 := M v13 v167
  have h508 := h v395 x v14
  have h509 := S h508
  have h510 := C h40 (T h318 h315)
  have h511 := C h40 (T h299 h305)
  have h512 := h v257 v0 v13
  have h513 := h v479 x v0
  let v514 := M x v256
  have h515 := h v514 v0 v13
  have h516 := h (M v13 v514) x x
  have h517 := h v0 v13 x
  have h518 := h v0 z x
  have h519 := C h6 (C h6 (S h518))
  have h520 := C h6 (C h6 h518)
  have h521 := h v0 y x
  have h522 := S h521
  have h523 := h (M y (M x (M v0 y))) x x
  have h524 := T h521 (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h523 (C (T (C h6 (C h6 h522)) h520) h6)) (C (T h519 (C h6 (C h6 h517))) h6)) (S h516)) (C h58 (T (T (T (T h515 (C (C h3 (T (T (C h58 (T (T (T (C (C h6 (C h3 h472)) h3) (S h513)) h480) h478)) (C h58 (T (T (T (T (T (T h477 h487) h481) h486) h388) h265) h271))) (C h58 h269))) h58)) (S h512)) h316) h511))) (C h58 h510)) h301) h283) h258) h255) h61) h59) h94) h135) h132) h126) h175) h452) h448) h439) h465) h455) h411) h405) h403) h400) h397) h6)
  have h525 := C (C h6 (C h40 h524)) h40
  have h526 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h396 h498) h497) h496) h495) h494) h493) h460) h457) h456) h185) h134) h129) h127) h95) h55) h52) h296) h295) h294) h317) (C h58 h511)) (C h58 (T (T (T (T h510 h300) h512) (C (C h3 (T (T (C h58 h290) (C h58 (T (T (T (T (T (T h268 h266) h387) h501) h482) h480) h478))) (C h58 (T (T (T h477 h487) h513) (C (C h6 (C h3 h473)) h3))))) h58)) (S h515)))) h516) (C (T (C h6 (C h6 (S h517))) h520) h6)) (C (T h519 (C h6 (C h6 h521))) h6)) (S h523)) h6
  have h527 := T h526 h522
  have h528 := C (C h6 (C h40 h527)) h40
  have h529 := h v395 x v13
  have h530 := C h58 h524
  have h531 := C h6 h530
  let v532 := M (M v13 v4) z
  have h533 := h v532 v13 v13
  have h534 := h v532 v13 v9
  have h535 := h v532 v13 v0
  let v536 := M v13 v0
  have h537 := h x v14 v13
  T (T (T (T (T (T (T (T (T (T (T (T (T h221 h235) h234) (h v230 x v13)) (C (T (T (T (T (T (T (T (T (T (T (T (T (C h6 (C h58 (C h241 h6))) (h (M x (M v13 v98)) v13 x)) (C (T (C h58 (C h6 (S (h x x v13)))) (C h58 (C h6 h537))) h6)) (C (T (C h58 (C h6 (S h537))) (C h58 (C h6 (h x z v13)))) h6)) (S (h (M z v536) v13 x))) (C h76 (T (T (T h530 (C h58 (T (T (T (T (T (T h526 h522) h227) (C h241 (T h15 h27))) (C h6 (T (T (T (T (T (T (T (T (T (T (T (T (T (T h22 h64) h63) h62) h48) h61) h59) h94) h135) h132) h130) h211) h205) h219) h386))) (C h6 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h374 h220) h155) h153) h131) h126) h175) h452) h448) h439) h465) h455) h411) h405) h403) h400) h397) h508) h528))) (C h6 (T (T (T h525 h509) h529) (C (C h6 (C h58 h527)) h58)))))) (C (T (T (T (T (T (T (T h393 h500) h492) h124) h491) h490) h489) (C h40 (T (T (T (T (T (T (T (T h477 h487) (h v479 x x)) (C (T (C h6 (C h6 h473)) (C h6 (C h6 (h v13 v0 x)))) h6)) (S (h (M v0 (M x v536)) x x))) (C h3 (T (T (T (T (T (T (T (T (T h531 (C h6 (C h58 (C h499 h6)))) (C h6 (C h58 (T (T h385 h383) h116)))) (h (M x (M v13 v243)) v13 x)) (C (T (C h58 (C h6 (S (h z x v13)))) h82) h6)) h81) h75) h80) h535) (C (C h58 (T h441 h440)) h3)))) (C h3 (T (T (T (C (C h58 (T h437 h436)) h3) (S h535)) h534) (C (C h58 (T (T h79 h24) h11)) h10)))) (C h3 (T (T (T (C (C h58 (T (T h37 h35) h214)) h10) (S h534)) h533) (C (C h58 (T (T (C h58 h78) h450) h449)) h58)))) (C h3 (T (T (T (C (C h58 (T (T h446 h445) (C h58 h177))) h58) (S h533)) (h v532 v13 v14)) (C (C h58 (T (T h182 h172) h171)) h40)))))) (T (T (T (T (C h6 (T (T (T (C h531 h58) (S h529)) h508) h528)) (C h6 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h525 h509) h396) h498) h497) h496) h495) h494) h493) h460) h457) h456) h185) h134) h130) h211) h205) h219) h386))) (C h6 (T (T (T (T (T (T (T (T (T (T (T (T (T (T h374 h220) h155) h153) h131) h129) h127) h95) h55) h52) h49) h47) h44) h41) h27))) (C h236 (T h22 h16))) h228))) (S (h v507 v14 v0))))) (h (M z v507) v13 x)) (C (T (T (T (T (T (C h58 (C h6 (S (h v14 z v13)))) (h (M v13 v467) x x)) (C (T (C h6 (C h6 (S (h y v13 x)))) (C h6 (C h6 h349))) h6)) (S (h v346 x x))) h347) h351) h6)) h379) h378) h356) h377) h376) (T (T (T (T (T (T (T (T (T h37 h35) h214) h213) h212) h157) h204) (C (T (T (T (T (T (T (T (T (T h162 h470) h488) h487) h481) h486) h388) h272) h288) h286) h6)) (C (T (T (T (T (T h278 h277) h273) h265) h506) h505) h6)) (C (T (T h504 h503) h266) h6)))) (C h17 (C (T (T h265 h506) h505) h6))) (C h17 (C (T (T (T (T (T h504 h503) h266) h272) h288) h286) h6))) (C h17 (T (T (T (T (C (T (T (T (T (T (T (T (T (T h278 h277) h273) h387) h501) h482) h480) h475) h471) h164) h6) h202) h274) (C (T (T (T (T (T (T (T (T (T h287 h278) h277) h273) h387) h501) h482) h480) h475) h471) h40)) (C (T (T h470 h488) h487) h40)))) (C h17 (C (T (T h480 h475) h471) h40))) (C h17 (T (T (T (T (T (C (T (T (T (T (T (T (T (T (T h470 h488) h487) h481) h486) h388) h272) h288) h286) h276) h40) h275) h191) h163) h158) (C h10 (T h219 h386))))) (C h17 (T (T (T (T (T (C h10 (T h374 h220)) h157) h204) h202) h192) h218))) (C h17 (T (T (T (T (T h216 h193) h191) h188) h187) h186))) h181) h25

