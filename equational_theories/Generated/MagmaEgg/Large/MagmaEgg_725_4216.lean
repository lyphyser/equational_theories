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
theorem Equation725_implies_Equation4216 (G: Type _) [Magma G] (h: Equation725 G) : Equation4216 G := fun x y z =>
  let v0 := M z y
  let v1 := M v0 z
  let v2 := M v1 x
  have h3 := h v2 y x
  have h4 := S h3
  let v5 := M y (M (M x v2) x)
  have h6 := h v5 y y
  have h7 := h y v2 z
  have h8 := S h7
  have h9 := h x v2 v1
  have h10 := T h9 (C h3 h8)
  have h11 := R y
  have h12 := R x
  let v13 := M x y
  have h14 := h y x v13
  have h15 := C (S h14) h12
  have h16 := C h11 (T (C h11 (T h15 (C h11 h10))) (S h6))
  let v17 := M (M v13 y) v13
  let v18 := M x v17
  have h19 := h v18 y x
  have h20 := h v18 x x
  have h21 := S h20
  have h22 := C h14 h12
  have h23 := h y x x
  have h24 := S h23
  have h25 := C h12 (C h12 (T (C h24 h12) h22))
  let v26 := M v13 x
  have h27 := h (M x v26) x x
  have h28 := h v13 v1 v1
  have h29 := S h28
  have h30 := h (M v1 (M (M v1 v13) v1)) x v1
  have h31 := S h30
  have h32 := R v1
  have h33 := h (M v13 v1) x v13
  have h34 := R v13
  have h35 := h y v13 z
  have h36 := h y v13 v0
  have h37 := C (S h36) h34
  let v38 := M v13 (M (M v0 y) v0)
  have h39 := h v38 x v13
  have h40 := h v38 y v13
  have h41 := C h36 h34
  have h42 := h x y v13
  have h43 := S h42
  have h44 := C h43 h11
  let v45 := M v26 v13
  let v46 := M y v45
  have h47 := h v46 y y
  have h48 := C h12 (C h12 (T (T (T (T (T (T h42 (C h11 (T h47 (C h11 (T (C h11 h44) h41))))) (S h40)) h39) (C h12 (C h12 (T h37 (C h35 h34))))) (S h33)) (C h28 h32)))
  have h49 := S h9
  have h50 := T (C h4 h7) h49
  have h51 := C h12 (C h12 h50)
  have h52 := h v5 x y
  have h53 := T (T (T h52 h51) h48) h31
  have h54 := C h32 h53
  have h55 := h v5 v1 y
  have h56 := S h55
  have h57 := C h32 (C h32 h10)
  have h58 := h v1 x y
  have h59 := S h58
  have h60 := C h59 h12
  have h61 := C h32 (T (T (C h32 h60) h57) h56)
  let v62 := M (M y v1) y
  let v63 := M x v62
  have h64 := h v63 v1 x
  have h65 := h v63 y x
  have h66 := S h65
  have h67 := C h58 h12
  have h68 := R v2
  have h69 := h y v2 y
  have h70 := C (S h69) h68
  have h71 := C h11 (T h70 (C h11 h67))
  have h72 := C h69 h68
  have h73 := h y x z
  have h74 := S h73
  have h75 := C h12 (C h12 (T (C h74 h12) h22))
  have h76 := h (M x v1) x x
  have h77 := h x v1 v0
  have h78 := T (T (T (T (T (T (C (S h77) h32) h76) h75) h21) h19) h16) h4
  have h79 := C h11 (T (C h11 h78) h72)
  let v80 := M v1 (M (M v0 x) v0)
  have h81 := h v80 y v1
  have h82 := h v80 x v1
  have h83 := S h82
  have h84 := S h76
  have h85 := C h12 (C h12 (T h15 (C h73 h12)))
  have h86 := S h19
  have h87 := C h11 (T h6 (C h11 (T (C h11 h50) h22)))
  have h88 := T (T (T (T (T (T h3 h87) h86) h20) h85) h84) (C h77 h32)
  have h89 := C h68 h7
  have h90 := T h89 h49
  let v91 := M (M v2 y) v2
  have h92 := h v91 x v0
  have h93 := S h92
  have h94 := R v0
  have h95 := h (M v0 v91) x v0
  have h96 := h y v0 v2
  have h97 := h y v0 v13
  have h98 := C (S h97) h94
  let v99 := M v0 v17
  have h100 := h v99 x v0
  have h101 := h v99 y v0
  have h102 := C h97 h94
  have h103 := h z y v1
  have h104 := S h103
  have h105 := C h104 h11
  let v106 := M y (M (M v1 z) v1)
  have h107 := h v106 y y
  have h108 := h z v0 z
  have h109 := S h108
  have h110 := C h109 h94
  have h111 := C h12 (C h12 (T h110 (C (T (T (T (T (T h103 (C h11 (T h107 (C h11 (T (C h11 h105) h102))))) (S h101)) h100) (C h12 (C h12 (T h98 (C h96 h94))))) (S h95)) h94)))
  let v112 := M (M z z) z
  have h113 := h (M v0 v112) x v0
  have h114 := C h12 (T (T (T h113 h111) h93) (C h90 h88))
  have h115 := S h113
  have h116 := C h108 h94
  have h117 := C h103 h11
  have h118 := C h12 (C h12 (T (C (T (T (T (T (T h95 (C h12 (C h12 (T (C (S h96) h94) h102)))) (S h100)) h101) (C h11 (T (C h11 (T h98 (C h11 h117))) (S h107)))) h104) h94) h116))
  have h119 := h x v1 z
  have h120 := S h119
  have h121 := C h68 h8
  have h122 := T h9 h121
  have h123 := C h12 (T (T (T (C h122 (T (T (T (T (T (T (C h120 h32) h76) h75) h21) h19) h16) h4)) h92) h118) h115)
  let v124 := M (M z x) z
  let v125 := M v1 v124
  have h126 := h v125 x v1
  have h127 := h v125 x x
  have h128 := S h126
  have h129 := C h12 (T (T (T h113 h111) h93) (C h90 (T (T (T (T (T (T h3 h87) h86) h20) h85) h84) (C h119 h32))))
  have h130 := C h12 (T (T (T (C h122 h78) h92) h118) h115)
  have h131 := S h81
  have h132 := C h11 (T h70 (C h11 h88))
  have h133 := C h11 (T (C h11 h60) h72)
  have h134 := S h64
  have h135 := C h32 (C h32 h50)
  have h136 := C h32 (T (T h55 h135) (C h32 h67))
  have h137 := S h52
  have h138 := C h12 (C h12 h10)
  have h139 := C h42 h11
  have h140 := S h35
  have h141 := C h12 (C h12 (T (T (T (T (T (T (C h29 h32) h33) (C h12 (C h12 (T (C h140 h34) h41)))) (S h39)) h40) (C h11 (T (C h11 (T h37 (C h11 h139))) (S h47)))) h43))
  have h142 := T (T (T h30 h141) h138) h137
  have h143 := C h32 h142
  have h144 := T (T (T (T (T (T (T (T (T (T (T h28 h143) h136) h134) h65) h133) h132) h131) h82) h130) h129) h128
  let v145 := M (M x v13) x
  have h146 := h v145 x x
  have h147 := h (M x v145) x x
  have h148 := h v13 x x
  have h149 := h v13 x v0
  have h150 := C h122 (T (T (T (T (T (T (C h12 (C (S h149) h12)) h27) h25) h21) h19) h16) h4)
  let v151 := M (M v0 v13) v0
  have h152 := h (M x v151) x x
  have h153 := T (T (T (T (T (T (T (T (T (T (T h126 h123) h114) h83) h81) h79) h71) h66) h64) h61) h54) h29
  have h154 := C (C h94 h153) h94
  have h155 := C h12 h154
  have h156 := C (C h94 h144) h94
  have h157 := h v151 x v13
  have h158 := h (M v13 v151) x v13
  have h159 := h v13 v13 v0
  have h160 := h v13 v13 v13
  let v161 := M (M v13 v13) v13
  have h162 := h (M v13 v161) x v13
  have h163 := h v161 x v13
  have h164 := C (C h34 h153) h34
  have h165 := C h12 (T (T (T (T h164 h163) (C h12 (C h12 (C (T (T h162 (C h12 (C h12 (T (C (S h160) h34) (C h159 h34))))) (S h158)) h34)))) (S h157)) h156)
  have h166 := C (C h34 h144) h34
  have h167 := h v161 v2 y
  have h168 := h v13 x z
  have h169 := h (M x (M (M z v13) z)) x x
  have h170 := R z
  have h171 := h (M y v161) x y
  have h172 := h v13 y v13
  have h173 := h v13 v1 x
  have h174 := S h173
  have h175 := C h174 h32
  have h176 := C h34 (T (C h34 h175) h140)
  let v177 := M v1 v145
  have h178 := h v177 v13 v1
  have h179 := S h178
  have h180 := C h173 h32
  have h181 := C h34 (T h35 (C h34 h180))
  have h182 := h v13 y v0
  have h183 := T (T (C (S h182) h11) h181) h179
  let v184 := M y v151
  have h185 := h v184 x y
  have h186 := h v184 v1 y
  have h187 := T (T h178 h176) (C h182 h11)
  have h188 := C (T (T (T (T (T (T h119 (C h32 h153)) (C h32 (T h173 (C h32 h187)))) (S h186)) h185) (C h12 (T (C h12 h183) (C h12 (T (T h178 h176) (C h172 h11)))))) (S h171)) (T (T (T (C h12 (C (C h170 h153) h170)) h169) (C h12 (C h12 (C (S h168) h12)))) h24)
  have h189 := h v125 x z
  have h190 := h v46 v2 y
  have h191 := C h12 (T (T (T h190 (C h68 (T (C h68 h44) (C h68 (T (T (T (T (T (T (T (T (T (T (T (T (T h28 h143) h136) h134) h65) h133) h132) h131) h82) h130) h129) h128) h189) h188))))) (S h167)) h166)
  have h192 := h v46 x y
  have h193 := S h192
  have h194 := C h12 h139
  have h195 := h x v13 x
  have h196 := C h12 (T (C h12 (T (C (S h195) h34) h194)) h193)
  let v197 := M (M x x) x
  have h198 := h (M v13 v197) x v13
  have h199 := C h12 (C (T (T (T (T (T (T (T (T (T (T (T (T (T (C h12 (T (T (T (T (T (T (T h198 h196) h191) h165) h155) h152) h150) (C h90 (T (T (T (T (T (T h3 h87) h86) h20) (C h12 (C h12 (T h15 (C (T (T h23 (C h12 (C h12 (C h148 h12)))) (S h147)) h12))))) (S h146)) (C (C h12 h144) h12))))) (S h127)) h126) h123) h114) h83) h81) h79) h71) h66) h64) h61) h54) h29) h12)
  have h200 := S h198
  have h201 := C h12 h44
  have h202 := C h12 (T h192 (C h12 (T h201 (C h195 h34))))
  have h203 := h x v13 v1
  have h204 := C h12 (T (C h12 (T (C (S h203) h34) h194)) h193)
  let v205 := M v2 v1
  have h206 := h (M v13 v205) x v13
  have h207 := C h12 (C (C h12 (T (T (T h206 h204) h202) h200)) h12)
  have h208 := S h206
  have h209 := C h12 (T h192 (C h12 (T h201 (C h203 h34))))
  have h210 := h x v13 z
  have h211 := C h12 (T (C h12 (T (C (S h210) h34) h194)) h193)
  have h212 := h (M v13 v124) x v13
  have h213 := C h12 (C (C h12 (T (T (T h212 h211) h209) h208)) h12)
  have h214 := S h212
  have h215 := C h12 (T h192 (C h12 (T h201 (C h210 h34))))
  have h216 := h x v13 y
  have h217 := S h216
  have h218 := C h12 (T (C h12 (T (C h217 h34) h194)) h193)
  let v219 := M (M y x) y
  have h220 := h (M v13 v219) x v13
  have h221 := C h12 (C (C h12 (T (T (T h220 h218) h215) h214)) h12)
  have h222 := S h220
  have h223 := C h12 (T h192 (C h12 (T h201 (C h216 h34))))
  have h224 := h x v13 v2
  have h225 := C h12 (T (C h12 (T (C (S h224) h34) h194)) h193)
  let v226 := M v2 x
  let v227 := M v226 v2
  let v228 := M v13 v227
  have h229 := h v228 x v13
  have h230 := T (T (T h229 h225) h223) h222
  have h231 := C h12 (C (C h12 h230) h12)
  have h232 := h v228 x x
  have h233 := S h232
  have h234 := S h229
  have h235 := C h12 (T h192 (C h12 (T h201 (C h224 h34))))
  have h236 := T (T (T h220 h218) h235) h234
  have h237 := C h12 h236
  have h238 := C h12 (T (T (T h212 h211) h223) h222)
  have h239 := C h12 (T (T (T h206 h204) h215) h214)
  have h240 := C h12 (T (T (T h198 h196) h209) h208)
  have h241 := T (T (T (T (T (T h171 (C h12 (T (C h12 (T (T (C (S h172) h11) h181) h179)) (C h12 h187)))) (S h185)) h186) (C h32 (T (C h32 h183) h174))) (C h32 h144)) h120
  have h242 := C h12 (T (T (T h164 h167) (C h68 (T (C h68 (T (T (T (T (T (T (T (T (T (T (T (T (T (C h241 (T (T (T h23 (C h12 (C h12 (C h168 h12)))) (S h169)) (C h12 (C (C h170 h144) h170)))) (S h189)) h126) h123) h114) h83) h81) h79) h71) h66) h64) h61) h54) h29)) (C h68 h139)))) (S h190))
  have h243 := C h12 (T (T (T (T h154 h157) (C h12 (C h12 (C (T (T h158 (C h12 (C h12 (T (C (S h159) h34) (C h160 h34))))) (S h162)) h34)))) (S h163)) h166)
  have h244 := C h12 h156
  have h245 := S h152
  have h246 := S h27
  have h247 := C h12 (C h12 (T h15 (C h23 h12)))
  have h248 := C h90 (T (T (T (T (T (T h3 h87) h86) h20) h247) h246) (C h12 (C h149 h12)))
  have h249 := C h12 (T (T (T (T (T (T (T (C h122 (T (T (T (T (T (T (C (C h12 h153) h12) h146) (C h12 (C h12 (T (C (T (T h147 (C h12 (C h12 (C (S h148) h12)))) h24) h12) h22)))) h21) h19) h16) h4)) h248) h245) h244) h243) h242) h202) h200)
  have h250 := T (C h11 h142) h4
  have h251 := h y x y
  have h252 := S h251
  have h253 := h y y z
  have h254 := h y v1 z
  have h255 := S h254
  let v256 := M v1 v1
  have h257 := h v256 y v1
  have h258 := h v1 v1 y
  have h259 := S h258
  have h260 := h (M v1 v62) v1 v1
  have h261 := h v1 y v1
  let v262 := M v256 v1
  have h263 := h (M y v262) v1 y
  have h264 := C h12 (C h12 (C (T (T (T h263 (C h32 (T (C h32 (T (T (C (S h261) h11) (C h32 (T h254 (C h32 (C h258 h32))))) (S h260))) h259))) h257) (C h11 (T (C h11 (C h255 h32)) (S h253)))) h11))
  have h265 := h v262 x y
  have h266 := h x v2 v2
  have h267 := C h12 (T (T (T (T (T (T (C h12 (T (T (T (C (T (T (S h266) h9) h121) h68) h92) h118) h115)) h114) h83) h81) h79) h71) h66)
  have h268 := h (M v2 v227) x v2
  have h269 := h v227 v2 v13
  have h270 := S h269
  have h271 := C h68 (C h68 (C h236 h34))
  have h272 := h v219 v2 v13
  have h273 := h v219 x y
  have h274 := S h273
  have h275 := h (M y v219) x y
  have h276 := h x y y
  have h277 := C h12 (C h12 (C (T (T h192 (C h12 (T h201 (C h12 (C h276 h11))))) (S h275)) h11))
  have h278 := h v45 x y
  have h279 := h v45 x z
  have h280 := S h279
  have h281 := h (M z v45) x z
  have h282 := h x z v13
  have h283 := h x z x
  have h284 := h (M z v197) x z
  have h285 := C h12 (C h12 (C (T (T h284 (C h12 (C h12 (T (C (S h283) h170) (C h282 h170))))) (S h281)) h170))
  have h286 := h v197 x z
  have h287 := h v197 x v1
  have h288 := S h287
  have h289 := h (M v1 v197) x v1
  have h290 := h x v1 x
  have h291 := C h12 (C h12 (T h175 (C (T (C h12 (T h73 (C h12 (C h290 h32)))) (S h289)) h32)))
  have h292 := h v177 x v1
  have h293 := h v177 v1 v2
  have h294 := S h292
  have h295 := C h12 (C h12 (T (C (T h289 (C h12 (T (C h12 (C (S h290) h32)) h74))) h32) h180))
  have h296 := S h286
  have h297 := C h12 (C h12 (C (T (T h281 (C h12 (C h12 (T (C (S h282) h170) (C h283 h170))))) (S h284)) h170))
  have h298 := S h278
  have h299 := C h12 (C h12 (C (T (T h275 (C h12 (T (C h12 (C (S h276) h11)) h194))) h193) h11))
  have h300 := S h272
  have h301 := C h68 (C h68 (C h230 h34))
  have h302 := S h268
  have h303 := C h12 (T (T (T (T (T (T h65 h133) h132) h131) h82) h130) (C h12 (T (T (T h113 h111) h93) (C (T (T h89 h49) h266) h68))))
  have h304 := C h68 (T (T (T (T (T (T (T (T (T (T (T (T (T (T h119 (C h32 (T (T (T (T (T (T (T (T (T (T (T h126 h123) h114) h83) h81) h79) h71) h66) h64) h61) h54) (C h32 (T (T (T (T (T (T h30 h141) h138) h137) h55) h135) (C (T (T (T h58 h303) h302) (C h68 (T (T (T (T (T (T (T (T (T (T (T h269 h301) h300) h273) h299) h298) h279) h297) h296) h287) h295) h294))) h68)))))) (S h293)) h292) h291) h288) h286) h285) h280) h278) h277) h274) h272) h271) h270)
  have h305 := h v2 x z
  have h306 := C (S h305) h12
  have h307 := C h305 h12
  have h308 := C (T (C h32 h307) (C h32 (T (T (T (T h306 h304) h268) h267) h59))) h32
  have h309 := T (T (T h308 h265) h264) h252
  have h310 := T h3 (C h11 h53)
  have h311 := C h68 (T (T (T (T (T (T (T (T (T (T (T (T (T (T h269 h301) h300) h273) h299) h298) h279) h297) h296) h287) h295) h294) h293) (C h32 (T (T (T (T (T (T (T (T (T (T (T (C h32 (T (T (T (T (T (T (C (T (T (T (C h68 (T (T (T (T (T (T (T (T (T (T (T h292 h291) h288) h286) h285) h280) h278) h277) h274) h272) h271) h270)) h268) h267) h59) h68) h57) h56) h52) h51) h48) h31)) h143) h136) h134) h65) h133) h132) h131) h82) h130) h129) h128))) h120)
  have h312 := C (T (C h32 (T (T (T (T h58 h303) h302) h311) h307)) (C h32 h306)) h32
  have h313 := S h265
  have h314 := C h12 (C h12 (C (T (T (T (C h11 (T h253 (C h11 (C h254 h32)))) (S h257)) (C h32 (T h258 (C h32 (T (T h260 (C h32 (T (C h32 (C h259 h32)) h255))) (C h261 h11)))))) (S h263)) h11))
  have h315 := h y v2 v0
  have h316 := S h315
  have h317 := h y v0 z
  have h318 := h v0 v1 v0
  have h319 := S h318
  have h320 := C h319 h32
  have h321 := C h94 (T (C h94 h320) (S h317))
  let v322 := M (M v0 v0) v0
  let v323 := M v1 v322
  have h324 := h v323 v0 v1
  have h325 := h v323 y v1
  have h326 := S h325
  have h327 := C h318 h32
  have h328 := h v226 v0 v1
  have h329 := S h328
  have h330 := T (T (T h251 h314) h313) h312
  have h331 := C h94 h330
  have h332 := S h324
  have h333 := C h94 (T h317 (C h94 h327))
  have h334 := h v0 y z
  have h335 := S h334
  have h336 := T (T (C h335 h11) h333) h332
  have h337 := C h94 (T (T (T (T (T (T (C h94 h336) (C h94 (T (T h324 h321) h331))) h329) h304) h268) h267) h59)
  let v338 := M z v0
  let v339 := M y (M v338 z)
  have h340 := h v339 v0 y
  have h341 := h v339 x y
  have h342 := S h341
  have h343 := T (T h324 h321) (C h334 h11)
  have h344 := C h12 h343
  have h345 := h v0 y y
  have h346 := S h345
  have h347 := C h12 (T (C h12 (T (T (C h346 h11) h333) h332)) h344)
  let v348 := M (M y v0) y
  have h349 := h (M y v348) x y
  have h350 := C h11 (T (T (T (T (T h349 h347) h342) h340) h337) h327)
  have h351 := C h11 (T h345 h350)
  have h352 := h v339 v1 y
  have h353 := S h352
  have h354 := C h32 (T h318 (C h32 h343))
  have h355 := h v1 v0 z
  have h356 := T (T (C (S h355) h94) h354) h353
  have h357 := C h11 (T (C h11 h356) h335)
  let v358 := M z v1
  let v359 := M v0 (M v358 z)
  have h360 := h v359 y v0
  have h361 := h v359 x v0
  have h362 := S h361
  have h363 := C h32 (T (C h32 h336) h319)
  have h364 := T (T h352 h363) (C h355 h94)
  have h365 := h v1 v0 v2
  have h366 := C h12 (T (C h12 (T (T (C (S h365) h94) h354) h353)) (C h12 h364))
  let v367 := M v205 v2
  have h368 := h (M v0 v367) x v0
  have h369 := C h68 (C h68 (C (T (T (T (T (T (T (T (T h368 h366) h362) h360) h357) h351) h326) h324) h321) h94))
  have h370 := h v367 v2 v0
  have h371 := C (T (T (T (C h68 (T (T (T (T (T (T h370 h369) h316) h251) h314) h313) h312)) (C h310 h309)) (C h250 h7)) h49) (T (T (T (T (T (T (T (T (T (T h3 h87) h86) h20) h247) h246) (C h12 (C (T (T (T (T (T (T (T (T (T (T (T (T (T h28 h143) h136) h134) h65) h133) h132) h131) h82) h130) h129) h128) h127) h249) h12))) (C h12 (C h240 h12))) (C h12 (C h239 h12))) (C h12 (C h238 h12))) (C h12 (C h237 h12)))
  have h372 := S h370
  have h373 := S h368
  have h374 := C h12 (T (C h12 h356) (C h12 (T (T h352 h363) (C h365 h94))))
  have h375 := S h360
  have h376 := C h11 (T h334 (C h11 h364))
  have h377 := S h349
  have h378 := C h12 h336
  have h379 := C h12 (T h378 (C h12 (T (T h324 h321) (C h345 h11))))
  have h380 := S h340
  have h381 := C h94 h309
  have h382 := C h94 (T (T (T (T (T (T h58 h303) h302) h311) h328) (C h94 (T (T h381 h333) h332))) (C h94 h343))
  have h383 := C h11 (T (T (T (T (T h320 h382) h380) h341) h379) h377)
  have h384 := C h11 (T h383 h346)
  have h385 := C h68 (C h68 (C (T (T (T (T (T (T (T (T h333 h332) h325) h384) h376) h375) h361) h374) h373) h94))
  have h386 := h y z x
  have h387 := S h386
  let v388 := M z v26
  have h389 := h v388 x z
  have h390 := S h389
  have h391 := C h386 h170
  have h392 := h v0 z v2
  let v393 := M (M v2 v0) v2
  have h394 := h (M z v393) x z
  have h395 := C h12 (C h12 (T (C (T (T h394 (C h12 (C h12 (C (S h392) h170)))) h74) h170) h391))
  have h396 := h v393 x z
  have h397 := h y z z
  have h398 := h v358 x z
  have h399 := h z v1 v2
  have h400 := T (T (T (C (S h399) h32) h398) (C h12 (C h12 (T (C (S h397) h170) h391)))) h390
  have h401 := C h170 (T (C h170 h400) h387)
  let v402 := M v1 (M (M v2 z) v2)
  have h403 := h v402 z v1
  have h404 := h v402 y v1
  have h405 := S h404
  have h406 := C h387 h170
  have h407 := T (T (T h389 (C h12 (C h12 (T h406 (C h397 h170))))) (S h398)) (C h399 h32)
  have h408 := h v388 v2 v2
  have h409 := S h408
  have h410 := h v393 x y
  have h411 := h (M y v393) x y
  have h412 := h v0 y v2
  have h413 := h v348 x y
  have h414 := h v348 x v13
  have h415 := h (M v13 v348) x v13
  have h416 := h v0 v13 y
  have h417 := h v0 v13 v1
  let v418 := M (M v1 v0) v1
  have h419 := h (M v13 v418) x v13
  have h420 := h v418 x v13
  have h421 := h v418 x y
  have h422 := h (M y v418) x y
  have h423 := h v0 y v1
  have h424 := h v0 y v13
  let v425 := M (M v13 v0) v13
  have h426 := h (M y v425) x y
  have h427 := h v425 x y
  have h428 := C h68 (T (T (T (T (T (T (T (T (T (T (T (T h427 (C h12 (C h12 (C (T (T h426 (C h12 (T (C h12 (T (T (C (S h424) h11) h333) h332)) h344))) h342) h11)))) (C h12 (C h12 (C (T (T h341 (C h12 (T h378 (C h12 (T (T h324 h321) (C h423 h11)))))) (S h422)) h11)))) (S h421)) h420) (C h12 (C h12 (C (T (T h419 (C h12 (C h12 (T (C (S h417) h34) (C h416 h34))))) (S h415)) h34)))) (S h414)) h413) (C h12 (C h12 (C (T (T (T h349 h347) (C h12 (T h378 (C h12 (T (T h324 h321) (C h412 h11)))))) (S h411)) h11)))) (S h410)) h396) h395) h390)
  have h429 := h (M v2 v425) x v2
  have h430 := S h429
  have h431 := h v0 v2 v13
  have h432 := h v0 v2 v0
  have h433 := C h12 (C h12 (T (C (S h432) h68) (C h431 h68)))
  have h434 := h (M v2 v322) x v2
  have h435 := C (T (T (T h434 h433) h430) h428) h68
  have h436 := C h68 (C h68 h435)
  have h437 := h v322 v2 v2
  have h438 := T (T h437 h436) h409
  have h439 := h v367 v0 v2
  have h440 := S h439
  have h441 := C h94 (T h108 (C h94 (T (T (T (T (T (T (T (T (T (T (T h113 h111) h93) h248) h245) h244) h243) h242) h235) h234) h232) (C (T (T (T h9 (C h310 h8)) (C h250 h330)) (C h68 (T (T (T (T (T (T h308 h265) h264) h252) h315) h385) h372))) (T (T (T (T (T (T (T (T (T (T h231 h221) h213) h207) h199) h27) h25) h21) h19) h16) h4)))))
  have h442 := T (T (T (T h441 h440) h370) h369) h316
  have h443 := S h437
  have h444 := S h434
  have h445 := C h12 (C h12 (T (C (S h431) h68) (C h432 h68)))
  have h446 := S h396
  have h447 := C h12 (C h12 (T h406 (C (T (T h73 (C h12 (C h12 (C h392 h170)))) (S h394)) h170)))
  have h448 := C h68 (T (T (T (T (T (T (T (T (T (T (T (T h389 h447) h446) h410) (C h12 (C h12 (C (T (T (T h411 (C h12 (T (C h12 (T (T (C (S h412) h11) h333) h332)) h344))) h379) h377) h11)))) (S h413)) h414) (C h12 (C h12 (C (T (T h415 (C h12 (C h12 (T (C (S h416) h34) (C h417 h34))))) (S h419)) h34)))) (S h420)) h421) (C h12 (C h12 (C (T (T h422 (C h12 (T (C h12 (T (T (C (S h423) h11) h333) h332)) h344))) h342) h11)))) (C h12 (C h12 (C (T (T h341 (C h12 (T h378 (C h12 (T (T h324 h321) (C h424 h11)))))) (S h426)) h11)))) (S h427))
  have h449 := C (T (T (T h448 h429) h445) h444) h68
  have h450 := C h68 (C h68 h449)
  have h451 := h v388 v2 v0
  have h452 := C h94 h438
  have h453 := h (M v0 v322) x v0
  have h454 := h v0 v0 v0
  have h455 := h v0 v0 v2
  have h456 := C (S h455) h94
  let v457 := M v0 v393
  have h458 := h v457 x v0
  have h459 := h v457 v0 v0
  have h460 := C h455 h94
  have h461 := h v106 v0 y
  have h462 := C (T (T (T (T (T (C h94 (T h461 (C h94 (T (C h94 h105) h460)))) (S h459)) h458) (C h12 (C h12 (T h456 (C h454 h94))))) (S h453)) h452) h94
  have h463 := h v106 v2 v0
  have h464 := h v106 x y
  have h465 := h z y z
  have h466 := S h465
  have h467 := h (M y v112) x y
  have h468 := C h94 (T (C h94 (T (T (T (T (T (T (T (T (T (T (T h371 h233) h229) h225) h191) h165) h155) h152) h150) h92) h118) h115)) h109)
  have h469 := T (T (T (T h315 h385) h372) h439) h468
  have h470 := C h469 (T (T (T (T (T (T (T (T h467 (C h12 (T (C h12 (C h466 h11)) (C h12 h117)))) (S h464)) h463) (C h68 (C h68 h462))) (S h451)) h408) h450) h443)
  have h471 := C h11 (T (T (T h465 h470) (C h442 h438)) (C h11 h407))
  have h472 := C h68 h391
  have h473 := C (T h472 (C h68 (T (T (T (T h406 h471) h405) h403) h401))) h68
  have h474 := C h170 (T (T (T h473 h396) h395) h390)
  have h475 := C h68 h406
  have h476 := T (T h408 h450) h443
  have h477 := C h94 h476
  have h478 := C (T (T (T (T (T h477 h453) (C h12 (C h12 (T (C (S h454) h94) h460)))) (S h458)) h459) (C h94 (T (C h94 (T h456 (C h94 h117))) (S h461)))) h94
  have h479 := C h442 (T (T (T (T (T (T (T (T h437 h436) h409) h451) (C h68 (C h68 h478))) (S h463)) h464) (C h12 (T (C h12 h105) (C h12 (C h465 h11))))) (S h467))
  have h480 := C h11 (T (T (T (C h11 h400) (C h469 h476)) h479) h466)
  have h481 := S h403
  have h482 := C h170 (T h386 (C h170 h407))
  have h483 := C (T (C h68 (T (T (T (T h482 h481) h404) h480) h391)) h475) h68
  let v484 := M y z
  have h485 := h v484 v2 v1
  have h486 := S h485
  have h487 := h (M v0 v1) v0 y
  have h488 := S h487
  have h489 := T (T h345 h350) (C h11 h320)
  have h490 := C h489 h309
  have h491 := T (T (C h11 h327) h383) h346
  have h492 := C h491 (T (T (T (T (T (T (T (T (T (T h315 h385) h372) h439) h468) h58) h303) h302) h311) h328) (C h94 h490))
  have h493 := C h491 h330
  have h494 := h v339 y y
  have h495 := C (T (T (T (T (T (T (T (T (T (T (T (T h465 h470) h324) h321) h331) h490) h492) h488) h382) h380) h494) (C h469 (T (T (T (T (T (T (T (T (T (C h11 h336) (C h11 (T (T (T h324 h321) h331) h490))) (C h11 (T (T (T (T (T (T (T (T (T (T h493 h381) h333) h332) h325) h384) h376) h375) h361) h374) h373))) (C h11 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h368 h366) h362) h360) h357) h351) h326) h324) h321) h331) h490) h492) h488) h382) h380) h341) h379) h377))) h346) h482) h481) h404) h480) h391))) (C h32 h406)) (T (T (T (T (T (T h474 h387) h315) h385) h372) h439) h468)
  have h496 := h v484 z v2
  have h497 := C h68 (T (T h406 h496) h495)
  have h498 := C h68 h497
  have h499 := h v388 v2 z
  have h500 := S h496
  have h501 := C h170 (T (T (T h389 h447) h446) h483)
  have h502 := C h489 (T (T (T (T (T (T (T (T (T (T (C h94 h493) h329) h304) h268) h267) h59) h441) h440) h370) h369) h316)
  have h503 := C (T (T (T (T (T (T (T (T (T (T (T (T (C h32 h391) (C h442 (T (T (T (T (T (T (T (T (T h406 h471) h405) h403) h401) h345) (C h11 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h349 h347) h342) h340) h337) h487) h502) h493) h381) h333) h332) h325) h384) h376) h375) h361) h374) h373))) (C h11 (T (T (T (T (T (T (T (T (T (T h368 h366) h362) h360) h357) h351) h326) h324) h321) h331) h490))) (C h11 (T (T (T h493 h381) h333) h332))) (C h11 h343)))) (S h494)) h340) h337) h487) h502) h493) h381) h333) h332) h479) h466) (T (T (T (T (T (T h441 h440) h370) h369) h316) h386) h501)
  have h504 := C h68 (T (T h503 h500) h391)
  have h505 := T (T (T (T (T (T h437 h436) h409) h389) h447) h446) h483
  have h506 := C (T (T (T (T (T (T (T h448 h429) h445) h444) (C h68 h505)) (C h68 (T (T (T (T (T (T (T (T h473 h396) h395) h390) h499) h498) h486) h496) h495))) h504) h475) h68
  have h507 := T (T (T (T (T (T (T (T (T (T (T h506 h473) h396) h395) h390) h499) h498) h486) h471) h405) h403) h401
  have h508 := T (T (T (T (T (T h473 h396) h395) h390) h408) h450) h443
  have h509 := S h499
  have h510 := C h68 h504
  have h511 := C (T (T (T (T (T (T (T h472 h497) (C h68 (T (T (T (T (T (T (T (T h503 h500) h485) h510) h509) h389) h447) h446) h483))) (C h68 h508)) h434) h433) h430) h428) h68
  have h512 := C (T (T (T (T h477 (C h94 h505)) (C h94 (T h511 h449))) (C h94 h435)) (C h94 h507)) h94
  have h513 := T (T (T (T (T (T (T (T (T (T (T h482 h481) h404) h480) h485) h510) h509) h389) h447) h446) h483) h511
  have h514 := C (T (T (T (T (C h94 h513) (C h94 h449)) (C h94 (T h435 h506))) (C h94 h508)) h452) h94
  T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h28 h143) h136) h134) h65) h133) h132) h131) h82) h130) h129) h128) h189) h188) (C h241 (T (T (T (T (T (T (T (T h386 h501) (C h170 (T (T (T (T (T (T (T (T h473 h396) h395) h390) h408) h450) h443) h514) h478))) (C h170 h462)) (C h170 (T (T (T (T (T (T (T (T (T h512 h437) h436) h409) h389) h447) h446) h483) h511) h449))) (C h170 h435)) (C h170 h507)) (h v338 v13 v2)) (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h28 h143) h136) h134) h65) h133) h132) h131) h82) h130) h129) h128) h127) h249) h240) h239) h238) h237) (T (C h34 (T (T (T (T (T (T (C (T (C h68 h116) (C h68 (T (T (T (T (T (T (T (T (T (T h110 (C h170 h513)) (C h170 h449)) (C h170 (T (T (T (T (T (T (T (T (T h435 h506) h473) h396) h395) h390) h408) h450) h443) h514))) (C h170 h478)) (C h170 (T (T (T (T (T (T (T (T h462 h512) h437) h436) h409) h389) h447) h446) h483))) h474) h387) h315) h385) h372))) h68) h371) h233) h229) h225) h223) h222)) h217))))) h231) h221) h213) h207) h199) h27) h25) h21) h19) h16) h4

