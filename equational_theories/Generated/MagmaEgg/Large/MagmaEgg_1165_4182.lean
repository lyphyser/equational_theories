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
theorem Equation1165_implies_Equation4182 (G: Type _) [Magma G] (h: Equation1165 G) : Equation4182 G := fun x y z =>
  let v0 := M y z
  let v1 := M v0 z
  let v2 := M v1 x
  have h3 := h v2 x x
  let v4 := M x v2
  have h5 := R x
  have h6 := h v2 x v2
  have h7 := S h6
  let v8 := M (M v2 v4) v2
  have h9 := h v8 x x
  let v10 := M x y
  have h11 := h v8 x v10
  have h12 := R v10
  have h13 := C h5 (C (T (C h5 (T (C h5 (C (C h12 h6) h12)) (S h11))) h7) h5)
  have h14 := h (M (M v10 v2) v10) x x
  have h15 := C (C h12 h7) h12
  let v16 := M v1 v4
  let v17 := M z v0
  let v18 := M v1 v17
  have h19 := h v1 v18 z
  have h20 := S h19
  have h21 := R z
  have h22 := h v0 z v1
  have h23 := R v18
  have h24 := C h23 (C h22 h21)
  have h25 := h (M v18 v1) z x
  have h26 := S h25
  have h27 := h v0 z v2
  have h28 := S h27
  have h29 := C h21 (T (C (C h5 h28) h5) (C (C h5 h22) h5))
  let v30 := M (M v2 v17) v2
  have h31 := h v30 z x
  have h32 := h v30 z y
  have h33 := S h32
  have h34 := R y
  have h35 := h (M (M y v0) y) x x
  have h36 := h v0 x v2
  have h37 := S h36
  let v38 := M x v0
  let v39 := M (M v2 v38) v2
  have h40 := h v39 x y
  have h41 := h v39 x v0
  have h42 := S h41
  have h43 := R v0
  have h44 := C h5 (C (C h43 h36) h43)
  let v45 := M (M v0 v0) v0
  have h46 := h v45 x x
  have h47 := C h21 (T (T (T h46 (C h5 (C (C h5 (T (T (T h44 h42) h40) (C h5 (C (C h34 h37) h34)))) h5))) (S h35)) (C (C h34 h27) h34))
  have h48 := S h46
  have h49 := C h5 (C (C h43 h37) h43)
  have h50 := h v39 x x
  have h51 := h (M v38 x) x x
  have h52 := h v0 z x
  have h53 := C h21 (T (T (T (C (C h5 (S h52)) h5) h51) (C h5 (C (C h5 (T (T (T (C h5 (C (C h5 h36) h5)) (S h50)) h41) h49)) h5))) h48)
  let v54 := M (M x v17) x
  have h55 := h v54 z x
  have h56 := h v54 v10 v2
  have h57 := S h56
  have h58 := R v2
  have h59 := S h55
  have h60 := C h21 (T (T (T h46 (C h5 (C (C h5 (T (T (T h44 h42) h50) (C h5 (C (C h5 h37) h5)))) h5))) (S h51)) (C (C h5 h52) h5))
  have h61 := C h21 (T (T (T (C (C h34 h28) h34) h35) (C h5 (C (C h5 (T (T (T (C h5 (C (C h34 h36) h34)) (S h40)) h41) h49)) h5))) h48)
  have h62 := S h31
  have h63 := S h22
  have h64 := C h21 (T (C (C h5 h63) h5) (C (C h5 h27) h5))
  have h65 := C h23 (C h63 h21)
  have h66 := C h12 (T (T (T (T (T (T (T (T h19 h65) h25) h64) h62) h32) h61) h60) h59)
  have h67 := C (C h58 h66) h58
  let v68 := M v10 v1
  have h69 := h (M (M v2 v68) v2) v10 x
  have h70 := S h69
  have h71 := h v1 v10 v2
  let v72 := M x v1
  have h73 := h (M v72 x) x x
  have h74 := S h73
  have h75 := h v1 x v2
  have h76 := S h75
  let v77 := M (M v2 v72) v2
  have h78 := h v77 x x
  have h79 := h v77 x z
  have h80 := S h79
  let v81 := M z v1
  have h82 := h (M v81 z) z x
  have h83 := S h82
  have h84 := h v1 z v10
  have h85 := S h84
  let v86 := M (M v10 v81) v10
  have h87 := h v86 z z
  have h88 := h v86 z v2
  have h89 := S h88
  have h90 := C h21 (C (C h58 h84) h58)
  have h91 := C h21 (C (C h5 (T (T (T h90 h89) h87) (C h21 (C (C h21 h85) h21)))) h5)
  let v92 := M v2 v1
  let v93 := M v92 v2
  have h94 := h v93 z x
  have h95 := C h5 (T (T (T h94 h91) h83) (C (C h21 h75) h21))
  have h96 := C h5 (C (C h5 (T (T (T h95 h80) h78) (C h5 (C (C h5 h76) h5)))) h5)
  have h97 := h v93 x x
  have h98 := C h12 (T (T (T h97 h96) h74) (C (C h5 h71) h5))
  have h99 := h (M v10 v93) v10 y
  have h100 := S h99
  have h101 := S h97
  have h102 := S h94
  have h103 := C h21 (C (C h58 h85) h58)
  have h104 := C h21 (C (C h5 (T (T (T (C h21 (C (C h21 h84) h21)) (S h87)) h88) h103)) h5)
  have h105 := C h5 (T (T (T (C (C h21 h76) h21) h82) h104) h102)
  have h106 := C h5 (C (C h5 (T (T (T (C h5 (C (C h5 h75) h5)) (S h78)) h79) h105)) h5)
  have h107 := C h12 (T (T (T (C (C h5 (S h71)) h5) h73) h106) h101)
  have h108 := C h12 (T (T (T (T (T (T (T (T h55 h53) h47) h33) h31) h29) h26) h24) h20)
  have h109 := C (C h58 h108) h58
  have h110 := C h12 (T (T h109 h69) h107)
  have h111 := T (T (T (T (T (T (T (T (T (T h19 h65) h25) h64) h62) h32) h61) h60) h59) h56) h110
  have h112 := C h34 h111
  have h113 := C h112 h34
  let v114 := M y v1
  have h115 := h (M v114 y) x x
  have h116 := S h115
  have h117 := h v77 x y
  have h118 := C h5 (C (C h5 (T (T (T h95 h80) h117) (C h5 (C (C h34 h76) h34)))) h5)
  have h119 := C h12 (T (T h98 h70) h67)
  have h120 := T (T (T (T (T (T (T (T (T (T h119 h57) h55) h53) h47) h33) h31) h29) h26) h24) h20
  have h121 := C h58 h120
  have h122 := C h121 h58
  have h123 := C h58 h111
  have h124 := h v92 v2 x
  have h125 := S h124
  have h126 := R v1
  have h127 := h x v2 v1
  have h128 := S h127
  have h129 := C h58 (C (C h126 h128) h126)
  let v130 := M v2 x
  let v131 := M (M v1 v130) v1
  have h132 := h v131 v2 v1
  have h133 := T h132 h129
  have h134 := h v131 v2 x
  have h135 := S h134
  have h136 := h x y x
  have h137 := S h136
  have h138 := C h5 h137
  have h139 := C (T h138 (C h5 h127)) h5
  have h140 := C h5 h136
  have h141 := h x v2 v10
  have h142 := h (M (M v10 v130) v10) v2 x
  have h143 := h v130 x v1
  have h144 := h x v1 v10
  have h145 := h v72 x v10
  have h146 := C h58 (T (T (T h97 h96) h74) (C (T (T h145 (C h5 (T (T (T (C (C h12 (T (C h5 (C (T h144 (C h126 (T h14 h13))) h126)) (S h143))) h12) h142) (C h58 (T (C (T (C h5 (S h141)) h140) h5) h139))) h135))) (C h5 h133)) h5))
  have h147 := h v93 v10 v10
  have h148 := S h147
  have h149 := C h111 h12
  have h150 := C h58 (T (C h12 h149) h148)
  have h151 := C (T (T (T h150 h146) h125) h123) h58
  have h152 := C h12 (T (T (T (T (T h151 h122) h97) h118) h116) h113)
  have h153 := h (M v1 v10) v10 v2
  have h154 := C h120 h12
  have h155 := C h12 (T (T (T (T (T (T h154 h153) h152) h100) h98) h70) h67)
  have h156 := h v93 v1 v2
  have h157 := S h156
  have h158 := h v1 v1 v2
  have h159 := C h126 (T (T (T (C (C h21 (S h158)) h21) h82) h104) h102)
  let v160 := M v1 v1
  have h161 := h (M (M v2 v160) v2) v1 z
  have h162 := h v160 v1 v2
  have h163 := S h162
  have h164 := h (M v1 v160) v1 y
  have h165 := S h164
  have h166 := C h126 h120
  have h167 := h v86 z v0
  have h168 := C h21 (C (C h5 (T (T (T (C h21 (C (C h43 h84) h43)) (S h167)) h88) h103)) h5)
  have h169 := h (M (M v0 v1) v0) z x
  have h170 := C (C h43 h120) h43
  have h171 := h v77 x v10
  have h172 := C h5 (C (C h5 (T (T (T (C h5 (C (C h12 h75) h12)) (S h171)) h79) h105)) h5)
  have h173 := h (M v68 v10) x x
  have h174 := C (T (C h12 (T h119 h57)) h108) h12
  have h175 := C h12 (T (T (T (T h151 h122) h147) h155) h110)
  have h176 := C h58 (T h147 (C h12 h154))
  have h177 := C (T (C h5 h128) h140) h5
  have h178 := S h132
  have h179 := C h58 (C (C h126 h127) h126)
  have h180 := T h179 h178
  have h181 := C h58 (T (T (T (C (T (T (C h5 h180) (C h5 (T (T (T h134 (C h58 (T h177 (C (T h138 (C h5 h141)) h5)))) (S h142)) (C (C h12 (T h143 (C h5 (C (T (C h126 (T (C h5 (C (T h6 (C h5 (T h11 (C h5 h15)))) h5)) (S h14))) (S h144)) h126)))) h12)))) (S h145)) h5) h73) h106) h101)
  have h182 := C (T (T (T h121 h124) h181) h176) h58
  have h183 := C h123 h58
  have h184 := C h5 (C (C h5 (T (T (T (C h5 (C (C h34 h75) h34)) (S h117)) h79) h105)) h5)
  have h185 := C h34 h120
  have h186 := C h185 h34
  have h187 := C h12 (T (T (T (T (T h186 h115) h184) h101) h183) h182)
  have h188 := h v93 v0 v0
  have h189 := h z v0 v2
  have h190 := C h43 (T (T (T (T (T (T (T (C (T (T (T (C h12 (T (C h43 (C (C h43 h189) h43)) (S h188))) h99) h187) h175) h12) h174) h173) h172) h101) h147) h155) h110)
  let v191 := M v1 v0
  have h192 := h v191 v0 v10
  have h193 := h v191 y x
  have h194 := S h193
  have h195 := h z y v0
  have h196 := S h195
  have h197 := h v45 y v0
  have h198 := h v45 y y
  have h199 := C h34 (C (T (C h5 (T (C h34 (C (C h34 h195) h34)) (S h198))) (C h5 (T h197 (C h34 (C (C h43 h196) h43))))) h5)
  have h200 := h (M v0 y) y x
  have h201 := h y y y
  have h202 := S h201
  have h203 := h y y v2
  have h204 := S h203
  let v205 := M y y
  let v206 := M (M v2 v205) v2
  have h207 := h v206 y x
  have h208 := S h207
  have h209 := C h34 (C (C h5 h203) h5)
  let v210 := M v10 x
  have h211 := h v210 y y
  have h212 := h v210 x x
  have h213 := S h212
  have h214 := h y x v10
  have h215 := S h214
  have h216 := C h5 (C (C h5 h215) h5)
  let v217 := M v10 v10
  let v218 := M v217 v10
  have h219 := h v218 x x
  let v220 := M y x
  have h221 := h v220 v10 x
  have h222 := S h221
  have h223 := h v218 v10 v10
  have h224 := h v10 v10 v2
  have h225 := S h224
  let v226 := M (M v2 v217) v2
  have h227 := h v226 v10 v10
  have h228 := h v217 v10 x
  have h229 := h (M (M x v217) x) v10 x
  have h230 := h v10 v10 x
  have h231 := h v226 v10 x
  have h232 := C h12 (T (T (T h231 (C h12 (T (C (C h5 h225) h5) (C (C h5 h230) h5)))) (S h229)) (C (C h5 (T h228 (C h12 (C (T (C h5 (T (C h12 (C (T h224 (C h12 (T h227 (C h12 (C (C h12 h225) h12))))) h12)) (S h223))) h215) h5)))) h5))
  have h233 := C h5 (T (T (T h224 h232) h222) (C (T h214 (C h5 (T h219 h216))) h5))
  have h234 := h x v10 y
  have h235 := S h234
  have h236 := C h34 (C (C h5 h204) h5)
  have h237 := h v206 y v0
  have h238 := S h237
  have h239 := h y z z
  have h240 := C h43 (S h239)
  have h241 := C h43 h239
  have h242 := S h200
  have h243 := C h34 (C (T (C h5 (T (C h34 (C (C h43 h195) h43)) (S h197))) (C h5 (T h198 (C h34 (C (C h34 h196) h34))))) h5)
  have h244 := S h192
  have h245 := C h12 (T (T (T (T (T (T h109 h69) h107) h99) h187) (S h153)) h149)
  have h246 := C h12 (T (T (T (T h119 h245) h148) h183) h182)
  have h247 := C (T h66 (C h12 (T h56 h110))) h12
  have h248 := S h173
  have h249 := C h5 (C (C h5 (T (T (T h95 h80) h171) (C h5 (C (C h12 h76) h12)))) h5)
  have h250 := C h43 (T (T (T (T (T (T (T h119 h245) h148) h97) h249) h248) h247) (C (T (T (T h246 h152) h100) (C h12 (T h188 (C h43 (C (C h43 (S h189)) h43))))) h12))
  have h251 := C (C h43 h111) h43
  have h252 := S h169
  have h253 := C h21 (C (C h5 (T (T (T h90 h89) h167) (C h21 (C (C h43 h85) h43)))) h5)
  have h254 := C h34 (T (T (T (T (T (T (T (T h119 h245) h148) h94) h253) h252) h251) (C (T (T (T (T (T h250 h244) h193) h243) h242) h241) h43)) (C (T h240 (C h43 h203)) h43))
  have h255 := C h12 (T (T (T (T (T (T h151 h122) h97) h118) h116) h113) (C (T (T (T h254 h238) h207) h236) h34))
  have h256 := C (T (T h246 h255) h235) h12
  have h257 := T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h19 h65) h25) h64) h62) h32) h61) h60) h59) h56) h245) h148) h97) h249) h248) h247) h256) h233) h213) h211) (C h34 (C (T (C h34 (T h209 h208)) h204) h34))
  have h258 := C h257 h34
  have h259 := C h34 h258
  let v260 := M v1 y
  have h261 := h (M y v260) v2 v2
  have h262 := S h261
  have h263 := C h34 (T (T (T (T (T (T (T (T (C (T (C h43 h204) h241) h43) (C (T (T (T (T (T h240 h200) h199) h194) h192) h190) h43)) h170) h169) h168) h102) h147) h155) h110)
  have h264 := C h12 (T (T (T (T (T (T (C (T (T (T h209 h208) h237) h263) h34) h186) h115) h184) h101) h183) h182)
  have h265 := C (T (T h234 h264) h175) h12
  have h266 := C h12 (T (T (T (C (C h5 (T (C h12 (C (T h214 (C h5 (T h223 (C h12 (C (T (C h12 (T (C h12 (C (C h12 h224) h12)) (S h227))) h225) h12))))) h5)) (S h228))) h5) h229) (C h12 (T (C (C h5 (S h230)) h5) (C (C h5 h224) h5)))) (S h231))
  have h267 := S h219
  have h268 := C h5 (C (C h5 h214) h5)
  have h269 := C h5 (T (T (T (C (T (C h5 (T h268 h267)) h215) h5) h221) h266) h225)
  have h270 := T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (C h34 (C (T h203 (C h34 (T h207 h236))) h34)) (S h211)) h212) h269) h265) h174) h173) h172) h101) h147) h155) h57) h55) h53) h47) h33) h31) h29) h26) h24) h20
  have h271 := C h270 h34
  have h272 := C h34 h271
  have h273 := C h58 (T h201 h272)
  have h274 := C (C h58 h273) h58
  let v275 := M v2 y
  have h276 := h (M (M v2 v275) v2) v2 x
  have h277 := S h276
  have h278 := h y v2 v2
  have h279 := C h58 (C (C h5 h278) h5)
  have h280 := C h58 (T (T h279 h277) h274)
  have h281 := T (T (T h280 h262) h259) h202
  have h282 := C (T (T (T (T (T (C h43 h281) h200) h199) h194) h192) h190) h43
  have h283 := C h58 (C (C h5 (S h278)) h5)
  have h284 := C h58 (T h259 h202)
  have h285 := C (C h58 h284) h58
  have h286 := C h58 (T (T h285 h276) h283)
  have h287 := h (M v2 v210) v2 v0
  have h288 := S h287
  have h289 := T (T (T h201 h272) h261) h286
  have h290 := C (T (T (T (T (T h250 h244) h193) h243) h242) (C h43 h289)) h43
  have h291 := C h58 (T (T (T (T (T (T (T h119 h245) h148) h94) h253) h252) h251) h290)
  have h292 := C h58 (T (T (T (T (T h123 h291) h288) h279) h277) h274)
  have h293 := h x v2 x
  have h294 := C h58 (T (C (T (C h5 (S h293)) h140) h5) h139)
  let v295 := M (M x v130) x
  have h296 := h v295 v2 x
  have h297 := h v295 v1 v2
  have h298 := S h297
  have h299 := S h296
  have h300 := C h58 (T h177 (C (T h138 (C h5 h293)) h5))
  have h301 := C h58 (T (T (T (T (T (T (T h282 h170) h169) h168) h102) h147) h155) h110)
  have h302 := C h58 (T (T (T (T (T h285 h276) h283) h287) h301) h121)
  have h303 := C h126 (T (T (T (T (T (T h280 h302) h179) h178) h134) h300) h299)
  have h304 := C h270 h289
  have h305 := C (C h58 (T (T h258 h304) h303)) h58
  have h306 := h (M (M v2 v260) v2) v1 x
  have h307 := S h306
  have h308 := h y v1 v2
  have h309 := C h126 (C (C h5 h308) h5)
  have h310 := C h126 (T (T h309 h307) h305)
  have h311 := T (T (T (T (T (T (T (T h310 h298) h296) h294) h135) h132) h129) h292) h286
  have h312 := C (C h43 h311) h43
  have h313 := C h126 (T (T (T (T (T (T (T (T h312 h282) h170) h169) h168) h102) h147) h155) h110)
  let v314 := M v1 v210
  have h315 := h v314 v1 v0
  have h316 := C h126 (C (C h5 (S h308)) h5)
  have h317 := C h257 h281
  have h318 := C h126 (T (T (T (T (T (T h296 h294) h135) h132) h129) h292) h286)
  have h319 := C (C h58 (T (T h318 h317) h271)) h58
  have h320 := C h126 (T (T (T (T (T h319 h306) h316) h315) h313) h166)
  have h321 := T h310 h320
  have h322 := C h126 (T (T h319 h306) h316)
  have h323 := C (T h201 (C h34 (T (T (T h304 h303) (C h126 (T h297 h322))) (C h126 h321)))) h34
  have h324 := C h126 h323
  have h325 := C h58 (T h324 h165)
  have h326 := C h126 (C h325 h58)
  have h327 := h v205 v1 v2
  have h328 := C (C h58 (T (T h327 h326) h163)) h58
  have h329 := C (C h58 (T (T (T (T (T h112 h254) h238) h328) h161) h159)) h58
  have h330 := h (M (M v2 v114) v2) y x
  have h331 := S h330
  have h332 := h v1 y v2
  have h333 := C h34 (T (T (T h97 h96) h74) (C (C h5 h332) h5))
  have h334 := h (M y v93) v1 v2
  have h335 := C h34 (T (T (T (C (C h5 (S h332)) h5) h73) h106) h101)
  have h336 := S h327
  have h337 := S h315
  have h338 := T (T (T (T (T (T (T (T h280 h302) h179) h178) h134) h300) h299) h297) h322
  have h339 := C (C h43 h338) h43
  have h340 := C h126 (T (T (T (T (T (T (T (T h119 h245) h148) h94) h253) h252) h251) h290) h339)
  have h341 := C h126 h111
  have h342 := C h126 (T (T (T (T (T h341 h340) h337) h309) h307) h305)
  have h343 := T h342 h322
  have h344 := C (T (C h34 (T (T (T (C h126 h343) (C h126 (T h310 h298))) h318) h317)) h202) h34
  have h345 := C h126 h344
  have h346 := C h58 (T h164 h345)
  have h347 := C h126 (C h346 h58)
  have h348 := C (C h58 (T (T h162 h347) h336)) h58
  have h349 := S h161
  have h350 := C h126 (T (T (T h94 h91) h83) (C (C h21 h158) h21))
  have h351 := C (C h58 (T (T (T (T (T h350 h349) h348) h237) h263) h185)) h58
  have h352 := C h126 (T (T h351 h330) h335)
  have h353 := C h58 (T (T (T (T (T (T h282 h170) h169) h168) h102) h156) h352)
  have h354 := C (T (T (T (T (T h150 h146) h125) h123) h291) h353) h58
  have h355 := C h126 (T (T (T (T (T (T (T (T h312 h282) h170) h169) h168) h102) h183) h182) h354)
  have h356 := C h126 (T (T (T (T (T (T (T (T (T (T h344 h327) h326) h163) h341) h340) h355) (S h334)) h333) h331) h329)
  have h357 := T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h201 h272) h261) h302) h179) h178) h134) h300) h299) h297) h320) h164) h356) h157) h147) h155) h57) h55) h53) h47) h33) h31) h29) h26) h24) h20
  have h358 := h v16 y v10
  have h359 := h x v10 x
  have h360 := S h359
  have h361 := h v218 x y
  have h362 := h y v10 x
  have h363 := C h34 (S h362)
  have h364 := C h126 (T (T h333 h331) h329)
  have h365 := C h58 (T (T (T (T (T (T h364 h157) h94) h253) h252) h251) h290)
  have h366 := C (T (T (T (T (T h365 h301) h121) h124) h181) h176) h58
  have h367 := C h126 (T (T (T (T (T (T (T (T h366 h151) h122) h94) h253) h252) h251) h290) h339)
  have h368 := C h126 (T (T (T (T (T (T (T (T (T (T h351 h330) h335) h334) h367) h313) h166) h162) h347) h336) h323)
  have h369 := T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h19 h65) h25) h64) h62) h32) h61) h60) h59) h56) h245) h148) h156) h368) h165) h342) h298) h296) h294) h135) h132) h129) h292) h262) h259) h202
  have h370 := C h34 h362
  have h371 := h v314 y v2
  have h372 := S h371
  have h373 := h (M v1 v205) v2 x
  have h374 := S h373
  have h375 := C h58 h321
  have h376 := C h58 h338
  have h377 := C h58 (T h261 h286)
  have h378 := h (M (M x v275) x) v2 x
  have h379 := h y v2 x
  have h380 := C h58 (T (T h324 h356) h352)
  have h381 := C h58 (T (T (T (T (T (T h380 h365) h288) (C h58 (C (C h5 h379) h5))) (S h378)) (C (C h5 (T (T (T h273 h377) h376) h375)) h5)) (C (C h5 h346) h5))
  have h382 := C h58 (T (T h364 h368) h345)
  have h383 := C h58 (T h280 h262)
  have h384 := C h58 h311
  have h385 := C h58 h343
  have h386 := C (C h58 (T (T h385 h384) h383)) h58
  have h387 := C (C h58 h325) h58
  have h388 := C h58 (T (T (T (T (T (T (C (C h5 h325) h5) (C (C h5 (T (T (T h385 h384) h383) h284)) h5)) h378) (C h58 (C (C h5 (S h379)) h5))) h287) h353) h382)
  have h389 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T h201 h272) h261) h302) h179) h178) h134) h300) h299) h297) h320) h164) h345) h373) h388) h58
  have h390 := C h58 (T (T (T (T (T (T (T (T h389 h387) h386) h285) h276) h283) h287) h353) h382)
  have h391 := C h126 (T (T (T (T (T (T (T (T h390 h381) h374) h324) h356) h157) h183) h182) h354)
  have h392 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T h381 h374) h324) h165) h342) h298) h296) h294) h135) h132) h129) h292) h262) h259) h202) h58
  have h393 := C (C h58 h346) h58
  have h394 := C (C h58 (T (T h377 h376) h375)) h58
  have h395 := C h58 (T (T (T (T (T (T (T (T h380 h365) h288) h279) h277) h274) h394) h393) h392)
  let v396 := M y v2
  have h397 := h (M v2 v396) v1 v2
  have h398 := C h126 (T (T (T (T (T (T (T (T h366 h151) h122) h156) h368) h345) h373) h388) h395)
  have h399 := C (C h58 (T (T (T (T (T (T h327 h326) h163) h341) h340) h355) h398)) h58
  have h400 := C h369 (T (T (T (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (C h357 (T (T (T h350 h349) h348) h399)) (S h397)) h390) h381) h374) h324) h356) h157) h147) h155) h57) h55) h53) h47) h33) h31) h29) h26) h24) h20) (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h201 h272) h261) h302) h179) h178) h134) h300) h299) h297) h320) h164) h345) h373) h388) h395)) h391) h367) h337)
  have h401 := h v93 v1 y
  have h402 := C h58 (T (T (T (T (T h390 h381) h374) h324) h356) h352)
  have h403 := C h402 h58
  have h404 := C h58 (T (T (T (T (T h403 h366) h151) h122) h401) h400)
  have h405 := h v396 v2 v2
  have h406 := C (T (T (T (T (T (T (T (T (T (T h402 h365) h288) h279) h277) h274) h394) h393) h392) h405) h404) h58
  have h407 := C h58 (T (T (T (T (T h364 h368) h345) h373) h388) h395)
  have h408 := C h407 h58
  have h409 := S h401
  have h410 := C (C h58 (T (T (T (T (T (T h391 h367) h313) h166) h162) h347) h336)) h58
  have h411 := C h357 (T (T (T h315 h355) h398) (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h19 h65) h25) h64) h62) h32) h61) h60) h59) h56) h245) h148) h156) h368) h345) h373) h388) h395) h397) (C h369 (T (T (T h410 h328) h161) h159))) (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h390 h381) h374) h324) h165) h342) h298) h296) h294) h135) h132) h129) h292) h262) h259) h202)))
  have h412 := C h369 (T (T (T (T (T (T h411 h409) h183) h182) h354) h408) h406)
  have h413 := C (T (T (T (T (T (T (T (T h412 h372) h315) h313) h166) h162) h347) h336) h370) h369
  have h414 := S h405
  have h415 := C h58 (T (T (T (T (T h411 h409) h183) h182) h354) h408)
  have h416 := C (T (T (T (T (T (T (T (T (T (T h415 h414) h389) h387) h386) h285) h276) h283) h287) h353) h407) h58
  have h417 := C h357 (T (T (T (T (T (T h416 h403) h366) h151) h122) h401) h400)
  have h418 := h v314 y v1
  have h419 := S h418
  have h420 := C (T (T (T (T (T (T (T (T h363 h327) h326) h163) h341) h340) h337) h371) h417) h357
  have h421 := C (T (C h34 h204) h370) h34
  have h422 := C h34 (T h421 h420)
  have h423 := h v206 y y
  have h424 := C (T (T (T (T (T (T h254 h238) h423) h422) h419) h371) h417) h357
  have h425 := C h5 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h201 h272) h261) h302) h179) h178) h134) h300) h299) h297) h320) h164) h356) h157) h97) h118) h116) h113) h424) h413) (C (T h363 (C h34 h214)) h34))
  have h426 := C (T (T (T h425 (S h361)) h219) h216) h5
  have h427 := h (M v10 y) y x
  have h428 := h v10 y v10
  have h429 := S h428
  have h430 := h (M (M v10 (M y v10)) v10) y v10
  have h431 := h v218 y y
  have h432 := h (M (M x v220) x) y v1
  have h433 := h v92 y y
  have h434 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h415 h414) h389) h387) h386) h285) h276) h283) h287) h301) h121) h433) (C h34 (C (T (C h34 (T (C h34 (C (C h126 h136) h126)) (S h432))) h137) h34))) (C h34 (T (T (T h224 h232) h222) (C (T h214 (C h5 (T h431 (C h34 (C (T (C h34 (T (C h34 (C (C h12 h428) h12)) (S h430))) h429) h34))))) h5)))) (S h427)) (C h12 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h201 h272) h261) h302) h179) h178) h134) h300) h299) h297) h320) h164) h356) h157) h97) h249) h248) h247) h256) h233) h213) h426))) h360) h58
  have h435 := S h423
  have h436 := C (T h363 (C h34 h203)) h34
  have h437 := C h34 (T h413 h436)
  have h438 := C (T (T (T (T (T (T h412 h372) h418) h437) h435) h237) h263) h369
  have h439 := C (T (C h34 h215) h370) h34
  have h440 := C (T (T (T h268 h267) h361) (C h5 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h439 h420) h438) h186) h115) h184) h101) h156) h368) h165) h342) h298) h296) h294) h135) h132) h129) h292) h262) h259) h202))) h5
  have h441 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h359 (C h12 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h440 h212) h269) h265) h174) h173) h172) h101) h156) h368) h165) h342) h298) h296) h294) h135) h132) h129) h292) h262) h259) h202))) h427) (C h34 (T (T (T (C (T (C h5 (T (C h34 (C (T h428 (C h34 (T h430 (C h34 (C (C h12 h429) h12))))) h34)) (S h431))) h215) h5) h221) h266) h225))) (C h34 (C (T h136 (C h34 (T h432 (C h34 (C (C h126 h137) h126))))) h34))) (S h433)) h123) h291) h288) h279) h277) h274) h394) h393) h392) h405) h404) h58
  have h442 := h v4 v1 v2
  have h443 := S h442
  have h444 := C h357 (T (T (T (T (T (T (T (T (T (T (T (T h421 h420) h438) h186) h115) h184) h101) h183) h182) h354) h408) h406) h434)
  have h445 := C h369 (T (T (T (T (T (T (T (T (T (T (T (T h441 h416) h403) h366) h151) h122) h97) h118) h116) h113) h424) h413) h436)
  have h446 := C h126 (T (T (T h445 h435) h399) (C (C h58 (T (T (T (T (T h391 h367) h337) h418) h437) h444)) h58))
  have h447 := C h369 (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h446 h443) h441) h416) h403) h366) h151) h122) h147) h155) h57) h55) h53) h47) h33) h31) h29) h26) h24) h20) (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h19 h65) h25) h64) h62) h32) h61) h60) h59) h56) h245) h148) h183) h182) h354) h408) h406) h434))
  have h448 := h v4 v1 v1
  have h449 := T (T (T h446 h443) h448) h447
  have h450 := C h126 (T (T (T (C (C h58 (T (T (T (T (T h445 h422) h419) h315) h355) h398)) h58) h410) h423) h444)
  have h451 := C (T (T (T (T h246 h255) h235) h359) (C h12 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h440 h212) h269) h265) h174) h173) h172) h101) h183) h182) h354) h408) h406) h434) h442) h450))) h12
  have h452 := S h448
  have h453 := C h357 (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h19 h65) h25) h64) h62) h32) h61) h60) h59) h56) h245) h148) h183) h182) h354) h408) h406) h434) h442) h450) (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h441 h416) h403) h366) h151) h122) h147) h155) h57) h55) h53) h47) h33) h31) h29) h26) h24) h20))
  have h454 := C (T (T (T (T (C h12 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h446 h443) h441) h416) h403) h366) h151) h122) h97) h249) h248) h247) h256) h233) h213) h426)) h360) h234) h264) h175) h12
  have h455 := T (T (T h453 h452) h442) h450
  have h456 := h v16 y v2
  have h457 := h v92 v2 v2
  have h458 := C (T (T (T (T (T (T (T (T (T (T (T (T (T h415 h414) h389) h387) h386) h285) h276) h283) h287) h301) h121) h457) (C h58 (C (T (C h58 h180) h128) h58))) (C h58 (T h442 h450))) h58
  have h459 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (C h58 (T h446 h443)) (C h58 (C (T h127 (C h58 h133)) h58))) (S h457)) h123) h291) h288) h279) h277) h274) h394) h393) h392) h405) h404) h58
  have h460 := h v16 v1 v10
  have h461 := h v16 v1 v2
  T (T (T (T h425 (C h5 (T (T (T (T (T (T (T (T (T (T (T (T (T (T h439 h420) h438) h186) h115) h184) h101) h183) h182) h354) h408) h406) h434) h442) h450))) (C h5 h449)) (C h5 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h453 h452) h441) h416) h403) h366) h151) h122) h97) h118) h116) h113) (C (T (T (T (T (T h254 h238) h423) h444) h461) (C h126 (T (T (T h459 h434) h442) h450))) h357)) (C (T (T (T (C h126 (T (T (T h446 h443) h441) h458)) (S h461)) h460) (C h369 (T (T (T (T (T (T (T (T (T (T (T (T h454 h174) h173) h172) h101) h183) h182) h354) h408) h406) h434) h442) h450))) h369)) (C (T (T (T (C h357 (T (T (T (T (T (T (T (T (T (T (T (T h446 h443) h441) h416) h403) h366) h151) h122) h97) h249) h248) h247) h451)) (S h460)) h456) (C h357 (T (T (T (T (C (C h58 h455) h58) h459) h434) h448) h447))) h357)) (C (T (T (T (C h369 (T (T (T (T h453 h452) h441) h458) (C (C h58 h449) h58))) (S h456)) h358) (C h34 (T (T (T (T (T (T (T (T (T (T (T (T (T (C (C h12 h455) h12) h454) h174) h173) h172) h101) h183) h182) h354) h408) h406) h434) h448) h447))) h369)) (C (T (C h34 (T (T (T (T (T (T (T (T (T (T (T (T (T h453 h452) h441) h416) h403) h366) h151) h122) h97) h249) h248) h247) h451) (C (C h12 h449) h12))) (S h358)) h357)) (h (M v16 v1) x x)) (C h5 (T (C (C h5 (S (h v2 x v1))) h5) (C (C h5 h6) h5)))) (S h9)) h11) (C h5 (T (T (T (T (T h15 h14) h13) (C h5 (C (T h6 (C h5 (T h9 (C h5 (C (C h5 h7) h5))))) h5))) (S (h (M v4 x) x x))) (C (C h5 h3) h5)))) (S (h (M (M x v4) x) x x))))) (S h3)

