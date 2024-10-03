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
theorem Equation759_implies_Equation3131 (G: Type _) [Magma G] (h: Equation759 G) : Equation3131 G := fun x y z =>
  let v0 := M y x
  let v1 := M v0 z
  let v2 := M v1 z
  have h3 := h y v2 x
  have h4 := S h3
  have h5 := R x
  let v6 := M v2 y
  have h7 := h v6 v2 v6
  have h8 := R v2
  have h9 := C h8 (C h5 (C (S h7) h5))
  let v10 := M v2 v6
  let v11 := M v10 v6
  have h12 := h (M v6 v11) v2 x
  have h13 := R v6
  have h14 := h v10 v6 x
  have h15 := S h14
  have h16 := h (M v6 v10) x x
  have h17 := h v2 x v1
  have h18 := S h17
  let v19 := M v1 (M (M x v2) v1)
  have h20 := h v19 x v6
  have h21 := h v19 x v2
  have h22 := S h21
  have h23 := C h5 (C h8 (C h17 h8))
  let v24 := M v2 v2
  let v25 := M v2 v24
  have h26 := h v25 x x
  have h27 := h v25 v1 v1
  have h28 := S h27
  have h29 := R v1
  have h30 := h z v1 v2
  have h31 := h z v2 v2
  have h32 := C (S h31) h29
  have h33 := C h31 h29
  have h34 := R z
  have h35 := h v0 v1 z
  have h36 := S h35
  have h37 := C h29 (T (C h34 (C h36 h34)) h33)
  let v38 := M v1 v0
  let v39 := M z (M v38 z)
  have h40 := h v39 v1 z
  have h41 := C h29 (T (T h40 h37) (C h29 (T h32 (C h30 h29))))
  have h42 := h (M x (M v0 x)) x x
  have h43 := S h42
  have h44 := h v0 x x
  have h45 := S h44
  let v46 := M x v0
  let v47 := M x (M v46 x)
  have h48 := h v47 x x
  have h49 := h v47 x v0
  have h50 := S h49
  have h51 := R v0
  have h52 := C h5 (C h51 (C h44 h51))
  have h53 := C h5 (C h5 (C (T (T (T h52 h50) h48) (C h5 (C h5 (C h45 h5)))) h5))
  let v54 := M v0 v0
  let v55 := M v0 v54
  have h56 := h v55 x x
  have h57 := h v0 v6 v6
  have h58 := C h51 (C (S h57) h51)
  have h59 := C h13 (T (T (T (T h58 h56) h53) h43) (C h5 (C (T (T (T (T (T h35 h41) h28) h26) (C h5 (C h5 (C (T (T (T h23 h22) h20) (C h5 (C h13 (C h18 h13)))) h5)))) (S h16)) h5)))
  have h60 := C h51 (C h57 h51)
  have h61 := h v55 v6 x
  have h62 := S h61
  let v63 := M v6 v0
  let v64 := M v63 v6
  have h65 := h (M v6 v64) v6 v0
  have h66 := C h13 (C h5 (C (T h65 (C h13 h58)) h5))
  have h67 := h v64 v6 x
  have h68 := S h40
  have h69 := C h29 (T h32 (C h34 (C h35 h34)))
  have h70 := C h29 (T (T (C h29 (T (C (S h30) h29) h33)) h69) h68)
  have h71 := S h26
  have h72 := C h5 (C h8 (C h18 h8))
  have h73 := h v19 x y
  have h74 := R y
  have h75 := C h5 (C h5 (C (T (T (T (C h5 (C h74 (C h17 h74))) (S h73)) h21) h72) h5))
  let v76 := M y v6
  have h77 := h v76 x x
  let v78 := M v6 x
  have h79 := h (M x v78) x x
  have h80 := S h79
  have h81 := h v6 x v6
  have h82 := S h81
  have h83 := C h5 (C h82 h5)
  let v84 := M x v6
  let v85 := M v6 (M v84 v6)
  have h86 := h v85 x x
  have h87 := h v85 x v0
  have h88 := h (M v0 v63) y x
  have h89 := S h88
  have h90 := h v6 y x
  have h91 := S h90
  let v92 := M x (M v76 x)
  have h93 := h v92 y v0
  have h94 := h v92 y z
  have h95 := C h74 (C h5 (C (T (T (T (C h74 (C h34 (C h90 h34))) (S h94)) h93) (C h74 (C h51 (C h91 h51)))) h5))
  let v96 := M z (M v6 z)
  have h97 := h v96 y x
  have h98 := C h5 (C h5 (C (T (T (T (C h5 (T (T (T h97 h95) h89) (C h51 (C h81 h51)))) (S h87)) h86) (C h5 h83)) h5))
  have h99 := h v96 x x
  have h100 := h v96 v1 v6
  have h101 := S h100
  have h102 := S h97
  have h103 := C h74 (C h5 (C (T (T (T (C h74 (C h51 (C h90 h51))) (S h93)) h94) (C h74 (C h34 (C h91 h34)))) h5))
  have h104 := h v6 v1 v6
  have h105 := S h104
  have h106 := C h29 (T (T (T (C h51 (C h105 h51)) h88) h103) h102)
  let v107 := M v6 (M (M v1 v6) v6)
  have h108 := h v107 v1 v0
  have h109 := h v107 v1 x
  have h110 := S h109
  have h111 := h v63 x x
  have h112 := S h111
  have h113 := h v0 v2 v6
  have h114 := S h113
  let v115 := M v2 v0
  let v116 := M v6 (M v115 v6)
  have h117 := h v116 v2 x
  have h118 := S h117
  have h119 := C h5 (C h113 h5)
  have h120 := C h8 (T (C h5 (C (T (T h27 h70) h36) h5)) h119)
  have h121 := h v24 v2 x
  have h122 := h v2 v6 v6
  have h123 := S h122
  have h124 := C h13 (T (C h8 (T (T (T (C h123 h8) h121) h120) h118)) h114)
  let v125 := M v6 (M (M v6 v2) v6)
  have h126 := h v125 v6 v2
  have h127 := h v125 v6 y
  have h128 := S h127
  have h129 := h y v1 y
  have h130 := S h129
  have h131 := C h130 h13
  have h132 := C h13 (T h131 (C h74 (C h122 h74)))
  have h133 := C h129 h13
  have h134 := h v6 v2 x
  let v135 := M v10 x
  have h136 := h (M x v135) v2 x
  have h137 := T (T h136 (C h8 (C h5 (C (S h134) h5)))) h4
  have h138 := C h5 (T (T (T (T (C h13 (T (C h137 h13) h133)) h132) h128) h126) h124)
  have h139 := h v135 x v6
  have h140 := h v135 x x
  have h141 := S h140
  have h142 := T (T h3 (C h8 (C h5 (C h134 h5)))) (S h136)
  have h143 := C h5 (C h142 h5)
  have h144 := C h5 (C h5 (C (T (T (T (C h5 h143) h141) h139) h138) h5))
  have h145 := h v46 x x
  have h146 := h x y v0
  have h147 := S h146
  have h148 := S h56
  have h149 := C h5 (C h51 (C h45 h51))
  have h150 := C h5 (C h5 (C (T (T (T (C h5 (C h5 (C h44 h5))) (S h48)) h49) h149) h5))
  have h151 := h v0 y v1
  have h152 := C h74 (T (T (T (C h5 (C (S h151) h5)) h42) h150) h148)
  let v153 := M y v0
  let v154 := M v153 v1
  have h155 := h (M v1 v154) y x
  have h156 := T (T h155 h152) h147
  have h157 := C h51 (T (T (T (C h156 h51) h145) h144) h112)
  have h158 := C h29 (T (T (T (T (T (T (T h157 h88) h103) h102) h99) h98) h80) (C h5 (C h104 h5)))
  have h159 := h v154 v1 v0
  have h160 := h v154 v1 v6
  have h161 := S h160
  have h162 := S h155
  have h163 := C h74 (T (T (T h56 h53) h43) (C h5 (C h151 h5)))
  have h164 := T (T h146 h163) h162
  have h165 := h x v6 y
  have h166 := S h165
  have h167 := C h166 h13
  have h168 := C h165 h13
  have h169 := h x v1 v6
  have h170 := S h169
  have h171 := C h29 (T (C h13 (T (C h170 h13) h168)) (C h13 (T h167 (C h164 h13))))
  let v172 := M v1 x
  let v173 := M v6 (M v172 v6)
  have h174 := h v173 v1 v6
  have h175 := h v173 v1 x
  have h176 := S h175
  have h177 := C h166 h5
  have h178 := C h5 (T h177 (C h169 h5))
  have h179 := C h165 h5
  have h180 := h x v1 x
  have h181 := C h29 (T (C h5 (T (C (S h180) h5) h179)) h178)
  have h182 := h (M x (M v172 x)) v1 x
  have h183 := S h182
  have h184 := C h29 (T (C h5 (T (C h170 h5) h179)) (C h5 (T h177 (C h180 h5))))
  have h185 := h v173 v1 v0
  have h186 := C h166 h51
  have h187 := C h29 (T (C h13 (C (T (T (T (T (C h29 (C h51 (T h186 (C h169 h51)))) (S h185)) h175) h184) h183) h13)) (C h13 (C (T (T (T (T (T (T (T (T (T (T h182 h181) h176) h174) h171) h161) h159) h158) h110) h108) h106) h13)))
  let v188 := M v0 (M (M v6 (M y (M v78 y))) v0)
  have h189 := h v188 v1 v6
  have h190 := h v188 v2 x
  have h191 := S h190
  have h192 := C h165 h51
  have h193 := h x v2 v6
  have h194 := S h193
  let v195 := M v2 x
  let v196 := M v6 (M v195 v6)
  have h197 := h v196 v2 v0
  have h198 := h v196 v2 x
  have h199 := S h198
  have h200 := C h5 (T h177 (C h193 h5))
  have h201 := h x v2 v2
  have h202 := C h8 (T (C h5 (T (C (S h201) h5) h179)) h200)
  let v203 := M v195 v2
  have h204 := h (M v2 v203) v2 x
  have h205 := C h8 (C h5 (C (T (T (T (T h204 h202) h199) h197) (C h8 (C h51 (T (C h194 h51) h192)))) h5))
  have h206 := h v203 v2 x
  have h207 := C h8 (T (T (T (T (T (T (T (T h206 h205) h191) h189) h187) h101) h99) h98) h80)
  have h208 := S h204
  have h209 := C h5 (T (C h194 h5) h179)
  have h210 := C h8 (T h209 (C h5 (T h177 (C h201 h5))))
  have h211 := h x v2 x
  have h212 := C h8 (T (C h5 (T (C (S h211) h5) h179)) h200)
  let v213 := M x (M v195 x)
  have h214 := h v213 v2 x
  have h215 := h v213 z v6
  have h216 := S h215
  have h217 := S h214
  have h218 := C h8 (T h209 (C h5 (T h177 (C h211 h5))))
  have h219 := S h206
  have h220 := C h8 (C h5 (C (T (T (T (T (C h8 (C h51 (T h186 (C h193 h51)))) (S h197)) h198) h210) h208) h5))
  have h221 := S h189
  have h222 := S h159
  have h223 := S h145
  have h224 := C h5 (C h137 h5)
  have h225 := S h139
  have h226 := C h13 (T (C h74 (C h123 h74)) h133)
  have h227 := S h126
  have h228 := S h121
  have h229 := C h5 (C h114 h5)
  have h230 := C h8 (T h229 (C h5 (C (T (T h35 h41) h28) h5)))
  have h231 := C h13 (T h113 (C h8 (T (T (T h117 h230) h228) (C h122 h8))))
  have h232 := C h5 (T (T (T (T h231 h227) h127) h226) (C h13 (T h131 (C h142 h13))))
  have h233 := C h5 (C h5 (C (T (T (T h232 h225) h140) (C h5 h224)) h5))
  have h234 := C h51 (T (T (T h111 h233) h223) (C h164 h51))
  have h235 := S h99
  have h236 := C h5 (C h81 h5)
  have h237 := C h5 (C h5 (C (T (T (T (C h5 h236) (S h86)) h87) (C h5 (T (T (T (C h51 (C h82 h51)) h88) h103) h102))) h5))
  have h238 := C h29 (T (T (T (T (T (T (T (C h5 (C h105 h5)) h79) h237) h235) h97) h95) h89) h234)
  have h239 := S h108
  have h240 := C h29 (T (T (T h97 h95) h89) (C h51 (C h104 h51)))
  have h241 := C h29 (T (C h13 (C (T (T (T (T (T (T (T (T (T (T h240 h239) h109) h238) h222) h160) (C h29 (T (C h13 (T (C h156 h13) h168)) (C h13 (T h167 (C h169 h13)))))) (S h174)) h175) h184) h183) h13)) (C h13 (C (T (T (T (T h182 h181) h176) h185) (C h29 (C h51 (T (C h170 h51) h192)))) h13)))
  have h242 := C h8 (T (T (T (T (T (T (T (T h79 h237) h235) h100) h241) h221) h190) h220) h219)
  have h243 := T (T (T (T (T h3 h242) h204) h202) h218) h217
  have h244 := h (M v6 (M (M z y) v6)) z v6
  have h245 := h y z v6
  have h246 := C h34 (T (T (C h34 (T (T (T (T h231 h227) h127) h226) (C h13 (T h131 (C h245 h13))))) (S h244)) (C h13 (C (C h34 h243) h13)))
  have h247 := T (T (T (T (T (T (T h246 h216) h214) h212) h210) h208) h207) h4
  have h248 := C h247 h13
  have h249 := C h13 (T (T (T (T (T (T h248 h77) h75) h71) h27) h70) h36)
  have h250 := T (T (T (T (T h214 h212) h210) h208) h207) h4
  have h251 := C h34 (T (T (C h13 (C (C h34 h250) h13)) h244) (C h34 (T (T (T (T (C h13 (T (C (S h245) h13) h133)) h132) h128) h126) h124)))
  have h252 := h v213 v0 v6
  have h253 := S h252
  have h254 := h (M v6 (M (M v0 y) v6)) v0 x
  have h255 := h y v0 v6
  have h256 := C h51 (T (T (T (T (T h206 h205) h191) (C h51 (T h186 (C h5 (C h255 h5))))) (S h254)) (C h13 (C (C h51 h243) h13)))
  have h257 := C (T (T (T h256 h253) h215) h251) h13
  have h258 := C h13 h257
  have h259 := C h51 (T (T (T (T (T (C h13 (C (C h51 h250) h13)) h254) (C h51 (T (C h5 (C (S h255) h5)) h192))) h190) h220) h219)
  have h260 := C (T (T (T h246 h216) h252) h259) h13
  have h261 := T (T (T (T (T (T (T h3 h242) h204) h202) h218) h217) h215) h251
  have h262 := C h261 h13
  have h263 := S h77
  have h264 := C h5 (C h5 (C (T (T (T h23 h22) h73) (C h5 (C h74 (C h18 h74)))) h5))
  have h265 := h v19 x x
  have h266 := C h5 (C h5 (C (T (T (T (C h5 (C h5 (C h17 h5))) (S h265)) h21) h72) h5))
  have h267 := h (M x v195) x x
  have h268 := h v2 v2 x
  have h269 := C h8 (T (T (T (T (T (T (C h5 (C (S h268) h5)) h267) h266) h71) h27) h70) h36)
  let v270 := M v24 x
  have h271 := h (M x v270) v2 x
  have h272 := h v270 x x
  have h273 := S h271
  have h274 := S h267
  have h275 := C h5 (C h5 (C (T (T (T h23 h22) h265) (C h5 (C h5 (C h18 h5)))) h5))
  have h276 := C h8 (T (T (T (T (T (T h35 h41) h28) h26) h275) h274) (C h5 (C h268 h5)))
  have h277 := h (M x (M v115 x)) v2 x
  have h278 := h v0 v2 x
  have h279 := C h51 (C h114 h51)
  have h280 := h v116 v2 v0
  have h281 := C h5 (T (C h5 (T (T (T h280 (C h8 (T (T (T (T h279 h56) h53) h43) (C h5 (C h278 h5))))) (S h277)) (C h5 (C (T h276 h273) h5)))) (S h272))
  have h282 := T (T h281 h271) h269
  have h283 := S h280
  have h284 := C h51 (C h113 h51)
  have h285 := C h5 (T h272 (C h5 (T (T (T (C h5 (C (T h271 h269) h5)) h277) (C h8 (T (T (T (T (C h5 (C (S h278) h5)) h42) h150) h148) h284))) h283)))
  have h286 := h v2 v2 v6
  have h287 := h (M v6 (M v24 v6)) v2 v2
  have h288 := h v55 v2 x
  have h289 := S h288
  have h290 := h v0 v2 v2
  let v291 := M v115 v2
  have h292 := h (M v2 v291) v2 x
  have h293 := C h8 (C h5 (C (T (T (T (T h292 (C h8 (T (C h5 (C (S h290) h5)) h119))) h118) h280) (C h8 h279)) h5))
  have h294 := h v291 v2 x
  have h295 := C h282 h8
  have h296 := T (T h276 h273) h285
  have h297 := C h296 h8
  have h298 := S h294
  have h299 := C h8 (C h5 (C (T (T (T (T (C h8 h284) h283) h117) (C h8 (T h229 (C h5 (C h290 h5))))) (S h292)) h5))
  have h300 := h v47 x v6
  have h301 := C h5 (C h5 (C (T (T (T (C h5 (C h13 (C h44 h13))) (S h300)) h49) h149) h5))
  let v302 := M v0 v6
  have h303 := h (M v6 v302) x x
  have h304 := h v25 v0 v6
  have h305 := S h304
  have h306 := h v2 v0 x
  have h307 := C h51 (C h8 (C (S h306) h8))
  let v308 := M v0 v2
  let v309 := M x (M v308 x)
  have h310 := h v309 v0 v2
  have h311 := h v309 v2 v6
  have h312 := S h311
  have h313 := h v308 v2 x
  have h314 := h (M v2 v308) x x
  have h315 := h v47 x v2
  have h316 := h v47 x z
  have h317 := C h5 (C h5 (C (T (T (T (C h5 (C h34 (C h44 h34))) (S h316)) h49) h149) h5))
  let v318 := M z v1
  have h319 := h v318 x x
  have h320 := R v55
  have h321 := h v6 v0 v6
  have h322 := S h321
  have h323 := C h5 (C h322 h5)
  have h324 := C h51 (T (T (T (T (T (T (T (T (T h323 h79) h237) h235) h100) h241) h221) h190) h220) h219)
  have h325 := C h5 (C h321 h5)
  have h326 := h v6 v0 x
  have h327 := C h51 (T (C h5 (C (S h326) h5)) h325)
  let v328 := M v302 x
  have h329 := h (M x v328) v0 x
  have h330 := h v328 x v6
  have h331 := S h330
  have h332 := S h329
  have h333 := C h51 (T h323 (C h5 (C h326 h5)))
  let v334 := M v6 (M v302 v6)
  have h335 := h v334 v0 x
  have h336 := h v334 v0 z
  have h337 := S h336
  have h338 := C h51 (C h34 (C h321 h34))
  have h339 := C h13 (C (T (T (T (T h338 h337) h335) h333) h332) h13)
  have h340 := C h51 (C h34 (C h322 h34))
  have h341 := S h335
  have h342 := C h51 (T (T (T (T (T (T (T (T (T h206 h205) h191) h189) h187) h101) h99) h98) h80) h325)
  have h343 := C h13 (C (T (T (T h342 h341) h336) h340) h13)
  have h344 := C h13 h260
  have h345 := C h13 (T (T (T (T (T (T h35 h41) h28) h26) h264) h263) h262)
  have h346 := C h5 (T (T (T h345 h344) h343) h339)
  have h347 := T h346 h331
  have h348 := T (C (T (T (T (T (T (T (T (T (T (T (T (C h5 h347) h329) h327) h324) h256) h253) h214) h212) h210) h208) h207) h4) h320) h147
  have h349 := S h319
  have h350 := C h5 (C h5 (C (T (T (T h52 h50) h316) (C h5 (C h34 (C h45 h34)))) h5))
  have h351 := C h5 (C (T (T h56 h350) h349) h348)
  let v352 := M x v63
  have h353 := h v352 x v55
  have h354 := C h13 (C (T (T (T h338 h337) h335) h324) h13)
  have h355 := C h13 (C (T (T (T (T h329 h327) h341) h336) h340) h13)
  have h356 := C h5 (T (T (T h355 h354) h258) h249)
  have h357 := T (C h8 (T (T (T (T h330 h356) h353) h351) (C h5 (C (T (T (T h319 h317) (C h5 (C h5 (C (T (T (T h52 h50) h315) (C h5 (C h8 (C h45 h8)))) h5)))) (S h314)) h5)))) (S h313)
  have h358 := C h8 (C h5 (C h357 h5))
  have h359 := h v328 v2 x
  have h360 := h v328 v0 v6
  have h361 := S h360
  have h362 := S h353
  have h363 := T h330 h356
  have h364 := T h146 (C (T (T (T (T (T (T (T (T (T (T (T h3 h242) h204) h202) h218) h217) h252) h259) h342) h333) h332) (C h5 h363)) h320)
  have h365 := h v54 v2 v6
  have h366 := S h365
  have h367 := h v2 v0 v6
  have h368 := h (M v6 (M v308 v6)) v0 x
  have h369 := C h8 (T (T (C h13 (C h357 h13)) h368) (C h51 (T (T (T (T (T (T (C h5 (C (S h367) h5)) h267) h266) h71) h27) h70) h36)))
  have h370 := h v328 v2 v6
  have h371 := h v328 v1 v6
  have h372 := S h371
  have h373 := C h5 (C (T (T h319 h317) h148) h364)
  have h374 := h v47 x v1
  let v375 := M v0 v1
  have h376 := h (M v1 v375) x x
  have h377 := h v375 v1 x
  have h378 := h (M v6 (M v375 v6)) v0 x
  have h379 := h v1 v0 v6
  let v380 := M x v172
  have h381 := h v380 v0 v1
  have h382 := S h381
  have h383 := h z v0 x
  have h384 := C h51 (T (T h40 h37) (C h29 (T h32 (C h383 h29))))
  have h385 := C h29 (T (T (C h51 (T (T h384 h382) (C h5 (C h379 h5)))) (S h378)) (C h13 (C (T h377 (C h29 (T (T (T (T (C h5 (C (T (T (T h376 (C h5 (C h5 (C (T (T (T (C h5 (C h29 (C h44 h29))) (S h374)) h49) h149) h5)))) h350) h349) h5)) h373) h362) h346) h331))) h13)))
  have h386 := C h51 (T (T (C h29 (T (C (S h383) h29) h33)) h69) h68)
  have h387 := C h29 (T (T (C h13 (C (T (C h29 (T (T (T (T h330 h356) h353) h351) (C h5 (C (T (T (T h319 h317) (C h5 (C h5 (C (T (T (T h52 h50) h374) (C h5 (C h29 (C h45 h29)))) h5)))) (S h376)) h5)))) (S h377)) h13)) h378) (C h51 (T (T (C h5 (C (S h379) h5)) h381) h386)))
  have h388 := h y x v2
  let v389 := M (M x y) v2
  have h390 := h (M v2 v389) x x
  have h391 := C h8 (T (T (C h13 (C (T (T (T (T h390 (C h5 (T (C h5 (C (S h388) h5)) h143))) h141) h139) h138) h13)) (C h13 (C (T (T (T h346 h331) h371) h387) h13))) (C h13 (C (T (T (T h385 h372) h370) h369) h13)))
  have h392 := h v389 v2 v6
  have h393 := C h51 (T (T (T (C h5 (C (C h51 (T (T h392 h391) h366)) h364)) h362) h346) h331)
  have h394 := h v389 v0 x
  have h395 := S h392
  have h396 := S h370
  have h397 := T h313 (C h8 (T (T (T (T (C h5 (C (T (T (T h314 (C h5 (C h5 (C (T (T (T (C h5 (C h8 (C h44 h8))) (S h315)) h49) h149) h5)))) h350) h349) h5)) h373) h362) h346) h331))
  have h398 := C h8 (T (T (C h51 (T (T (T (T (T (T h35 h41) h28) h26) h275) h274) (C h5 (C h367 h5)))) (S h368)) (C h13 (C h397 h13)))
  have h399 := C h8 (T (T (C h13 (C (T (T (T h398 h396) h371) h387) h13)) (C h13 (C (T (T (T h385 h372) h330) h356) h13))) (C h13 (C (T (T (T (T h232 h225) h140) (C h5 (T h224 (C h5 (C h388 h5))))) (S h390)) h13)))
  have h400 := T (T (T (T h365 h399) h395) h394) h393
  have h401 := C h13 (C h400 h13)
  have h402 := h (M v6 (M v54 v6)) v0 x
  have h403 := S h402
  have h404 := h v0 v0 v6
  have h405 := C h51 (T (T (T h56 h53) h43) (C h5 (C h404 h5)))
  have h406 := C h51 (T (T h405 h403) h401)
  have h407 := C h51 (T (T (T (C h5 (C (S h404) h5)) h42) h150) h148)
  have h408 := S h394
  have h409 := C h51 (T (T (T h330 h356) h353) (C h5 (C (C h51 (T (T h365 h399) h395)) h348)))
  have h410 := T (T (T (T h409 h408) h392) h391) h366
  have h411 := C h13 (C h410 h13)
  have h412 := C h51 (T (T h411 h402) h407)
  have h413 := C h51 h347
  have h414 := C h13 (C (T (T (T (T (T (T (T (T h413 h409) h408) h392) h391) (C h8 (T (C h13 (C (T (T (T h398 h396) h360) h412) h13)) (C h13 (C (T (T (T h406 h361) h359) h358) h13))))) h312) h310) h307) h13)
  have h415 := C h51 h363
  have h416 := C h13 (C h415 h13)
  have h417 := h v0 v0 x
  have h418 := h (M x (M v54 x)) v0 x
  have h419 := C h51 (T (T (T (T (T (T (T (T (C h5 (C h413 h5)) (C h5 (C h410 h5))) h418) (C h51 (T (T (T (C h5 (C (S h417) h5)) h42) h150) h148))) h405) h403) h401) h416) h414)
  have h420 := h v352 v0 x
  have h421 := S h359
  have h422 := C h8 (C h5 (C h397 h5))
  have h423 := C h13 (C (T (T (T (T (T (T (T (T (T h422 h421) h330) h356) h420) h419) h305) h27) h70) h36) h13)
  have h424 := S h310
  have h425 := C h51 (C h8 (C h306 h8))
  have h426 := h v0 v0 v2
  let v427 := M v54 v2
  have h428 := h (M v2 v427) v0 x
  have h429 := C h8 (T (T (T (T (T (C h13 (C (T h428 (C h51 (T (T (T (C h5 (C (S h426) h5)) h42) h150) h148))) h13)) (C h13 (C (T (T (T (T (T (T (T (T (T (T h405 h403) h401) h416) h414) (C h13 (C (T (T (T (T (T (T (T (T h425 h424) h311) (C h8 (T (T (T (T (T (T (T h423 h303) h301) h148) h288) h299) h298) h297))) (C h8 (T (T (T (T h295 h294) h293) h289) h284))) h283) h117) h230) h228) h13))) h287) (C h8 (T (T (T (C h8 (C (S h286) h8)) h27) h70) h36))) h276) h273) h285) h13))) (C h13 (C h282 h13))) h117) h230) h228)
  have h430 := h v427 v2 v6
  have h431 := C h13 (T (T (T (T (T (T h430 h429) h26) h264) h263) h262) h260)
  have h432 := T (T h431 h258) h249
  have h433 := C h432 h13
  have h434 := C h13 (T (T (T (T h433 h67) h66) h62) h60)
  have h435 := S h430
  have h436 := C h13 (C h413 h13)
  have h437 := C h13 (C (T (T (T (T (T (T (T (T h425 h424) h311) (C h8 (T (C h13 (C (T (T (T h422 h421) h360) h412) h13)) (C h13 (C (T (T (T h406 h361) h370) h369) h13))))) h399) h395) h394) h393) h415) h13)
  have h438 := S h420
  have h439 := C h51 (T (T (T (T (T (T (T (T h437 h436) h411) h402) h407) (C h51 (T (T (T h56 h53) h43) (C h5 (C h417 h5))))) (S h418)) (C h5 (C h400 h5))) (C h5 (C h415 h5)))
  have h440 := C h13 (C (T (T (T (T (T (T (T (T (T h35 h41) h28) h304) h439) h438) h346) h331) h359) h358) h13)
  have h441 := S h303
  have h442 := C h5 (C h5 (C (T (T (T h52 h50) h300) (C h5 (C h13 (C h45 h13)))) h5))
  have h443 := C h8 (T (T (T (T (T h121 h120) h118) (C h13 (C h296 h13))) (C h13 (C (T (T (T (T (T (T (T (T (T (T h281 h271) h269) (C h8 (T (T (T h35 h41) h28) (C h8 (C h286 h8))))) (S h287)) (C h13 (C (T (T (T (T (T (T (T (T h121 h120) h118) h280) (C h8 (T (T (T (T h279 h288) h299) h298) h297))) (C h8 (T (T (T (T (T (T (T h295 h294) h293) h289) h56) h442) h441) h440))) h312) h310) h307) h13))) h437) h436) h411) h402) h407) h13))) (C h13 (C (T (C h51 (T (T (T h56 h53) h43) (C h5 (C h426 h5)))) (S h428)) h13)))
  have h444 := C h13 (T (T (T (T (T (T h257 h248) h77) h75) h71) h443) h435)
  have h445 := T (T h345 h344) h444
  have h446 := C h445 h13
  have h447 := S h67
  have h448 := C h13 (C h5 (C (T (C h13 h60) (S h65)) h5))
  have h449 := h v55 v1 v6
  have h450 := S h449
  have h451 := h v39 v1 v0
  have h452 := h v39 v0 x
  have h453 := h v380 y x
  have h454 := h v1 y x
  have h455 := S h454
  let v456 := M x (M (M y v1) x)
  have h457 := h v456 y x
  have h458 := h v456 y v1
  let v459 := M v1 (M v1 v1)
  have h460 := h v459 y x
  have h461 := h v459 x x
  have h462 := h v1 x v6
  have h463 := S h462
  let v464 := M v6 (M (M x v1) v6)
  have h465 := h v464 x v1
  have h466 := h v464 x v0
  have h467 := h (M v0 v38) x x
  have h468 := h v38 v0 x
  have h469 := h v1 z v0
  have h470 := S h469
  have h471 := h (M v0 (M v318 v0)) z x
  have h472 := T (C h34 (T (C h34 (T (T h384 h382) (C h5 (C h469 h5)))) (S h471))) h470
  have h473 := T h469 (C h34 (T h471 (C h34 (T (T (C h5 (C h470 h5)) h381) h386))))
  have h474 := C h29 (C h13 (C (T (T (T (T (T (T (C h473 (T (T (T (T h430 h429) h27) h70) h36)) (C h472 h51)) h468) (C h51 (C h5 (C (T (T (T (T (T (T (T h467 (C h5 (C h5 (C (T (T (T (C h5 (C h51 (C h462 h51))) (S h466)) h465) (C h5 (C h29 (C h463 h29)))) h5)))) (S h461)) h460) (C h74 (C h5 (C (T (T (T (C h74 (C h29 (C h454 h29))) (S h458)) h457) (C h74 (C h5 (C h455 h5)))) h5)))) (S h453)) h381) h386) h5)))) (S h452)) h451) (C h29 (C h51 (C h36 h51)))) h13))
  have h475 := h v427 v1 v6
  have h476 := C h13 (T (T (T (T (T (T h475 h474) h450) h61) h448) h447) h446)
  have h477 := C (T (T (T h476 h434) h59) h15) h13
  have h478 := h v196 v2 y
  have h479 := C h166 h74
  have h480 := C h165 h74
  have h481 := C h29 (T (T (T (T h240 h239) h109) h238) h222)
  have h482 := T (T (T h481 h155) h152) h147
  have h483 := C h74 (T (C h482 h74) h480)
  have h484 := h v10 x x
  have h485 := S h484
  have h486 := h v10 y v6
  have h487 := S h486
  have h488 := h y y v0
  have h489 := C h74 (T (T (T (C h5 (C (S h488) h5)) h145) h144) h112)
  let v490 := M y y
  have h491 := h (M v0 (M v490 v0)) y x
  have h492 := S h491
  have h493 := C h74 (T (T (T h111 h233) h223) (C h5 (C h488 h5)))
  have h494 := h y y v2
  have h495 := S h494
  let v496 := M v2 (M v490 v2)
  have h497 := h v496 y x
  have h498 := h v496 y y
  have h499 := C h130 h74
  have h500 := C h129 h74
  have h501 := h y y y
  let v502 := M v490 y
  have h503 := h (M y v502) y y
  have h504 := C h74 (T (C h13 (C (T (T (T (T (T (T h503 (C h74 (T (C h74 (T (C (S h501) h74) h500)) (C h74 (T h499 (C h494 h74)))))) (S h498)) h497) (C h74 (T (T (T (C h5 (C h495 h5)) h145) h144) h112))) h493) h492) h13)) (C h13 (C (T (T h491 h489) (C h74 (T (T (T (T (T (T h345 h344) h444) h476) h434) h59) h15))) h13)))
  have h505 := h v502 y v6
  have h506 := C h5 (T (T h505 h504) h487)
  have h507 := S h505
  have h508 := S h475
  have h509 := C h29 (C h13 (C (T (T (T (T (T (T (C h29 (C h51 (C h35 h51))) (S h451)) h452) (C h51 (C h5 (C (T (T (T (T (T (T (T h384 h382) h453) (C h74 (C h5 (C (T (T (T (C h74 (C h5 (C h454 h5))) (S h457)) h458) (C h74 (C h29 (C h455 h29)))) h5)))) (S h460)) h461) (C h5 (C h5 (C (T (T (T (C h5 (C h29 (C h462 h29))) (S h465)) h466) (C h5 (C h51 (C h463 h51)))) h5)))) (S h467)) h5)))) (S h468)) (C h473 h51)) (C h472 (T (T (T (T h35 h41) h28) h443) h435))) h13))
  have h510 := C h13 (T (T (T (T (T (T h433 h67) h66) h62) h449) h509) h508)
  have h511 := C h13 (T (T (T (T h58 h61) h448) h447) h446)
  have h512 := C h13 (T (T (T (T (C h5 (C (T (T (T (T (T h16 (C h5 (C h5 (C (T (T (T (C h5 (C h13 (C h17 h13))) (S h20)) h21) h72) h5)))) h71) h27) h70) h36) h5)) h42) h150) h148) h60)
  have h513 := C h74 (T (C h13 (C (T (T (C h74 (T (T (T (T (T (T h14 h512) h511) h510) h431) h258) h249)) h493) h492) h13)) (C h13 (C (T (T (T (T (T (T h491 h489) (C h74 (T (T (T h111 h233) h223) (C h5 (C h494 h5))))) (S h497)) h498) (C h74 (T (C h74 (T (C h495 h74) h500)) (C h74 (T h499 (C h501 h74)))))) (S h503)) h13)))
  have h514 := C h5 (T (T (T (T (T (T (T (T (T h355 h354) h444) h476) h434) h59) h15) h486) h513) h507)
  have h515 := h v427 v6 v6
  have h516 := S h515
  have h517 := C h13 (T (T (T (T (T h505 h504) h487) h14) h512) h511)
  have h518 := T (T (T (T (T (T (T (T h517 h516) h430) h429) h304) h439) h438) h346) h514
  have h519 := C h13 (T (T (T (T (T h434 h59) h15) h486) h513) h507)
  have h520 := h v427 v6 x
  have h521 := S h520
  have h522 := C h5 (C h445 h5)
  have h523 := h (M x (M v63 x)) v6 x
  have h524 := S h523
  have h525 := h v0 v6 x
  have h526 := C h13 (T (T (T (T h58 h56) h53) h43) (C h5 (C h525 h5)))
  have h527 := C h13 (T (T (T (T (T (T (T h345 h344) h444) h476) h434) h526) h524) h522)
  have h528 := T (T (T h527 h521) h515) h519
  have h529 := C h5 (C h528 h5)
  have h530 := C h13 (T (T (T (T (C h5 (C (S h525) h5)) h42) h150) h148) h60)
  have h531 := C h5 (C h432 h5)
  have h532 := C h13 (T (T (T (T (T (T (T h531 h523) h530) h511) h510) h431) h258) h249)
  have h533 := C h5 (C (T (T (T (T (T (T h35 h41) h28) h443) h435) h520) h532) h5)
  have h534 := C (T (T (T h14 h512) h511) h510) h13
  have h535 := C h5 (T (T (T (T (T (T (T (T (T (T (T h534 h433) h67) h66) h62) h56) h53) h43) h533) h529) (C h5 (C h518 h5))) (C h5 (C h506 h5)))
  have h536 := C (T h535 h485) h13
  have h537 := C h5 (C (T (T (T (T (T (T h527 h521) h430) h429) h27) h70) h36) h5)
  have h538 := T (T (T h517 h516) h520) h532
  have h539 := C h5 (C h538 h5)
  have h540 := C h5 (T (T (T (T (T (T (T (T (T h505 h504) h487) h14) h512) h511) h510) h431) h343) h339)
  have h541 := T (T (T (T (T (T (T (T h540 h356) h420) h419) h305) h443) h435) h515) h519
  have h542 := C h5 (T (T h486 h513) h507)
  have h543 := C h5 (T (T (T (T (T (T (T (T (T (T (T (C h5 (C h542 h5)) (C h5 (C h541 h5))) h539) h537) h42) h150) h148) h61) h448) h447) h446) h477)
  have h544 := C (T h484 h543) h13
  have h545 := h v502 v6 x
  have h546 := C h29 (T (T (T (T h159 h158) h110) h108) h106)
  have h547 := T (T (T h146 h163) h162) h546
  have h548 := h v11 x x
  have h549 := h v11 y y
  have h550 := C h247 (T (T (T (T (T (T (T (T (T (T (T (T h35 h41) h28) h443) h435) h475) h474) h450) h61) h448) h447) h446) h477)
  have h551 := C h261 h51
  have h552 := T h551 h550
  let v553 := M v153 y
  have h554 := h v553 y x
  have h555 := h (M y v553) y x
  have h556 := h v0 y y
  have h557 := h x y x
  have h558 := h v55 y x
  have h559 := C h74 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (C h13 (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (C h74 (T (T h551 h550) (C h74 (T (T (T (T (T (T (T (T h534 h433) h67) h66) h62) h558) (C h74 (T (C h5 (T (C h147 h5) h179)) (C h5 (T h177 (C (T (T h557 (C h74 (C h5 (C h556 h5)))) (S h555)) h5)))))) (S h554)) (C h552 h74))))) (S h549)) h534) h433) h67) h66) h62) h449) h509) h508) h430) h429) h304) h439) h438) h346) h514) h506) h13)) (C h13 (C h542 h13))) (C h13 (C h541 h13))) (C h13 (C h538 h13))) (C h13 (C (T (T (T (T (T (T (T (T (T (T h527 h521) h430) h429) h304) h439) h438) h346) h331) h359) h358) h13))) h423) h303) h301) h148) h61) h448) h447) h446) h477) h548) (C h547 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (C h5 (C (T (T (T (T (T h535 h485) h14) h512) h511) h510) h5)) h531) h523) h530) h59) h15) h486) h513) h507) h545) (C h13 (T (T (T (T (T (T (T (T (T (T h539 h537) h42) h150) h148) h61) h448) h447) h446) h477) h544))) (C h13 h536)) h12) h9) h4)))
  have h560 := h v153 y v6
  have h561 := h v153 v1 v6
  have h562 := S h561
  have h563 := S h560
  have h564 := C h247 h51
  have h565 := C h261 (T (T (T (T (T (T (T (T (T (T (T (T h534 h433) h67) h66) h62) h449) h509) h508) h430) h429) h27) h70) h36)
  have h566 := T h565 h564
  have h567 := S h12
  have h568 := C h8 (C h5 (C h7 h5))
  have h569 := C h74 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (C h482 (T (T (T (T (T (T (T (T (T (T (T (T (T (T h3 h568) h567) (C h13 h544)) (C h13 (T (T (T (T (T (T (T (T (T (T h536 h534) h433) h67) h66) h62) h56) h53) h43) h533) h529))) (S h545)) h505) h504) h487) h14) h512) h526) h524) h522) (C h5 (C (T (T (T (T (T h476 h434) h59) h15) h484) h543) h5)))) (S h548)) h534) h433) h67) h66) h62) h56) h442) h441) h440) (C h13 (C (T (T (T (T (T (T (T (T (T (T h422 h421) h330) h356) h420) h419) h305) h443) h435) h520) h532) h13))) (C h13 (C h528 h13))) (C h13 (C h518 h13))) (C h13 (C h506 h13))) (C h13 (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h542 h540) h356) h420) h419) h305) h443) h435) h475) h474) h450) h61) h448) h447) h446) h477) h549) (C h74 (T (T (C h74 (T (T (T (T (T (T (T (T (C h566 h74) h554) (C h74 (T (C h5 (T (C (T (T h555 (C h74 (C h5 (C (S h556) h5)))) (S h557)) h5) h179)) (C h5 (T h177 (C h146 h5)))))) (S h558)) h61) h448) h447) h446) h477)) h565) h564))) h13)))
  let v570 := M v1 v96
  have h571 := h v570 v1 y
  have h572 := h v570 v1 v0
  have h573 := C h29 (C h13 (C (T (T (T (C h29 (T (T (T (T (T (T (T (T (T (T h206 h205) h191) h189) h187) h101) h97) h95) h89) h234) (C h51 (C h546 h51)))) (S h572)) h571) (C h29 (T h569 h563))) h13))
  have h574 := h v203 v1 v6
  have h575 := h v203 x v6
  have h576 := S h574
  have h577 := C h29 (C h13 (C (T (T (T (C h29 (T h560 h559)) (S h571)) h572) (C h29 (T (T (T (T (T (T (T (T (T (T (C h51 (C h481 h51)) h157) h88) h103) h102) h100) h241) h221) h190) h220) h219))) h13))
  have h578 := C h74 (T h479 (C h547 h74))
  have h579 := h x x v6
  have h580 := h (M v6 (M (M x x) v6)) x y
  have h581 := C (T h580 (C h5 (T (T (T (T (T (T (C h74 (T (C (S h579) h74) h480)) h578) h569) h563) h561) h577) h576))) h13
  have h582 := C (T (C h5 (T (T (T (T (T (T h574 h573) h562) h560) h559) h483) (C h74 (T h479 (C h579 h74))))) (S h580)) h13
  have h583 := h v6 x x
  let v584 := M v84 x
  have h585 := h (M x v584) x x
  have h586 := h v584 x v6
  have h587 := h v584 v2 v6
  have h588 := h x v1 v2
  T (T (T (T (T h588 (C h29 (T (T (T (T (T (T (h (M v2 (M v172 v2)) v1 x) (C h29 (T (C h5 (T (C (S h588) h5) h179)) h178))) h176) h174) h171) h161) (C h552 h29)))) (C h29 (T (T (T (T (C h566 h29) h159) h158) h110) (C h13 (C (T (C h473 h13) (C h472 (T (C h8 (T (T (T h3 h568) h567) (C h13 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h534 h433) h67) h66) h62) h449) h509) h508) h430) h429) h26) h264) h263) h262) h260) (C (T (T (T (T (T (T h256 h253) h214) h212) h199) h478) (C h8 (T (T (T (T (T (T (T (T (T (C h74 (T (C h194 h74) h480)) h578) h569) h563) h561) h577) h576) h575) (C h5 (T (C h13 h582) (C h13 (T h581 (C (T (T (C h5 (T (T (T (T (T (T (T (T (T h206 h205) h191) h189) h187) h101) h99) h98) h80) h236)) (C h5 (T h83 (C h5 (C h583 h5))))) (S h585)) h13)))))) (S h586)))) h13))))) (S h587)))) h13))))) (S (h v584 v1 v6))) h587) (C h8 (T (T (T (C h13 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (C (T (T (T (T (T (T (C h8 (T (T (T (T (T (T (T (T (T h586 (C h5 (T (C h13 (T (C (T (T h585 (C h5 (T (C h5 (C (S h583) h5)) h236))) (C h5 (T (T (T (T (T (T (T (T (T h83 h79) h237) h235) h100) h241) h221) h190) h220) h219))) h13) h582)) (C h13 h581)))) (S h575)) h574) h573) h562) h560) h559) h483) (C h74 (T h479 (C h193 h74))))) (S h478)) h198) h218) h217) h252) h259) h13) h257) h248) h77) h75) h71) h443) h435) h475) h474) h450) h61) h448) h447) h446) h477)) h12) h9) h4))

