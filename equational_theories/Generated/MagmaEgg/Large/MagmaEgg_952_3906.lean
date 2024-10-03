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
theorem Equation952_implies_Equation3906 (G: Type _) [Magma G] (h: Equation952 G) : Equation3906 G := fun x y z =>
  let v0 := M z z
  let v1 := M y v0
  let v2 := M v1 y
  have h3 := h v2 y v1
  have h4 := S h3
  let v5 := M v1 v2
  have h6 := h (M v5 v2) x y
  have h7 := R (M y x)
  have h8 := h v2 y x
  have h9 := S h8
  have h10 := R x
  let v11 := M x y
  let v12 := M x v2
  let v13 := M v12 v11
  have h14 := h v13 x y
  have h15 := h v13 x v1
  have h16 := R (M v1 x)
  have h17 := h v13 v0 y
  have h18 := R v1
  have h19 := h v0 v2 z
  have h20 := S h19
  let v21 := M z v0
  let v22 := M v21 (M z v2)
  have h23 := h v22 v1 v2
  have h24 := h v22 x v2
  have h25 := S h24
  have h26 := R (M v2 x)
  have h27 := h v0 v2 y
  let v28 := M y v2
  have h29 := h (M v1 v28) x v2
  have h30 := h v28 x v1
  have h31 := h y y x
  have h32 := S h31
  have h33 := C h32 (T (T (T (T (T h30 (C h10 (C (T (T (T (T h29 (C h10 (C (T (S h27) h19) h26))) h25) h23) (C h18 (T (C h20 (C h8 h18)) (S h17)))) h16))) (S h15)) h14) (C h10 (C (T h9 h3) h7))) (S h6))
  have h34 := R v2
  have h35 := h y v1 y
  have h36 := S h35
  have h37 := C h31 (C h36 h34)
  let v38 := M y v1
  let v39 := M (M y y) v38
  have h40 := h v39 y v1
  let v41 := M x v0
  have h42 := h v39 x v1
  have h43 := S h42
  have h44 := C h35 h16
  have h45 := h y v1 v0
  let v46 := M v0 v1
  have h47 := h (M (M v0 y) v46) x v1
  have h48 := C h36 h16
  have h49 := h y v1 v2
  let v50 := M v2 v1
  let v51 := M v2 y
  have h52 := h (M v51 v50) x v1
  let v53 := M x x
  have h54 := h y v1 v53
  have h55 := h (M (M v53 y) (M v53 v1)) x v1
  have h56 := h y v1 z
  let v57 := M z v1
  let v58 := M z y
  have h59 := h (M v58 v57) x v1
  have h60 := h y v1 v1
  have h61 := C h10 (T (C (S h60) h16) h44)
  let v62 := M v1 v1
  have h63 := h (M v2 v62) x v1
  have h64 := S h63
  have h65 := C h10 (T h48 (C h60 h16))
  have h66 := h y v1 x
  let v67 := M x v1
  have h68 := h (M v11 v67) x v1
  have h69 := h v39 v1 v2
  have h70 := h v1 v2 v2
  have h71 := S h70
  let v72 := M v2 v2
  have h73 := h (M v50 v72) x v2
  have h74 := h v1 v2 v0
  have h75 := S h74
  let v76 := M v0 v2
  let v77 := M v46 v76
  have h78 := h v77 x v2
  have h79 := h v77 v0 v2
  have h80 := S h79
  have h81 := h v0 x v1
  have h82 := S h81
  have h83 := h v0 v0 y
  have h84 := S h83
  have h85 := R v62
  have h86 := h v0 v1 v1
  have h87 := S h86
  have h88 := C h18 (T (C h87 h85) h84)
  let v89 := M v1 v0
  let v90 := M v89 v62
  have h91 := h v90 v1 v1
  have h92 := h v90 x v1
  have h93 := S h92
  have h94 := h v0 v1 y
  have h95 := h (M v1 v38) x v1
  have h96 := C h10 (C (T (T (T (T h95 (C h10 (C (T (S h94) h86) h16))) h93) h91) h88) h16)
  have h97 := h v38 x v1
  have h98 := R v28
  have h99 := T (T (C h31 h98) h33) h4
  have h100 := C h99 (T (T h97 h96) h82)
  have h101 := C h74 h100
  have h102 := h v28 v1 y
  have h103 := T h102 h101
  have h104 := h v0 y z
  have h105 := S h104
  have h106 := C h105 h103
  have h107 := C h34 (T (T (T (T h106 h80) h78) (C h10 (C (T h75 h70) h26))) (S h73))
  have h108 := S h102
  have h109 := S h97
  have h110 := S h91
  have h111 := C h18 (T h83 (C h86 h85))
  have h112 := C h10 (C (T (T (T (T h111 h110) h92) (C h10 (C (T h87 h94) h16))) (S h95)) h16)
  have h113 := C h31 (T (T (T (T (T h6 (C h10 (C (T h4 h8) h7))) (S h14)) h15) (C h10 (C (T (T (T (T (C h18 (T h17 (C h19 (C h9 h18)))) (S h23)) h24) (C h10 (C (T h20 h27) h26))) (S h29)) h16))) (S h30))
  have h114 := T (T h3 h113) (C h32 h98)
  have h115 := C h114 (T (T h81 h112) h109)
  have h116 := C h75 h115
  have h117 := T h116 h108
  have h118 := C h104 h117
  have h119 := h v0 v1 z
  have h120 := S h119
  have h121 := h (M v21 v57) x v1
  have h122 := S h121
  have h123 := C h10 (C (T h87 h119) h16)
  have h124 := h v89 v0 v0
  have h125 := S h124
  let v126 := M v0 v0
  have h127 := R v126
  have h128 := R v89
  have h129 := h v62 x v0
  have h130 := S h129
  have h131 := R (M v0 x)
  have h132 := h v0 v0 v1
  have h133 := S h132
  have h134 := C h10 (C (T h133 h83) h131)
  have h135 := h v0 v0 v0
  have h136 := C h10 (C (T (S h135) h132) h131)
  have h137 := h (M v126 v126) x v0
  have h138 := h v126 v0 z
  have h139 := R v0
  have h140 := h z z v53
  have h141 := S h140
  have h142 := h z z z
  let v143 := M v53 z
  let v144 := M v143 v143
  have h145 := h v144 z z
  have h146 := h v144 x z
  have h147 := R (M z x)
  have h148 := S h142
  have h149 := h v126 x z
  have h150 := C h139 (T (T (T (T (C (T (T (C h132 h127) (C h133 (T (T (T (T h149 (C h10 (C (T h148 h140) h147))) (S h146)) h145) (C h142 (C h141 h139))))) (S h138)) h127) h137) h136) h134) h130)
  have h151 := h v126 v0 v0
  let v152 := M v21 v58
  have h153 := h v152 v2 y
  have h154 := h v152 v0 y
  have h155 := S h154
  have h156 := C h104 h18
  have h157 := C h139 h156
  have h158 := C (T (T (T (T h157 h155) h153) h107) h71) (T (T h151 h150) h84)
  have h159 := h v46 v0 v0
  have h160 := C h139 (C (T (T h159 (C h86 h158)) (C h87 h128)) h127)
  have h161 := h v1 v0 v0
  have h162 := C h18 (T (T (T (T (T (T (T h161 h160) h125) h111) h110) h92) h123) h122)
  let v163 := M v89 v89
  have h164 := h v163 x v0
  have h165 := h v163 v2 v1
  have h166 := S h165
  have h167 := R v5
  have h168 := S h164
  have h169 := C h10 (C (T h84 h132) h131)
  have h170 := S h161
  have h171 := S h159
  have h172 := S h151
  have h173 := S h137
  have h174 := C h10 (C (T h133 h135) h131)
  have h175 := C h139 (T (T (T (T h129 h169) h174) h173) (C (T (T h138 (C h132 (T (T (T (T (C h148 (C h140 h139)) (S h145)) h146) (C h10 (C (T h141 h142) h147))) (S h149)))) (C h133 h127)) h127))
  have h176 := C h105 h18
  have h177 := C h139 h176
  have h178 := S h153
  have h179 := C h34 (T (T (T (T h73 (C h10 (C (T h71 h74) h26))) (S h78)) h79) h118)
  have h180 := C (T (T (T (T h70 h179) h178) h154) h177) (T (T h83 h175) h172)
  have h181 := C h139 (C (T (T (C h86 h128) (C h87 h180)) h171) h127)
  have h182 := C h10 (C (T h120 h86) h16)
  have h183 := C h18 (T (T (T (T (T (T (T h121 h182) h93) h91) h88) h124) h181) h170)
  have h184 := h v0 v0 x
  have h185 := S h184
  have h186 := h (M v41 v41) x v0
  have h187 := S h186
  have h188 := C h10 (C (T h133 h184) h131)
  have h189 := h v163 v1 v0
  have h190 := T (T (T (T (T (T (C h18 (T h154 (C h132 h176))) (S h189)) h164) h134) h130) h162) h120
  let v191 := M v1 v152
  have h192 := R (M v191 v62)
  have h193 := h v152 v1 v1
  have h194 := h v1 v1 v0
  have h195 := S h194
  have h196 := C h34 (C (T (T (T (T (T h195 h70) h179) h178) h193) (C h18 (T (T (T (T (T (T (T h192 (C h190 (T (T (T h129 h169) h188) h187))) h185) h119) h183) h129) h169) h168))) h167)
  let v197 := M v46 v46
  have h198 := h v197 v2 v1
  have h199 := h v197 y v1
  have h200 := S h199
  have h201 := C h194 h34
  have h202 := R y
  have h203 := C (T (T (T (T (T (T (T (T (T (C h202 h201) h200) h198) h196) h166) h164) h134) h130) h162) h120) h103
  have h204 := C h34 (T h203 h118)
  have h205 := C h195 h34
  have h206 := S h198
  have h207 := C h10 (C (T h185 h132) h131)
  have h208 := T (T (T (T (T (T h119 h183) h129) h169) h168) h189) (C h18 (T (C h133 h156) h155))
  have h209 := C h34 (C (T (T (T (T (T (C h18 (T (T (T (T (T (T (T h164 h134) h130) h162) h120) h184) (C h208 (T (T (T h186 h207) h134) h130))) h192)) (S h193)) h153) h107) h71) h194) h167)
  have h210 := C (T (T (T (T (T (T (T (T (T h119 h183) h129) h169) h168) h165) h209) h206) h199) (C h202 h205)) h117
  have h211 := R v76
  have h212 := h v46 v2 v0
  have h213 := S h212
  have h214 := h v1 v0 v2
  have h215 := S h214
  have h216 := C h34 (C (T (T (T (T (T h215 h70) h179) h178) h154) h177) h211)
  let v217 := M v2 v0
  let v218 := M v50 v217
  have h219 := h v218 v2 v0
  have h220 := h v218 v2 v2
  have h221 := S h220
  have h222 := R v72
  have h223 := S h219
  have h224 := C h34 (C (T (T (T (T (T h157 h155) h153) h107) h71) h214) h211)
  have h225 := R (M v191 v89)
  have h226 := h v5 v2 y
  have h227 := R (M v191 v5)
  have h228 := h v152 v2 v1
  have h229 := C h34 (C (T (T (T (T (T h75 h70) h179) h178) h228) (C h34 (T (T (T (T (T (T (T (T (T h227 (C h190 h167)) (C h208 (T (T (T (T (T (T h226 h204) h107) h71) h161) h160) h125))) h225) (C h190 (T (T (T (T h111 h110) h92) h123) h122))) (C h139 (T (T (T (T (T h121 h182) h93) h91) h88) h180))) h171) h212) h224) h223))) h222)
  have h230 := h v77 v2 v2
  have h231 := C (T (T (T (T (T (T (T (T (C h104 h98) h106) h80) h230) h229) h221) h219) h216) h213) h211
  have h232 := C h34 (T (T h231 h79) h210)
  have h233 := S h230
  have h234 := S h226
  have h235 := C h34 (T h106 h210)
  have h236 := C h34 (C (T (T (T (T (T (C h34 (T (T (T (T (T (T (T (T (T h219 h216) h213) h159) (C h139 (T (T (T (T (T h158 h111) h110) h92) h123) h122))) (C h208 (T (T (T (T h121 h182) h93) h91) h88))) h225) (C h190 (T (T (T (T (T (T h124 h181) h170) h70) h179) h235) h234))) (C h208 h167)) h227)) (S h228)) h153) h107) h71) h74) h222)
  have h237 := C (T (T (T (T (T (T (T (T h212 h224) h223) h220) h236) h233) h79) h118) (C h105 h98)) h211
  have h238 := h v218 x v0
  have h239 := h v28 v2 v0
  have h240 := h v28 v72 y
  have h241 := S h240
  have h242 := h y y v1
  have h243 := C h114 h242
  have h244 := h v72 v0 v0
  have h245 := S h244
  have h246 := R (M (M v0 v72) v126)
  have h247 := h v197 x v1
  have h248 := S h247
  have h249 := h v1 v1 v1
  have h250 := S h249
  have h251 := C h10 (C (T h250 h194) h16)
  have h252 := h (M v62 v62) x v1
  have h253 := h v163 v1 v2
  have h254 := R v50
  have h255 := C h99 (T (T (T (T (T (T (T h97 h96) h82) h119) h183) h129) h169) h168)
  have h256 := T h115 h255
  have h257 := h (M v217 v50) x v1
  have h258 := h v0 v1 v2
  have h259 := R v217
  have h260 := T (T (T (T (T (T (T (C h74 h259) h116) h108) h239) h232) h204) h107) h71
  have h261 := S h252
  have h262 := C h10 (C (T h195 h249) h16)
  have h263 := S h239
  have h264 := C h34 (T (T h203 h80) h237)
  have h265 := T (T (T (T (T (T (T h70 h179) h235) h264) h263) h102) h101) (C h75 h259)
  have h266 := h v217 v1 v1
  have h267 := C h114 (T (T (T (T (T (T (T h164 h134) h130) h162) h120) h81) h112) h109)
  have h268 := C (T (T (T (T (T (T (T (T (T (T (T h267 h100) h266) (C h265 (T (T (T (T (T (C h260 (T (T (T (T (T (T (T (T h129 h169) h168) h165) h209) h206) h247) h262) h261)) h250) h70) h179) h235) h234))) (C h260 (T (T (T (T (T (T (T (T (T (T (T (T h226 h204) h107) h71) h161) h160) h125) h111) h110) h92) (C h10 (C (T h87 h258) h16))) (S h257)) (C h256 h254)))) (S h253)) h164) h134) h130) h162) h120) h19) h222
  have h269 := h (M v217 v72) x v2
  have h270 := h v0 v2 v2
  have h271 := h v22 v2 v2
  have h272 := h v163 v2 v2
  have h273 := T (T (T (T (T (T (T (T (T (T (T (T (T h119 h183) h129) h169) h168) h272) (C h34 h268)) (S h271)) h24) (C h10 (C (T h20 h270) h26))) (S h269)) (C h256 h222)) h268) (C h20 h222)
  have h274 := C h273 (T (T (T (T (T (T (T (T (T (T (T (T (T h252 h251) h248) h198) h196) h166) h164) h134) h130) h162) h120) h83) h175) h172)
  have h275 := h v1 v1 x
  have h276 := C h10 (C (T (S h275) h194) h16)
  have h277 := h (M v67 v67) x v1
  have h278 := T (T (T h277 h276) h262) h261
  have h279 := C h139 h278
  have h280 := S h277
  have h281 := C h10 (C (T h195 h275) h16)
  have h282 := h v1 v1 y
  have h283 := C h10 (C (T (S h282) h194) h16)
  have h284 := h (M v38 v38) x v1
  have h285 := T (T (T h284 h283) h281) h280
  have h286 := C h139 h285
  have h287 := S h284
  have h288 := C h10 (C (T h195 h282) h16)
  have h289 := h v0 v0 v2
  have h290 := C h10 (C (T (S h289) h132) h131)
  have h291 := h (M v217 v217) x v0
  have h292 := T h267 h100
  have h293 := C h139 (T (T (T (T (T (T (T (T (T (C h292 h259) h291) h290) h168) h165) h209) h206) h247) h288) h287)
  have h294 := h v163 v0 v2
  have h295 := C (T (T (T (T (T (T (T (T (T (T (T h20 h119) h183) h129) h169) h168) h253) (C h265 (T (T (T (T (T (T (T (T (T (T (T (T (C h292 h254) h257) (C h10 (C (T (S h258) h86) h16))) h93) h91) h88) h124) h181) h170) h70) h179) h235) h234))) (C h260 (T (T (T (T (T h226 h204) h107) h71) h249) (C h265 (T (T (T (T (T (T (T (T h252 h251) h248) h198) h196) h166) h164) h134) h130))))) (S h266)) h115) h255) h222
  have h296 := T (T (T (T (T (T (T (T (T (T (T (T (T (C h19 h222) h295) (C h292 h222)) h269) (C h10 (C (T (S h270) h19) h26))) h25) h271) (C h34 h295)) (S h272)) h164) h134) h130) h162) h120
  have h297 := C h296 (T (T (T (T (T (T (T (T (T (T (T (T (T h151 h150) h84) h119) h183) h129) h169) h168) h294) h293) h286) h279) h274) h246)
  have h298 := R v51
  have h299 := h v51 x v0
  have h300 := S h242
  have h301 := h y v2 x
  have h302 := S h301
  have h303 := C h34 (T (C h302 h222) h300)
  let v304 := M v11 v12
  have h305 := h v304 v2 v2
  have h306 := h v304 x v2
  have h307 := S h306
  have h308 := h y v2 v1
  have h309 := S h308
  have h310 := C h10 (C (T h309 h301) h26)
  have h311 := h (M v2 v5) x v2
  have h312 := C h34 (T (T (T (T (T (T (T (T (T (T (T h311 h310) h307) h305) h303) h299) (C h10 (C (T (T (T (T (T (T (T (T (C h19 h298) (C (T (T (T (T (T (T (T (T (T (T (T (T h20 h119) h183) h129) h169) h168) h294) h293) h286) h279) h274) h297) h245) h243)) h241) h239) h232) h204) h107) h71) h214) h131))) (S h238)) h220) h236) h233) h237)
  have h313 := T (T (T (T (T (T h311 h310) h307) h305) h303) h243) (C h99 (T (T (T (T (T (T h300 h308) h312) h232) h204) h107) h71))
  have h314 := S h40
  have h315 := C h32 (C h35 h34)
  have h316 := h v72 v2 y
  have h317 := S h311
  have h318 := C h10 (C (T h302 h308) h26)
  have h319 := S h305
  have h320 := C h34 (T h242 (C h301 h222))
  have h321 := C h99 h300
  have h322 := S h294
  have h323 := S h291
  have h324 := C h10 (C (T h133 h289) h131)
  have h325 := C h139 (T (T (T (T (T (T (T (T (T h284 h283) h248) h198) h196) h166) h164) h324) h323) (C h256 h259))
  have h326 := C h139 (T (T (T h277 h276) h288) h287)
  have h327 := C h139 (T (T (T h252 h251) h281) h280)
  have h328 := C h296 (T (T (T (T (T (T (T (T (T (T (T (T (T h151 h150) h84) h119) h183) h129) h169) h168) h165) h209) h206) h247) h262) h261)
  have h329 := C h273 (T (T (T (T (T (T (T (T (T (T (T (T (T h246 h328) h327) h326) h325) h322) h164) h134) h130) h162) h120) h83) h175) h172)
  have h330 := C h34 (T (T (T (T (T (T (T (T (T (T (T h231 h230) h229) h221) h238) (C h10 (C (T (T (T (T (T (T (T (T h215 h70) h179) h235) h264) h263) h240) (C (T (T (T (T (T (T (T (T (T (T (T (T h244 h329) h328) h327) h326) h325) h322) h164) h134) h130) h162) h120) h19) h321)) (C h20 h298)) h131))) (S h299)) h320) h319) h306) h318) h317)
  have h331 := T (T (T (T (T (T (C h114 (T (T (T (T (T (T h70 h179) h235) h264) h330) h309) h242)) h321) h320) h319) h306) h318) h317
  have h332 := h v39 v2 v1
  have h333 := h v197 v1 v2
  have h334 := h v0 v0 z
  have h335 := h (M v21 v21) x v0
  have h336 := h v0 v0 v53
  let v337 := M v53 v0
  have h338 := h (M v337 v337) x v0
  have h339 := S h333
  have h340 := C h18 (T (T (T (T (T (T (C (T (T (T (T (T (T (T (T (T (T (T (T (T (C h34 (T (T h40 h37) (C (T h32 h242) h98))) (S h316)) h244) h329) h328) h327) h326) h325) h322) h164) h134) h130) h162) h120) h331) (C (T (T (T (T (T (T (T (T (T (T (T h119 h183) h129) h169) h168) h294) h293) h286) h279) h274) h297) h245) (T (T (T (T (T h311 h310) h307) h305) h303) h243))) h241) h239) h330) (C (T (T (T (T (T (T h3 h113) h315) h314) h42) h65) h64) h313)) (C (T (T (T (T h63 h61) h43) h332) (C h34 (T (C h36 h201) h200))) h254))
  have h341 := h v2 v53 y
  let v342 := M y v53
  let v343 := M v53 v53
  have h344 := R v53
  have h345 := h x x x
  have h346 := h v53 v2 v0
  let v347 := M (M v0 v53) v76
  have h348 := h v53 v2 y
  let v349 := M v342 v28
  T (T (T (T (T (T (T h348 (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T h3 h113) h315) h314) h69) h340) h339) h198) h196) h166) h164) h134) h130) h162) h120) (R v349))) (C h139 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (h v349 x v2) (C h10 (C (T (S h348) h346) h26))) (S (h v347 x v2))) (h v347 v53 v2)) (C h344 (T (C (S h346) (C h341 (T (T (h v53 v53 v53) (C h344 (C (T (h v343 v53 x) (C h344 (T (C (S h345) (C h345 h344)) (S (h v343 x x))))) (R v343)))) (S (h v343 v53 v53))))) (S (h (M v28 v342) v53 v53))))) (S h341)) h3) h113) h315) h314) h69) h340) h339) h198) h196) h166) h164) h188) h187) (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (C h10 (T (T (T (T (T h119 h183) h129) h169) (C h10 (C (T h133 h336) h131))) (S h338))) (C h10 (T (T (T h338 (C h10 (C (T (S h336) h132) h131))) (C h10 (C (T h133 h334) h131))) (S h335)))) (C h10 (T (T (T h335 (C h10 (C (T (S h334) h132) h131))) h324) h323))) (C h10 (T (T (T h291 h290) h174) h173))) (C h10 (T (T (T h137 h136) h188) h187))) (C h10 (T (T (T (T (T (T (T (T h186 h207) h168) h165) h209) h206) h247) h288) h287))) (C h10 h285)) (C h10 h278)) (C h10 (T (T (T (T (T (T (T (T h252 h251) h248) h333) (C h18 (T (T (T (T (T (T (C (T (T (T (T (C h34 (T h199 (C h35 h205))) (S h332)) h42) h65) h64) h254) (C (T (T (T (T (T (T h63 h61) h43) h40) h37) h33) h4) h331)) h312) h263) h240) (C (T (T (T (T (T (T (T (T (T (T (T h244 h329) h328) h327) h326) h325) h322) h164) h134) h130) h162) h120) (T (T (T (T (T h321 h320) h319) h306) h318) h317))) (C (T (T (T (T (T (T (T (T (T (T (T (T (T h119 h183) h129) h169) h168) h294) h293) h286) h279) h274) h297) h245) h316) (C h34 (T (T (C (T h300 h31) h98) h315) h314))) h313)))) (S h69)) h42) (C h10 (T h48 (C h66 h16)))) (S h68)))) (C h10 (T (T (T h68 (C h10 (T (C (S h66) h16) h44))) h65) h64))) (C h10 (T (T (T h63 h61) (C h10 (T h48 (C h56 h16)))) (S h59)))) (C h10 (T (T (T h59 (C h10 (T (C (S h56) h16) h44))) (C h10 (T h48 (C h54 h16)))) (S h55)))) (C h10 (T (T (T h55 (C h10 (T (C (S h54) h16) h44))) (C h10 (T h48 (C h49 h16)))) (S h52)))) (C h10 (T (T (T h52 (C h10 (T (C (S h49) h16) h44))) (C h10 (T h48 (C h45 h16)))) (S h47)))) (C h10 (T (T h47 (C h10 (T (C (S h45) h16) h44))) h43))) (R v41))))) (S (h v39 v0 x))) h40) h37) h33) h4

