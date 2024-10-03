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
theorem Equation2383_implies_Equation1117 (G: Type _) [Magma G] (h: Equation2383 G) : Equation1117 G := fun x y z =>
  let v0 := M x z
  let v1 := M y v0
  let v2 := M v1 z
  let v3 := M y v2
  have h4 := R v3
  let v5 := M x v2
  let v6 := M v1 v5
  let v7 := M x x
  let v8 := M x (M z v7)
  have h9 := h z v8 v6
  have h10 := S h9
  have h11 := R v6
  have h12 := h x x z
  have h13 := h z v1 x
  have h14 := R v8
  have h15 := C (T h12 (C h14 (T h13 (C h11 h12)))) h11
  have h16 := T h15 h10
  have h17 := R v1
  have h18 := C h17 h16
  have h19 := R y
  have h20 := C h19 h18
  have h21 := S h12
  have h22 := C (T (C h14 (T (C h11 h21) (S h13))) h21) h11
  have h23 := T h9 h22
  have h24 := C h17 h23
  let v25 := M v0 v3
  let v26 := M y v25
  let v27 := M y (M v2 v1)
  have h28 := h v2 v27 v26
  have h29 := S h28
  have h30 := R v26
  have h31 := h v0 y v2
  have h32 := h v2 y v0
  have h33 := R v27
  have h34 := C (T h31 (C h33 (T h32 (C h30 h31)))) h30
  have h35 := T (T h34 h29) h24
  have h36 := C h19 h35
  have h37 := T h36 h20
  have h38 := R z
  have h39 := S h31
  have h40 := C (T (C h33 (T (C h30 h39) (S h32))) h39) h30
  have h41 := T (T h18 h28) h40
  have h42 := C h19 h41
  have h43 := C h19 h24
  have h44 := T h43 h42
  let v45 := M v1 v3
  let v46 := M x (M z (M x y))
  have h47 := R v45
  have h48 := h y x z
  have h49 := h v25 y v0
  have h50 := S h49
  have h51 := h v5 v1 x
  have h52 := R x
  have h53 := C h52 (C h17 (T (C h24 h52) (S h51)))
  have h54 := T (T h53 h15) h10
  have h55 := C h52 h54
  have h56 := C h52 (C h17 (T h51 (C h18 h52)))
  have h57 := C h52 h56
  have h58 := T h57 h55
  have h59 := C h44 h58
  have h60 := C h52 h53
  have h61 := T (T h9 h22) h56
  have h62 := C h52 h61
  have h63 := T h62 h60
  have h64 := C h4 h63
  have h65 := C h19 (T (T h64 h59) h50)
  have h66 := R v0
  have h67 := C h66 h65
  have h68 := C h19 h67
  have h69 := C h4 h58
  have h70 := C h37 h63
  have h71 := C h19 (T (T h49 h70) h69)
  have h72 := C h66 h71
  have h73 := C h17 h53
  let v74 := M v3 v0
  let v75 := M x v74
  let v76 := M x v3
  let v77 := M x (M z v76)
  have h78 := h z v77 v75
  have h79 := S h78
  have h80 := R v75
  have h81 := h v3 x z
  have h82 := h z x v3
  have h83 := R v77
  have h84 := C (T h81 (C h83 (T h82 (C h80 h81)))) h80
  have h85 := C h4 (T (C h52 (T h49 h70)) (C h52 h69))
  have h86 := T (T (T (T (T h85 h84) h79) h9) h22) h56
  have h87 := C h17 h86
  have h88 := C h4 (T (C h52 h64) (C h52 (T h59 h50)))
  have h89 := S h81
  have h90 := C (T (C h83 (T (C h80 h89) (S h82))) h89) h80
  let v91 := M v0 v2
  let v92 := M v1 v91
  have h93 := h z x v92
  have h94 := S h93
  have h95 := R v92
  have h96 := h z v1 v0
  have h97 := C h52 h96
  have h98 := C h97 h95
  have h99 := T (T (T (T h98 h94) h78) h90) h88
  have h100 := C h17 h99
  have h101 := C h19 (T (T (T (T (T (T h100 h87) h73) h18) h28) h40) h72)
  have h102 := S h96
  have h103 := C h52 h102
  have h104 := C h103 h95
  have h105 := T (T (T (T h85 h84) h79) h93) h104
  have h106 := C h17 h105
  have h107 := T (T (T (T (T h53 h15) h10) h78) h90) h88
  have h108 := C h17 h107
  have h109 := C h17 h56
  have h110 := C h19 (T (T (T (T (T (T h67 h34) h29) h24) h109) h108) h106)
  have h111 := C h19 h72
  have h112 := C h19 h58
  have h113 := T (T (T (T h85 h84) h79) h9) h22
  have h114 := C h52 h113
  let v115 := M v2 v0
  let v116 := M x v115
  have h117 := h z v1 v116
  have h118 := S h117
  have h119 := R v116
  have h120 := h z x v2
  have h121 := C (C h17 h120) h119
  have h122 := R v2
  have h123 := C h122 h58
  have h124 := C h52 h123
  have h125 := C (T (T (T h100 h87) h73) h18) h63
  have h126 := h v91 v1 v0
  have h127 := C h66 h18
  have h128 := C h66 h35
  have h129 := C h52 (T (T (T h128 h127) h126) h125)
  have h130 := C h66 h41
  have h131 := C h66 h24
  have h132 := C h52 (T h131 h130)
  have h133 := C h122 (T (T h132 h129) h124)
  have h134 := T (T (T (T (T h133 h121) h118) h78) h90) h88
  have h135 := C h52 h134
  have h136 := C h52 (T h128 h127)
  have h137 := S h126
  have h138 := C (T (T (T h24 h109) h108) h106) h58
  have h139 := C h52 (T (T (T h138 h137) h131) h130)
  have h140 := C h122 h63
  have h141 := C h52 h140
  have h142 := C h122 (T (T h141 h139) h136)
  have h143 := C (C h17 (S h120)) h119
  have h144 := C h66 (T (C h17 h128) (C h17 h127))
  have h145 := C h66 (C h17 (T (T (T (T h140 h138) h137) h131) h130))
  have h146 := T (T (T (T (T (T h145 h144) h98) h94) h117) h143) h142
  have h147 := C h52 h146
  have h148 := C h66 (C h17 (T (T (T (T h128 h127) h126) h125) h123))
  have h149 := C h66 (T (C h17 h131) (C h17 h130))
  have h150 := T h149 h148
  have h151 := C h52 h150
  have h152 := T (T (T h151 h147) h135) h114
  have h153 := C h19 h152
  have h154 := T h145 h144
  have h155 := C h52 h154
  have h156 := T (T (T (T (T (T h133 h121) h118) h93) h104) h149) h148
  have h157 := C h52 h156
  have h158 := T (T (T (T (T h85 h84) h79) h117) h143) h142
  have h159 := C h52 h158
  have h160 := T (T (T (T h15 h10) h78) h90) h88
  have h161 := C h52 h160
  let v162 := M v0 v1
  let v163 := M y v162
  have h164 := h v0 v163 v163
  have h165 := S h164
  have h166 := R v163
  have h167 := h v0 y v0
  have h168 := C (T h167 (C h166 (T h167 (C h166 h167)))) h166
  let v169 := M x (M v0 v7)
  have h170 := h v0 v169 z
  have h171 := S h170
  have h172 := h v74 y v0
  have h173 := S h172
  have h174 := T (T (T (T (T h151 h147) h135) h114) h57) h55
  have h175 := T (T h43 h42) h111
  have h176 := C h175 h174
  have h177 := h v0 v92 x
  have h178 := S h177
  have h179 := C (T h96 (C h95 h97)) h52
  have h180 := T (T (T (T (T (T (T h179 h178) h62) h60) h161) h159) h157) h155
  have h181 := C h4 h180
  have h182 := C h4 (T (C h52 h181) (C h52 (T (T (T (T h176 h173) h64) h59) h50)))
  have h183 := h x x v0
  have h184 := C (T (C h95 h103) h102) h52
  have h185 := R v169
  have h186 := C (T h183 (C h185 (T (T h177 h184) (C h38 h183)))) (T (T (T h182 h85) h84) h79)
  have h187 := T (T (T (T (T (T (T h151 h147) h135) h114) h57) h55) h177) h184
  have h188 := C h4 h187
  have h189 := T (T (T (T (T h62 h60) h161) h159) h157) h155
  have h190 := T (T h68 h36) h20
  have h191 := C h190 h189
  have h192 := C h4 (T (C h52 (T (T (T (T h49 h70) h69) h172) h191)) (C h52 h188))
  have h193 := h v115 v1 v0
  have h194 := T (T (T (T h98 h94) h117) h143) h142
  have h195 := C h122 (T (T (T (T (C h52 (C h122 h180)) (C h52 (T (C (T (T (T (T (T h24 h109) h108) h106) (C h17 h194)) (C h17 h156)) h174) (S h193)))) h141) h139) h136)
  have h196 := C h52 (T (T (T (T (T (T (T h195 h133) h121) h118) h78) h90) h88) h192)
  have h197 := T (T (T (T h133 h121) h118) h93) h104
  have h198 := C h122 (T (T (T (T h132 h129) h124) (C h52 (T h193 (C (T (T (T (T (T (C h17 h146) (C h17 h197)) h100) h87) h73) h18) h189)))) (C h52 (C h122 h187)))
  let v199 := M v1 v0
  let v200 := M x v199
  let v201 := M x (M z (M x v1))
  have h202 := h z v201 v200
  have h203 := S h202
  have h204 := R v200
  have h205 := h v1 x z
  have h206 := h z x v1
  have h207 := R v201
  have h208 := C (T h205 (C h207 (T h206 (C h204 h205)))) h204
  have h209 := C h17 h58
  have h210 := C h17 h152
  have h211 := C h17 h180
  have h212 := C h17 (T (T (C h52 h211) (C h52 h210)) (C h52 h209))
  have h213 := C h52 (T (T (T (T (T (T h212 h208) h203) h117) h143) h142) h198)
  have h214 := C (T (T (T h213 h196) h186) h171) h17
  let v215 := M z x
  have h216 := h (M v1 v215) x v1
  have h217 := T h216 h214
  have h218 := C h66 (C h19 h217)
  have h219 := C h19 (T (T (T (T (T (T (T (T h218 h168) h165) h62) h60) h161) h159) h157) h155)
  have h220 := C h17 h187
  have h221 := T (T (T h161 h159) h157) h155
  have h222 := C h17 h221
  have h223 := C h17 h63
  have h224 := C h66 (C h19 (T (T h223 h222) h220))
  have h225 := C h19 h224
  have h226 := C h66 (C h19 (T (T h211 h210) h209))
  have h227 := S h216
  have h228 := C h17 (T (T (C h52 h223) (C h52 h222)) (C h52 h220))
  have h229 := S h205
  have h230 := C (T (C h207 (T (C h204 h229) (S h206))) h229) h204
  have h231 := C h52 (T (T (T (T (T (T h195 h133) h121) h118) h202) h230) h228)
  have h232 := C h52 (T (T (T (T (T (T (T h182 h85) h84) h79) h117) h143) h142) h198)
  have h233 := S h183
  have h234 := C (T (C h185 (T (T (C h38 h233) h179) h178)) h233) (T (T (T h78 h90) h88) h192)
  have h235 := C (T (T (T h170 h234) h232) h231) h17
  have h236 := T h235 h227
  have h237 := C h66 (C h19 h236)
  have h238 := S h167
  have h239 := C (T (C h166 (T (C h166 h238) h238)) h238) h166
  have h240 := T (T (T (T (T h179 h178) h164) h239) h237) h226
  have h241 := C h19 h240
  have h242 := h v162 x v1
  have h243 := S h242
  have h244 := T (T (T (T h241 h225) h219) h153) h112
  have h245 := C h17 (C h52 h217)
  have h246 := C h52 h245
  have h247 := C (T (T (T (T h170 h234) h232) h231) h246) h244
  have h248 := T (T (T (T (T h224 h218) h168) h165) h177) h184
  have h249 := C h19 h226
  have h250 := C h19 (T (T (T (T (T (T (T (T h151 h147) h135) h114) h57) h55) h164) h239) h237)
  have h251 := C h19 h221
  have h252 := C h19 h63
  have h253 := T (T (T (T h252 h251) h250) h249) (C h19 h248)
  have h254 := C h17 (C h52 h236)
  have h255 := C h52 h254
  have h256 := C (T (T (T (T h255 h213) h196) h186) h171) h253
  have h257 := h v199 y v0
  have h258 := T (T (T h224 h218) h168) h165
  have h259 := h v215 y z
  have h260 := S h259
  let v261 := M x (M z v0)
  let v262 := M v1 (M z v2)
  have h263 := h z v262 v261
  have h264 := S h263
  have h265 := R v261
  have h266 := h z v1 z
  have h267 := h z x z
  have h268 := R v262
  have h269 := C (T h266 (C h268 (T h267 (C h265 h266)))) h265
  have h270 := T (T (T (T (T (T (T (T (T h224 h218) h168) h165) h62) h60) h161) h159) h157) h155
  have h271 := C h38 (T (T (C h52 (T (C h38 h240) (C h38 h270))) (C h52 (C h38 h152))) (C h52 (C h38 h58)))
  have h272 := h (M z v215) x z
  have h273 := T (T (T (T (T (T (T (T (T h151 h147) h135) h114) h57) h55) h164) h239) h237) h226
  have h274 := C h38 (T (T (C h52 (C h38 h63)) (C h52 (C h38 h221))) (C h52 (T (C h38 h273) (C h38 h248))))
  have h275 := S h266
  have h276 := C (T (C h268 (T (C h265 h275) (S h267))) h275) h265
  let v277 := M x (M v0 v0)
  have h278 := h z x v277
  have h279 := S h278
  have h280 := R v277
  have h281 := h z x v0
  have h282 := C (C h52 h281) h280
  have h283 := C h66 (T (T (C h52 (T (C h66 h240) (C h66 h270))) (C h52 (T (C h66 h151) (C h66 (T (T h147 h135) h114))))) (C h52 (C h66 h58)))
  have h284 := C h66 (T (T (C h52 (C h66 h63)) (C h52 (T (C h66 (T (T h161 h159) h157)) (C h66 h155)))) (C h52 (T (C h66 h273) (C h66 h248))))
  have h285 := C (C h52 (S h281)) h280
  have h286 := C h38 (T (T (T (C h52 (C h66 h61)) (C h52 (C h66 h53))) (C h52 (T (T (T (C h66 h160) (C h66 h158)) (C h66 h156)) (C h66 h154)))) (C h52 (T (T (C h66 (T (T (T (T (T h98 h94) h202) h230) h228) h245)) (C (T (T (T (T (T (T h170 h234) h232) h231) h246) (C h52 (T (T (T (T (T (T h254 h212) h208) h203) h278) h285) h284))) (C h52 (T (T (T (T (T h283 h282) h279) h263) h276) h274))) (T (T (T h254 h212) h208) h203))) (S h272))))
  have h287 := C (T h98 h94) h253
  have h288 := h v2 v0 v1
  have h289 := h v25 x v3
  have h290 := S h289
  have h291 := C (T (T h62 h60) h161) h190
  have h292 := C h66 h111
  have h293 := C h66 h68
  have h294 := C (T (T h114 h57) h55) h175
  have h295 := C h66 (T (T (C h19 (T (T (T (T (T (T (T (T h181 h176) h173) h64) h59) h50) h289) h294) h293)) (C h19 (T (T h292 h291) h290))) h71)
  have h296 := C h66 (T (T h65 (C h19 (T (T h289 h294) h293))) (C h19 (T (T (T (T (T (T (T (T h292 h291) h290) h49) h70) h69) h172) h191) h188)))
  have h297 := C h19 (T (T (T (T (T (T (T h100 h87) h73) h18) h28) h40) h72) h296)
  have h298 := C (T (T (T (T (T h43 h42) h111) h110) h297) (C h19 (T (T (T (T (T h295 h67) h34) h29) h288) h287))) (T (T (T h286 h271) h269) h264)
  have h299 := C h38 (T (T (T (C h52 (T (T h272 (C (T (T (T (T (T (T (C h52 (T (T (T (T (T h271 h269) h264) h278) h285) h284)) (C h52 (T (T (T (T (T (T h283 h282) h279) h202) h230) h228) h245))) h255) h213) h196) h186) h171) (T (T (T h202 h230) h228) h245))) (C h66 (T (T (T (T (T h254 h212) h208) h203) h93) h104)))) (C h52 (T (T (T (C h66 h150) (C h66 h146)) (C h66 h134)) (C h66 h113)))) (C h52 (C h66 h56))) (C h52 (C h66 h54)))
  have h300 := C h4 (T (T (T (T (T (T (T h254 h212) h208) h203) h263) h276) h274) h299)
  have h301 := C h4 (T (T (T (T (T (T (T h145 h144) h98) h94) h202) h230) h228) h245)
  have h302 := C h4 h156
  have h303 := C h4 h194
  have h304 := C h4 h105
  have h305 := C h4 h107
  have h306 := C h4 h56
  have h307 := T (T h306 h305) h304
  have h308 := C h4 h23
  have h309 := C h19 (T (T (T (T (T (C h66 (C h19 (T (T (T (T (T (T (T (T (T (T (T (T (T (C h17 h308) (C h17 h307)) (C h17 (T (T h303 h302) h301))) (C h17 (T (T (T (T (T (T (T (T (T h300 h298) h260) h179) h178) h170) h234) h232) h231) h246))) (C h17 (T (T (T (T (T (T (T (T h255 h213) h196) h186) h171) h164) h239) h237) h226))) (C (T (T (T h252 h251) h250) h249) h258)) (S h257)) h223) h222) h220) h216) h214) h242) h256))) (C h66 (C h19 (T h247 h243)))) h168) h165) h177) h184)
  have h310 := C h4 h16
  have h311 := C h4 h53
  have h312 := C h4 h86
  have h313 := C h4 h99
  have h314 := C h4 h197
  have h315 := C h4 h146
  have h316 := C h4 (T (T (T (T (T (T (T h254 h212) h208) h203) h93) h104) h149) h148)
  have h317 := C h4 (T (T (T (T (T (T (T h286 h271) h269) h264) h202) h230) h228) h245)
  have h318 := C h19 (T (T (T (T (T (T (T h295 h67) h34) h29) h24) h109) h108) h106)
  have h319 := C h19 (T (T (T (T (T (C (T h93 h104) h244) (S h288)) h28) h40) h72) h296)
  have h320 := C (T (T (T (T (T h319 h318) h101) h68) h36) h20) (T (T (T h263 h276) h274) h299)
  have h321 := T (T (T h164 h239) h237) h226
  have h322 := C h19 (T (T (T (T (T (T (T (T (T (T (T h303 h302) h301) h300) h298) h260) h179) h178) h164) h239) (C h66 (C h19 (T h242 h256)))) (C h66 (C h19 (T (T (T (T (T (T (T (T (T (T (T (T (T h247 h243) h235) h227) h211) h210) h209) h257) (C (T (T (T h225 h219) h153) h112) h321)) (C h17 (T (T (T (T (T (T (T (T h224 h218) h168) h165) h170) h234) h232) h231) h246))) (C h17 (T (T (T (T (T (T (T (T (T h255 h213) h196) h186) h171) h177) h184) h259) h320) h317))) (C h17 (T (T h316 h315) h314))) (C h17 (T (T h313 h312) h311))) (C h17 h310)))))
  let v323 := M y (M v3 v1)
  let v324 := M x (M v0 v76)
  have h325 := R v323
  have h326 := h v3 x v0
  let v327 := M v3 z
  have h328 := h (M v3 v215) y v0
  T (T (h x z v3) (C (T (C h38 (T (T (T (T (T h328 (C (T (T (T (T h318 h101) h68) h36) h20) h321)) (C h4 (T (T (T (T (T (T (T (T (T (T (T h224 h218) h168) h165) h177) h184) h259) h320) h317) h316) h315) h314))) (C h4 h313)) (C h4 (T h312 h311))) (C h4 h310))) (C h38 (T (h (M v3 v327) y v0) (C (T (T (T (T (T (T (C h19 (T (T (T (T (T (T (C h66 (C h19 (T (T (T (T (T (C h4 h308) (C h4 (T h306 h305))) (C h4 h304)) (C h4 (T (T (T (T (T (T (T (T (T (T (T h303 h302) h301) h300) h298) h260) h179) h178) h164) h239) h237) h226))) (C (T (T (T (T h43 h42) h111) h110) h297) h258)) (S h328)))) h295) h67) h34) h29) h288) h287)) h319) h318) h101) h68) h36) h20) (T (T (T (T (T (T (T (T (T (T (T (T (T (T h177 h184) h259) h320) h317) h316) h315) h314) h313) h312) h311) h310) (h v327 y v3)) (C (T (T (T (C h19 (T (T (h (M v3 (M y v327)) y v3) (C (T (T (T (T (T (T (T (C h19 (T (T (T (T (T (T (T (T (T (T (T (C h4 (C h19 (T (T (C h4 (C h19 h308)) (C h4 (C h19 h307))) (C h4 (T h322 h309))))) (C h4 (C h19 (C h4 h244)))) (C (T h326 (C (R v324) (T (h v0 y v3) (C h325 h326)))) h325)) (S (h v0 v324 v323))) h177) h184) h259) h320) h317) h316) h315) h314)) h322) h309) h241) h225) h219) h153) h112) (T (T (T h43 h42) h111) h110))) (C h17 (T h101 h68)))) (C h19 (T (C h17 h36) (C h17 h20)))) (C (T h48 (C (R v46) (T (h z v1 y) (C h47 h48)))) h47)) (S (h z v46 v45))) h44)) (C h38 h37)))))) h4)) (S (h v3 z v3))

