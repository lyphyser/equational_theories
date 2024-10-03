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
theorem Equation1571_implies_Equation3161 (G: Type _) [Magma G] (h: Equation1571 G) : Equation3161 G := fun x y z =>
  let v0 := M y y
  let v1 := M v0 z
  let v2 := M v1 x
  let v3 := M v2 z
  have h4 := h z v3 v2
  have h5 := S h4
  let v6 := M z v2
  have h7 := h v6 v1 v0
  have h8 := h v0 v0 (M y (M z y))
  have h9 := h z y y
  have h10 := R v0
  let v11 := M v0 v1
  have h12 := h v1 v1 v11
  have h13 := S h12
  have h14 := h v0 v0 z
  have h15 := R v1
  have h16 := C h14 (C h15 h14)
  let v17 := M v1 v0
  have h18 := h (M v0 v17) v0 v3
  have h19 := S h18
  have h20 := R v3
  have h21 := S h14
  have h22 := C h21 (C h15 h21)
  have h23 := C (T h12 h22) h20
  let v24 := M v2 v3
  let v25 := M v1 v3
  have h26 := h v25 v25 (M v1 v24)
  have h27 := S h26
  have h28 := h v2 v1 v3
  have h29 := h v2 v0 z
  have h30 := S h29
  have h31 := R v25
  have h32 := h v0 v1 v3
  have h33 := C h28 (T h32 (C h31 (T h30 h28)))
  have h34 := C h10 (T (T h33 h27) h23)
  have h35 := h v0 v1 x
  have h36 := S h35
  have h37 := R v2
  have h38 := C h36 (C h37 h36)
  let v39 := M v0 x
  have h40 := h v2 v2 (M v1 v39)
  let v41 := M v0 v3
  have h42 := R v41
  have h43 := C h42 (T (T h40 h38) h34)
  have h44 := T (T (T h43 h19) h16) h13
  have h45 := R z
  have h46 := R v6
  have h47 := C h46 (T (T (C h45 h44) (C h9 (C h10 h9))) (S h8))
  have h48 := h v41 z v2
  have h49 := C h15 (T h48 h47)
  have h50 := R v17
  let v51 := M v3 v2
  have h52 := R v51
  have h53 := C h52 (C h20 (T (C h50 (T h29 h49)) (S h7)))
  have h54 := h v17 v3 v2
  have h55 := h v17 z v3
  have h56 := S h55
  have h57 := S h54
  have h58 := S h48
  have h59 := S h40
  have h60 := C h35 (C h37 h35)
  have h61 := S h32
  have h62 := S h28
  have h63 := C h62 (T (C h31 (T h62 h29)) h61)
  have h64 := C (T h16 h13) h20
  have h65 := C h10 (T (T h64 h26) h63)
  have h66 := C h42 (T (T h65 h60) h59)
  have h67 := T (T (T h12 h22) h18) h66
  have h68 := S h9
  have h69 := C h46 (T (T h8 (C h68 (C h10 h68))) (C h45 h67))
  have h70 := C h15 (T h69 h58)
  have h71 := C h52 (C h20 (T h7 (C h50 (T h70 h30))))
  have h72 := C (T (T h4 h71) h57) h20
  have h73 := h z v1 x
  have h74 := S h73
  have h75 := C h74 (C h37 h74)
  let v76 := M z x
  have h77 := h v2 v2 (M v1 v76)
  have h78 := T (T h77 h75) h72
  have h79 := T h77 h75
  have h80 := C h79 (C h45 h78)
  let v81 := M v2 v6
  have h82 := h v81 x v3
  have h83 := S h82
  have h84 := S h77
  have h85 := C h73 (C h37 h73)
  have h86 := C (T (T h54 h53) h5) h20
  have h87 := T (T h86 h85) h84
  have h88 := T h85 h84
  have h89 := C h88 (C h45 h87)
  have h90 := C (T h55 h89) h20
  have h91 := T (T (T h77 h75) h72) h90
  have h92 := R x
  have h93 := C h92 h91
  have h94 := h x v0 z
  have h95 := S h94
  have h96 := C h95 (C h15 h95)
  let v97 := M x z
  have h98 := h v1 v1 (M v0 v97)
  let v99 := M x v3
  have h100 := R v99
  have h101 := C h100 (T (T h98 h96) h93)
  have h102 := T (T (T (T (T (T h101 h83) h80) h56) h54) h53) h5
  have h103 := C h37 h102
  have h104 := S h98
  have h105 := C h94 (C h15 h94)
  have h106 := C (T h80 h56) h20
  have h107 := T (T (T h106 h86) h85) h84
  have h108 := C h92 h107
  have h109 := C h100 (T (T h108 h105) h104)
  have h110 := h v81 v2 v3
  have h111 := S h110
  have h112 := h v2 v3 v3
  have h113 := S h112
  have h114 := h v2 v2 z
  let v115 := M v3 v3
  have h116 := R v115
  have h117 := C h116 h114
  have h118 := T h117 h113
  have h119 := C h118 (T (C h116 (T (T h117 h113) h114)) h113)
  have h120 := h v115 v115 v2
  let v121 := M v2 v0
  have h122 := h v115 v121 v2
  have h123 := S h122
  have h124 := S h114
  have h125 := C h116 h124
  have h126 := T h112 h125
  have h127 := R v121
  have h128 := h v41 v2 v2
  have h129 := S h128
  let v130 := M v2 v1
  have h131 := h v130 v2 v3
  have h132 := S h131
  have h133 := R v130
  have h134 := C h133 h103
  have h135 := h v99 v2 v1
  have h136 := R v24
  have h137 := C h136 (C h37 (T h135 h134))
  have h138 := h x v2 v3
  let v139 := M v2 v2
  have h140 := R v139
  have h141 := C h140 (T (T (T h138 h137) h132) (C h37 h67))
  have h142 := C h15 (T (T (T h141 h129) h48) h47)
  have h143 := S h138
  have h144 := S h135
  have h145 := T (T (T (T (T (T h4 h71) h57) h55) h89) h82) h109
  have h146 := C h37 h145
  have h147 := C h133 h146
  have h148 := C h136 (C h37 (T h147 h144))
  have h149 := C h140 (T (T (T (C h37 h44) h131) h148) h143)
  have h150 := h v0 z v3
  have h151 := S h150
  have h152 := h v41 v3 v2
  have h153 := S h152
  have h154 := C (T (T h131 h148) h143) h91
  have h155 := C h20 (T (T (T (T (T (T (T h154 h108) h105) h104) h12) h22) h18) h66)
  have h156 := C h52 h155
  have h157 := h v130 v3 v2
  have h158 := T (T (T (T (T (T (T h138 h137) h132) h157) h156) h153) h128) h149
  have h159 := C h79 (T (C h45 h158) (C h45 (T h141 h129)))
  have h160 := C (T h159 h151) h20
  have h161 := T (T h160 h128) h149
  have h162 := C (T h26 h63) (T (T (T (C h15 h161) h142) h70) h30)
  let v163 := M v2 v76
  have h164 := h v163 v1 v3
  have h165 := S h157
  have h166 := C (T (T h138 h137) h132) h107
  have h167 := C h20 (T (T (T (T (T (T (T h43 h19) h16) h13) h98) h96) h93) h166)
  have h168 := C h52 h167
  have h169 := T (T (T (T (T (T (T h141 h129) h152) h168) h165) h131) h148) h143
  have h170 := C h88 (T (C h45 (T h128 h149)) (C h45 h169))
  have h171 := C (T (T (T h150 h170) h164) h162) (T (T (T (T h150 h170) h164) h162) (C h127 h126))
  let v172 := M v0 v0
  have h173 := h v172 v172 y
  have h174 := S h173
  have h175 := h y y y
  have h176 := S h175
  have h177 := R v172
  have h178 := C h177 h176
  have h179 := h y v0 v0
  have h180 := C (T h179 h178) (T h179 (C h177 (T (T h176 h179) h178)))
  have h181 := C h136 (T (T (T (T (T (T (T h180 h174) h171) h123) h120) h119) (C h37 h78)) (C h37 h90))
  have h182 := T (T (T h181 h111) h82) h109
  have h183 := C h37 h182
  have h184 := S h179
  have h185 := C h177 h175
  have h186 := C (T h185 h184) (T (C h177 (T (T h185 h184) h175)) h184)
  have h187 := S h164
  have h188 := C (T h150 h170) h20
  have h189 := T (T h141 h129) h188
  have h190 := C h15 (T (T (T h69 h58) h128) h149)
  have h191 := C (T h33 h27) (T (T (T h29 h49) h190) (C h15 h189))
  have h192 := C (T (T (T h191 h187) h159) h151) (T (T (T (T (C h127 h118) h191) h187) h159) h151)
  have h193 := S h120
  have h194 := C h126 (T h112 (C h116 (T (T h124 h112) h125)))
  have h195 := C h136 (T (T (T (T (T (T (T (C h37 h106) (C h37 h87)) h194) h193) h122) h192) h173) h186)
  have h196 := h v81 v0 v3
  have h197 := S h196
  have h198 := h v24 v2 v0
  have h199 := S h198
  have h200 := T (T (T h101 h83) h110) h195
  have h201 := C h37 h200
  have h202 := T h146 h201
  have h203 := C h127 h202
  have h204 := C h20 (T h203 h199)
  have h205 := T (T (T h122 h192) h173) h186
  have h206 := C h205 (T (T (T (T (T h204 h124) h77) h75) h72) h90)
  have h207 := h v121 v3 v3
  have h208 := h v25 v1 v2
  have h209 := S h208
  let v210 := M v1 v2
  have h211 := R v210
  have h212 := C h211 (T (T (T h4 h71) h57) (C h15 (T h32 (C h31 h30))))
  have h213 := T (T (T (T (T h138 h137) h132) h157) h156) h153
  have h214 := C h213 (T (T (T (T (T h212 h209) h26) h63) h207) h206)
  have h215 := h v2 v2 v3
  have h216 := S h215
  have h217 := S h207
  have h218 := T h183 h103
  have h219 := C h127 h218
  have h220 := C h20 (T h198 h219)
  have h221 := T (T (T h180 h174) h171) h123
  have h222 := C h221 (T (T (T (T (T h106 h86) h85) h84) h114) h220)
  have h223 := C h10 h91
  have h224 := h v2 v3 v1
  have h225 := S h224
  have h226 := h v0 v2 z
  have h227 := h v0 v3 v1
  have h228 := S h227
  let v229 := M v3 v1
  have h230 := R v229
  have h231 := C h228 (T (C h230 (T h228 h226)) h225)
  have h232 := h v229 v229 (M v3 v11)
  have h233 := C h20 h44
  have h234 := h v1 v1 x
  have h235 := h v210 x z
  have h236 := S h235
  have h237 := C h211 (T (T (T (C h15 (T (C h31 h29) h61)) h54) h53) h5)
  have h238 := T (T (T (T (T h152 h168) h165) h131) h148) h143
  have h239 := C h238 (T (T (T (T (T h222 h217) h33) h27) h208) h237)
  have h240 := T (T (T (T (T (T h4 h71) h57) h55) h89) h196) h239
  have h241 := R v97
  have h242 := C h20 (T (T (T (T (T (C h37 (T (C h241 h240) h236)) (S h234)) h98) h96) h93) h166)
  have h243 := h v97 v2 z
  have h244 := T (T (T (T (T (T (T (T h243 h242) h155) h233) h232) h231) h223) h222) h217
  have h245 := C h244 h202
  have h246 := C h136 (C h37 (T h245 h199))
  have h247 := h v97 v2 v3
  have h248 := C (T (T h247 h246) h216) (T (T (T h214 h197) h110) h195)
  have h249 := h v81 v3 v3
  have h250 := S h249
  have h251 := C h20 h90
  have h252 := C h20 h78
  have h253 := h v51 v0 v2
  have h254 := S h253
  have h255 := C h20 (T h245 h219)
  have h256 := S h243
  have h257 := T (T (T (T (T (T h214 h197) h80) h56) h54) h53) h5
  have h258 := C h20 (T (T (T (T (T h154 h108) h105) h104) h234) (C h37 (T h235 (C h241 h257))))
  have h259 := C h20 h67
  have h260 := S h232
  have h261 := S h226
  have h262 := C h227 (T h224 (C h230 (T h261 h227)))
  have h263 := C h10 h107
  have h264 := T (T (T (T (T (T (T (T h207 h206) h263) h262) h260) h259) h167) h258) h256
  have h265 := C h264 h218
  have h266 := h v24 v3 v0
  let v267 := M v3 z
  have h268 := h v267 v3 v0
  have h269 := S h268
  have h270 := R v267
  have h271 := C h270 (T (T (T (T (C h20 (T (T (T (C h264 h240) h248) h183) h103)) h122) h192) h173) h186)
  have h272 := h v121 v3 z
  have h273 := S h247
  have h274 := C h136 (C h37 (T h198 h265))
  have h275 := C h20 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h106 h86) h85) h84) h215) h274) h273) h243) h242) h155) h233) h232) h231) h223) h222) h217) h272) h271)
  let v276 := M v3 v0
  have h277 := R v276
  have h278 := C h277 (T (T (T (C h20 (T (C h230 h226) h225)) h252) h251) h275)
  have h279 := h v229 v3 v0
  have h280 := C h52 (T (T (T (C h20 (T (T (T (C h277 (T (T (T (T (T (T (T (T (T (T (T h215 h274) h273) h243) h242) h155) h233) h279) h278) h269) (C h20 h145)) (C h20 h200))) (S h266)) h198) h265)) h255) h204) h124)
  have h281 := h v276 v3 v2
  have h282 := C h10 (T h281 h280)
  have h283 := C h261 (C h20 h261)
  have h284 := h v3 v3 v130
  have h285 := C (T (T (T (T (T (T (T (T h215 h274) h273) h243) h242) h155) h233) h232) h231) (T (T h284 h283) h282)
  have h286 := C h221 (T (T (T h285 h254) h252) h251)
  let v287 := M v0 v24
  have h288 := h v287 v3 v3
  have h289 := S h288
  have h290 := S h284
  have h291 := C h226 (C h20 h226)
  have h292 := S h281
  have h293 := S h279
  have h294 := C h20 h87
  have h295 := C h20 h106
  have h296 := S h272
  have h297 := T (T h215 h274) h273
  have h298 := C h297 (T (T (T h181 h111) h196) h239)
  have h299 := C h270 (T (T (T (T h180 h174) h171) h123) (C h20 (T (T (T h146 h201) h298) (C h244 h257))))
  have h300 := C h20 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h299 h296) h207) h206) h263) h262) h260) h259) h167) h258) h256) h247) h246) h216) h77) h75) h72) h90)
  have h301 := C h277 (T (T (T h300 h295) h294) (C h20 (T h224 (C h230 h261))))
  have h302 := C h20 (T h203 h265)
  have h303 := C h52 (T (T (T h114 h220) h302) (C h20 (T (T (T h245 h199) h266) (C h277 (T (T (T (T (T (T (T (T (T (T (T (C h20 h182) (C h20 h102)) h268) h301) h293) h259) h167) h258) h256) h247) h246) h216)))))
  have h304 := C h10 (T h303 h292)
  have h305 := C (T (T (T (T (T (T (T (T h262 h260) h259) h167) h258) h256) h247) h246) h216) (T (T h304 h291) h290)
  have h306 := C h205 (T (T (T h295 h294) h253) h305)
  have h307 := C (T h249 h306) h20
  have h308 := h v210 v0 z
  have h309 := C (T h286 h250) h20
  have h310 := C (T (T (T (T h26 h63) h207) h206) h263) (T (T (T (T (T (T (T (T (T (T (C h15 h309) (C h15 h106)) (C h15 (T (T (T (T (T (T h86 h85) h84) h40) h38) h34) (C h10 (T (T h64 h208) h237))))) (S h308)) h235) h248) h183) h103) h284) h283) h282)
  have h311 := h v287 v1 v3
  have h312 := C h221 (T (T (T (T (T (T (T (T (T (T (T (T (T h4 h71) h57) h55) h89) h249) h306) h311) h310) h254) h252) h251) h275) (C h20 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h299 h296) h207) h206) h263) h262) h260) h259) h167) h258) h256) h247) h246) h216) h77) h75) h72) h90) h307)))
  have h313 := S h311
  have h314 := C (T (T (T (T h223 h222) h217) h33) h27) (T (T (T (T (T (T (T (T (T (T h304 h291) h290) h146) h201) h298) h236) h308) (C h15 (T (T (T (T (T (T (C h10 (T (T h212 h209) h23)) h65) h60) h59) h77) h75) h72))) (C h15 h90)) (C h15 h307))
  have h315 := C h205 (T (T (T (T (T (T (T (T (T (T (T (T (T (C h20 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h309 h106) h86) h85) h84) h215) h274) h273) h243) h242) h155) h233) h232) h231) h223) h222) h217) h272) h271)) h300) h295) h294) h253) h314) h313) h286) h250) h80) h56) h54) h53) h5)
  have h316 := h v51 v3 v2
  have h317 := S h316
  have h318 := h v163 v2 v3
  have h319 := S h318
  have h320 := h v130 v1 v2
  have h321 := S h320
  have h322 := T (T (T h146 h201) h298) h236
  have h323 := C h322 (C (T (T (T (T (T (T (T (T h4 h71) h57) h55) h89) h249) h306) h288) h315) (T (T (T (T (T (T (T (T (T (T (T (T h4 h71) h57) h55) h89) h249) h306) h288) h315) h98) h96) h93) h166))
  let v324 := M v3 (M z z)
  have h325 := h v324 v3 v2
  have h326 := T (T (T h235 h248) h183) h103
  have h327 := C h326 (C (T (T (T (T (T (T (T (T h312 h289) h286) h250) h80) h56) h54) h53) h5) (T (T (T (T (T (T (T (T (T (T (T (T h154 h108) h105) h104) h312) h289) h286) h250) h80) h56) h54) h53) h5))
  have h328 := T h320 h327
  have h329 := C h328 h37
  have h330 := C h20 h329
  have h331 := T (T (T (T (T (T (T (T (T h4 h71) h57) h55) h89) h249) h306) h311) h310) h254
  have h332 := h v81 z v3
  have h333 := T (T (T (T h312 h289) h311) h310) h305
  have h334 := C h333 (T (T (T (T (T (T (T (T (T h154 h108) h105) h104) h312) h289) h286) h250) h332) (C h88 (T (T (T (T (T (T (T (C h331 (T (T (T (T (T (T (T (T (T h106 h86) h85) h84) h215) h274) h273) h243) h242) h330)) (S h325)) h323) h321) h157) h156) h153) h188)))
  have h335 := C h331 (T (T (C h20 h158) (C h20 h189)) (C h20 (T (T (T (T (T (T (T h160 h152) h168) h165) h320) (C h326 (T (T (T h334 h319) h159) h151))) h281) h280)))
  have h336 := h (M z (M v3 x)) v2 v3
  have h337 := S h336
  have h338 := T h323 h321
  have h339 := C h338 h37
  have h340 := C h20 h339
  have h341 := T (T (T (T (T (T (T (T (T h253 h314) h313) h286) h250) h80) h56) h54) h53) h5
  have h342 := C (T (T (T (T h285 h314) h313) h288) h315) (T (T (T (T (T (T (T (T (T (C h79 (T (T (T (T (T (T (T h160 h152) h168) h165) h320) h327) h325) (C h341 (T (T (T (T (T (T (T (T (T h340 h258) h256) h247) h246) h216) h77) h75) h72) h90)))) (S h332)) h249) h306) h288) h315) h98) h96) h93) h166)
  have h343 := C h341 (T (T (C h20 (T (T (T (T (T (T (T h303 h292) (C h322 (T (T (T h150 h170) h318) h342))) h321) h157) h156) h153) h188)) (C h20 h161)) (C h20 h169))
  have h344 := C (T (T (T (T h311 h310) h254) h316) h343) h20
  have h345 := C h37 h344
  have h346 := C h37 (T (T (T (T (T (T (T h142 h70) h30) h77) h75) h72) h90) h307)
  have h347 := h v139 v1 x
  have h348 := C (T (T (T (T (T (T (T (T (T h4 h71) h57) h55) h89) h249) h306) h311) h310) h305) (T (T (T (T (T (T (T (T h180 h174) h171) h123) h120) h119) h347) h346) h345)
  let v349 := M z v0
  have h350 := S h347
  have h351 := C h37 (T (T (T (T (T (T (T h309 h106) h86) h85) h84) h29) h49) h190)
  have h352 := C (T (T (T (T h335 h317) h253) h314) h313) h20
  have h353 := C h37 h352
  have h354 := C (T (T (T (T (T (T (T (T (T h285 h314) h313) h286) h250) h80) h56) h54) h53) h5) (T (T (T (T (T (T (T (T h353 h351) h350) h194) h193) h122) h192) h173) h186)
  have h355 := C (T h336 h354) h20
  have h356 := h v349 x v3
  have h357 := h v97 v3 v3
  have h358 := C (T h348 h337) h20
  have h359 := h v349 v0 v3
  have h360 := C (T (T (T (T (T (T (T (T (T h268 h301) h293) h259) h167) h258) h256) h247) h246) h216) (T (T (T (T (T (T (T (T (T (T (T (T (T (C h20 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (C h100 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h4 h71) h57) h55) h89) h249) h306) h311) h310) h254) h316) h343) h336) h354) h359) (C h238 (T (T (T (T (T (T (T (T (T (T (T (C h221 (T (T (T (T (T (T (T (T (T h358 h352) h309) h106) h86) h85) h84) h114) h220) h302)) (S h357)) h247) h246) h216) h77) h75) h72) h90) h307) h344) h355)))) (S h356)) h348) h337) h335) h317) h253) h314) h313) h288) h315) h98) h96) h93) h166) h329)) h340) h258) h256) h247) h246) h216) h77) h75) h72) h90) h307) h344) h355)
  have h361 := h v99 v3 z
  have h362 := C h338 h20
  have h363 := h v324 v3 v3
  T (T (T (T (T (T (T (T (T (T (T (T h138 h137) h132) h320) h327) h363) (C h205 (T (T (T (T (C h322 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h362 h147) h144) h361) h360) (C h37 h358)) h353) h351) h350) h194) h193) h122) h192) h173) h186) h150) h170) h318) h342)) h321) h131) h148) h143))) (h v39 v1 v3)) (C (T (T (T (T (T (T (T (T (T (T (T (T (T h26 h63) h207) h206) h263) h262) h260) h259) h167) h258) h256) h247) h246) h216) (T (T (T (T (T (T (T (T (T (T (T (T (T (T (C h333 (T (T (T (T (T (C (T (C h221 (T (T (T (T h138 h137) h132) h320) (C h326 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h334 h319) h159) h151) h180) h174) h171) h123) h120) h119) h347) h346) h345) (C h37 h355)) (C (T (T (T (T (T (T (T (T (T h215 h274) h273) h243) h242) h155) h233) h279) h278) h269) (T (T (T (T (T (T (T (T (T (T (T (T (T h358 h352) h309) h106) h86) h85) h84) h215) h274) h273) h243) h242) h330) (C h20 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h339 h154) h108) h105) h104) h312) h289) h311) h310) h254) h316) h343) h336) h354) h356) (C h100 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (C h213 (T (T (T (T (T (T (T (T (T (T (T h358 h352) h309) h106) h86) h85) h84) h215) h274) h273) h357) (C h205 (T (T (T (T (T (T (T (T (T h255 h204) h124) h77) h75) h72) h90) h307) h344) h355)))) (S h359)) h348) h337) h335) h317) h253) h314) h313) h286) h250) h80) h56) h54) h53) h5))))))) (S h361)) h135) h134) (C h328 h20))))) (S h363)) h20) h362) h147) h144) h361) h360)) (S (h v349 v2 v3))) h348) h337) h335) h317) h253) h314) h313) h288) h315) h98) h96) h93) h166))) (C h297 (T (T (T (T (T (T (T (T (T h154 h108) h105) h104) h312) h289) h286) h250) h196) h239))) h248) h183) h103

