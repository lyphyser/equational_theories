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
theorem Equation2349_implies_Equation3417 (G: Type _) [Magma G] (h: Equation2349 G) : Equation3417 G := fun x y z =>
  have h0 := h x z y
  have h1 := S h0
  let v2 := M y x
  let v3 := M z v2
  let v4 := M z v3
  let v5 := M x (M x (M x x))
  have h6 := h y v5 v4
  have h7 := S h6
  have h8 := R v4
  have h9 := R v5
  have h10 := h x x x
  have h11 := C (T h10 (C h9 (T h10 (C h9 h0)))) h8
  have h12 := C h8 (T h11 h7)
  have h13 := T h12 h1
  have h14 := R y
  have h15 := C h14 h13
  have h16 := R z
  have h17 := C h16 h15
  have h18 := C h16 h17
  have h19 := S h10
  have h20 := C (T (C h9 (T (C h9 h1) h19)) h19) h8
  have h21 := C h8 (T h6 h20)
  let v22 := M x (M x (M v2 v2))
  have h23 := h x v22 y
  have h24 := h v2 x v2
  have h25 := R v22
  let v26 := M x y
  let v27 := M x (M x (M v26 v26))
  have h28 := h y v27 x
  have h29 := S h28
  have h30 := R x
  have h31 := h v26 x v26
  have h32 := R v27
  have h33 := C (T h31 (C h32 h31)) h30
  have h34 := R v26
  have h35 := C h34 h13
  have h36 := T (T h35 h33) h29
  have h37 := R v2
  have h38 := T h0 h21
  have h39 := C h34 h38
  have h40 := S h31
  have h41 := C (T (C h32 h40) h40) h30
  have h42 := T (T (T (T (T (C h37 (T (T (T (T h11 h7) h28) h41) h39)) (C h37 h36)) (C (T h24 (C h25 h24)) h14)) (S h23)) h0) h21
  have h43 := C h14 h42
  have h44 := C h16 h43
  have h45 := C h16 h44
  have h46 := T (T h28 h41) h39
  have h47 := S h24
  have h48 := T (T (T (T (T h12 h1) h23) (C (T (C h25 h47) h47) h14)) (C h37 h46)) (C h37 (T (T (T (T h35 h33) h29) h6) h20))
  have h49 := C h14 h48
  have h50 := C h16 h49
  have h51 := C h14 h38
  have h52 := C h16 h51
  have h53 := h v3 x z
  have h54 := S h53
  have h55 := C h34 h42
  have h56 := C h30 (T (T (T (T (T h55 h35) h33) h29) h6) h20)
  have h57 := C h34 h48
  have h58 := C h30 h57
  have h59 := C h30 h46
  have h60 := T (T h59 h58) h56
  have h61 := C h60 h16
  let v62 := M v26 z
  have h63 := h v62 v3 v4
  have h64 := S h63
  have h65 := h v62 v4 v4
  have h66 := S h65
  have h67 := C h30 h36
  have h68 := C h30 h55
  have h69 := C h30 (T (T (T (T (T h11 h7) h28) h41) h39) h57)
  have h70 := T (T h69 h68) h67
  have h71 := C h70 h16
  have h72 := C h8 (T h53 h71)
  have h73 := C h8 (C h8 h72)
  let v74 := M v4 (M v4 v3)
  have h75 := R v74
  have h76 := h v2 v4 z
  have h77 := C (C h16 (C h16 (S h76))) h75
  have h78 := h z z v74
  have h79 := T (T h78 h77) h73
  have h80 := C h8 (T (C h79 h8) h66)
  let v81 := M z v4
  have h82 := R v81
  have h83 := h v2 z z
  have h84 := C (C h16 (C h16 (S h83))) h82
  have h85 := h z z v81
  have h86 := S h78
  have h87 := C (C h16 (C h16 h76)) h75
  have h88 := C h8 (T h61 h54)
  have h89 := C h8 (C h8 h88)
  have h90 := R v3
  have h91 := C h90 (T (T (T (T (T h89 h87) h86) h85) h84) h80)
  have h92 := C h90 h91
  have h93 := C h92 h8
  let v94 := M v4 v62
  let v95 := M v4 v94
  have h96 := h v95 v3 v4
  have h97 := C h16 (T (T (T (T (T (T h96 h93) h64) h61) h54) h52) h50)
  have h98 := S h96
  have h99 := S h85
  have h100 := C (C h16 (C h16 h83)) h82
  have h101 := T (T h89 h87) h86
  have h102 := C h8 (T h65 (C h101 h8))
  have h103 := C h90 (T (T (T (T (T h102 h100) h99) h78) h77) h73)
  have h104 := C h90 h103
  have h105 := C h104 h8
  have h106 := T (T h97 h45) h18
  have h107 := C h79 h106
  have h108 := C h16 (T (T (T (T h107 h66) h63) h105) h98)
  have h109 := C h16 (T (T (T (T (T (T h44 h17) h53) h71) h63) h105) h98)
  have h110 := C h16 h50
  have h111 := C h16 h52
  have h112 := T (T h111 h110) h109
  have h113 := C h101 h112
  have h114 := h v95 v3 z
  have h115 := S h114
  have h116 := C (T (T (T h107 h66) h61) h54) h112
  have h117 := h v94 z v4
  have h118 := C h90 (T h117 h116)
  have h119 := C h90 h79
  have h120 := h v3 x v3
  have h121 := S h120
  let v122 := M x (M x (M v3 v3))
  have h123 := R v122
  have h124 := C (T (C h123 h121) h121) h16
  have h125 := h v2 v122 z
  have h126 := T (T (T (T h125 h124) h119) h91) h118
  have h127 := C h126 h101
  have h128 := C h37 h79
  let v129 := M v2 z
  have h130 := h v129 v2 v2
  have h131 := S h130
  have h132 := C h37 h101
  have h133 := C h37 h132
  have h134 := S h125
  have h135 := C (T h120 (C h123 h120)) h16
  have h136 := C h90 h101
  have h137 := S h117
  have h138 := C (T (T (T h53 h71) h65) h113) h106
  have h139 := C h90 (T h138 h137)
  have h140 := T (T (T (T h139 h103) h136) h135) h134
  have h141 := C h140 h79
  have h142 := C h37 (T h114 h141)
  have h143 := T h142 h133
  have h144 := C h37 h143
  have h145 := C h37 h144
  have h146 := C h37 (T (T (T (T h53 h71) h63) h105) h98)
  have h147 := C h37 h146
  have h148 := C h37 h147
  let v149 := M v2 v3
  let v150 := M v2 v149
  have h151 := R v150
  have h152 := h v2 v2 z
  have h153 := C (T (C h25 (T (C h25 (S h152)) h47)) h47) h151
  have h154 := h z v22 v150
  have h155 := h v95 z z
  have h156 := S h155
  have h157 := S h154
  have h158 := C (T h24 (C h25 (T h24 (C h25 h152)))) h151
  have h159 := C h37 (T (T (T (T h96 h93) h64) h61) h54)
  have h160 := C h37 h159
  have h161 := C h37 h160
  have h162 := C h37 (T h127 h115)
  have h163 := C h37 h128
  have h164 := T h163 h162
  have h165 := C h37 h164
  have h166 := C h37 h165
  have h167 := C h16 (T (T (T (T h96 h93) h64) h65) h113)
  have h168 := C (T (T (T h111 h110) h109) h167) (T (T (T h166 h161) h158) h157)
  have h169 := C h8 (T h168 h156)
  have h170 := C (T (T (T (T (T (T (T h169 h89) h87) h86) h154) h153) h148) h145) h37
  let v171 := M v2 v129
  have h172 := h (M v2 v171) v4 v2
  have h173 := h v171 v4 v2
  have h174 := S h173
  have h175 := C (T (T (T h108 h97) h45) h18) (T (T (T h154 h153) h148) h145)
  have h176 := C h8 (T (T (T (T (T (T (T h172 h170) h131) h128) h127) h115) h155) h175)
  have h177 := C h90 (T (T (T (T (T (T (T (T (T h176 h169) h89) h87) h86) h85) h84) h80) h117) h116)
  have h178 := C h8 (T h147 h144)
  have h179 := C h90 h178
  have h180 := S h172
  have h181 := C h8 (T h155 h175)
  have h182 := C (T (T (T (T (T (T (T h166 h161) h158) h157) h78) h77) h73) h181) h37
  have h183 := C h8 (T (T (T (T (T (T (T h168 h156) h114) h141) h132) h130) h182) h180)
  have h184 := C h8 (T (T (T (T (T (T (T (T h166 h161) h158) h157) h78) h77) h73) h181) h183)
  have h185 := C (T (T (T (T (T (T (T h53 h71) h63) h105) h98) h155) h175) h184) (T (T (T (T (T (T h179 h177) h139) h103) h136) h135) h134)
  have h186 := C h8 (T h165 h160)
  have h187 := C h90 h186
  have h188 := C h90 h187
  have h189 := C h90 (T (T (T (T (T (T (T (T (T h138 h137) h102) h100) h99) h78) h77) h73) h181) h183)
  have h190 := C h90 (T h118 h189)
  have h191 := C h90 (C h90 h72)
  have h192 := T (T (T (T h191 h190) h188) h185) h174
  have h193 := C h37 h192
  have h194 := C h16 (T (T (T (T (T (T (T (T (T (T (T h193 h172) h170) h131) h128) h127) h115) h96) h93) h64) h65) h113)
  have h195 := C h90 (C h90 h88)
  have h196 := C h90 (T h177 h139)
  have h197 := C h90 h179
  have h198 := C h8 (T (T (T (T (T (T (T (T h176 h169) h89) h87) h86) h154) h153) h148) h145)
  have h199 := C (T (T (T (T (T (T (T h198 h168) h156) h96) h93) h64) h61) h54) (T (T (T (T (T (T h125 h124) h119) h91) h118) h189) h187)
  have h200 := C h126 (T (T (T (T h176 h169) h89) h87) h86)
  have h201 := C h37 (T h200 h141)
  have h202 := C h37 h178
  have h203 := C h37 h202
  have h204 := C h37 h186
  have h205 := C h140 (T (T (T (T h78 h77) h73) h181) h183)
  have h206 := C h37 (T (T (T (T (T (T (T h193 h172) h170) h131) h128) h127) h205) h204)
  have h207 := C h37 (T (T (T (T (T (T (T (T h206 h203) h201) h133) h173) h199) h197) h196) h195)
  have h208 := T (T (T (T h173 h199) h197) h196) h195
  have h209 := C h37 h208
  have h210 := C h37 (T (T (T (T (T (T (T h202 h200) h141) h132) h130) h182) h180) h209)
  have h211 := C h37 h204
  have h212 := C h37 (T h127 h205)
  have h213 := C h90 (T (T (T (T h43 h15) h125) h124) h119)
  have h214 := C h90 h49
  have h215 := C h90 h51
  have h216 := C h37 (T (T (T (T (T (T (T (T (T (T (T h215 h214) h213) h92) h190) h188) h185) h174) h163) h212) h211) h210)
  have h217 := T h216 h207
  have h218 := C h16 h217
  let v219 := M v3 v2
  let v220 := M v2 v219
  have h221 := h v220 v4 v4
  have h222 := S h221
  have h223 := C h90 h15
  have h224 := C h90 h43
  have h225 := C h90 (T (T (T (T h136 h135) h134) h51) h49)
  have h226 := C h37 (T (T (T (T (T (T (T (T (T (T (T h206 h203) h201) h133) h173) h199) h197) h196) h104) h225) h224) h223)
  have h227 := C h37 (T (T (T (T (T (T (T (T h191 h190) h188) h185) h174) h163) h212) h211) h210)
  have h228 := T h227 h226
  have h229 := C h8 h228
  have h230 := C h8 (T (T (T (T (T (T (T (T (T h198 h168) h156) h114) h141) h132) h130) h182) h180) h209)
  have h231 := C h8 (T (T (T (T (T (T (T (T h172 h170) h131) h128) h127) h115) h155) h175) h184)
  have h232 := C (T (T (T (T (T (T (T (T h78 h77) h73) h181) h183) h231) h230) h229) (C h8 (T (T (T (T (T (T (T (T (T (T (T (T (T h216 h207) h193) h172) h170) h131) h128) h127) h115) h155) h175) h184) (C h8 (T h231 h230))) (C h8 h229)))) (T (T (T (T (T h218 h194) h108) h97) h45) h18)
  have h233 := C h16 (T h232 h222)
  have h234 := C h16 h228
  have h235 := C h16 (T (T (T (T (T (T (T (T (T (T (T h107 h66) h63) h105) h98) h114) h141) h132) h130) h182) h180) h209)
  have h236 := C h8 (T (T (T (T (T (T (T (T h198 h168) h156) h114) h141) h132) h130) h182) h180)
  have h237 := C h8 (T (T (T (T (T (T (T (T (T h193 h172) h170) h131) h128) h127) h115) h155) h175) h184)
  have h238 := C h8 h217
  have h239 := C (T (T (T (T (T (T (T (T (C h8 (T (T (T (T (T (T (T (T (T (T (T (T (T (C h8 h238) (C h8 (T h237 h236))) h198) h168) h156) h114) h141) h132) h130) h182) h180) h209) h227) h226)) h238) h237) h236) h176) h169) h89) h87) h86) (T (T (T (T (T h111 h110) h109) h167) h235) h234)
  have h240 := C h37 (T (T h238 h237) h236)
  have h241 := C h37 (T (T (T (T (T (T (T h240 h200) h141) h132) h130) h182) h180) h209)
  have h242 := C h37 (T (T h231 h230) h229)
  have h243 := C h37 (T (T (T (T (T (T (T (T (T h216 h207) h193) h172) h170) h131) h128) h127) h205) h242)
  have h244 := T (T (T (T (T (T (T (T (T (T (T (T (T h243 h241) h206) h203) h201) h133) h173) h199) h197) h196) h104) h225) h224) h223
  have h245 := C h37 h244
  have h246 := C h16 (T (T h245 h221) h239)
  have h247 := C h37 (T (T (T (T (T (T (T (T (T h240 h200) h141) h132) h130) h182) h180) h209) h227) h226)
  have h248 := C h37 (T (T (T (T (T (T (T h193 h172) h170) h131) h128) h127) h205) h242)
  have h249 := T (T (T (T (T (T (T (T (T (T (T (T (T h215 h214) h213) h92) h190) h188) h185) h174) h163) h212) h211) h210) h248) h247
  have h250 := C h37 h249
  have h251 := C h8 h178
  have h252 := C h37 (T (T (T h245 h216) h207) h193)
  have h253 := C h37 h250
  have h254 := C h8 (T (T (T (T (T (T (T (T (T (T (T h253 h252) h166) h161) h158) h157) h78) h77) h73) h181) h183) h186)
  have h255 := C h16 (T (T (T (T (T (T (T (T (T (T (T (T (T (T h254 h251) h198) h168) h156) h114) h141) h132) h130) h182) h180) h209) h227) h226) h250)
  have h256 := C h37 h245
  have h257 := C h37 (T (T (T h209 h227) h226) h250)
  have h258 := C h8 (T (T (T (T (T (T (T (T (T (T (T h178 h176) h169) h89) h87) h86) h154) h153) h148) h145) h257) h256)
  have h259 := C h8 h186
  have h260 := C h16 (T h246 h233)
  have h261 := C h16 h255
  have h262 := C h8 h249
  have h263 := C h16 h262
  have h264 := C h16 h263
  have h265 := C h16 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h264 h261) h260) h232) h222) h216) h207) h193) h172) h170) h131) h128) h127) h115) h155) h175) h184) h259) h258)
  have h266 := C h8 (T (T (T (T h191 h104) h225) h224) h223)
  have h267 := C h16 h266
  have h268 := C h16 h267
  have h269 := C h8 h208
  have h270 := C h16 h269
  have h271 := C h16 h270
  have h272 := C h8 h143
  have h273 := C h8 h146
  have h274 := T h273 h272
  have h275 := C h16 h274
  have h276 := C h16 h275
  have h277 := C h16 (T (T h276 h271) h268)
  have h278 := C h8 h159
  have h279 := C h8 h164
  have h280 := T h279 h278
  have h281 := C h16 h280
  have h282 := C h16 h281
  have h283 := C h8 h192
  have h284 := C h16 h283
  have h285 := C h16 h284
  have h286 := C h8 (T (T (T (T h215 h214) h213) h92) h195)
  have h287 := C h16 h286
  have h288 := C h16 h287
  have h289 := C h8 h244
  have h290 := C h16 h289
  have h291 := C h16 h290
  have h292 := C h16 (T (T (T (T (T (T (T (T (T (T (T (T (T (T h245 h216) h207) h193) h172) h170) h131) h128) h127) h115) h155) h175) h184) h259) h258)
  have h293 := C h16 h292
  have h294 := C h16 (T (T h232 h222) h250)
  have h295 := C h16 (T h221 h239)
  have h296 := C h16 (T h295 h294)
  let v297 := M v4 v149
  have h298 := h v297 z z
  have h299 := S h298
  have h300 := C h8 h251
  have h301 := C h37 (T (T (T (T (T (T (T (T (T (T h254 h251) h198) h168) h156) h114) h141) h132) h130) h182) h180)
  have h302 := C h37 h262
  have h303 := C h8 (T (T (T h302 h301) h257) h256)
  have h304 := C h8 (T h303 h254)
  have h305 := C h37 h266
  have h306 := C h37 h269
  have h307 := C h37 h274
  have h308 := T (T h307 h306) h305
  have h309 := C h8 h308
  have h310 := C h8 h309
  have h311 := C h37 h280
  have h312 := C h37 h283
  have h313 := C h37 h286
  have h314 := T (T h313 h312) h311
  have h315 := C h8 h314
  have h316 := C h37 h289
  have h317 := C h37 (T (T (T (T (T (T (T (T (T (T h172 h170) h131) h128) h127) h115) h155) h175) h184) h259) h258)
  have h318 := C h8 (T (T (T h253 h252) h317) h316)
  have h319 := C h8 (T h318 h315)
  have h320 := T (T (T (T (T (T (T (T (T h319 h310) h304) h300) h236) h176) h169) h89) h87) h86
  have h321 := C (T (T (T (T (T (T (T (T (T (T h111 h110) h109) h167) h235) h234) h295) h294) h292) (C h16 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h254 h251) h198) h168) h156) h114) h141) h132) h130) h182) h180) h209) h227) h226) h221) h239) h296) h293) h291))) (C h16 (T (T h288 h285) h282))) h320
  have h322 := C h8 h262
  have h323 := C h8 h322
  have h324 := C h8 h266
  have h325 := C h8 h269
  have h326 := C h8 h272
  have h327 := C h8 h273
  have h328 := T (T (C h8 (T h327 h326)) (C h8 h325)) (C h8 h324)
  have h329 := C h8 h278
  have h330 := C h8 h279
  have h331 := C h8 (T h330 h329)
  have h332 := C h8 h283
  have h333 := C h8 h332
  have h334 := C h8 h286
  have h335 := C h8 h334
  have h336 := C h8 h289
  have h337 := C h8 h336
  have h338 := C h8 (T h309 h303)
  have h339 := C h8 h315
  have h340 := C h8 (T h258 h318)
  have h341 := C h8 h259
  have h342 := T (T (T (T (T (T (T (T (T h78 h77) h73) h181) h183) h231) h341) h340) h339) h338
  have h343 := C (T (T (T (T (T (T (T (T (T (T h277 h265) h255) h246) h233) h218) h194) h108) h97) h45) h18) h342
  have h344 := h v220 v4 v2
  have h345 := C h90 (T (T (T (T (T (T (T (T (T (T (T h302 h301) h166) h161) h158) h157) h78) h77) h73) h181) h183) h186)
  have h346 := C h90 h308
  have h347 := h v149 z v4
  have h348 := S h347
  have h349 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h53 h71) h63) h105) h98) h114) h141) h132) h130) h182) h180) h209) h227) h226) h221) h239) h296) h293) h291) h288) h285) h282) (T (T (T (T (T (T (T (T (T h263 h255) h246) h233) h218) h194) h108) h97) h45) h18)
  have h350 := C h90 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h349 h348) h146) h142) h212) h211) h210) h248) h247) h253) h252) h317) h316) h313) h312) h311)
  have h351 := T (T h275 h270) h267
  have h352 := C h90 h351
  have h353 := C h90 h352
  have h354 := T (T h287 h284) h281
  have h355 := C h90 h354
  have h356 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h276 h271) h268) h264) h261) h260) h232) h222) h216) h207) h193) h172) h170) h131) h128) h127) h115) h96) h93) h64) h61) h54) (T (T (T (T (T (T (T (T (T h111 h110) h109) h167) h235) h234) h295) h294) h292) h290)
  have h357 := C h90 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h322 h319) h310) h304) h300) h236) h176) h169) h89) h87) h86) h154) h153) h148) h145) h257) h256) h243) h241) h206) h203) h201) h162) h159) h347) h356) h355)
  have h358 := T (T (T h327 h326) h325) h324
  have h359 := C h90 h358
  have h360 := T (T (T h334 h332) h330) h329
  have h361 := C h90 h360
  have h362 := C h90 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h352 h349) h348) h146) h142) h212) h211) h210) h248) h247) h253) h252) h166) h161) h158) h157) h78) h77) h73) h181) h183) h231) h341) h340) h339) h338) h336)
  have h363 := C h90 h355
  have h364 := C h90 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h307 h306) h305) h302) h301) h257) h256) h243) h241) h206) h203) h201) h162) h159) h347) h356)
  have h365 := C h90 h314
  have h366 := C h90 (T (T (T (T (T (T (T (T (T (T (T h178 h176) h169) h89) h87) h86) h154) h153) h148) h145) h317) h316)
  have h367 := h v297 v3 z
  have h368 := S h367
  have h369 := C h37 h256
  have h370 := C h37 (T h301 h257)
  have h371 := C h37 h302
  have h372 := C h37 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h371 h370) h369) h245) h216) h207) h193) h172) h170) h131) h128) h127) h115) h155) h175) h184) h259) h258)
  have h373 := C h37 h305
  have h374 := C h37 h306
  have h375 := C h37 h307
  have h376 := C h37 (T (T h375 h374) h373)
  have h377 := C h37 h311
  have h378 := C h37 h312
  have h379 := C h37 h313
  have h380 := C h37 h316
  have h381 := C h37 (T h252 h317)
  have h382 := C h37 h253
  have h383 := C h37 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h323 h321) h299) h273) h272) h269) h266) h262) h254) h251) h198) h168) h156) h114) h141) h132) h130) h182) h180) h209) h227) h226) h250) h382) h381) h380) h379) h378) h377)
  have h384 := C (T (T (T (T (T (T (T (T (T (T h125 h124) h119) h91) h118) h189) h187) h366) h365) h364) h363) (T (T (T (T (T (T (T h383 h376) h372) h301) h166) h161) h158) h157)
  have h385 := C h37 h328
  have h386 := C h37 h385
  have h387 := C h37 (T (T h335 h333) h331)
  have h388 := C h37 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h375 h374) h373) h371) h370) h369) h245) h216) h207) h193) h172) h170) h131) h128) h127) h115) h155) h175) h184) h259) h258) h289) h286) h283) h279) h278) h298) h343) h337)
  have h389 := C h37 (T (T h379 h378) h377)
  have h390 := C h37 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h254 h251) h198) h168) h156) h114) h141) h132) h130) h182) h180) h209) h227) h226) h250) h382) h381) h380)
  have h391 := C h37 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h322 h319) h310) h304) h300) h236) h176) h169) h89) h87) h86) h154) h153) h148) h145) h317) h390) h389) h388) h387)
  have h392 := C h37 h358
  have h393 := C h37 h360
  have h394 := C h37 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h385 h383) h376) h372) h301) h166) h161) h158) h157) h78) h77) h73) h181) h183) h231) h341) h340) h339) h338) h336)
  have h395 := C h37 h387
  have h396 := C (T (T (T (T (T (T (T (T (T (T h353 h350) h346) h345) h179) h177) h139) h103) h136) h135) h134) (T (T (T (T (T (T (T h154 h153) h148) h145) h317) h390) h389) h388)
  have h397 := h (M v4 v297) y v3
  have h398 := S h397
  let v399 := M y v2
  have h400 := R v399
  have h401 := h y x y
  have h402 := S h401
  have h403 := h y y v4
  let v404 := M x (M x (M y y))
  have h405 := R v404
  have h406 := h v4 v404 v399
  have h407 := C (T (T (T (T (T h406 (C (T (C h405 (T (C h405 (T (C (C h14 (C h14 h0)) h8) (S h403))) h402)) h402) h400)) (C h14 (C h14 h51))) (C h14 (C h14 h49))) (C h14 (C h14 (T (T (T (T (T (T (T (T (T (T (T (T (T h43 h15) h125) h124) h119) h91) h118) h189) h187) h366) h365) h364) h363) h362)))) (C h14 (C h14 h361))) (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h391 h386) h384) h368) h273) h272) h269) h266) h262) h254) h251) h198) h168) h156) h96) h93) h64) h61) h54)
  have h408 := C h8 h392
  have h409 := h v297 x z
  let v410 := M y (M y v26)
  have h411 := h x v404 v410
  have h412 := R v410
  have h413 := h y y x
  let v414 := M x (M x v4)
  have h415 := h v414 y y
  have h416 := C h8 (T (T (T (T (T (T (C (T (T (T (T (T (T (T h59 h58) h56) h415) (C (T (T (C h14 (C h14 (C h14 h70))) (C (T h401 (C h405 (T h401 (C h405 h413)))) h412)) (S h411)) (T (T h6 h20) (C h30 h112)))) (C h30 (C h30 (T (T h167 h235) h234)))) (C h30 (C h30 (T (T (T h295 h294) h292) h290)))) (C h30 (C h30 h354))) (T (T (T (T (T (T (T (T (T (T h322 h319) h310) h304) h300) h236) h176) h169) h89) h87) h86)) (S h409)) h367) h396) h395) h394) h393)
  have h417 := C (T (T (T (T (T (T (T (C h30 (C h30 h351)) (C h30 (C h30 (T (T (T h263 h255) h246) h233)))) (C h30 (C h30 (T (T h218 h194) h108)))) (C (T (T h411 (C (T (C h405 (T (C h405 (S h413)) h402)) h402) h412)) (C h14 (C h14 (C h14 h60)))) (T (T (C h30 h106) h11) h7))) (S h415)) h69) h68) h67) (T (T (T (T (T (T (T (T (T (T h78 h77) h73) h181) h183) h231) h341) h340) h339) h338) h336)
  have h418 := C h8 (T (T (T (T (T (T h392 h391) h386) h384) h368) h409) h417)
  have h419 := C h8 h393
  have h420 := C (T (T (T (T (T (C h14 (C h14 h359)) (C h14 (C h14 (T (T (T (T (T (T (T (T (T (T (T (T (T h357 h353) h350) h346) h345) h179) h177) h139) h103) h136) h135) h134) h51) h49)))) (C h14 (C h14 h43))) (C h14 (C h14 h15))) (C (T h401 (C h405 (T h401 (C h405 (T h403 (C (C h14 (C h14 h1)) h8)))))) h400)) (S h406)) (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h53 h71) h63) h105) h98) h155) h175) h184) h259) h258) h289) h286) h283) h279) h278) h367) h396) h395) h394)
  T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h59 h58) h56) (h v414 v4 v3)) (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (C h8 (T (T (T (T (T (T (T (T (C h8 (T (T (T (T (T (T (T (T (T (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h53 h71) h63) h105) h98) h155) h175) h184) h259) h258) h289) h286) h283) h279) h278) h298) h343) h337) (C h8 (T (T (T (T (T h334 h332) h330) h329) h397) h420))) (C h8 h419)) (C h8 h418)) h70) (S (h (M v4 (M v4 v219)) v4 v26))) h334) h332) h330) h329) h397) h420) h419) h418)) (C h8 h416)) (C h8 h408)) (C h8 (T (T (T (T (T h407 h398) h327) h326) h325) h324))) h323) h321) h299) h409) h417)) h416) h408) h407) h398) h327) h326) h325) h324) h322) h319) h310) h304) h300) h236) h176) h169) h89) h87) h86) (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h53 h71) h63) h105) h98) h155) h175) h184) h259) h258) h289) h286) h283) h279) h278) h367) h396) h395) h394) h393))) (C h16 h392)) (C h16 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h391 h386) h384) h368) h273) h272) h269) h266) h262) h254) h251) h198) h168) h156) h114) h141) h132) h130) h182) h180) h209) h227) h226) h344) (C h320 (T (T (T (T (T (T (T (T (T (T (T h125 h124) h119) h91) h118) h189) h187) h366) h365) h364) h363) h362))) (C h16 h361)))) (C h16 (C h16 h359))) (C h16 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (C h342 (T (T (T (T (T (T (T (T (T (T (T h357 h353) h350) h346) h345) h179) h177) h139) h103) h136) h135) h134)) (S h344)) h216) h207) h193) h172) h170) h131) h128) h127) h115) h155) h175) h184) h259) h258) h289) h286) h283) h279) h278) h298) h343) h337) h335) h333) h331))) (C h16 h328)) (C h16 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h323 h321) h299) h273) h272) h269) h266) h262) h254) h251) h198) h168) h156) h114) h141) h132) h130) h182) h180) h209) h227) h226) h221) h239) h296) h293) h291) h288) h285) h282))) h277) h265) h255) h246) h233) h218) h194) h108) h97) h45) h18

