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
theorem Equation1571_implies_Equation2688 (G: Type _) [Magma G] (h: Equation1571 G) : Equation2688 G := fun x y z =>
  let v0 := M z z
  let v1 := M x y
  let v2 := M v1 v0
  let v3 := M v2 y
  have h4 := h v3 y y
  have h5 := S h4
  have h6 := h y v2 y
  have h7 := S h6
  have h8 := R v3
  have h9 := C h7 (C h8 h7)
  let v10 := M y y
  have h11 := h v3 v3 (M v2 v10)
  have h12 := R v10
  have h13 := C h12 (T h11 h9)
  have h14 := h v10 v3 v1
  have h15 := S h14
  have h16 := h v1 v1 (M x v10)
  have h17 := S h16
  have h18 := h y x y
  have h19 := R v1
  have h20 := C h18 (C h19 h18)
  have h21 := R y
  have h22 := h v1 v2 v0
  have h23 := S h22
  let v24 := M v2 v2
  have h25 := h v24 v24 v1
  have h26 := S h25
  have h27 := h v1 v1 v0
  have h28 := S h27
  have h29 := R v24
  have h30 := C h29 h28
  have h31 := h v1 v2 v2
  have h32 := C (T h31 h30) (T h31 (C h29 (T (T h28 h31) h30)))
  let v33 := M x v1
  have h34 := h v1 v1 v33
  have h35 := S h34
  have h36 := h x x y
  have h37 := C h36 (C h19 h36)
  have h38 := h (M x (M v1 x)) v3 v3
  have h39 := S h38
  have h40 := S h36
  have h41 := C h40 (C h19 h40)
  have h42 := C (T h34 h41) h8
  have h43 := C h8 h42
  have h44 := h v3 x y
  have h45 := S h44
  have h46 := C h45 (C h19 h45)
  have h47 := h v1 v1 (M x (M v3 y))
  let v48 := M v1 v3
  let v49 := M v3 v3
  have h50 := h v49 v48 v2
  have h51 := S h50
  have h52 := h v2 v2 y
  have h53 := S h52
  have h54 := R v49
  have h55 := h v2 v3 v3
  have h56 := h v2 x y
  have h57 := S h56
  have h58 := R v48
  have h59 := h x v1 v3
  have h60 := T h59 (C h58 h57)
  have h61 := C h60 (T h59 (C h58 (T (T h57 h55) (C h54 h53))))
  have h62 := C (T h61 h51) (T (T h47 h46) h43)
  have h63 := T (T (T h62 h39) h37) h35
  have h64 := h v1 v1 (M x (M z y))
  have h65 := S h64
  have h66 := h z x y
  have h67 := C h66 (C h19 h66)
  let v68 := M v2 z
  let v69 := M v1 z
  have h70 := h v69 v69 (M v1 v68)
  have h71 := h v2 v1 z
  have h72 := R v69
  have h73 := h z v1 z
  have h74 := h z v1 v0
  have h75 := S h74
  have h76 := R v2
  have h77 := C h75 (T (T (C h76 h75) (C h71 (T h73 (C h72 h71)))) (S h70))
  have h78 := h v2 v2 (M v1 (M z v0))
  have h79 := T (T (T h78 h77) h67) h65
  have h80 := C h79 h63
  have h81 := S h47
  have h82 := C h44 (C h19 h44)
  have h83 := C (T h37 h35) h8
  have h84 := C h8 h83
  have h85 := S h59
  have h86 := T (C h58 h56) h85
  have h87 := C h86 (T (C h58 (T (T (C h54 h52) (S h55)) h56)) h85)
  have h88 := C (T h50 h87) (T (T h84 h82) h81)
  let v89 := M x x
  have h90 := h v89 v2 v1
  have h91 := S h90
  have h92 := T (T (T h34 h41) h38) h88
  have h93 := S h78
  have h94 := S h71
  have h95 := C h74 (T (T h70 (C h94 (T (C h72 h94) (S h73)))) (C h76 h74))
  have h96 := S h66
  have h97 := C h96 (C h19 h96)
  have h98 := T (T (T h64 h97) h95) h93
  have h99 := C h98 h92
  let v100 := M v1 v1
  have h101 := h v100 v100 x
  have h102 := S h101
  have h103 := R v100
  have h104 := C h103 h40
  have h105 := h x v1 v1
  have h106 := C (T h105 h104) (T h105 (C h103 (T (T h40 h105) h104)))
  have h107 := h v1 v1 (M x (M v0 y))
  have h108 := S h107
  have h109 := h v0 x y
  have h110 := C h109 (C h19 h109)
  have h111 := h v2 z z
  have h112 := S h111
  have h113 := R v0
  have h114 := h v0 v0 (M z v68)
  have h115 := C (T h114 (C h112 (T (T (C h113 h112) h110) h108))) (T (T h106 h102) h99)
  have h116 := C (T (T (T h115 h91) h61) h51) (T (T (T (T (T (T h78 h77) h67) h65) h47) h46) h43)
  have h117 := T h116 h88
  have h118 := C h76 h117
  have h119 := S h105
  have h120 := C h103 h36
  have h121 := C (T h120 h119) (T (C h103 (T (T h120 h119) h36)) h119)
  have h122 := S h109
  have h123 := C h122 (C h19 h122)
  have h124 := C (T (C h111 (T (T h107 h123) (C h113 h111))) (S h114)) (T (T h80 h101) h121)
  have h125 := C (T (T (T h50 h87) h90) h124) (T (T (T (T (T (T h84 h82) h81) h64) h97) h95) h93)
  let v126 := M v0 v89
  have h127 := h v126 v2 v2
  have h128 := S h127
  have h129 := T h62 h125
  have h130 := C h76 h129
  have h131 := h v126 v0 v2
  have h132 := S h131
  have h133 := C h113 (T (T (T h34 h41) h38) h125)
  have h134 := T h107 h123
  have h135 := C h134 h133
  have h136 := C (T h32 h26) (T (T (T (T (T (T (T h135 h132) h115) h91) h106) h102) h99) h130)
  have h137 := h v0 v1 v1
  have h138 := T (T (T (T (T (T (T (T h137 h136) h128) h115) h91) h106) h102) h32) h26
  let v139 := M v2 v0
  have h140 := h v139 v1 v1
  have h141 := S h140
  have h142 := R (M v139 v1)
  have h143 := S h137
  have h144 := C h113 (T (T (T h116 h39) h37) h35)
  have h145 := T h110 h108
  have h146 := C h145 h144
  have h147 := S h31
  have h148 := C h29 h27
  have h149 := C (T h148 h147) (T (C h29 (T (T h148 h147) h27)) h147)
  have h150 := C (T h25 h149) (T (T (T (T (T (T (T h118 h80) h101) h121) h90) h124) h131) h146)
  let v151 := M v0 v1
  let v152 := M v1 v151
  have h153 := h v152 v1 v2
  have h154 := S h153
  have h155 := R (M v152 v2)
  have h156 := T (T (T (T h137 h136) h128) h131) h146
  have h157 := C h156 (T (T (T (T (T (T (T h116 h39) h37) h35) h64) h97) h95) h93)
  have h158 := C (T (T (T (T (T h110 h108) h64) h97) h95) h93) h157
  let v159 := M v1 v2
  have h160 := R v159
  have h161 := C h160 (T (T (T (T (T h137 h136) h128) h131) h158) (C h79 h155))
  have h162 := T (T (T (T (T (T h161 h154) h135) h132) h127) h150) h143
  have h163 := C h79 h162
  have h164 := R v139
  have h165 := C h164 (T (T (T (T h163 h78) h77) h67) h65)
  have h166 := h v159 v2 v0
  have h167 := h v159 v0 v0
  have h168 := S h167
  have h169 := T (T (T (T h135 h132) h127) h150) h143
  have h170 := C h169 (T (T (T (T (T (T (T h78 h77) h67) h65) h34) h41) h38) h125)
  have h171 := C (T (T (T (T (T h78 h77) h67) h65) h107) h123) h170
  have h172 := C h160 (T (T (T (T (T (C h98 h155) h171) h132) h127) h150) h143)
  have h173 := T (T (T (T (T (T (T (T h25 h149) h101) h121) h90) h124) h127) h150) h143
  have h174 := C h173 (T (T (T h171 h146) h153) h172)
  have h175 := h v152 v2 v2
  let v176 := M v0 v0
  have h177 := h v176 v176 z
  have h178 := h z z z
  have h179 := S h178
  have h180 := R v176
  have h181 := C h180 h179
  have h182 := h z v0 v0
  have h183 := T (C (T h182 h181) (T h182 (C h180 (T (T h179 h182) h181)))) (S h177)
  have h184 := C h183 (T (T (T h161 h154) h175) h174)
  have h185 := T (T (T (T (T (T (T h161 h154) h175) h174) h184) h168) h166) h165
  have h186 := T (T (T (T (T (T h137 h136) h128) h131) h146) h153) h172
  have h187 := C h98 h186
  have h188 := C (T (T (T (T (T h135 h132) h115) h91) h106) h102) (T (T h187 (C h76 h185)) (C h79 h142))
  have h189 := C (T (T (T h133 h157) h188) h141) h138
  have h190 := T (T (T (T (T h189 h23) h34) h41) h38) h125
  have h191 := C h76 h190
  have h192 := C h164 (T (T (T (T h191 h118) h80) h32) h26)
  have h193 := h v151 v2 v0
  have h194 := S h175
  have h195 := C h138 (T (T (T h161 h154) h135) h158)
  have h196 := S h182
  have h197 := C h180 h178
  have h198 := T h177 (C (T h197 h196) (T (C h180 (T (T h197 h196) h178)) h196))
  have h199 := C h198 (T (T (T h195 h194) h153) h172)
  have h200 := S h166
  have h201 := C h164 (T (T (T (T h64 h97) h95) h93) h187)
  have h202 := T (T (T (T (T (T (T h201 h200) h167) h199) h195) h194) h153) h172
  have h203 := C (T (T (T (T (T h101 h121) h90) h124) h131) h146) (T (T (C h98 h142) (C h76 h202)) h163)
  have h204 := T (T (T (T (T (T h140 h203) h170) h144) h193) h192) h23
  have h205 := C h21 (C h204 h21)
  have h206 := C h12 (T (T h205 h20) h17)
  have h207 := h v139 y y
  have h208 := h v139 v0 v2
  have h209 := S h208
  have h210 := S h193
  have h211 := C (T (T (T h140 h203) h170) h144) h173
  have h212 := T (T (T (T (T h116 h39) h37) h35) h22) h211
  have h213 := C h76 h212
  have h214 := C h164 (T (T (T (T h25 h149) h99) h130) h213)
  have h215 := T (T (T (T (T (T (T (T (T (T h78 h77) h67) h65) h22) h214) h210) h133) h157) h188) h141
  have h216 := C h215 (T (T (T (T (T h189 h23) h64) h97) h95) h93)
  have h217 := T (T (T (T (T (T (T (T (T (T h140 h203) h170) h144) h193) h192) h23) h64) h97) h95) h93
  have h218 := C h217 (T (T (T (T (T h78 h77) h67) h65) h22) h211)
  have h219 := C h134 (T (T (T (T (T (T (T (T (T (T (T (T (T h218 h191) h118) h80) h101) h121) h90) h124) h131) h146) h175) h174) h184) (C h198 (T (T (T (T (T (T (T (T (T (T (T h195 h194) h135) h132) h115) h91) h106) h102) h99) h130) h213) h216)))
  have h220 := C h204 (T (T (T (T (T (T (T (T (T (T h137 h136) h128) h115) h91) h106) h102) h99) h130) h213) h216)
  have h221 := C h8 (T (T (T (T h220 h219) h209) h207) h206)
  have h222 := T (T (T (T (T (T h22 h214) h210) h133) h157) h188) h141
  have h223 := C h222 (T (T (T (T (T (T (T (T (T (T h218 h191) h118) h80) h101) h121) h90) h124) h127) h150) h143)
  have h224 := C h145 (T (T (T (T (T (T (T (T (T (T (T (T (T (C h183 (T (T (T (T (T (T (T (T (T (T (T h218 h191) h118) h80) h101) h121) h90) h124) h131) h146) h175) h174)) h199) h195) h194) h135) h132) h115) h91) h106) h102) h99) h130) h213) h216)
  have h225 := C h8 (T (T (T (T (T (T (T (T (T h189 h214) h210) h133) h157) h188) h141) h208) h224) h223)
  have h226 := C h8 h212
  have h227 := C h8 h129
  let v228 := M v3 v1
  have h229 := R v228
  have h230 := C h229 (T (T (T h227 h226) h225) h221)
  have h231 := h v89 v3 v1
  have h232 := T (T (T (T (T (T (T h137 h136) h128) h115) h91) h231) h230) h15
  have h233 := C h232 (T (T (T h13 h5) h11) h9)
  have h234 := C (T (T (T (T (T (T h135 h132) h115) h91) h231) h230) h15) h8
  have h235 := C h113 h234
  have h236 := C h156 h8
  have h237 := C h113 h236
  let v238 := M v0 v3
  let v239 := M v0 v238
  have h240 := h v239 v2 v3
  have h241 := S h240
  have h242 := C h169 h8
  have h243 := C h113 h242
  have h244 := S h231
  have h245 := C h8 h117
  have h246 := C h8 h190
  have h247 := C h8 (T (T (T (T (T (T (T (T (T h220 h219) h209) h140) h203) h170) h144) h193) h192) h211)
  have h248 := S h207
  have h249 := C h21 (C h222 h21)
  have h250 := S h18
  have h251 := C h250 (C h19 h250)
  have h252 := C h12 (T (T h16 h251) h249)
  have h253 := C h8 (T (T (T (T h252 h248) h208) h224) h223)
  have h254 := C h229 (T (T (T h253 h247) h246) h245)
  have h255 := C (T (T (T (T (T (T h14 h254) h244) h90) h124) h131) h146) h8
  have h256 := C h113 h255
  have h257 := S h11
  have h258 := C h6 (C h8 h6)
  have h259 := C h12 (T h258 h257)
  have h260 := T (T (T (T (T (T (T h14 h254) h244) h90) h124) h127) h150) h143
  have h261 := C h260 (T (T (T h258 h257) h4) h259)
  have h262 := C (T (T (T (T (T h236 h234) h13) h261) h256) h243) (T (T h235 h233) h5)
  have h263 := h v152 v0 v3
  have h264 := h v10 v1 v2
  have h265 := S h264
  have h266 := C h12 (T (T (T (T (T (T h78 h77) h67) h65) h16) h251) h249)
  have h267 := h v10 v0 v2
  have h268 := C (T (T (T (T (T (T (T (T (T (T h14 h254) h244) h90) h124) h131) h146) h175) h174) h184) h168) (T (T (T (T (T (T (T (T (T h137 h136) h128) h115) h91) h231) h230) h15) h267) (C h145 (C h232 (T (T (T (T (T (T (T (T (T (T (T (T h266 h248) h140) h203) h170) h144) h193) h192) h23) h64) h97) h95) h93))))
  have h269 := T (T (T (T (T (T (T (T (T (T h268 h265) h14) h254) h244) h90) h124) h131) h146) h263) h262
  have h270 := C h98 h269
  have h271 := R (M v10 v0)
  have h272 := C h79 h271
  have h273 := C h12 (T (T (T (T (T (T h205 h20) h17) h64) h97) h95) h93)
  have h274 := C (T (T (T (T (T (T (T (T (T (T h167 h199) h195) h194) h135) h132) h115) h91) h231) h230) h15) (T (T (T (T (T (T (T (T (T (C h134 (C h260 (T (T (T (T (T (T (T (T (T (T (T (T h78 h77) h67) h65) h22) h214) h210) h133) h157) h188) h141) h207) h273))) (S h267)) h14) h254) h244) h90) h124) h127) h150) h143)
  have h275 := R (M v139 v0)
  have h276 := C h76 (T (T (T (T (T (T (T (T (T (T (T (T (C h98 h275) (C h215 (T (T (T (T (T (T (T (T (T (T (T (T (T h220 h219) h209) h140) h203) h170) h144) h193) h192) h23) h64) h97) h95) h93))) h218) h191) h118) h80) h101) h121) h231) h230) h15) h264) h274)
  have h277 := h v139 v1 v0
  have h278 := h v33 v3 x
  have h279 := S h278
  have h280 := h x v3 v2
  have h281 := S h280
  let v282 := M x v2
  have h283 := h v282 v3 v0
  have h284 := S h263
  have h285 := C (T (T (T (T (T h237 h235) h233) h259) h255) h242) (T (T h4 h261) h256)
  let v286 := M v2 v3
  have h287 := R v286
  have h288 := C h287 (T (T (T (T (T (T (T (T (T (T h22 h214) h210) h133) h157) h188) h141) h277) h276) h272) h270)
  have h289 := C (T (T (T h4 h261) h256) h243) (T (T (T (T (T h288 h241) h237) h235) h233) h5)
  have h290 := h v2 v3 v1
  have h291 := S h290
  have h292 := h x v2 y
  have h293 := h x v3 v1
  have h294 := S h293
  have h295 := C h294 (T (C h229 (T h294 h292)) h291)
  have h296 := h v228 v228 (M v3 v33)
  have h297 := h v286 v3 v1
  have h298 := C h8 h162
  have h299 := C h8 h202
  have h300 := C h8 (T h166 h165)
  let v301 := M v3 v159
  have h302 := R v301
  let v303 := M v3 v2
  have h304 := R v303
  have h305 := C h304 (T (C h8 (C h302 h79)) (C h8 (T (C (T (T h300 h299) h298) (T (T (T (T (T h64 h97) h95) h93) h52) (C h8 (T h297 (C (T h296 h295) (T (T (T (T (T (T (T h289 h285) h284) h135) h132) h127) h150) h143)))))) (S h283))))
  have h306 := h v301 v3 v2
  have h307 := C h8 (T h201 h200)
  have h308 := C h8 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h218 h191) h118) h80) h101) h121) h90) h124) h131) h146) h175) h174) h184) h168) h166) h165)
  have h309 := T (T (T (T h308 h307) h306) h305) h281
  have h310 := R x
  have h311 := C h310 (T (T (T (T (T (T (T (T (T h220 h219) h209) h140) h203) h170) h144) h193) h192) h23)
  have h312 := C h310 (T (T (T (T h266 h248) h208) h224) h223)
  have h313 := h v1 v0 v3
  have h314 := C (T (T (T (T (T (T (T (T h140 h203) h170) h144) h193) h192) h23) h34) h41) h8
  have h315 := C (T (T (T (T (T (T (T (T h37 h35) h22) h214) h210) h133) h157) h188) h141) h8
  have h316 := h v48 v48 (M v1 v286)
  have h317 := h v2 v1 v3
  have h318 := T (T (T (T h64 h97) h95) h93) h317
  have h319 := C h215 (T h13 h5)
  have h320 := C h98 h234
  have h321 := R (M v152 v3)
  have h322 := C h79 h321
  have h323 := C h98 h236
  have h324 := h (M v1 v238) v2 v2
  have h325 := C h79 h242
  have h326 := C h98 h321
  have h327 := C h79 h255
  have h328 := C h217 (T h4 h259)
  have h329 := h v48 v3 v2
  let v330 := M v3 x
  have h331 := h v330 v3 v0
  have h332 := S h331
  have h333 := S h277
  have h334 := C h76 (T (T (T (T (T (T (T (T (T (T (T (T h268 h265) h14) h254) h244) h106) h102) h99) h130) h213) h216) (C h217 (T (T (T (T (T (T (T (T (T (T (T (T (T h78 h77) h67) h65) h22) h214) h210) h133) h157) h188) h141) h208) h224) h223))) (C h79 h275))
  have h335 := C h98 h271
  have h336 := T (T (T (T (T (T (T (T (T (T h285 h284) h135) h132) h115) h91) h231) h230) h15) h264) h274
  have h337 := C h287 (T (T (T (T (T (T (T (T (T (T (C h79 h336) h335) h334) h333) h140) h203) h170) h144) h193) h192) h23)
  have h338 := h v239 v3 v3
  have h339 := C h8 h269
  have h340 := C h8 (T (T (T (T (T (T (T (T (T (T h218 h191) h118) h80) h101) h121) h231) h230) h15) h264) h274)
  have h341 := C h8 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h201 h200) h167) h199) h195) h194) h135) h132) h115) h91) h106) h102) h99) h130) h213) h216)
  have h342 := S h306
  have h343 := C (T (T (T h237 h235) h233) h5) (T (T (T (T (T h4 h261) h256) h243) h240) h337)
  have h344 := S h296
  have h345 := S h292
  have h346 := C h293 (T h290 (C h229 (T h345 h293)))
  have h347 := C h8 h185
  have h348 := C h8 h186
  have h349 := C h304 (T (C h8 (T h283 (C (T (T h348 h347) h307) (T (T (T (T (T (C h8 (T (C (T h346 h344) (T (T (T (T (T (T (T h137 h136) h128) h131) h146) h263) h262) h343)) (S h297))) h53) h78) h77) h67) h65)))) (C h8 (C h302 h98)))
  have h350 := R v330
  have h351 := h v10 v3 x
  have h352 := T (T (T (T (T h280 h349) h342) h300) h299) h298
  have h353 := C h352 (T (T (T (T (T (T (T h280 h349) h342) h300) h341) h340) h339) (C h8 (T (T (T (T (T (T (T (T (T (T h285 h284) h135) h132) h115) h91) h231) h230) h15) h351) (C h350 (T (T (T (T (T (T (T (T (C h8 (T (T (T (C (T (T (T (T h14 h254) h244) h61) h51) (T (T (T (T (T (T h280 h349) h342) h300) h341) h340) h339)) (S h338)) h240) h337)) h289) h285) h284) h135) h132) h127) h150) h143)))))
  have h354 := T (T (T (T (T h348 h347) h307) h306) h305) h281
  have h355 := C h354 (T (T (T (T (T (T (T (T (T (T (C (T (T (T h4 h259) h255) h242) (T (T (T (T (T (T (T (T (T (T (C h304 (T (T (T (T (T (T (T h137 h136) h128) h115) h91) h353) h332) (C h8 h60))) (S h329)) h42) h315) h328) h327) h326) h325) h324) (C h173 (T (T (T (T (C h79 (C (T (T (T (T (T h323 h322) h320) h319) h314) h83) h79)) (C h318 (C h58 h318))) (S h316)) h42) h315))) (C h113 (T h314 h83)))) (S h313)) h22) h214) h210) h133) h157) h188) h141) h207) h273)
  have h356 := h v303 v3 v0
  have h357 := h v139 v3 v2
  have h358 := C (T (T (T (T (T (T h137 h136) h128) h115) h91) h353) h332) (T (T (T (T (T (T (T (T h346 h344) (C h8 h92)) h227) h226) h225) h221) (C h8 (T h252 h273))) (C h8 (T (T (T h266 h248) h357) (C (T (T (T h356 h355) h312) h311) h309))))
  have h359 := h (M v0 v282) v2 x
  have h360 := S h357
  have h361 := T (T (T (T h280 h349) h342) h300) h341
  have h362 := S h356
  have h363 := C h8 (T (T (T (T (T (T (T (T (T (T h268 h265) h14) h254) h244) h106) h102) h99) h130) h213) h216)
  have h364 := C h8 h336
  have h365 := C h354 (T (T (T (T (T (T (T (C h8 (T (T (T (T (T (T (T (T (T (T (C h350 (T (T (T (T (T (T (T (T h137 h136) h128) h131) h146) h263) h262) h343) (C h8 (T (T (T h288 h241) h338) (C (T (T (T (T h50 h87) h231) h230) h15) (T (T (T (T (T (T h364 h363) h308) h307) h306) h305) h281)))))) (S h351)) h14) h254) h244) h90) h124) h131) h146) h263) h262)) h364) h363) h308) h307) h306) h305) h281)
  have h366 := T (T (T (T (S h317) h78) h77) h67) h65
  have h367 := C h352 (T (T (T (T (T (T (T (T (T (T h266 h248) h140) h203) h170) h144) h193) h192) h23) h313) (C (T (T (T h236 h234) h13) h5) (T (T (T (T (T (T (T (T (T (T (C h113 (T h42 h315)) (C h138 (T (T (T (T h314 h83) h316) (C h366 (C h58 h366))) (C h98 (C (T (T (T (T (T h42 h315) h328) h327) h326) h325) h98))))) (S h324)) h323) h322) h320) h319) h314) h83) h329) (C h304 (T (T (T (T (T (T (T (C h8 h86) h331) h365) h90) h124) h127) h150) h143)))))
  have h368 := C h310 (T (T (T (T h220 h219) h209) h207) h273)
  have h369 := C h310 (T (T (T (T (T (T (T (T (T h22 h214) h210) h133) h157) h188) h141) h208) h224) h223)
  have h370 := C (T (T (T (T (T (T h331 h365) h90) h124) h127) h150) h143) (T (T (T (T (T (T (T (T (C h8 (T (T (T (C (T (T (T h369 h368) h367) h362) h361) h360) h207) h273)) (C h8 (T h266 h206))) h253) h247) h246) h245) (C h8 h63)) h296) h295)
  have h371 := h v10 v1 v0
  let v372 := M v2 x
  have h373 := R v372
  have h374 := C h79 (T (T (T (C h373 (T (T (T (T (T (T (T (T (T h137 h136) h128) h115) h91) h231) h230) h15) h371) (C h76 (T (T (T (T h335 h334) h333) h357) (C (T (T (T (T (T h356 h355) h312) h311) h278) h370) h309))))) (S h359)) h358) h279)
  have h375 := h v372 v2 v0
  have h376 := C h98 (T (T (T h278 h370) h359) (C h373 (T (T (T (T (T (T (T (T (T (C h76 (T (T (T (T (C (T (T (T (T (T h358 h279) h369) h368) h367) h362) h361) h360) h277) h276) h272)) (S h371)) h14) h254) h244) h90) h124) h127) h150) h143)))
  have h377 := C (T (C h222 (T h36 h376)) (S h375)) h113
  have h378 := C (T h375 (C h204 (T h374 h40))) h113
  have h379 := h v228 v2 x
  T (T (T (T (T (T (T (T (T (T h36 h376) (C h76 h378)) (C h79 (T (T (T (T h377 (C h373 (T (T (T (T (T (T (T (T (T h137 h136) h128) h115) h91) h106) h102) h32) h26) (C h76 (T h290 (C h229 h345)))))) (S h379)) h296) h295))) (h (M v1 v282) v2 v3)) (C h287 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (C h79 (C (T (T (T (C h98 (T (T (T (T h346 h344) h379) (C h373 (T (T (T (T (T (T (T (T (T (C h76 (T (C h229 h292) h291)) h25) h149) h101) h121) h90) h124) h127) h150) h143))) h378)) (C h76 h377)) h374) h40) h8)) h57) h78) h77) h67) h65) h22) h214) h210) h133) h157) h188) h141) h277) h276) h272) h270))) h241) h237) h235) h233) h5

