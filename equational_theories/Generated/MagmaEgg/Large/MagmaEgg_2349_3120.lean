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
theorem Equation2349_implies_Equation3120 (G: Type _) [Magma G] (h: Equation2349 G) : Equation3120 G := fun x y z =>
  let v0 := M y x
  let v1 := M v0 y
  let v2 := M v1 z
  let v3 := M v2 z
  let v4 := M x (M x (M v1 v1))
  have h5 := h y v4 v0
  have h6 := S h5
  have h7 := R v0
  have h8 := h v1 x v1
  have h9 := R v4
  have h10 := C (T h8 (C h9 h8)) h7
  let v11 := M v1 v0
  have h12 := h v11 v2 v0
  have h13 := S h12
  have h14 := S h8
  have h15 := C (T (C h9 h14) h14) h7
  have h16 := T h5 h15
  have h17 := C h7 h16
  have h18 := R v2
  have h19 := R v1
  have h20 := h v2 x v2
  have h21 := S h20
  let v22 := M x (M x (M v2 v2))
  have h23 := R v22
  have h24 := h z v22 v1
  have h25 := C h18 (T (T h24 (C (T (C h23 h21) h21) h19)) (C h18 h17))
  have h26 := C h25 h7
  let v27 := M v3 v0
  have h28 := h v27 v2 v0
  have h29 := S h28
  have h30 := h v0 v1 v1
  have h31 := S h30
  have h32 := R y
  have h33 := h v0 x v0
  have h34 := S h33
  let v35 := M x (M x (M v0 v0))
  have h36 := R v35
  have h37 := C (T (C h36 h34) h34) h32
  have h38 := h x v35 y
  have h39 := T h38 h37
  have h40 := R (M v1 v11)
  have h41 := R v11
  have h42 := C h39 h41
  have h43 := R x
  have h44 := R (M x v11)
  have h45 := S h38
  have h46 := C (T h33 (C h36 h33)) h32
  have h47 := T h46 h45
  have h48 := T h26 h13
  have h49 := C h43 h48
  have h50 := R (M x v27)
  have h51 := R v27
  have h52 := C h47 h51
  have h53 := R (M v1 v27)
  have h54 := C h39 h51
  have h55 := T h10 h6
  have h56 := C h7 h55
  have h57 := C h18 (T (T (C h18 h56) (C (T h20 (C h23 h20)) h19)) (S h24))
  have h58 := C h57 h7
  have h59 := T h12 h58
  have h60 := C h43 h59
  have h61 := C h47 h41
  let v62 := M x v0
  let v63 := M x v62
  let v64 := M x (M x (M x x))
  have h65 := h y v64 v63
  have h66 := S h65
  have h67 := R v63
  have h68 := h x x y
  have h69 := R v64
  have h70 := h x x x
  have h71 := C (T h70 (C h69 (T h70 (C h69 h68)))) h67
  have h72 := C h39 (T (T (T h71 h66) h5) h15)
  have h73 := R (M x (M x v63))
  have h74 := C (T (T (T (T (T (T (T (T (C h39 h73) (C h47 (T (T (T h72 h61) h60) h54))) (C h39 h53)) (C h19 h52)) (C h47 h50)) (C h39 h49)) (C h47 h44)) (C h43 h42)) (C h39 h40)) h39
  have h75 := h v63 x x
  have h76 := T (T h75 h74) h31
  have h77 := C h7 h59
  have h78 := C h18 (C h18 h77)
  have h79 := C (T h25 h78) h76
  have h80 := S h75
  have h81 := S h70
  have h82 := S h68
  have h83 := C (T (C h69 (T (C h69 h82) h81)) h81) h67
  have h84 := C h47 (T (T (T h10 h6) h65) h83)
  have h85 := C (T (T (T (T (T (T (T (T (C h47 h40) (C h43 h61)) (C h39 h44)) (C h47 h60)) (C h39 h50)) (C h19 h54)) (C h47 h53)) (C h39 (T (T (T h52 h49) h42) h84))) (C h47 h73)) h47
  let v86 := M y v1
  let v87 := M y v86
  let v88 := M x (M x (M y y))
  have h89 := h v0 v88 v87
  have h90 := S h89
  have h91 := R v87
  have h92 := h y y v0
  have h93 := R v88
  have h94 := h y x y
  have h95 := C (T h94 (C h93 (T h94 (C h93 h92)))) h91
  have h96 := C h7 h48
  have h97 := T h96 h56
  have h98 := C h32 h97
  have h99 := C h32 h98
  have h100 := C h32 h99
  have h101 := C h32 h77
  have h102 := C h32 h101
  have h103 := C h32 h102
  have h104 := C h32 h96
  have h105 := C h32 h104
  have h106 := T h17 h77
  have h107 := C h32 h106
  have h108 := C h32 h107
  have h109 := h v87 x y
  have h110 := S h109
  have h111 := R (M x (M y v87))
  have h112 := S h94
  have h113 := C (T (C h93 (T (C h93 (S h92)) h112)) h112) h91
  have h114 := C h43 (T (T (T (T h75 h74) h31) h89) h113)
  have h115 := C h19 h76
  have h116 := T (T (T (T (T h115 h10) h6) h65) h83) h114
  have h117 := R (M v1 v63)
  have h118 := T (T h30 h85) h80
  have h119 := C h19 h118
  have h120 := T (T (T (T h79 h29) h26) h13) h119
  have h121 := R (M v3 v63)
  have h122 := C h18 (C h18 h96)
  have h123 := C (T h122 h57) h118
  have h124 := C (T (T (T (T (T (T h84 (C h39 (T (T (T (T (T (T (T h71 h66) h5) h15) h12) h58) h28) h123))) (C h47 h121)) (C h43 h120)) (C h39 h117)) (C h19 h116)) (C h47 h111)) h32
  have h125 := h x v1 y
  have h126 := C h32 (T (T (T (T (T (T (T h56 h46) h45) h125) h124) h110) h108) h105)
  have h127 := T (T (T (T (T (T (T h126 h103) h100) h95) h90) h30) h85) h80
  have h128 := R v3
  have h129 := C h128 h127
  have h130 := C h128 h104
  have h131 := C h128 h107
  let v132 := M v3 v86
  have h133 := h v132 y v0
  have h134 := S h133
  have h135 := h v63 v2 y
  have h136 := S h135
  have h137 := h v11 y v0
  have h138 := S h137
  have h139 := C (T (T (T (T (T (T h46 h45) h125) h124) h110) h108) h105) (T (T (T (T h126 h103) h100) h95) h90)
  have h140 := C h39 h104
  have h141 := R (M y (M v0 v27))
  have h142 := C h47 h141
  have h143 := C h19 h107
  have h144 := C h118 (T (T (T (T (T (T (T (T h131 h130) h129) h79) h29) h26) h13) h10) h6)
  have h145 := C h32 (T (T (T (T (T (T h144 h82) h125) h124) h110) h108) h105)
  have h146 := C h32 (T (T (T (T (T (T (T h145 h103) h100) h95) h90) h30) h85) h80)
  have h147 := C h128 h98
  have h148 := C h128 h101
  have h149 := S h125
  have h150 := T (T (T (T h115 h12) h58) h28) h123
  have h151 := C h43 (T (T (T (T h95 h90) h30) h85) h80)
  have h152 := T (T (T (T (T h151 h71) h66) h5) h15) h119
  have h153 := C (T (T (T (T (T (T (C h39 h111) (C h19 h152)) (C h47 h117)) (C h43 h150)) (C h39 h121)) (C h47 (T (T (T (T (T (T (T h79 h29) h26) h13) h10) h6) h65) h83))) h72) h32
  have h154 := C h32 (T (T (T (T (T (T (T h102 h99) h109) h153) h149) h38) h37) h17)
  have h155 := C h32 h105
  have h156 := C h32 h108
  have h157 := T (T (T (T (T (T (T h75 h74) h31) h89) h113) h156) h155) h154
  have h158 := C h128 h157
  have h159 := T (T (T (T (T (T (T (T (T (T (T h143 h142) h140) h139) h138) h12) h58) h28) h123) h158) h148) h147
  have h160 := C h7 h159
  have h161 := C h32 h160
  have h162 := C h32 h161
  have h163 := C h19 h98
  have h164 := C h39 h141
  have h165 := C h47 h101
  have h166 := C (T (T (T (T (T (T h102 h99) h109) h153) h149) h38) h37) (T (T (T (T h89 h113) h156) h155) h154)
  have h167 := T (T (T (T (T (T (T (T (T (T (T h131 h130) h129) h79) h29) h26) h13) h137) h166) h165) h164) h163
  have h168 := C h7 h167
  have h169 := C h32 h168
  have h170 := C h76 (T (T (T (T (T (T (T (T h5 h15) h12) h58) h28) h123) h158) h148) h147)
  have h171 := C h32 (T (T (T (T (T (T h102 h99) h109) h153) h149) h68) h170)
  have h172 := C h32 (T (T h126 h171) h169)
  have h173 := C h18 (C h18 (T (T (T (T (T (T (T (T (T (T h160 h144) h82) h125) h124) h110) h108) h105) h172) h162) h146))
  have h174 := C h18 (C h18 h168)
  have h175 := C h18 (C h18 (T (T (T (T (T h96 h56) h46) h45) h68) h170))
  have h176 := T (T (T (T h25 h78) h175) h174) h173
  have h177 := C h176 (T (T (T (T (T (T h143 h142) h140) h139) h138) h10) h6)
  have h178 := C (T (T (T (T (T (T (T (T h46 h45) h125) h124) h110) h108) h105) h172) h162) (T (T (T (T h177 h136) h75) h74) h31)
  have h179 := C h39 (C h128 h167)
  have h180 := R (M v3 v132)
  have h181 := C h47 h180
  have h182 := C h39 (T (T (T (T (T (C h128 (T h28 h123)) (C h128 h120)) (C h128 h116)) (C h128 (T (T (T (T (T (T (T (T (T h151 h71) h66) h5) h15) h12) h58) h28) h123) h158))) (C h128 h148)) (C h128 h147))
  let v183 := M v3 v27
  have h184 := R v183
  have h185 := C h47 h184
  have h186 := C h39 (C h128 h59)
  let v187 := M v3 v11
  have h188 := R v187
  have h189 := C h47 h188
  have h190 := C h19 (C h128 h16)
  let v191 := M v1 (M v3 y)
  have h192 := h v191 v1 x
  have h193 := S h192
  have h194 := C h18 (C h18 (T (T (T (T (T h144 h82) h38) h37) h17) h77))
  have h195 := C h18 (C h18 h160)
  have h196 := C h32 (T (T h161 h145) h154)
  have h197 := C h32 h169
  have h198 := C h32 (T (T (T (T (T (T (T h75 h74) h31) h89) h113) h156) h155) h171)
  have h199 := C h18 (C h18 (T (T (T (T (T (T (T (T (T (T h198 h197) h196) h102) h99) h109) h153) h149) h68) h170) h168))
  have h200 := T (T (T (T h199 h195) h194) h122) h57
  have h201 := C h200 (T (T (T (T (T (T h5 h15) h137) h166) h165) h164) h163)
  have h202 := C h176 (T (T (T (T (T (T (T (T (T (T (T h179 h178) h134) h131) h130) h129) h79) h29) h26) h13) h10) h6)
  have h203 := C h47 (C h128 h159)
  have h204 := C (T (T (T (T (T (T (T (T h197 h196) h102) h99) h109) h153) h149) h38) h37) (T (T (T (T h30 h85) h80) h135) h201)
  let v205 := M v1 v86
  have h206 := h v205 v2 v0
  have h207 := S h206
  have h208 := C (T (T (T h25 h78) h175) h174) (T (T (T (T h202 h136) h75) h74) h31)
  have h209 := C h128 (C h128 (T h182 h181))
  have h210 := C h128 (C h128 h185)
  have h211 := C h128 (C h128 h186)
  have h212 := C h128 (C h128 h189)
  have h213 := C h128 (C h128 h190)
  have h214 := C h128 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h213 h212) h211) h210) h209) h208) h207) h143) h142) h140) h139) h138) h12) h58) h28) h123) h158) h148) h147) h133) h204) h203)
  have h215 := C h19 (C h128 h55)
  have h216 := C h128 (C h128 h215)
  have h217 := C h39 h188
  have h218 := C h128 (C h128 h217)
  have h219 := C h47 (C h128 h48)
  have h220 := C h128 (C h128 h219)
  have h221 := C h39 h184
  have h222 := C h128 (C h128 h221)
  have h223 := C h47 (T (T (T (T (T (C h128 h131) (C h128 h130)) (C h128 (T (T (T (T (T (T (T (T (T h129 h79) h29) h26) h13) h10) h6) h65) h83) h114))) (C h128 h152)) (C h128 h150)) (C h128 (T h79 h29)))
  have h224 := C h39 h180
  have h225 := C h128 (C h128 (T h224 h223))
  have h226 := C h200 (T (T (T (T (T (T (T (T (T (T (T h5 h15) h12) h58) h28) h123) h158) h148) h147) h133) h204) h203)
  have h227 := C (T (T (T h195 h194) h122) h57) (T (T (T (T h30 h85) h80) h135) h226)
  have h228 := h v191 v3 v3
  have h229 := S h228
  have h230 := C h128 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h179 h178) h134) h131) h130) h129) h79) h29) h26) h13) h137) h166) h165) h164) h163) h206) h227) h225) h222) h220) h218) h216)
  have h231 := C (T (T (T (T (T h30 h85) h80) h135) h226) h230) h128
  have h232 := C h128 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h231 h229) h190) h189) h186) h185) h182) h181) h179) h178) h134) h131) h130) h129) h79) h29) h26) h13) h137) h166) h165) h164) h163) h206) h227) h225) h222) h220) h218) h216)
  have h233 := T (T (T h232 h214) h202) h201
  have h234 := C h19 h233
  let v235 := M v3 (M v0 v3)
  have h236 := R v235
  have h237 := C h39 h236
  have h238 := C h7 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h237 h234) h178) h134) h131) h130) h129) h79) h29) h26) h13) h137) h166) h165) h164) h163)
  have h239 := C h47 h236
  have h240 := C h7 h239
  have h241 := C (T (T (T (T (T h214 h202) h136) h75) h74) h31) h128
  have h242 := C h128 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h213 h212) h211) h210) h209) h208) h207) h143) h142) h140) h139) h138) h12) h58) h28) h123) h158) h148) h147) h133) h204) h203) h224) h223) h221) h219) h217) h215) h228) h241)
  have h243 := T (T (T h177 h226) h230) h242
  have h244 := C h19 h243
  have h245 := C h32 (T (T (T (T (T (T (T (T (T (T (T h232 h214) h202) h136) h75) h74) h31) h89) h113) h156) h155) h154)
  have h246 := C h43 (T (T (T h221 h219) h217) h215)
  have h247 := R (M x v183)
  have h248 := C h47 h247
  have h249 := C h39 h185
  have h250 := R (M v1 v183)
  have h251 := C h47 h250
  have h252 := C h39 h186
  have h253 := R (M x v187)
  have h254 := C h47 h253
  have h255 := C h39 h189
  have h256 := R (M v1 v187)
  have h257 := C h47 h256
  have h258 := C h19 h190
  have h259 := C h19 h215
  have h260 := C h39 h256
  have h261 := C h47 h217
  have h262 := C h39 h253
  have h263 := C h47 h219
  have h264 := C h39 h250
  have h265 := C h47 h221
  have h266 := C h39 h247
  have h267 := C h43 (T (T (T h190 h189) h186) h185)
  have h268 := R (M v3 v205)
  have h269 := C h39 h268
  have h270 := C h47 h268
  have h271 := R (M v1 v235)
  have h272 := h v235 v3 v1
  have h273 := T (T (T (T (T (T (T (T (C h32 (T (C (T (T (T (T (T (T (T (T (T (T h5 h15) h137) h166) h165) h164) h163) h206) h227) (C h128 (T (T h230 h242) (C h128 (T (T (T (T (T (T (T (T (T (T h231 h229) h190) h189) h186) h185) h182) h181) h179) h244) h239))))) (C h128 (C h128 h237))) (T (T (T (T (T (T (T h245 h102) h99) h109) h153) h149) h38) h37)) (S h272))) h245) h102) h99) h109) h153) h149) h38) h37
  have h274 := h v235 y y
  have h275 := T (T (T (T (T (T (T (T h30 h85) h80) h135) h226) h230) h242) h274) (C h273 (T (T (T (T (T (T (T (T (T (T (T (T (T (T h5 h15) h12) h58) h28) h123) h158) h148) h147) h133) h204) h244) (C h19 (T (T (T h274 (C h273 (T (T (T (T (T (T (T (T (T (T (T h5 h15) h12) h58) h28) h123) h158) h148) h147) h133) h204) h244))) (C h47 h271)) (C h39 h239)))) (C h47 (T (T (T (T (T (T (T (T (T (T (T (T (T (C h19 (T h237 h234)) (C h47 h270)) (C h43 (T (T h269 h203) h224))) (C h39 h181)) (C h47 (T (T (T (T (T h224 h223) h221) h219) h217) h215))) h267) h266) h265) h264) h263) h262) h261) h260) h259))) (C h39 (T (T (T (T (T (T (T (T h258 h257) h255) h254) h252) h251) h249) h248) h246))))
  have h276 := C h275 (T (T (T (T (T h245 h102) h99) h109) h153) h149)
  have h277 := C h7 (T (T (T (T (T (T (T (T (T h276 h193) h190) h189) h186) h185) h182) h181) h179) h244)
  have h278 := C h32 (T (T (T (T (T (T (T (T (T (T (T h126 h103) h100) h95) h90) h30) h85) h80) h135) h226) h230) h242)
  have h279 := C h7 h237
  have h280 := C h7 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h143 h142) h140) h139) h138) h12) h58) h28) h123) h158) h148) h147) h133) h204) h244) h239)
  have h281 := C h7 (T (T (C h7 h280) (C h7 h279)) (C h7 (T (T (T (T (T (T (T (T (T (T h240 h238) h160) h144) h82) h125) h124) h110) h108) h105) h278)))
  have h282 := C h7 (C h7 h168)
  have h283 := h (M v0 v11) y y
  have h284 := S h283
  have h285 := C (T (T (T h89 h113) h156) h155) (T (T (T (T (T h79 h29) h26) h13) h10) h6)
  have h286 := C h7 h150
  have h287 := C h7 h120
  have h288 := C (T (T (T h103 h100) h95) h90) (T (T (T (T (T h5 h15) h12) h58) h28) h123)
  have h289 := C h7 (T (T (C h7 (T h283 h288)) (C h7 h287)) (C h7 (T (T (T (T (T (T (T h286 h285) h284) h56) h46) h45) h68) h170)))
  have h290 := C h275 (T (T (T (T (T (T (T (T h289 h282) h281) h277) h240) h238) h160) h144) h82)
  have h291 := C h7 h106
  have h292 := C h7 (T h291 (C h7 h96))
  have h293 := C h7 h292
  let v294 := M v0 (M v0 v1)
  let v295 := M v0 v294
  have h296 := h v295 v2 v0
  have h297 := S h296
  have h298 := h v235 v2 y
  have h299 := S h298
  have h300 := C h18 (C h18 (T (T (T h198 h197) h196) h278))
  have h301 := C (T (T (T (T (T h25 h78) h175) h174) h173) h300) (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h293 h290) h193) h190) h189) h186) h185) h182) h181) h179) h178) h134) h131) h130) h129) h79) h29) h26) h13) h10) h6)
  have h302 := T (T (T (T (T (T (T (T h301 h299) h232) h214) h202) h136) h75) h74) h31
  have h303 := C h7 h97
  have h304 := C h7 h303
  have h305 := C h7 h304
  have h306 := C h7 h305
  have h307 := C h7 h291
  have h308 := C h7 h307
  have h309 := C h7 (T (C h7 h77) h303)
  have h310 := C h7 h309
  have h311 := C h7 (T h310 h308)
  have h312 := C h7 (T (T (C h7 (T (T (T (T (T (T (T h144 h82) h38) h37) h17) h283) h288) h287)) (C h7 h286)) (C h7 (T h285 h284)))
  have h313 := C h7 (C h7 h160)
  have h314 := C h7 (T (T (C h7 (T (T (T (T (T (T (T (T (T (T h245 h102) h99) h109) h153) h149) h68) h170) h168) h280) h279)) (C h7 h240)) (C h7 h238))
  have h315 := S h274
  have h316 := T (T (T (T (T (T (T (T h46 h45) h125) h124) h110) h108) h105) h278) (C h32 (T h272 (C (T (T (T (T (T (T (T (T (T (T (C h128 (C h128 h239)) (C h128 (T (T (C h128 (T (T (T (T (T (T (T (T (T (T h237 h234) h203) h224) h223) h221) h219) h217) h215) h228) h241)) h232) h214))) h208) h207) h143) h142) h140) h139) h138) h10) h6) (T (T (T (T (T (T (T h46 h45) h125) h124) h110) h108) h105) h278))))
  have h317 := T (T (T (T (T (T (T (T (C h316 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (C h47 (T (T (T (T (T (T (T (T h267 h266) h265) h264) h263) h262) h261) h260) h259)) (C h39 (T (T (T (T (T (T (T (T (T (T (T (T (T h258 h257) h255) h254) h252) h251) h249) h248) h246) (C h39 (T (T (T (T (T h190 h189) h186) h185) h182) h181))) (C h47 h224)) (C h43 (T (T h181 h179) h270))) (C h39 h269)) (C h19 (T h244 h239))))) (C h19 (T (T (T (C h47 h237) (C h39 h271)) (C h316 (T (T (T (T (T (T (T (T (T (T (T h234 h178) h134) h131) h130) h129) h79) h29) h26) h13) h10) h6))) h315))) h234) h178) h134) h131) h130) h129) h79) h29) h26) h13) h10) h6)) h315) h232) h214) h202) h136) h75) h74) h31
  have h318 := C h317 (T (T (T (T (T h125 h124) h110) h108) h105) h278)
  have h319 := C h7 (T (T (T (T (T (T (T (T (T h234 h203) h224) h223) h221) h219) h217) h215) h192) h318)
  have h320 := C h317 (T (T (T (T (T (T (T (T h68 h170) h168) h280) h279) h319) h314) h313) h312)
  have h321 := C h7 (T h276 h320)
  have h322 := T (T (T (T (T h289 h282) h281) h321) h311) h306
  have h323 := C h18 h292
  have h324 := C h18 (T h323 (C h18 h322))
  have h325 := C h18 h304
  have h326 := C h18 h325
  have h327 := C h18 h307
  have h328 := C h18 h309
  have h329 := C h18 (T h328 h327)
  have h330 := C h18 (C h18 (T (T (T (T (T (T (T (T (T (T (T (T (T (T h245 h102) h99) h109) h153) h149) h68) h170) h168) h280) h279) h319) h314) h313) h312))
  have h331 := C (T (T (T (T (T (T (T (T (T h25 h78) h175) h174) h173) h300) h330) h329) h326) h324) h302
  have h332 := C h18 (C h18 (T (T (T h245 h172) h162) h146))
  have h333 := C (T (T (T (T (T h332 h199) h195) h194) h122) h57) (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h5 h15) h12) h58) h28) h123) h158) h148) h147) h133) h204) h203) h224) h223) h221) h219) h217) h215) h192) h320) h310)
  have h334 := h v235 v0 y
  have h335 := S h334
  have h336 := h v295 v0 v0
  have h337 := S h336
  have h338 := C (T (T (T (T (T (T (T (T (T h46 h45) h68) h170) h168) h280) h279) h319) h321) (C h7 (C h7 h322))) h302
  have h339 := R (M v3 v295)
  have h340 := C h39 h339
  have h341 := C (T (T (T (T (T h68 h170) h168) h280) h279) h319) (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h340 h338) h337) h293) h290) h193) h190) h189) h186) h185) h182) h181) h179) h178) h134) h131) h130) h129) h79) h29) h26) h13) h10) h6)
  have h342 := C h47 h339
  have h343 := C h47 h342
  have h344 := T (T (T (T (T (T (T (T h30 h85) h80) h135) h226) h230) h242) h298) h333
  have h345 := C h7 (T h290 h318)
  have h346 := C h7 (T h305 h293)
  have h347 := C h7 h308
  have h348 := T (T (T (T (T h347 h346) h345) h314) h313) h312
  have h349 := C (T (T (T (T (T (T (T (T (T (C h7 (C h7 h348)) h345) h277) h240) h238) h160) h144) h82) h38) h37) h344
  have h350 := C h19 (T h336 h349)
  have h351 := R v295
  have h352 := C h39 h351
  have h353 := T (T (T (T (T (T h352 h350) h343) h341) h335) h298) h333
  have h354 := C h128 h353
  have h355 := C h47 h351
  have h356 := C h19 (T h338 h337)
  have h357 := C h39 h340
  have h358 := C (T (T (T (T (T h277 h240) h238) h160) h144) h82) (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h5 h15) h12) h58) h28) h123) h158) h148) h147) h133) h204) h203) h224) h223) h221) h219) h217) h215) h192) h320) h310) h336) h349) h342)
  have h359 := C h128 (T h331 h297)
  have h360 := C h128 h354
  have h361 := C h128 h355
  have h362 := C h128 h361
  have h363 := C h128 h352
  have h364 := T (T (T (T (T (T h301 h299) h334) h358) h357) h356) h355
  have h365 := C h128 h364
  have h366 := C h18 (C h18 (T (T (T (T (T (T (T (T (T (T (T (T (T (T h289 h282) h281) h277) h240) h238) h160) h144) h82) h125) h124) h110) h108) h105) h278))
  have h367 := C h18 (T h325 h323)
  have h368 := C h18 h327
  have h369 := C h18 (T (C h18 h348) h328)
  have h370 := C (T (T (T (T (T (T (T (T (T h369 h368) h367) h366) h332) h199) h195) h194) h122) h57) h344
  have h371 := h v295 v2 x
  have h372 := S h371
  have h373 := C h18 h118
  have h374 := C h18 h76
  have h375 := C (T (T (T (C h18 h374) (C h18 (T (T (T h373 (C h18 h157)) (C h18 (T (T (T (T (T (T (T (T (T h126 h103) h100) h95) h90) h30) h85) h80) h135) h201))) (C h18 h243)))) (C h18 (C h18 (T h298 h333)))) (C h18 (C h18 h364))) h43
  have h376 := h v62 v2 x
  have h377 := C h128 (T (T (T (T (T (T h376 h375) h372) h296) h370) h365) h363)
  have h378 := S h376
  have h379 := C (T (T (T (C h18 (C h18 h353)) (C h18 (C h18 (T h301 h299)))) (C h18 (T (T (T (C h18 h233) (C h18 (T (T (T (T (T (T (T (T (T h177 h136) h75) h74) h31) h89) h113) h156) h155) h154))) (C h18 h127)) h374))) (C h18 h373)) h43
  have h380 := C h47 (T (T (T h377 h362) h360) h359)
  let v381 := M v3 v62
  have h382 := R v381
  have h383 := C h39 h382
  have h384 := C h128 (T (T (T (T (T (T (T h383 h380) h340) h338) h337) h371) h379) h378)
  have h385 := C h128 (T (T (T (T (T (T (T (T (T (T (T h384 h377) h362) h360) h359) h301) h299) h334) h358) h357) h356) h355)
  have h386 := C h47 h382
  have h387 := C h128 h386
  have h388 := C h128 h387
  have h389 := C h128 h383
  have h390 := C h128 (T (T (T (T (T (T h361 h354) h331) h297) h371) h379) h378)
  have h391 := C h128 h363
  have h392 := C h128 h365
  have h393 := C h128 (T h296 h370)
  have h394 := C h39 (T (T (T h393 h392) h391) h390)
  have h395 := C h128 (T (T (T (T (T (T (T h376 h375) h372) h336) h349) h342) h394) h386)
  have h396 := C h128 (T h395 h389)
  have h397 := h v381 y y
  have h398 := S h397
  have h399 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h331 h297) h293) h290) h193) h190) h189) h186) h185) h182) h181) h179) h178) h134) h131) h130) h129) h79) h29) h26) h13) h10) h6) (T (T (T (T (T (T (T (T (T (T (T (T h30 h85) h80) h135) h226) h230) h242) h298) h333) h393) h392) h391) h390)
  have h400 := h v294 v3 v0
  have h401 := h v295 v3 v1
  have h402 := S h401
  have h403 := C h7 (T (T (T (T (T h383 h380) h340) h338) h337) h308)
  have h404 := C (T (T (T (T (T (T (T (T (T (T (T h30 h85) h80) h135) h226) h230) h242) h298) h333) h393) h392) h391) (T (T (T (T (T (T (T (T (T (T h403 h346) h345) h277) h240) h238) h160) h144) h82) h38) h37)
  have h405 := C h7 h386
  have h406 := C h7 h405
  have h407 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h406 h404) h402) h293) h290) h193) h190) h189) h186) h185) h182) h181) h179) h178) h134) h131) h130) h129) h79) h29) h26) h13) h10) h6) (T (T (T (T (T (T (T (T (T (T (T (T (T h46 h45) h68) h170) h168) h280) h279) h319) h314) h313) h312) h309) h400) h399)
  have h408 := h v381 v0 v1
  have h409 := C h32 (T h408 h407)
  have h410 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T h46 h45) h68) h170) h168) h280) h279) h319) h314) h313) h312) h309) h400) h399) h409) (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h396 h388) h385) h354) h331) h297) h293) h290) h193) h190) h189) h186) h185) h182) h181) h179) h178) h134) h131) h130) h129) h79) h29) h26) h13) h10) h6)
  let v411 := M v3 v381
  have h412 := R v411
  have h413 := C h39 h412
  have h414 := T (T h413 h410) h398
  have h415 := C h128 h414
  have h416 := C h47 h412
  have h417 := C h128 (T h387 h384)
  have h418 := C h128 h389
  have h419 := C h128 (T (T (T (T (T (T (T (T (T (T (T h352 h350) h343) h341) h335) h298) h333) h393) h392) h391) h390) h395)
  have h420 := S h400
  have h421 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h5 h15) h12) h58) h28) h123) h158) h148) h147) h133) h204) h203) h224) h223) h221) h219) h217) h215) h192) h320) h310) h296) h370) (T (T (T (T (T (T (T (T (T (T (T (T h377 h362) h360) h359) h301) h299) h232) h214) h202) h136) h75) h74) h31)
  have h422 := S h408
  have h423 := C h7 h383
  have h424 := C h7 h423
  have h425 := C h7 (T (T (T (T (T h305 h336) h349) h342) h394) h386)
  have h426 := C (T (T (T (T (T (T (T (T (T (T (T h362 h360) h359) h301) h299) h232) h214) h202) h136) h75) h74) h31) (T (T (T (T (T (T (T (T (T (T h46 h45) h68) h170) h168) h280) h279) h319) h321) h311) h425)
  have h427 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h5 h15) h12) h58) h28) h123) h158) h148) h147) h133) h204) h203) h224) h223) h221) h219) h217) h215) h192) h320) h310) h401) h426) h424) (T (T (T (T (T (T (T (T (T (T (T (T (T h421 h420) h292) h289) h282) h281) h277) h240) h238) h160) h144) h82) h38) h37)
  have h428 := C h32 (T h427 h422)
  have h429 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T h428 h421) h420) h292) h289) h282) h281) h277) h240) h238) h160) h144) h82) h38) h37) (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h5 h15) h12) h58) h28) h123) h158) h148) h147) h133) h204) h203) h224) h223) h221) h219) h217) h215) h192) h320) h310) h296) h370) h365) h419) h418) h417)
  have h430 := h v381 x v3
  have h431 := S h430
  have h432 := R (M x v411)
  have h433 := C h47 h432
  have h434 := T (T h397 h429) h416
  have h435 := C h39 h434
  have h436 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h5 h15) h12) h58) h28) h123) h158) h148) h147) h133) h204) h203) h224) h223) h221) h219) h217) h215) h192) h320) h310) h336) h349) h342) h394) h386) h435) h433) h128
  have h437 := C h128 (T (T (T (T h436 h431) h397) h429) h416)
  let v438 := M v3 (M y v3)
  have h439 := h v438 y v1
  have h440 := S h439
  have h441 := C h7 (T (T (T (T (T (T (T (T (T h421 h420) h292) h289) h282) h281) h321) h311) h425) h423)
  have h442 := C h7 (T (T (T (T (T (T (T h441 h406) h404) h402) h336) h349) h342) h394)
  have h443 := C h7 (T (T (T (T (T (T (T (T (T h405 h403) h346) h345) h314) h313) h312) h309) h400) h399)
  have h444 := C h7 (T (T (T (T (T (T (T (T (T (T (T h437 h415) h396) h388) h385) h354) h331) h297) h401) h426) h424) h443)
  have h445 := R v438
  have h446 := C h39 h445
  have h447 := C h32 h446
  have h448 := C h32 h447
  have h449 := C h47 h445
  have h450 := C h47 h414
  have h451 := C h39 h432
  have h452 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h451 h450) h383) h380) h340) h338) h337) h293) h290) h193) h190) h189) h186) h185) h182) h181) h179) h178) h134) h131) h130) h129) h79) h29) h26) h13) h10) h6) h128
  have h453 := C h128 (T (T (T (T h413 h410) h398) h430) h452)
  have h454 := C h128 h434
  have h455 := C h39 (T (T (T (T (T (T (T (T (T (T (T (T (T (T h451 h450) h383) h380) h340) h338) h337) h296) h370) h365) h419) h418) h417) h454) h453)
  have h456 := C h47 h433
  have h457 := C h19 (T (T (T (T (T (T (T (T (T (T (T h396 h388) h385) h354) h331) h297) h336) h349) h342) h394) h386) h435)
  have h458 := C h32 (T (T (T (T (T (T (T h427 h422) h397) h429) h457) h456) h455) h449)
  have h459 := C h32 (T h409 h458)
  have h460 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h30 h85) h80) h135) h226) h230) h242) h298) h333) h393) h392) h391) h390) h408) h407) h459) h448) (T (T (T (T (T (T (T (T (T (T (T (T (T h444 h442) h405) h403) h346) h345) h277) h240) h238) h160) h144) h82) h38) h37)
  have h461 := C h7 (T h460 h440)
  have h462 := C h7 (T (T (T (T (T (T (T (T (T (T (T h441 h406) h404) h402) h296) h370) h365) h419) h418) h417) h454) h453)
  have h463 := C h7 (T (T (T (T (T (T (T h380 h340) h338) h337) h401) h426) h424) h443)
  have h464 := C h19 (T (T (T (T (T (T (T (T (T (T (T h450 h383) h380) h340) h338) h337) h296) h370) h365) h419) h418) h417)
  have h465 := C h39 h451
  have h466 := C h47 (T (T (T (T (T (T (T (T (T (T (T (T (T (T h437 h415) h396) h388) h385) h354) h331) h297) h336) h349) h342) h394) h386) h435) h433)
  have h467 := C h32 (T (T (T (T (T (T (T h446 h466) h465) h464) h410) h398) h408) h407)
  have h468 := C h32 (T h467 h428)
  have h469 := C h32 h449
  have h470 := C h32 h469
  have h471 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h470 h468) h427) h422) h377) h362) h360) h359) h301) h299) h232) h214) h202) h136) h75) h74) h31) (T (T (T (T (T (T (T (T (T (T (T (T (T h46 h45) h68) h170) h168) h280) h279) h319) h321) h311) h425) h423) h463) h462)
  have h472 := h v438 v2 v0
  have h473 := S h472
  have h474 := h v381 v2 y
  have h475 := S h474
  have h476 := C h18 (C h18 (T (T (T (T (T (T (T (T h347 h346) h345) h314) h313) h312) h309) h400) h399))
  have h477 := C (T (T (T (T (T (T (T (T (T (T h25 h78) h175) h174) h173) h300) h330) h329) h326) h324) h476) (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h415 h396) h388) h385) h354) h331) h297) h293) h290) h193) h190) h189) h186) h185) h182) h181) h179) h178) h134) h131) h130) h129) h79) h29) h26) h13) h10) h6)
  have h478 := C h128 h416
  have h479 := C h128 h478
  have h480 := C h128 h413
  have h481 := C h128 (T (T (T (T (T (T (T h446 h466) h465) h464) h410) h398) h430) h452)
  have h482 := C h128 (T (T h481 h437) h480)
  have h483 := C h128 h449
  have h484 := C h128 h483
  have h485 := C h128 h446
  have h486 := C h128 (T (T (T (T (T (T (T h436 h431) h397) h429) h457) h456) h455) h449)
  have h487 := C h128 (T h486 h485)
  have h488 := C (T (T (T (T (T (T (T (T (T (T (T h25 h78) h175) h174) h173) h300) h330) h329) h326) h324) h476) (C h18 (C h18 (T (T (T (T (T (T (T (T (T (T (T h421 h420) h292) h289) h282) h281) h321) h311) h425) h423) h463) h462)))) (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h487 h484) h482) h479) h477) h475) h377) h362) h360) h359) h301) h299) h232) h214) h202) h136) h75) h74) h31)
  have h489 := C h7 (T (T (T h488 h473) h439) h471)
  have h490 := C h128 (T h483 h481)
  have h491 := C h128 h485
  have h492 := C h128 (T (T h478 h453) h486)
  have h493 := C h128 h480
  have h494 := C h18 (C h18 (T (T (T (T (T (T (T (T h421 h420) h292) h289) h282) h281) h321) h311) h306))
  have h495 := C (T (T (T (T (T (T (T (T (T (T h494 h369) h368) h367) h366) h332) h199) h195) h194) h122) h57) (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h5 h15) h12) h58) h28) h123) h158) h148) h147) h133) h204) h203) h224) h223) h221) h219) h217) h215) h192) h320) h310) h296) h370) h365) h419) h418) h417) h454)
  have h496 := T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h30 h85) h80) h135) h226) h230) h242) h298) h333) h393) h392) h391) h390) h474) h495) h493) h492) h491) h490
  have h497 := C (T (T (T (T (T (T (T (T (T (T (T (C h18 (C h18 (T (T (T (T (T (T (T (T (T (T (T h444 h442) h405) h403) h346) h345) h314) h313) h312) h309) h400) h399))) h494) h369) h368) h367) h366) h332) h199) h195) h194) h122) h57) h496
  have h498 := h v438 y v0
  have h499 := S h498
  have h500 := C h47 (T h488 h473)
  let v501 := M v3 v438
  have h502 := R (M v3 v501)
  have h503 := C h39 h502
  have h504 := C h32 (T (T (T (T (T (T (T (T (T (T (T (T (T (T h469 h467) h428) h421) h420) h292) h289) h282) h281) h321) h311) h425) h423) h463) h462)
  have h505 := C h32 (T (T (T (T (T (T (T (T (T h466 h465) h464) h410) h398) h408) h407) h459) h448) h504)
  have h506 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h68 h170) h168) h280) h279) h319) h314) h313) h312) h309) h400) h399) h409) h458) h447) h505) (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h503 h500) h446) h466) h465) h464) h410) h398) h377) h362) h360) h359) h301) h299) h232) h214) h202) h136) h75) h74) h31)
  have h507 := C h47 h502
  have h508 := C h47 h507
  have h509 := C h39 (T h472 h497)
  have h510 := C h19 (T (T (T (T (T (T (T (T (T (T (T (T h487 h484) h482) h479) h477) h475) h397) h429) h457) h456) h455) h449) h509)
  have h511 := R v501
  have h512 := C h39 h511
  have h513 := C h7 (T (T (T (T (T (T h512 h510) h508) h506) h499) h472) h497)
  have h514 := C h47 h511
  have h515 := C h7 h514
  have h516 := C h7 h512
  have h517 := C h32 (T (T (T (T (T (T (T (T (T (T (T (T (T (T h444 h442) h405) h403) h346) h345) h314) h313) h312) h309) h400) h399) h409) h458) h447)
  have h518 := C h32 (T (T (T (T (T (T (T (T (T h517 h470) h468) h427) h422) h397) h429) h457) h456) h455)
  have h519 := C h7 (T (T (T (T (T (T h488 h473) h498) (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h518 h469) h467) h428) h421) h420) h292) h289) h282) h281) h277) h240) h238) h160) h144) h82) (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h30 h85) h80) h135) h226) h230) h242) h298) h333) h393) h392) h391) h390) h397) h429) h457) h456) h455) h449) h509) h507))) (C h39 h503)) (C h19 (T (T (T (T (T (T (T (T (T (T (T (T h500 h446) h466) h465) h464) h410) h398) h474) h495) h493) h492) h491) h490))) h514)
  have h520 := C h7 (T (T (T h460 h440) h472) h497)
  have h521 := C h7 (T h439 h471)
  T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h68 h170) h168) h280) h279) h319) h321) h311) h425) h423) h463) h462) h521) h520) h519) h516) (C h7 (T (T (T (T (T (T (T (T (T h510 h508) h506) h499) h439) h471) (C h7 (T h521 h520))) (C h7 h519)) (C h7 h516)) (C h7 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h515 h513) h489) h461) h444) h442) h405) h403) h346) h345) h314) h313) h312) h309) h400) h399) h409) h458) h447) h505) (C h32 (T (T (T (T (T (T (T (T (T (T h517 h470) h468) h427) h422) h474) h495) h493) h492) h491) h490))))))) (C h496 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (C h7 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (C h32 (T (T (T (T (T (T (T (T (T (T h487 h484) h482) h479) h477) h475) h408) h407) h459) h448) h504)) h518) h469) h467) h428) h421) h420) h292) h289) h282) h281) h321) h311) h425) h423) h463) h462) h521) h520) h519) h516)) (C h7 h515)) (C h7 h513)) (C h7 (T h489 h461))) h460) h440) h437) h415) h396) h388) h385) h354) h331) h297) h293) h290) h193) h190) h189) h186) h185) h182) h181) h179) h178) h134) h131) h130) h129) h79) h29) h26) h13) h10) h6))) (S (h v3 v3 y))

