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
theorem Equation2789_implies_Equation16 (G: Type _) [Magma G] (h: Equation2789 G) : Equation16 G := fun x y =>
  let v0 := M y x
  let v1 := M y v0
  let v2 := M v1 v0
  let v3 := M v1 v2
  have h4 := h v1 v0 v3
  have h5 := S h4
  have h6 := R v3
  let v7 := M x y
  let v8 := M x v1
  have h9 := h v1 (M v8 v7) v1
  have h10 := S h9
  have h11 := R v1
  have h12 := h y x v1
  have h13 := C (C h12 h12) h11
  have h14 := T h13 h10
  have h15 := R v0
  have h16 := C h15 h14
  have h17 := S h12
  have h18 := C (C h17 h17) h11
  have h19 := h v0 y y
  have h20 := S h19
  have h21 := R y
  have h22 := T h9 h18
  have h23 := C h22 h21
  have h24 := T h23 h20
  have h25 := C h21 h24
  have h26 := T (T h25 h9) h18
  have h27 := C h15 h26
  let v28 := M v1 y
  have h29 := h v28 y v0
  have h30 := S h29
  have h31 := C h14 h21
  have h32 := T h19 h31
  have h33 := C h21 h32
  have h34 := T (T h13 h10) h33
  have h35 := C h11 h34
  have h36 := C h11 h22
  have h37 := C (T h36 h35) h24
  have h38 := T h37 h30
  have h39 := C h21 h38
  have h40 := C h15 h39
  have h41 := C h11 h14
  have h42 := C h11 h26
  have h43 := C (T h42 h41) h32
  have h44 := T h29 h43
  have h45 := C h21 h44
  have h46 := T (T (T h37 h30) h23) h20
  have h47 := C h46 (T h33 h45)
  have h48 := h y v1 v1
  have h49 := T (T (T (T h48 h47) h40) h27) h16
  have h50 := h v2 v1 y
  have h51 := C (T h50 (C (C h24 h6) h49)) h6
  have h52 := C h11 h24
  have h53 := C h11 h38
  have h54 := h v0 y x
  have h55 := S h54
  have h56 := h x y v0
  have h57 := S h56
  let v58 := M v1 v1
  let v59 := M v58 v28
  have h60 := h v59 y y
  have h61 := S h60
  have h62 := S h48
  have h63 := T (T (T h19 h31) h29) h43
  have h64 := C h63 (T h39 h25)
  have h65 := C h15 h45
  have h66 := C h15 h34
  have h67 := C h15 h22
  have h68 := T (T (T (T h67 h66) h65) h64) h62
  let v69 := M y y
  have h70 := R v69
  have h71 := C (T (T (T h9 h18) (C h70 h33)) (C h70 h45)) h68
  have h72 := T (T (T (T (T h71 h61) h37) h30) h23) h20
  have h73 := R v2
  have h74 := C h73 h72
  let v75 := M v0 v1
  have h76 := h v75 v1 v0
  have h77 := S h76
  have h78 := C (T (T (T (C h70 h39) (C h70 h25)) h13) h10) h49
  have h79 := T (T (T (T (T h19 h31) h29) h43) h60) h78
  have h80 := C h73 h79
  have h81 := C (T h56 h80) h46
  have h82 := R x
  have h83 := C h82 h44
  have h84 := C h82 h32
  have h85 := T (T (T h84 h83) h81) h77
  have h86 := C h11 h85
  have h87 := C h73 h86
  let v88 := M x v0
  have h89 := h v88 v1 y
  have h90 := S h89
  have h91 := T (T (T h66 h65) h64) h62
  have h92 := C h82 h24
  have h93 := C h82 h38
  have h94 := C (T h74 h57) h63
  have h95 := T (T (T h76 h94) h93) h92
  have h96 := C h11 h95
  have h97 := C h32 (T (T h60 h78) h96)
  have h98 := C h15 h44
  have h99 := C h15 h32
  have h100 := C (T (T h99 h98) h97) h91
  let v101 := M v0 v0
  have h102 := R v101
  have h103 := C h102 h67
  have h104 := T (T h103 h100) h90
  have h105 := C h11 h104
  have h106 := C h73 h105
  have h107 := C h102 h16
  have h108 := T (T (T h48 h47) h40) h27
  have h109 := C h15 h24
  have h110 := C h15 h38
  have h111 := C h24 (T (T h86 h71) h61)
  have h112 := C (T (T h111 h110) h109) h108
  have h113 := T (T h89 h112) h107
  have h114 := C h11 h113
  have h115 := C h73 (T (T (T (T (T h29 h43) h60) h78) h96) h114)
  have h116 := T (T (T (T h115 h106) h87) h74) h57
  have h117 := C h49 h116
  have h118 := C h11 (T (T (T (T (T h117 h55) h19) h31) h29) h43)
  have h119 := h (M v2 v28) y y
  have h120 := S h119
  have h121 := C h73 (T (T (T (T (T h105 h86) h71) h61) h37) h30)
  have h122 := C h73 h114
  have h123 := C h73 h96
  have h124 := T (T (T (T h56 h80) h123) h122) h121
  have h125 := C h68 h124
  have h126 := C h68 h91
  have h127 := R v88
  have h128 := h v0 x v0
  have h129 := C (T h128 (C (T (T (T (C h127 h84) (C h127 h83)) (C h85 (T (T h81 h77) h67))) h126) (T h54 h125))) h68
  have h130 := C h68 (T h129 h120)
  have h131 := C h15 h85
  have h132 := R v75
  have h133 := C h132 h131
  have h134 := C h15 h104
  have h135 := C h132 h134
  have h136 := T (T (T (T (T (T (T (T (T (T (T h48 h47) h40) h27) h16) h76) h94) h93) h92) h89) h112) h107
  have h137 := C h15 h136
  have h138 := C h132 h137
  have h139 := C h11 (T (T (T h138 h135) h133) h130)
  have h140 := T (T (T (T (T (T (T (T (T (T (T h103 h100) h90) h84) h83) h81) h77) h67) h66) h65) h64) h62
  have h141 := C h15 h140
  have h142 := C h132 h141
  have h143 := C h49 h137
  have h144 := T h143 h142
  have h145 := C h11 h144
  have h146 := C h68 h141
  let v147 := M v0 y
  let v148 := M v75 v147
  have h149 := h v148 y x
  have h150 := S h149
  have h151 := h v147 y x
  have h152 := S h151
  have h153 := T h138 h146
  have h154 := C h15 h153
  have h155 := C h15 h113
  have h156 := C h132 h155
  have h157 := C h15 h95
  have h158 := C h132 h157
  have h159 := C h49 h108
  have h160 := C (T (C (T (T (T h159 (C h95 (T (T h16 h76) h94))) (C h127 h93)) (C h127 h92)) (T h117 h55)) (S h128)) h49
  have h161 := C h49 (T h119 h160)
  have h162 := C h24 (T (T (T (T (T (T (T (T (T (T (T h71 h61) h37) h30) h23) h20) h54) h125) h161) h158) h156) h142)
  have h163 := R v28
  have h164 := C h163 (T h105 h86)
  have h165 := C h163 h114
  have h166 := C (T (T (T (T (T (T h99 h98) h97) h165) h164) h162) h154) (T (T (T (T (T (T h129 h120) h115) h106) h87) h74) h57)
  have h167 := C h102 h131
  have h168 := C h102 h134
  have h169 := C h102 h137
  have h170 := T (T (T (T (T (T (T (T (T (T (T (T (T (T h169 h168) h167) h166) h152) h137) h134) h131) h129) h120) h115) h106) h87) h74) h57
  have h171 := T (T (T (T (T h54 h125) h161) h158) h156) h142
  have h172 := C h140 h171
  have h173 := h v1 v0 v0
  have h174 := T h173 h172
  have h175 := h v59 y v0
  have h176 := C h11 h45
  have h177 := R v58
  let v178 := M v101 v75
  have h179 := h v178 v1 v1
  have h180 := C (T (T (T (T (T (T (T (T (T (T (T (T (T h48 h47) h40) h27) h16) h76) h94) h93) h92) h89) h112) h107) h179) (C (T (T (T (T (T (T (T (C h177 h105) (C h177 h86)) (C (T (T h36 h35) h176) h72)) (S h175)) h37) h30) h23) h20) h174)) h170
  have h181 := T (T (T h180 h150) h138) h146
  have h182 := C h11 h181
  have h183 := C h102 h141
  have h184 := C h102 h155
  have h185 := C h102 h157
  have h186 := C h163 h105
  have h187 := C h163 (T h96 h114)
  have h188 := C h32 (T (T (T (T (T (T (T (T (T (T (T h138 h135) h133) h130) h117) h55) h19) h31) h29) h43) h60) h78)
  have h189 := C h15 h144
  have h190 := C (T (T (T (T (T (T h189 h188) h187) h186) h111) h110) h109) (T (T (T (T (T (T h56 h80) h123) h122) h121) h119) h160)
  have h191 := h x y v8
  have h192 := R v8
  have h193 := C h82 h14
  have h194 := T (T (T (T (T (T (T (T h84 h83) h81) h77) h67) h66) h65) h64) h62
  have h195 := C h82 h22
  have h196 := h (M v69 v1) v0 y
  have h197 := S h196
  have h198 := h v178 v1 v0
  have h199 := S h198
  have h200 := T (T (T (T (T h138 h135) h133) h130) h117) h55
  have h201 := C (T (T (T h56 h80) h123) h122) h200
  have h202 := T (T (T (T (T (T (T (T (T (T (T (T (T h201 h199) h103) h100) h90) h84) h83) h81) h77) h67) h66) h65) h64) h62
  have h203 := h v75 v0 y
  have h204 := S h203
  have h205 := T (T (T (T (T (T (T (T (T h56 h80) h123) h122) h121) h119) h160) h157) h155) h141
  have h206 := T (T (T (T (T (T (T (T (T (T (T (T (T (T h56 h80) h123) h122) h121) h119) h160) h157) h155) h141) h151) h190) h185) h184) h183
  have h207 := C (T (C h82 h206) (C h205 (T (T (T (T (T (T (T h169 h168) h167) h166) h152) h137) h134) h131))) h202
  have h208 := C (T (T (T h106 h87) h74) h57) h171
  have h209 := T (T (T (T h89 h112) h107) h198) h208
  let v210 := M x x
  have h211 := R v210
  have h212 := C h211 h209
  have h213 := T (T (T (T h201 h199) h103) h100) h90
  have h214 := C h211 h213
  have h215 := T (T (T (T (T (T (T (T (T (T (T (T (T h48 h47) h40) h27) h16) h76) h94) h93) h92) h89) h112) h107) h198) h208
  have h216 := T (T (T (T (T (T (T (T (T h137 h134) h131) h129) h120) h115) h106) h87) h74) h57
  have h217 := C (T (C h216 (T (T (T (T (T (T (T h157 h155) h141) h151) h190) h185) h184) h183)) (C h82 h170)) h215
  have h218 := C (T (T (T (T (C h82 h136) (C h82 h104)) (C h82 h85)) (C h82 (T (T h203 h217) h214))) (C h205 (T (T (T h212 h207) h204) h67))) h202
  have h219 := R v7
  have h220 := C h219 h209
  let v221 := M v7 v88
  have h222 := h v221 x v0
  have h223 := C h219 h213
  have h224 := C (T (T (T (T (C h216 (T (T (T h16 h203) h217) h214)) (C h82 (T (T h212 h207) h204))) (C h82 h95)) (C h82 h113)) (C h82 h140)) h215
  have h225 := T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (C (T (T (T (T (T (T h9 h18) h196) h224) h223) h222) (C (T (T (C h127 (T (C h82 (T (T h220 h218) h197)) h193)) (C h127 h195)) (C h194 h193)) h15)) h192) (S h191)) h56) h80) h123) h122) h121) h119) h160) h157) h155) h141) h151) h190) h185) h184) h183
  have h226 := C h21 h225
  have h227 := C h11 h226
  have h228 := T (T h196 h224) h223
  have h229 := T (T (T (T (T (T (T (T h48 h47) h40) h27) h16) h76) h94) h93) h92
  have h230 := C (T (T (T (T (T (T (C (T (T (C h229 h195) (C h127 h193)) (C h127 (T h195 (C h82 h228)))) h15) (S h222)) h220) h218) h197) h13) h10) h192
  have h231 := T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h169 h168) h167) h166) h152) h137) h134) h131) h129) h120) h115) h106) h87) h74) h57) h191) h230
  have h232 := C h21 h231
  have h233 := S h173
  have h234 := C h136 h200
  have h235 := T h234 h233
  have h236 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (C (T (T (T (T (T (T (T h19 h31) h29) h43) h175) (C (T (T (C h11 h39) h42) h41) h79)) (C h177 h96)) (C h177 h114)) h235) (S h179)) h103) h100) h90) h84) h83) h81) h77) h67) h66) h65) h64) h62) h206
  have h237 := h v221 v0 v0
  have h238 := S h237
  have h239 := h v0 (M v88 v7) v0
  have h240 := S h239
  have h241 := h y x v0
  have h242 := C (C h241 h241) h15
  have h243 := h v28 x x
  let v244 := M v101 v147
  have h245 := h v244 y y
  have h246 := T (T (T (T (T (T (T h212 h207) h204) h67) h66) h65) h64) h62
  have h247 := T (T (T h143 h142) h149) h236
  have h248 := C h132 h67
  have h249 := h v148 x v0
  let v250 := M v210 v88
  have h251 := h v250 v0 v1
  have h252 := h v148 y y
  have h253 := S h252
  have h254 := h v1 v0 v1
  have h255 := C (T h254 (C (T h248 h126) h174)) h246
  have h256 := C h24 (T (T (T h255 h253) h149) h236)
  have h257 := h v250 v1 y
  have h258 := C (T (T (T (T (T (T (T (T (T h48 h47) h40) h27) h16) h203) h217) h214) h257) (C (T (T (T (T (T (T (T (T h256 (C h15 h181)) h189) h188) h187) h186) h111) h110) h109) (T (T (T (T (T (T (T (T (T h48 h47) h40) h27) h16) h203) h217) h214) h251) (C (T (T (T (C (T (T (T h203 h217) h214) (C h211 h84)) (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (C (T (T (T (T (T (T (T (T h54 h125) h161) h158) h156) h142) h249) (C (T (T (C h85 (T (T (T (T (T (T (T (T h201 h199) h103) h100) h90) h84) h83) h81) h77)) h248) h126) (T (T (T (T (T h54 h125) h161) h158) h156) h146))) (C h70 h247)) h246) (S h245)) h169) h168) h167) h166) h152) h137) h134) h131) h129) h120) h115) h106) h87) h74) h57)) (S h243)) h23) h20) (T (T (T (T h9 h18) h196) h224) h223))))) (T h242 h240)
  have h259 := S h241
  have h260 := C (C h259 h259) h15
  let v261 := M v0 x
  have h262 := h v0 y v261
  have h263 := S h262
  have h264 := C h15 h116
  have h265 := C h15 (T (T (T (T (T (T (T (T (T h169 h168) h167) h166) h152) h137) h134) h131) h129) h120)
  have h266 := R v261
  have h267 := h v244 v0 v1
  have h268 := C (T (T (T (T (T (T h151 h190) h185) h184) h183) h267) (C (T (T (C h132 h265) (C h132 h264)) (C h68 h266)) h11)) (T h265 h264)
  have h269 := C h24 h225
  have h270 := C h205 h269
  have h271 := C (T (T (T (T (T (T (T (C h194 (T (T (T (T h270 h268) h263) h239) h260)) h258) h238) h220) h218) h197) h13) h10) (T (T (T (T (T (T (T (T h54 h125) h161) h158) h156) h142) h149) h236) h232)
  let v272 := M v1 v8
  let v273 := M v28 v272
  have h274 := h v273 x v0
  have h275 := C h73 (C h11 (T (T (T (T (T (T (T (T h274 h271) h227) h182) h145) h139) h118) h53) h52))
  have h276 := C h32 h231
  have h277 := C h15 (T (T (T (T (T (T (T (T (T h119 h160) h157) h155) h141) h151) h190) h185) h184) h183)
  have h278 := C h15 h124
  have h279 := C h73 (C h11 (T (T h278 h277) h276))
  have h280 := C h73 (C h11 (T (T h269 h265) h264))
  have h281 := S h274
  have h282 := T (T (T (T (T (T (T (T h226 h180) h150) h138) h135) h133) h130) h117) h55
  have h283 := T (T (T (T (T (T (T h48 h47) h40) h27) h16) h203) h217) h214
  have h284 := C h132 h16
  have h285 := C (T (C (T h159 h284) h235) (S h254)) h283
  have h286 := C h32 (T (T (T h180 h150) h252) h285)
  have h287 := C h15 h247
  have h288 := C (T (T (T (T (T (T (T (T (T (C (T (T (T (T (T (T (T (T h99 h98) h97) h165) h164) h162) h154) h287) h286) (T (T (T (T (T (T (T (T (T (C (T (T (T h19 h31) h243) (C (T (T (T (C h211 h92) h212) h207) h204) (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h56 h80) h123) h122) h121) h119) h160) h157) h155) h141) h151) h190) h185) h184) h183) h245) (C (T (T (T (T (T (T (T (T (C h70 h181) (C (T (T h159 h284) (C h95 (T (T (T (T (T (T (T (T h76 h94) h93) h92) h89) h112) h107) h198) h208))) (T (T (T (T (T h143 h135) h133) h130) h117) h55))) (S h249)) h138) h135) h133) h130) h117) h55) h283)))) (T (T (T (T h220 h218) h197) h13) h10)) (S h251)) h212) h207) h204) h67) h66) h65) h64) h62)) (S h257)) h212) h207) h204) h67) h66) h65) h64) h62) (T h239 h260)
  have h289 := C (T (T (T (T (T (T (T h9 h18) h196) h224) h223) h237) h288) (C h229 (T (T (T (T h242 h240) h262) (C (T (T (T (T (T (T (C (T (T (C h49 h266) (C h132 h278)) (C h132 h277)) h11) (S h267)) h169) h168) h167) h166) h152) (T h278 h277))) (C h216 h276)))) h282
  have h290 := C h11 h232
  have h291 := C h11 h247
  have h292 := C h11 h153
  have h293 := C h11 (T (T (T h161 h158) h156) h142)
  have h294 := C h11 (T (T (T (T (T h37 h30) h23) h20) h54) h125)
  have h295 := C h11 h44
  have h296 := C h11 h32
  have h297 := C h73 (C h11 (T (T (T (T (T (T (T (T h296 h295) h294) h293) h292) h291) h290) h289) h281))
  have h298 := C (T (C (C h32 h6) h68) (S h50)) h6
  have h299 := C h11 (T (T (T (T (T (T h234 h233) h9) h18) h196) h224) h223)
  have h300 := C h11 (T (T (T h39 h25) h173) h172)
  have h301 := T (T (T (T (T (T h296 h295) h294) h293) h292) h291) (C h11 (T (T (T (T (T (T (T (T (T h180 h150) h138) h135) h133) h130) h117) h55) h239) h260))
  let v302 := M v69 v0
  have h303 := T (T (T (T (T (T (T (T (T (T h99 h98) h97) h165) h164) h162) h154) h287) h286) (C h24 (T (T (T (T (T h255 h253) h138) h135) h133) h130))) (C h32 (T (T (T h117 h55) h19) h31))
  have h304 := R v147
  T (T (T (T (T (T (T (T h191 h230) (h v272 v0 y)) (C (T (T (T (T (T (T (C h216 (C h32 (R v272))) h270) h268) h263) (h v0 x v101)) (C (T (T (T (C (T (T (T (T (T (C h205 (T (T (T (T (T h99 h98) h97) h165) h164) h162)) (C h304 (T (T (T h188 h187) h186) h111))) (C h304 h110)) (C h304 h109)) (C h216 h303)) (C h205 (C h24 (T (T (T h23 h20) h239) h260)))) h194) (S (h v302 v0 y))) h242) h240) h303)) (C h32 (T (T (T (T (T (T (T (T (T (T (T (T (C h24 (T (T (T h23 h20) h54) h125)) (C h32 (T (T (T (T (T h161 h158) h156) h142) h252) h285))) h256) (C h15 h232)) (C (T (T (T h239 h260) (h v302 y v1)) (C (T (T (T (T (T (T (T (T (T (T (C (T (T (T (C h21 h22) (C h21 h228)) (C h21 (T (T (T (T (T (T (T (T h220 h218) h197) h13) h10) h4) h298) h297) h280))) (C h49 (T (T (T (T (T (T h279 h275) h51) h5) (h v1 v0 v2)) (C (T (T (T (T (T (C (T (T (T (T (C h32 h296) (C h163 h295)) (C h163 (T h294 h293))) (C h163 (T (T (T h139 h118) h53) h52))) (C h163 h301)) h68) (S (h v302 v1 y))) h242) h240) h19) h31) h301)) (C h24 (T (T (T (C h11 (T (T (T (T (T (T (T (T (T h242 h240) h54) h125) h161) h158) h156) h142) h149) h236)) h290) h289) h281))))) (T (T (T (T (T (T h258 h238) h220) h218) h197) h13) h10)) (S (h v273 v0 v1))) h274) h271) h227) h182) h145) h139) h118) h53) h52) (T (h v1 v0 v58) (C (T (T (T (T (T (T (C (T (T (C h32 h36) (C h163 h41)) (C h163 (T (T (T (T h36 h35) h176) h300) h299))) h68) (S (h v221 v1 y))) h220) h218) h197) h13) h10) h177)))) h282)) (S (h v58 v1 v0))) h36) h35) h176) h300) h299) (C h11 (T h237 h288))) (C h11 (T (T (T (T (T (T (T (T (T (T h258 h238) h220) h218) h197) h13) h10) h4) h298) h297) h280))))) h21)) (S (h (M v2 (M v1 v261)) v1 y))) h279) h275) h51) h5

