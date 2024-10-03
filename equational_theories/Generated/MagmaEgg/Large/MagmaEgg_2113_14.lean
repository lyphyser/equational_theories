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
theorem Equation2113_implies_Equation14 (G: Type _) [Magma G] (h: Equation2113 G) : Equation14 G := fun x y =>
  let v0 := M x y
  let v1 := M y v0
  let v2 := M y v1
  have h3 := h v1 (M v2 v0) v1
  have h4 := S h3
  have h5 := h v1 y v0
  have h6 := R v1
  have h7 := R v0
  have h8 := h y v0 v0
  have h9 := S h8
  let v10 := M v0 v0
  have h11 := R v10
  have h12 := h y x y
  have h13 := C h12 h11
  have h14 := T h13 h9
  have h15 := C (C h14 h7) h6
  have h16 := h v10 y v0
  have h17 := C (T (T h16 h15) (C h5 h6)) h5
  have h18 := S h16
  have h19 := S h12
  have h20 := C h19 h11
  have h21 := T h8 h20
  have h22 := C (C h21 h7) h6
  have h23 := T h17 h4
  have h24 := C h6 h23
  have h25 := T (T h24 h22) h18
  have h26 := C h25 h6
  have h27 := S h5
  have h28 := C (T (T (C h27 h6) h22) h18) h27
  have h29 := T h3 h28
  have h30 := C h6 h29
  have h31 := h v10 y v10
  have h32 := S h31
  have h33 := C (T h8 (C (T (T h19 h8) h20) h11)) h21
  have h34 := h y v0 v1
  have h35 := S h34
  let v36 := M v0 v1
  have h37 := R v36
  let v38 := M v0 y
  have h39 := h v38 v0 v1
  have h40 := S h39
  have h41 := R v38
  have h42 := h v0 v38 v0
  have h43 := S h42
  have h44 := C (C h12 h7) h12
  have h45 := R y
  let v46 := M v10 v1
  have h47 := h v46 v1 v1
  have h48 := S h47
  have h49 := T h16 h15
  have h50 := T (T h16 h15) h30
  have h51 := C h50 h6
  have h52 := C (T (T h3 h28) h51) h49
  have h53 := T (T (T h52 h48) h17) h4
  have h54 := C h53 h45
  have h55 := T h22 h18
  have h56 := C (T (T h26 h17) h4) h55
  have h57 := h v46 v1 v0
  have h58 := S h57
  let v59 := M v1 v0
  have h60 := R v59
  have h61 := C h50 h7
  have h62 := h v0 x y
  have h63 := S h62
  have h64 := C (C h63 h7) h63
  let v65 := M x v0
  let v66 := M v65 y
  have h67 := h v0 v66 v0
  have h68 := C (T (T h67 h64) h61) h60
  have h69 := T (T (T h68 h58) h47) h56
  have h70 := C h69 h45
  have h71 := C (T (T (T h70 h54) h44) h43) h41
  have h72 := h v59 v0 y
  have h73 := C (T h72 h71) h6
  have h74 := h v0 y v0
  have h75 := C (T h74 h73) h37
  have h76 := C (C (T h75 h40) h6) h37
  have h77 := h v36 v0 v1
  have h78 := T (T h77 h76) h35
  have h79 := C h45 h78
  have h80 := C (T (T (T (T (T h79 h33) h32) h16) h15) h30) h6
  have h81 := S h77
  have h82 := S h74
  have h83 := S h72
  have h84 := S h67
  have h85 := C (C h62 h7) h62
  have h86 := C h25 h7
  have h87 := C (T (T h86 h85) h84) h60
  have h88 := T (T (T h52 h48) h57) h87
  have h89 := C h88 h45
  have h90 := T (T (T h3 h28) h47) h56
  have h91 := C h90 h45
  have h92 := C (C h19 h7) h19
  have h93 := C (T (T (T h42 h92) h91) h89) h41
  have h94 := C (T h93 h83) h6
  have h95 := C (T h94 h82) h37
  have h96 := C (C (T h39 h95) h6) h37
  have h97 := T (T h34 h96) h81
  have h98 := h v36 y v1
  have h99 := S h98
  have h100 := R v2
  have h101 := C h45 h97
  have h102 := C (T (C (T (T h13 h9) h12) h11) h9) h14
  have h103 := C (T (T (T (T (T h24 h22) h18) h31) h102) h101) h6
  have h104 := C (T (T (T h3 h28) h51) h103) h100
  have h105 := T (T (T (T h104 h99) h77) h76) h35
  have h106 := C h105 h97
  have h107 := h v38 v0 v0
  have h108 := S h107
  have h109 := h v59 v1 v1
  have h110 := S h109
  have h111 := R (M v1 v1)
  have h112 := C h105 h7
  have h113 := h v2 v1 v0
  have h114 := h v2 v1 y
  have h115 := S h114
  have h116 := T h42 h92
  have h117 := C (T (T (T h80 h26) h17) h4) h100
  have h118 := T (T (T (T h34 h96) h81) h98) h117
  have h119 := C h118 h78
  have h120 := C (T (T (T (T (T (T h24 h22) h18) h31) h102) h101) h119) h116
  have h121 := C (T (T (T h3 h28) h57) h87) h78
  have h122 := C (C (T (T (T (T (T (T (T (T (T (T (T h121 h70) h54) h44) h43) h67) h64) h61) h120) h115) h113) (C h112 h60)) h6) h111
  have h123 := h v36 v1 v1
  have h124 := C (T (T (T (T (T (T h104 h99) h123) h122) h110) h72) h71) h7
  have h125 := C h118 h7
  have h126 := C (T (T (T (T h26 h17) h4) h125) h124) h55
  have h127 := C (T (T (T (T (T (T h68 h58) h47) h126) h108) h39) h95) h6
  have h128 := C h88 h6
  have h129 := C h90 h23
  have h130 := C (T (T (T (T (T h16 h15) h30) h129) h128) h127) h97
  have h131 := T (T h130 h76) h35
  have h132 := C h118 h131
  have h133 := C (T h132 h106) h6
  have h134 := C h53 h29
  have h135 := C h69 h6
  have h136 := S h123
  have h137 := C (T (T (T h68 h58) h17) h4) h97
  have h138 := T h44 h43
  have h139 := C (T (T (T (T (T (T h106 h79) h33) h32) h16) h15) h30) h138
  have h140 := C (C (T (T (T (T (T (T (T (T (T (T (T (C h125 h60) (S h113)) h114) h139) h86) h85) h84) h42) h92) h91) h89) h137) h6) h111
  have h141 := C (T (T (T (T (T (T h93 h83) h109) h140) h136) h98) h117) h7
  have h142 := C (T (T (T (T h141 h112) h3) h28) h51) h49
  have h143 := C (T (T (T (T (T (T h75 h40) h107) h142) h48) h57) h87) h6
  have h144 := C (T (T (T (T (T h143 h135) h134) h24) h22) h18) h78
  have h145 := T (T h34 h96) h144
  have h146 := C h105 h145
  have h147 := h v10 v1 y
  have h148 := S h147
  have h149 := C (T h121 h70) h116
  have h150 := C h6 (T h130 h81)
  have h151 := C h150 h7
  have h152 := T (T (T (T h114 h139) h86) h85) h84
  have h153 := C h6 (T h77 h144)
  let v154 := M v10 y
  have h155 := h v154 x v1
  have h156 := S h155
  let v157 := M x v1
  have h158 := R v157
  have h159 := R x
  have h160 := C h159 h145
  have h161 := C h132 h116
  have h162 := C (T (T (T (T (T h161 h139) h86) h85) h84) h160) h6
  have h163 := h v154 y v0
  have h164 := C (T (T (T (T h34 h96) h144) h163) h162) h158
  have h165 := C (T (T (T (T (T (T (T (T h164 h156) h130) h81) h123) h122) h110) h72) h71) h6
  have h166 := C (T (T (T (T (T (T (T (T h165 h94) h82) h42) h92) h91) h89) h137) h153) h152
  have h167 := h v157 y v1
  have h168 := C (T (T (T (T (T (T (T (T (T h167 h166) h151) h149) h148) h31) h102) h101) h119) h146) h6
  let v169 := M v157 v1
  have h170 := h v169 y v1
  have h171 := S h170
  have h172 := T (T (T (T h67 h64) h61) h120) h115
  have h173 := T (T (T (T (T h168 h133) h80) h26) h17) h4
  have h174 := S h167
  have h175 := S h163
  have h176 := C h146 h138
  have h177 := C h159 h131
  have h178 := C (T (T (T (T (T h177 h67) h64) h61) h120) h176) h6
  have h179 := C (T (T (T (T h178 h175) h130) h76) h35) h158
  have h180 := C (T (T (T (T (T (T (T (T h93 h83) h109) h140) h136) h77) h144) h155) h179) h6
  have h181 := C (T (T (T (T (T (T (T (T h150 h121) h70) h54) h44) h43) h74) h73) h180) h172
  have h182 := C h153 h7
  have h183 := C (T h89 h137) h138
  have h184 := C (T (T (T (T (T (T (T (T (T h132 h106) h79) h33) h32) h147) h183) h182) h181) h174) h6
  have h185 := C (T h119 h146) h6
  have h186 := T (T (T (T (T h3 h28) h51) h103) h185) h184
  have h187 := C h160 h173
  have h188 := T (T (T (T (T h187 h178) h175) h130) h76) h35
  have h189 := C h188 h186
  have h190 := C h177 h186
  have h191 := C (T (T (T (T h164 h156) h163) h162) h190) h6
  have h192 := h v154 v0 v1
  have h193 := S h192
  have h194 := T (T (T (T (T h150 h121) h70) h54) h44) h43
  have h195 := C h194 h145
  have h196 := T (T (T (T (T h42 h92) h91) h89) h137) h153
  have h197 := C h196 h78
  have h198 := C (T h197 h195) h6
  have h199 := C (T (T (T (T (T (T (T (T (T (T (T h132 h106) h79) h33) h32) h16) h15) h30) h129) h128) h127) h198) h97
  have h200 := C h194 h97
  have h201 := C h196 h131
  have h202 := C (T h201 h200) h6
  have h203 := T (T (T (T h167 h166) h151) h149) h148
  have h204 := C (T h125 h124) h203
  have h205 := T (T (T (T (T h204 h108) h39) h95) h197) h195
  have h206 := C h205 h6
  have h207 := T (T (T (T h147 h183) h182) h181) h174
  have h208 := C (T h141 h112) h207
  have h209 := T (T (T (T h3 h28) h47) h126) h208
  have h210 := C h209 h173
  have h211 := T (T (T (T (T (T (T (T (T (T (T (T (T h210 h206) h202) h143) h135) h134) h24) h22) h18) h31) h102) h101) h119) h146
  have h212 := C h211 h45
  have h213 := h v169 x v0
  have h214 := S h213
  have h215 := R v65
  have h216 := C h159 h186
  have h217 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T h210 h206) h202) h143) h135) h134) h24) h22) h18) h147) h183) h182) h181) h174) h216) h7
  have h218 := T (T (T (T h204 h142) h48) h17) h4
  have h219 := C h218 h186
  have h220 := T (T (T (T (T h201 h200) h75) h40) h107) h208
  have h221 := C h220 h6
  have h222 := T (T (T (T (T (T (T (T (T (T (T (T (T h132 h106) h79) h33) h32) h16) h15) h30) h129) h128) h127) h198) h221) h219
  have h223 := C h222 h7
  have h224 := C (T (T (T (T (T (T h67 h64) h61) h120) h176) h223) h217) h215
  have h225 := C (C (T (T (T (T (T (T (T h224 h214) h168) h133) h80) h26) h17) h4) h186) h78
  have h226 := h v65 v0 v1
  have h227 := h v65 x y
  have h228 := S h227
  have h229 := C (T (T (T (T h187 h178) h175) h155) h179) h6
  have h230 := T (T (T (T (T h34 h96) h144) h163) h162) h190
  have h231 := C h230 h173
  have h232 := T (T (T (T (T (T (T h226 h225) h212) h199) h193) h130) h76) h35
  have h233 := C h232 h186
  have h234 := T (T (T (T (T h233 h231) h229) h165) h94) h82
  have h235 := S h226
  have h236 := C h211 h7
  have h237 := C h159 h173
  have h238 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T h237 h167) h166) h151) h149) h148) h16) h15) h30) h129) h128) h127) h198) h221) h219) h7
  have h239 := C (T (T (T (T (T (T h238 h236) h161) h139) h86) h85) h84) h215
  have h240 := C (C (T (T (T (T (T (T (T h3 h28) h51) h103) h185) h184) h213) h239) h173) h97
  have h241 := C h222 h45
  have h242 := C (T (T (T (T (T (T (T (T (T (T (T h202 h143) h135) h134) h24) h22) h18) h31) h102) h101) h119) h146) h78
  have h243 := C h159 (T (T (T (T h192 h242) h241) h240) h235)
  have h244 := C (T (T (T (T (T (T (T (T h3 h28) h51) h103) h185) h184) h213) h239) (C (T h160 h243) h232)) h234
  have h245 := C (T (T (T (T (T (T (T (T (T (T h244 h228) h226) h225) h212) h199) h193) h163) h162) h190) (C (T (T (T (T h74 h73) h180) h191) h189) h173)) h172
  have h246 := T (T (T (T (T (T (T h34 h96) h144) h192) h242) h241) h240) h235
  have h247 := C h246 h173
  have h248 := T (T (T (T (T h74 h73) h180) h191) h189) h247
  have h249 := C h159 (T (T (T (T h226 h225) h212) h199) h193)
  have h250 := C (T (T (T (T (T (T (T (T (C (T h249 h177) h246) h224) h214) h168) h133) h80) h26) h17) h4) h248
  have h251 := C (T (T (T (T (T (T (T (T (T h34 h96) h144) h192) h242) h241) h240) h235) h227) h250) h234
  have h252 := C h159 h234
  have h253 := C (T (T (T (T (T (T (T (T h252 h226) h225) h212) h199) h193) h130) h76) h35) h248
  have h254 := C h159 h248
  have h255 := C h254 h7
  let v256 := M v65 v0
  have h257 := h v256 y v0
  have h258 := S h257
  have h259 := C h252 h7
  have h260 := C (T (T (T (T (T (T (T (T h34 h96) h144) h192) h242) h241) h240) h235) h254) h234
  have h261 := C (T (T (T (T (T (T (T (T (T h244 h228) h226) h225) h212) h199) h193) h130) h76) h35) h248
  have h262 := C (T (T (T (T (T (T (T (T (T (T (C (T (T (T (T h231 h229) h165) h94) h82) h186) h187) h178) h175) h192) h242) h241) h240) h235) h227) h250) h152
  have h263 := T (T (T (T (T (T (T (T (T (T h3 h28) h51) h103) h185) h184) h170) h262) h261) h260) h259
  have h264 := h v65 y v0
  have h265 := S h264
  have h266 := h v154 y v1
  have h267 := h v157 v1 v0
  have h268 := C (T (T (T (T (T (T (T (T (T h249 h177) h67) h64) h61) h120) h176) h223) h217) (C (T (T (T h237 h267) (C (T (T (T (T (C (T (T (T (T (T h204 h142) h48) h51) h103) h185) h172) (S h266)) h163) h162) h190) (T (T (T (T (T h109 h140) h136) h77) h76) h35))) (C h188 h246)) h7)) h6
  let v269 := M v65 v1
  have h270 := h v269 v1 v1
  have h271 := S h270
  have h272 := C (T (T (T (T (T (T h74 h73) h180) h191) h189) h247) (C (T h227 h250) h6)) (T (T (T (T (T (T h167 h166) h151) h149) h148) h16) h15)
  have h273 := T (T (T (T (T (T (T (T (T h272 h271) h233) h231) h229) h165) h94) h82) h160) h243
  have h274 := C h273 h6
  have h275 := C h7 h207
  have h276 := C h275 h6
  have h277 := T (T (T (T (T (T (T (T (T (T h255 h253) h251) h245) h171) h168) h133) h80) h26) h17) h4
  have h278 := C h7 h203
  have h279 := C (T (T (T (T (T (T (C (T h244 h228) h6) h233) h231) h229) h165) h94) h82) (T (T (T (T (T (T h22 h18) h147) h183) h182) h181) h174)
  have h280 := T (T (T (T (T (T (T (T h74 h73) h180) h191) h189) h247) h270) h279) h278
  have h281 := C h280 h277
  have h282 := C (T (T (T (T (T (T (T (T (T (T (T (T h281 h276) h274) h268) h265) h226) h225) h212) h199) h193) h130) h76) h35) h263
  have h283 := T (T (T (T (T (T (T (T h275 h272) h271) h233) h231) h229) h165) h94) h82
  have h284 := C h283 h263
  have h285 := C h278 h6
  have h286 := T (T (T (T (T (T (T (T (T h249 h177) h74) h73) h180) h191) h189) h247) h270) h279
  have h287 := C h286 h6
  have h288 := C (T (T (T (T (T (T (T (T (T (C (T (T (T (C h230 h232) (C (T (T (T (T h187 h178) h175) h266) (C (T (T (T (T (T h133 h80) h26) h47) h126) h208) h152)) (T (T (T (T (T h34 h96) h81) h123) h122) h110))) (S h267)) h216) h7) h238) h236) h161) h139) h86) h85) h84) h160) h243) h6
  have h289 := T (T (T (T (T h252 h264) h288) h287) h285) h284
  have h290 := C h289 h6
  have h291 := T (T (T (T (T (T (T (T h251 h245) h171) h168) h133) h80) h26) h17) h4
  have h292 := C (T (T (T (C h291 h248) h244) h228) h254) h6
  have h293 := h v269 y v0
  have h294 := T (T (T (T (T (T (T (T (T h74 h73) h180) h191) h189) h247) h293) h292) h290) h282
  have h295 := C h283 h248
  have h296 := C h278 h7
  have h297 := C h286 h7
  have h298 := C (T (T (T (T (T (T (T (T h201 h200) h75) h40) h107) h142) h48) h17) h4) h145
  have h299 := C h205 h45
  have h300 := C h209 h232
  have h301 := T (T (T (T (T (T (T (T (T (T h300 h299) h298) h150) h121) h70) h54) h44) h43) h160) h243
  have h302 := C h301 h7
  have h303 := C h218 h246
  have h304 := C h220 h45
  have h305 := C (T (T (T (T (T (T (T (T h3 h28) h47) h126) h108) h39) h95) h197) h195) h131
  have h306 := T (T (T (T (T (T (T (T (T (T (T (T (T h231 h229) h165) h94) h82) h42) h92) h91) h89) h137) h153) h305) h304) h303
  have h307 := C h306 h7
  have h308 := C (T (T (T (T (T (T (T (T (T (T (T (T h299 h298) h150) h121) h70) h54) h44) h43) h74) h73) h180) h191) h189) h138
  have h309 := h v157 v1 y
  have h310 := C h159 (T (T (T (T h255 h253) h251) h245) h171)
  have h311 := C (T (T (T (T (T (T (T (T (T h310 h237) h309) h308) h307) h302) h297) h296) h295) (C h294 h234)) h6
  have h312 := C h159 (T (T (T (T h170 h262) h261) h260) h259)
  have h313 := h v10 v0 v1
  have h314 := S h313
  have h315 := C (T (T (T (T (T h244 h228) h264) h288) h287) h285) h97
  have h316 := T (T h252 h227) h250
  have h317 := C h316 h45
  have h318 := T (T (T (T (T h281 h276) h274) h268) h265) h254
  have h319 := C h318 h45
  have h320 := C (T (T (T (T h264 h288) h287) h285) h284) h45
  have h321 := h v66 y x
  have h322 := S h321
  have h323 := h v65 x v1
  have h324 := S h323
  have h325 := T (T (T (T (T (T (T (T (T h320 h319) h317) h315) h314) h147) h183) h182) h181) h174
  have h326 := C (T (T (T (T (T (T (T (T (T h34 h96) h144) h192) h242) h241) h240) h235) h264) h288) h325
  have h327 := C (T (T (T (T (T (T h326 h324) h264) h288) h287) h285) h284) h159
  have h328 := C (T (T (T (T h281 h276) h274) h268) h265) h45
  have h329 := C h289 h45
  have h330 := T (T h244 h228) h254
  have h331 := C h330 h45
  have h332 := C (T (T (T (T (T h276 h274) h268) h265) h227) h250) h78
  have h333 := T (T (T (T (T (T (T (T (T h167 h166) h151) h149) h148) h313) h332) h331) h329) h328
  have h334 := C (T (T (T (T (T (T (T (T (T h268 h265) h226) h225) h212) h199) h193) h130) h76) h35) h333
  have h335 := C (T h323 h334) h159
  have h336 := h x x y
  have h337 := S h336
  have h338 := C (C h337 h7) h337
  let v339 := M x x
  have h340 := h v0 (M v339 y) v0
  have h341 := S h293
  have h342 := T (T (T (T (T (T (T (T h3 h28) h51) h103) h185) h184) h170) h262) h261
  have h343 := C (T (T (T h252 h227) h250) (C h342 h234)) h6
  have h344 := C h318 h6
  have h345 := C (T (T (T (T (T (T (T (T (T (T (T (T h34 h96) h144) h192) h242) h241) h240) h235) h264) h288) h287) h285) h284) h277
  have h346 := C (T (T (T (T (T (T (T (T (T h326 h324) h226) h225) h212) h199) h193) h130) h76) h35) h263
  have h347 := h v65 x x
  have h348 := R v339
  let v349 := M v0 x
  have h350 := h v349 v0 v1
  have h351 := R v349
  have h352 := S h340
  have h353 := C (C h336 h7) h336
  have h354 := C (T h326 h324) h159
  have h355 := C (T (T (T (T (T (T h281 h276) h274) h268) h265) h323) h334) h159
  have h356 := h v256 v0 x
  have h357 := h v256 x y
  have h358 := h v10 v0 y
  have h359 := S h358
  have h360 := C (T (T (T (T (T h251 h245) h171) h213) (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T h238 h236) h161) h139) h86) h85) h84) h74) h73) h180) h191) h189) h247) h270) h279) h232)) (C h278 h45)) (T (T (T (T h3 h28) h47) h126) h108)
  have h361 := C h342 h277
  have h362 := C (T (T (T (T (T (T (T (T (T h361 h360) h359) h147) h183) h182) h181) h174) h216) h312) h45
  have h363 := C h291 h263
  have h364 := C (T (T (T (T (T (C h275 h45) (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T h272 h271) h233) h231) h229) h165) h94) h82) h67) h64) h61) h120) h176) h223) h217) h246)) h214) h170) h262) h261) (T (T (T (T h107 h142) h48) h17) h4)
  have h365 := S h309
  have h366 := C (T (T (T (T (T (T (T (T (T (T (T (T h231 h229) h165) h94) h82) h42) h92) h91) h89) h137) h153) h305) h304) h116
  have h367 := T (T (T (T (T (T (T (T (T (T (T (T (T h300 h299) h298) h150) h121) h70) h54) h44) h43) h74) h73) h180) h191) h189
  have h368 := C h367 h7
  have h369 := T (T (T (T (T (T (T (T (T (T h249 h177) h42) h92) h91) h89) h137) h153) h305) h304) h303
  have h370 := C h369 h7
  have h371 := C h273 h7
  have h372 := C h275 h7
  have h373 := C h280 h234
  have h374 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T h373 h372) h371) h370) h368) h366) h365) h167) h166) h151) h149) h148) h358) h364) h363) h45
  have h375 := C (T (T (T (T (T (T (T (T (T (T (T h147 h183) h182) h181) h174) h309) h308) h307) h302) h297) h296) h295) h232
  have h376 := h y x v0
  have h377 := h v66 y v0
  have h378 := C (T (T (T (C (T (T (T (T (T (T (T (T (T (T h376 h375) h374) h362) (C (T (T (T (T (T (T (T (T (T (T (T (T (T h310 h237) h167) h166) h151) h149) h148) h313) h332) h331) h329) h328) h377) (C (T (T (T (C (T (T (T (T (T (T (T (T (T (T (T (T (T h326 h324) h226) h225) h212) h199) h193) h130) h76) h35) h376) h375) h374) h362) h7) (S h357)) h356) (C (T (T (T h355 h354) h353) h352) h351)) h6)) h97)) (S h350)) (C (T (T (T (T h42 h92) h91) h89) h137) h159)) (C h153 h159)) (C (T (T (T (T (T (T (T (T (T (T h150 h121) h70) h54) h44) h43) h74) h73) h180) h191) h189) h159)) (C h306 h159)) (C h301 h159)) h348) (S h347)) h323) h334) h6
  have h379 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T h378 h346) h345) h344) h343) h341) h233) h231) h229) h165) h94) h82) h340) h338) h335) (T (T (T (T (T (T (T (T (T (T (T (T h114 h139) h86) h85) h84) h340) h338) h335) h327) (C h318 h159)) (C h316 h159)) (C (T (T (T (T (T (T (T (T (T h244 h228) h226) h225) h212) h199) h193) h163) h162) h190) h159)) (C h188 h159))
  have h380 := h v339 y v1
  have h381 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T h380 h379) h322) h320) h319) h317) h315) h314) h147) h183) h182) h181) h174) h216) h312) h6
  let v382 := M v339 v1
  have h383 := S h380
  have h384 := S h376
  have h385 := C (T (T (T (T (T (T (T (T (T (T (T h373 h372) h371) h370) h368) h366) h365) h167) h166) h151) h149) h148) h246
  have h386 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T h361 h360) h359) h147) h183) h182) h181) h174) h309) h308) h307) h302) h297) h296) h295) h45
  have h387 := C (T (T (T (T (T (T (T (T (T h310 h237) h167) h166) h151) h149) h148) h358) h364) h363) h45
  have h388 := C (T (T (T (T (T (T (T (T (T (T (C h369 h159) (C h367 h159)) (C (T (T (T (T (T (T (T (T (T (T h231 h229) h165) h94) h82) h42) h92) h91) h89) h137) h153) h159)) (C h150 h159)) (C (T (T (T (T h121 h70) h54) h44) h43) h159)) h350) (C (T (T (T (T (T (T (T (T (T (T (T (T (T (C (T (T (T (C (T (T (T h340 h338) h335) h327) h351) (S h356)) h357) (C (T (T (T (T (T (T (T (T (T (T (T (T (T h387 h386) h385) h384) h34) h96) h144) h192) h242) h241) h240) h235) h323) h334) h7)) h6) (S h377)) h320) h319) h317) h315) h314) h147) h183) h182) h181) h174) h216) h312) h78)) h387) h386) h385) h384) h348
  have h389 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T h354 h353) h352) h74) h73) h180) h191) h189) h247) h293) h292) h290) h282) (C (T (T (T (T (T (T (T (T (T h34 h96) h144) h192) h242) h241) h240) h235) h323) h334) h277)) (C (T (T (T h326 h324) h347) h388) h6)) (T (T (T (T (T (T (T (T (T (T (T (T (C h230 h159) (C (T (T (T (T (T (T (T (T (T h187 h178) h175) h192) h242) h241) h240) h235) h227) h250) h159)) (C h330 h159)) (C h289 h159)) h355) h354) h353) h352) h67) h64) h61) h120) h115)
  have h390 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T h310 h237) h167) h166) h151) h149) h148) h313) h332) h331) h329) h328) h321) h389) h383) h6
  have h391 := T (T (T (T (T (T (T (T (T h345 h344) h343) h341) h233) h231) h229) h165) h94) h82
  have h392 := C (T (T (T (T (T (T (T (T (T (C h391 h248) h373) h372) h371) h370) h368) h366) h365) h216) h312) h6
  have h393 := T (T h321 h389) h383
  have h394 := h v0 x v1
  have h395 := S h394
  have h396 := C h248 h325
  have h397 := C h7 (T (T h380 h379) h322)
  have h398 := C h7 h393
  have h399 := C h234 h333
  have h400 := T (T (T (T (T (T (T (T (T (T (T (T (T h381 h311) h258) h255) h253) h251) h245) h171) h168) h133) h80) h26) h17) h4
  T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (h x x v1) (C (T (h v382 y v0) (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h34 h96) h144) h192) h242) h241) h240) h235) h264) h288) h287) h285) h284) (C h294 h277)) (C (T (T (T (T (T (T (T (T (T (T (T h345 h344) h343) h341) h233) h231) h229) h165) h94) h82) h394) h399) h6)) (C h398 h6)) (C (T (T h397 h396) h395) (T (T (T (T (T (T (T (T (T (T (T (T (T h3 h28) h51) h103) h185) h184) h170) h262) h261) h260) h259) h257) h392) h390))) h400) (C (T (T (T (T (T (T (T (T (T (T (C (T (T h394 h399) h398) h400) (C h397 h6)) (C (T (T (T (T (T (T (T (T (T (T (T h396 h395) h74) h73) h180) h191) h189) h247) h293) h292) h290) h282) h6)) (C h391 h263)) h281) h276) h274) h268) h265) h347) h388) h6)) h378) h346) h345) h344) h343) h341) h233) h231) h229) h165) h94) h82) h394) h399) h398) h7) (C (T (T (T (T (T h397 h396) h395) (h v0 x v0)) (C (T (h v256 x v1) (C (T (T (T (T (T (T (T (T (T (T (T (T h311 h258) h255) h253) h251) h245) h171) h168) h133) h80) h26) h17) h4) h333)) h232)) (C (C h6 h393) h45)) h116)) (S (h v339 v1 y))) h380) h379) h322) h320) h319) h317) h315) h314) h147) h183) h182) h181) h174) h216) h312) (C h159 (T (T h257 h392) h390))) h6)) h158)) (S (h v382 x v1))) h381) h311) h258) h255) h253) h251) h245) h171) h168) h133) h80) h26) h17) h4

