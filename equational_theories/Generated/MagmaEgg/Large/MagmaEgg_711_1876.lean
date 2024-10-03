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
theorem Equation711_implies_Equation1876 (G: Type _) [Magma G] (h: Equation711 G) : Equation1876 G := fun x y z =>
  let v0 := M y z
  let v1 := M z y
  let v2 := M x v0
  let v3 := M v2 v1
  let v4 := M v3 v0
  let v5 := M v4 v0
  have h6 := h v0 v3 x
  have h7 := S h6
  have h8 := R x
  let v9 := M v0 x
  let v10 := M v9 x
  let v11 := M v0 v10
  have h12 := h v0 v2 v11
  have h13 := S h12
  have h14 := R v11
  have h15 := h v0 v0 x
  have h16 := T h15 (C h15 h14)
  have h17 := R v2
  have h18 := C h17 (C h17 h16)
  have h19 := T h18 h13
  have h20 := C h19 h8
  have h21 := C h20 h8
  have h22 := R v3
  have h23 := C h22 h21
  have h24 := S h15
  have h25 := T (C h24 h14) h24
  have h26 := C h17 (C h17 h25)
  have h27 := T h12 h26
  have h28 := C h27 h8
  have h29 := C h28 h8
  have h30 := h x v2 v0
  have h31 := S h30
  have h32 := C h17 h27
  let v33 := M v2 v0
  have h34 := h v33 v0 v2
  have h35 := S h34
  have h36 := R v0
  have h37 := T h32 h31
  have h38 := C h37 h36
  let v39 := M v33 v0
  have h40 := h v39 v3 v1
  have h41 := S h40
  have h42 := R v1
  have h43 := C h17 h19
  have h44 := T h30 h43
  have h45 := C h44 h36
  have h46 := C h45 h42
  have h47 := C h22 (C h46 h42)
  have h48 := h v1 v1 x
  have h49 := S h48
  let v50 := M v1 (M (M v1 x) x)
  have h51 := R v50
  have h52 := C h22 (C h22 (T (C h49 h51) h49))
  have h53 := h v1 v3 v50
  have h54 := T (T h53 h52) h47
  have h55 := C h38 h42
  have h56 := h v39 v1 v1
  have h57 := S h56
  have h58 := S h53
  have h59 := C h22 (C h22 (T h48 (C h48 h51)))
  have h60 := C h22 (C h55 h42)
  have h61 := T (T h60 h59) h58
  have h62 := C h46 h61
  have h63 := T (T h45 h40) h62
  have h64 := C h22 h63
  have h65 := T (T (T h64 h60) h59) h58
  have h66 := C h42 (C h65 h63)
  have h67 := C (T h66 h57) h42
  have h68 := C (T h67 h55) h54
  have h69 := C h44 h17
  have h70 := C h8 (C h8 h25)
  have h71 := h v0 x v11
  have h72 := C (T (T h71 h70) h69) (T (T h68 h41) h38)
  have h73 := C h36 h72
  let v74 := M v1 (M (M v3 v2) v2)
  have h75 := h v74 v0 v1
  have h76 := C h55 h54
  have h77 := T (T h76 h41) h38
  have h78 := C h22 h77
  have h79 := T (T (T h53 h52) h47) h78
  have h80 := C h42 (C h79 h77)
  have h81 := C h36 (T (T (T (T (T h68 h41) h56) h80) h75) h73)
  have h82 := C (T h56 h80) h42
  have h83 := C (T h46 h82) h61
  have h84 := S h71
  have h85 := C h8 (C h8 h16)
  have h86 := C h37 h17
  have h87 := C (T (T h86 h85) h84) (T (T h45 h40) h83)
  have h88 := C h27 (T (T (T h81 h35) h32) h31)
  have h89 := T (T (T (T (T h45 h56) h80) h75) h88) h20
  have h90 := C h89 (T (T (T (T h87 h81) h35) h32) h31)
  have h91 := S h75
  have h92 := C h36 h87
  have h93 := C h36 (T (T (T (T (T h92 h91) h66) h57) h40) h83)
  have h94 := h v33 v2 v2
  have h95 := S h94
  have h96 := C h19 (T (T (T h30 h43) h34) h93)
  have h97 := T (T (T (T (T h28 h96) h91) h66) h57) h38
  have h98 := C h97 (T (T (T (T h30 h43) h34) h93) h72)
  have h99 := C h17 (T h21 h98)
  have h100 := C h17 (T (T (T (T h99 h95) h34) h93) h72)
  let v101 := M v2 v33
  have h102 := h v101 v2 x
  have h103 := h v101 y x
  have h104 := S h103
  have h105 := C (T (T (T (T h45 h56) h80) h75) h88) h8
  let v106 := M v2 x
  have h107 := h v106 x x
  have h108 := S h107
  have h109 := C (T (T (T (T h96 h91) h66) h57) h38) h8
  have h110 := T h29 h109
  have h111 := C h110 h8
  have h112 := C h111 h8
  have h113 := h v74 v3 v1
  have h114 := S h113
  have h115 := C h22 (T h76 h83)
  have h116 := C (T (T h28 h96) h91) h42
  have h117 := C (T (T h116 h67) h55) (T (T (T h53 h52) h47) h115)
  have h118 := C h44 (T (T (T (T h117 h114) h66) h57) h38)
  have h119 := C h22 (T h68 h62)
  have h120 := C (T (T h75 h88) h20) h42
  have h121 := C (T (T h46 h82) h120) (T (T (T h119 h60) h59) h58)
  have h122 := h v9 x v1
  have h123 := S h122
  have h124 := C h37 (T (T (T (T h45 h56) h80) h113) h121)
  have h125 := C (T (C h97 h27) h31) (T (T (T h71 h70) h69) h124)
  have h126 := T (T (T (T (T (T h125 h123) h28) h96) h91) h113) h121
  have h127 := C h8 h126
  have h128 := C (T h30 (C h89 h19)) (T (T (T h118 h86) h85) h84)
  have h129 := T (T (T (T (T (T (T h45 h56) h80) h75) h88) h20) h122) h128
  have h130 := C h36 (T (T (T h117 h114) h75) h73)
  have h131 := C h36 h126
  have h132 := S h102
  have h133 := C h17 (T h90 h29)
  have h134 := C h17 (T (T (T (T h87 h81) h35) h94) h133)
  have h135 := T (T (T (T (T (T h105 h21) h98) h134) h132) h18) h13
  have h136 := C h135 h129
  have h137 := C (T (T (T (T (T h136 h131) h130) h35) h32) h31) h129
  have h138 := C h17 (T (T (T (T (T (T (T (T (T h137 h127) h118) h86) h85) h84) h12) h26) h102) h100)
  have h139 := C (C h110 h17) h17
  have h140 := C h17 h139
  have h141 := T h105 h21
  have h142 := C h141 h8
  have h143 := T (T (T (T (T (T h12 h26) h102) h100) h90) h29) h109
  have h144 := C h143 (T (T (T (T h131 h130) h35) h32) h31)
  have h145 := h v9 v0 v0
  have h146 := T (T (T (T (T (T (T (T h45 h56) h80) h75) h88) h20) h145) h144) h142
  have h147 := C h146 (T (T (T (T h140 h138) h95) h32) h31)
  have h148 := h v10 v2 v2
  have h149 := T (T (T (T (T (T (T (T (T (T (T (T (T h139 h137) h127) h118) h86) h85) h84) h12) h26) h102) h100) h90) h148) h147
  have h150 := C (C h141 h17) h17
  have h151 := T (T (T (T (T (T (T h125 h123) h28) h96) h91) h66) h57) h38
  have h152 := C h143 h151
  have h153 := T (T (T (T (T (T h117 h114) h75) h88) h20) h122) h128
  have h154 := C h36 h153
  have h155 := C h36 (T (T (T h92 h91) h113) h121)
  have h156 := C (T (T (T (T (T h30 h43) h34) h155) h154) h152) h151
  have h157 := h v9 x v0
  have h158 := S h145
  have h159 := C h135 (T (T (T (T h30 h43) h34) h155) h154)
  have h160 := S h148
  have h161 := C h17 h150
  have h162 := C h8 h153
  have h163 := C h17 (T (T (T (T (T (T (T (T (T h134 h132) h18) h13) h71) h70) h69) h124) h162) h156)
  have h164 := T (T (T (T (T (T (T (T h111 h159) h158) h28) h96) h91) h66) h57) h38
  have h165 := C h164 (T (T (T (T h30 h43) h94) h163) h161)
  have h166 := C h142 h8
  have h167 := C (T (T (T (T h166 h165) h160) h29) h109) h8
  have h168 := C h8 (T (T (T (T (T (T (T h167 h159) h158) h157) (C h8 h156)) (C h8 h150)) (C h8 h149)) (C h8 h112))
  have h169 := C (T (T (T (T h105 h21) h148) h147) h112) h8
  have h170 := T (T (T (T (T (T (T (T h45 h56) h80) h75) h88) h20) h145) h144) h169
  have h171 := T (T (T (T (T (T (T (T h167 h159) h158) h28) h96) h91) h66) h57) h38
  have h172 := C h143 h171
  have h173 := T h111 h169
  have h174 := C h36 h173
  have h175 := C h36 h142
  have h176 := T (T (T (T (T (T (T (T h175 h174) h172) h136) h131) h130) h35) h32) h31
  have h177 := C h176 h170
  have h178 := C h36 h111
  have h179 := T h167 h142
  have h180 := C h36 h179
  have h181 := C h135 h170
  have h182 := T (T (T (T (T (T (T (T h30 h43) h34) h155) h154) h152) h181) h180) h178
  have h183 := C h182 h164
  have h184 := C h8 h142
  let v185 := M v106 x
  let v186 := M x v185
  have h187 := h v186 v2 v2
  have h188 := S h187
  have h189 := h v9 v0 x
  have h190 := C (T (T (T (T (T (T (T (T (T h177 h168) h108) h105) h21) h98) h134) h132) h18) h13) h146
  have h191 := C h182 h171
  have h192 := T (T (T (T (T (T (T (T (T (T (T (T (T h165 h160) h98) h134) h132) h18) h13) h71) h70) h69) h124) h162) h156) h150
  have h193 := C h8 (T (T (T (T (T (T (T (C h8 h166) (C h8 h192)) (C h8 h139)) (C h8 h137)) (S h157)) h145) h144) h169)
  have h194 := C (T (T (T (T (T (T (T (T (T h12 h26) h102) h100) h90) h29) h109) h107) h193) h191) h164
  let v195 := M v0 v185
  have h196 := h v195 v2 v2
  have h197 := C h17 (T (T (T (T (T (T (T (T (T (T (T (C h17 h166) (C h17 h192)) h140) h138) h95) h34) h155) h154) h152) h181) h180) h194)
  have h198 := h v106 v2 x
  have h199 := h v185 x x
  have h200 := T (T (T (C (T (T (T (T (T (T (T (T (T (C h176 (T (T (T (T (T (T (T (T h12 h26) h102) h100) h90) h29) h109) h107) h193)) (S h199)) h159) h158) h28) h96) h91) h66) h57) h38) (T (T (T (T (T (T (T (T h12 h26) h102) h100) h90) h29) h109) h198) h197)) (S h196)) h175) h194
  have h201 := C h8 h111
  have h202 := C h176 h146
  have h203 := T (T (T (T (T (T (T (T (T (T (T h12 h26) h102) h100) h90) h29) h109) h107) h193) h191) h202) h201
  have h204 := C h203 (T (T (T (T (T (T (T (T (C h36 h200) (C h36 h190)) (S h189)) h28) h96) h91) h66) h57) h38)
  have h205 := h v195 v0 v0
  have h206 := C (T (T (T (T (T (T (T (T (T (T h30 h43) h34) h155) h154) h152) h181) h180) h178) h205) h204) h164
  have h207 := S h198
  have h208 := C h17 (T (T (T (T (T (T (T (T (T (T (T h190 h174) h172) h136) h131) h130) h35) h94) h163) h161) (C h17 h149)) (C h17 h112))
  have h209 := C h17 (T (T (T (T (T (T (T (C h17 h200) h208) h207) h107) h193) h191) h202) h206)
  have h210 := h v195 v2 v0
  have h211 := h v2 v0 x
  have h212 := T (T (T (T (T (T (T (T (T (T (T h184 h183) h177) h168) h108) h105) h21) h98) h134) h132) h18) h13
  have h213 := C (T (C h212 h182) (S h211)) (T (T (T (T (T (T (T (T (T (T h30 h43) h34) h155) h154) h152) h181) h180) h178) h210) h209)
  have h214 := T (T (T (T (T (T (T h213 h188) h184) h183) h177) h168) h108) h105
  have h215 := R y
  have h216 := C h215 h214
  have h217 := S h210
  have h218 := T (T (T h190 h178) h196) (C (T (T (T (T (T (T (T (T (T h45 h56) h80) h75) h88) h20) h145) h144) h199) (C h182 (T (T (T (T (T (T (T (T h168 h108) h105) h21) h98) h134) h132) h18) h13))) (T (T (T (T (T (T (T (T h208 h207) h105) h21) h98) h134) h132) h18) h13))
  have h219 := S h205
  have h220 := C h212 (T (T (T (T (T (T (T (T h45 h56) h80) h75) h88) h20) h189) (C h36 h194)) (C h36 h218))
  have h221 := C (T (T (T (T (T (T (T (T (T (T h220 h219) h175) h174) h172) h136) h131) h130) h35) h32) h31) h146
  have h222 := C h17 (T (T (T (T (T (T (T h221 h183) h177) h168) h108) h198) h197) (C h17 h218))
  have h223 := C (T h211 (C h203 h176)) (T (T (T (T (T (T (T (T (T (T h222 h217) h175) h174) h172) h136) h131) h130) h35) h32) h31)
  have h224 := T (T (T h221 h201) h187) h223
  have h225 := C h215 h224
  have h226 := T (T (T (T (T (T (T (T (T h166 h165) h160) h29) h109) h107) h193) h191) h202) h206
  have h227 := C h215 h226
  have h228 := C h215 h112
  have h229 := C h215 h149
  have h230 := C h215 h150
  have h231 := T (T (T (T (T h71 h70) h69) h124) h162) h156
  have h232 := C h215 h231
  have h233 := h z z x
  have h234 := S h233
  let v235 := M z (M (M z x) x)
  have h236 := R v235
  have h237 := C h215 (C h215 (T (C h234 h236) h234))
  have h238 := h z y v235
  let v239 := M y (M (M y x) x)
  have h240 := h y v1 v239
  have h241 := S h240
  have h242 := R v239
  have h243 := h y y x
  have h244 := C h42 (C h42 (T h243 (C h243 h242)))
  have h245 := C h22 (T (T (T (T (T h117 h114) h66) h57) h40) h83)
  have h246 := C h22 h126
  have h247 := C h22 (T (T (T (T h167 h159) h158) h122) h128)
  have h248 := C h22 h173
  have h249 := C h22 h142
  have h250 := C h22 h111
  have h251 := C h22 h179
  have h252 := C h22 (T (T (T (T h125 h123) h145) h144) h169)
  have h253 := C h22 h153
  have h254 := C h22 (T (T (T (T (T h68 h41) h56) h80) h113) h121)
  have h255 := S h238
  have h256 := C h215 (C h215 (T h233 (C h233 h236)))
  have h257 := T (T (T (T (T h137 h127) h118) h86) h85) h84
  have h258 := C h215 h257
  have h259 := C h215 h139
  have h260 := C h215 h192
  have h261 := C h215 h166
  have h262 := T (T (T (T (T (T (T (T (T h221 h183) h177) h168) h108) h105) h21) h148) h147) h112
  have h263 := C h215 h262
  have h264 := T (T (T h213 h188) h184) h206
  have h265 := C h215 h264
  have h266 := T (T (T (T (T (T (T h109 h107) h193) h191) h202) h201) h187) h223
  have h267 := C h215 h266
  have h268 := C h215 h29
  have h269 := C (T (T (T (T (T (T (T (T (T h268 h267) h265) h263) h261) h260) h259) h258) h256) h255) h215
  have h270 := C h42 (T (T (C (T (T (T (T (T (T (T (T (T h269 h53) h52) h47) h115) h254) h253) h252) h251) h250) h215) (C (T (T (T (T (T (T h249 h248) h247) h246) h245) h119) h78) h215)) (C h65 h215))
  have h271 := C h215 h21
  have h272 := C (T (T (T (T (T (T (T (T (T h238 h237) h232) h230) h229) h228) h227) h225) h216) h271) h215
  have h273 := C h272 (T (T h270 h244) h241)
  have h274 := h (M y v10) v1 y
  have h275 := T (T (T (T (T (T (T (T h249 h248) h247) h246) h245) h119) h60) h59) h58
  have h276 := C (T (T (T (C h275 (T (T (T (T (T (T (T (T (T (T (T h238 h237) h232) h230) h229) h228) h227) h225) h216) h271) h274) h273)) h270) h244) h241) (T (T (T (T (T (T (T (T h238 h237) h232) h230) h229) h228) h227) h225) h216)
  have h277 := C h22 (T (T (T (T (T h276 h104) h102) h100) h90) h29)
  have h278 := C h22 (T h277 h23)
  have h279 := h (M v3 v185) v3 z
  have h280 := T (T (T (T (T (T (T (T (T (T (T h53 h52) h47) h115) h254) h253) h252) h251) h250) h279) h278) h7
  have h281 := S h279
  have h282 := S h274
  have h283 := C h42 (T (T (C h79 h215) (C (T (T (T (T (T (T h64 h115) h254) h253) h252) h251) h250) h215)) (C (T (T (T (T (T (T (T (T (T h249 h248) h247) h246) h245) h119) h60) h59) h58) h272) h215))
  have h284 := S h243
  have h285 := C h42 (C h42 (T (C h284 h242) h284))
  have h286 := C h269 (T (T h240 h285) h283)
  have h287 := T (T (T (T (T (T (T (T h53 h52) h47) h115) h254) h253) h252) h251) h250
  have h288 := C (T (T (T h240 h285) h283) (C h287 (T (T (T (T (T (T (T (T (T (T (T h286 h282) h268) h267) h265) h263) h261) h260) h259) h258) h256) h255))) (T (T (T (T (T (T (T (T h267 h265) h263) h261) h260) h259) h258) h256) h255)
  have h289 := C h22 (T (T (T (T (T h21 h98) h134) h132) h103) h288)
  have h290 := C h22 h29
  have h291 := C h22 (T h290 h289)
  let v292 := M (M v0 y) y
  let v293 := M v2 v292
  have h294 := h v293 v2 v0
  have h295 := S h294
  have h296 := h v101 v2 y
  have h297 := S h296
  have h298 := C (C (T (T (T (T h105 h21) h98) h134) h132) h215) h215
  have h299 := C h17 h298
  have h300 := C h110 h215
  have h301 := C h300 h215
  have h302 := C h17 h301
  have h303 := C h141 h215
  have h304 := C (T (C (T (T (T (T h184 h183) h177) h168) h108) h215) h303) h215
  have h305 := C h17 h304
  have h306 := C (T (T h274 h273) (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h269 h53) h52) h47) h115) h254) h253) h252) h251) h250) h279) h278) h7) h12) h26) h102) h100) h90) h29) h109) h107) h193) h191) h202) h201) h215)) h215
  have h307 := T h272 h306
  have h308 := h v185 x v0
  have h309 := S h308
  have h310 := h v186 x x
  have h311 := S h310
  have h312 := h v9 x x
  have h313 := h v2 v3 x
  have h314 := S h313
  have h315 := C (T (T (T (C (T h159 h158) h42) h116) h67) h55) h287
  have h316 := C h8 (T (T (T (T (T (T (T (T (T (T h315 h314) h45) h56) h80) h75) h88) h20) h312) (C h8 h206)) (C h8 h224))
  have h317 := T (T (T (T (T (T (T h45 h56) h80) h75) h88) h20) h145) h144
  have h318 := h v185 x v1
  have h319 := T (T (T (T (T (T (T (T (T (T (T h315 h314) h45) h56) h80) h75) h88) h20) h145) h144) h318) (C (T (T (T (T (T (T (T (T (T (T (T (T h30 h43) h34) h155) h154) h152) h181) h180) h178) h210) h209) (C h17 h224)) (C h317 (T (T (T (T (T (T (T (T (T (T (T (T (T h213 h188) h184) h183) h177) h168) h108) h105) h21) h98) h134) h132) h18) h13))) (T (T (T (T (T (T (T (T (T (T (T (T (T h316 h311) h184) h183) h177) h168) h108) h105) h21) h98) h134) h132) h18) h13))
  have h320 := C (T (T (T h46 h82) h120) (C (T h145 h144) h42)) h275
  have h321 := C h8 (T (T (T (T (T (T (T (T (T (T (C h8 h264) (C h8 h221)) (S h312)) h28) h96) h91) h66) h57) h38) h313) h320)
  have h322 := C (T (T (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h184 h183) h177) h168) h108) h105) h21) h98) h134) h132) h18) h13) h6) h291) h281) h249) h248) h247) h246) h245) h119) h60) h59) h58) h272) h215) h286) h282) h215
  have h323 := C h17 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h322 h269) h53) h52) h47) h115) h254) h253) h252) h251) h250) h279) h278) h7) h12) h26) h102) h100) h90) h29)
  have h324 := C (T h300 (C (T (T (T (T h107 h193) h191) h202) h201) h215)) h215
  have h325 := C h17 h324
  have h326 := C h303 h215
  have h327 := C h17 h326
  have h328 := C (C (T (T (T (T h102 h100) h90) h29) h109) h215) h215
  have h329 := C h17 h328
  have h330 := C (C h27 h215) h215
  have h331 := C h17 h330
  have h332 := T (T (T (T (T (T (T (T h331 h329) h327) h325) h323) h99) h95) h32) h31
  have h333 := C h332 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h53 h52) h47) h115) h254) h253) h252) h251) h250) h279) h278) h7) h12) h26) h102) h100) h90) h29) h109) h107) h193) h191) h202) h201) h310) h321) (C h8 h319))
  have h334 := C (T (T (T (T (T (T (T (T (T h333 h309) h159) h158) h28) h96) h91) h66) h57) h38) h307
  have h335 := C h17 (T (T (T h334 h305) h302) h299)
  have h336 := T h322 h269
  have h337 := T (T (T (T (T (T (T h159 h158) h28) h96) h91) h66) h57) h38
  have h338 := T (T (T (T (T (T (T (T (T (T (T (C (T (T (T (T (T (T (T (T (T (T (T (T (C h337 (T (T (T (T (T (T (T (T (T (T (T (T (T h12 h26) h102) h100) h90) h29) h109) h107) h193) h191) h202) h201) h187) h223)) (C h17 h264)) h222) h217) h175) h174) h172) h136) h131) h130) h35) h32) h31) (T (T (T (T (T (T (T (T (T (T (T (T (T h12 h26) h102) h100) h90) h29) h109) h107) h193) h191) h202) h201) h310) h321)) (S h318)) h159) h158) h28) h96) h91) h66) h57) h38) h313) h320
  have h339 := C (C h19 h215) h215
  have h340 := C h17 h339
  have h341 := C h17 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h21 h98) h134) h132) h18) h13) h6) h291) h281) h249) h248) h247) h246) h245) h119) h60) h59) h58) h272) h306)
  have h342 := T (T (T (T (T (T (T (T h30 h43) h94) h133) h341) h305) h302) h299) h340
  have h343 := C h342 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (C h8 h338) h316) h311) h184) h183) h177) h168) h108) h105) h21) h98) h134) h132) h18) h13) h6) h291) h281) h249) h248) h247) h246) h245) h119) h60) h59) h58)
  have h344 := C (T (T (T (T (T (T (T (T (T h45 h56) h80) h75) h88) h20) h145) h144) h308) h343) h336
  have h345 := h v293 v0 v1
  have h346 := S h345
  have h347 := R (M (M v293 v1) v1)
  have h348 := C h280 h347
  have h349 := T (T (T (T (T (T (T (T (T (T (T h6 h291) h281) h249) h248) h247) h246) h245) h119) h60) h59) h58
  have h350 := C h349 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (C h36 h338) (C h203 (T h315 h314))) h220) h219) h175) h174) h172) h136) h131) h130) h35) h94) h133) h341) h344)
  have h351 := h v185 v0 v0
  have h352 := C (T (T (T (T (T (T (T (T (T (T (T (T (C h332 h317) h184) h183) h177) h168) h108) h105) h21) h98) h134) h132) h18) h13) (T (T (T (T (T (T (T (T (T (T h45 h56) h80) h75) h88) h20) h145) h144) h351) h350) h348)
  have h353 := C h17 (T (T (T (T (T (T h352 h346) h331) h329) h327) h325) h344)
  have h354 := R v293
  have h355 := C h354 h280
  have h356 := h v293 v2 v2
  have h357 := T (T (T h352 h346) h356) (C (T (T (T (T (T (T (T (T (T (T h45 h56) h80) h75) h88) h20) h145) h144) h308) h343) h355) (T (T (T (T h353 h335) h297) h18) h13))
  have h358 := C (T (T (T (T (T (T (T (T (T (T (T (T h12 h26) h102) h100) h90) h29) h109) h107) h193) h191) h202) h201) (C h342 h337)) (T (T (T (T (T (T (T (T (T (T (C h349 h347) (C h280 (T (T (T (T (T (T (T (T (T (T (T (T (T (T h334 h323) h99) h95) h34) h155) h154) h152) h181) h180) h178) h205) h204) (C h212 (T h313 h320))) (C h36 h319)))) (S h351)) h159) h158) h28) h96) h91) h66) h57) h38)
  have h359 := T (T (T (T (T (T h334 h305) h302) h299) h340) h345) h358
  have h360 := C h17 h359
  have h361 := C h17 (T (T (T h329 h327) h325) h344)
  have h362 := C h354 h349
  have h363 := C h342 (T (T (T (T (T (T (T (T (T (T (T (T (T h322 h269) h53) h52) h47) h115) h254) h253) h252) h251) h250) h279) h278) h7)
  have h364 := C h8 h324
  have h365 := C h8 h326
  have h366 := C h8 h328
  have h367 := C h8 h330
  have h368 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h367 h366) h365) h364) h363) h362) h333) h309) h159) h158) h28) h96) h91) h66) h57) h38) (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h53 h52) h47) h115) h254) h253) h252) h251) h250) h279) h278) h7) h12) h26) h296) h361) h360) (C h17 h357))
  have h369 := h (M x v292) v3 v1
  have h370 := S h369
  have h371 := C h8 h339
  have h372 := C h8 h298
  have h373 := C h8 h301
  have h374 := C h8 h304
  have h375 := C h332 (T (T (T (T (T (T (T (T (T (T (T (T (T h6 h291) h281) h249) h248) h247) h246) h245) h119) h60) h59) h58) h272) h306)
  have h376 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h45 h56) h80) h75) h88) h20) h145) h144) h308) h343) h355) h375) h374) h373) h372) h371) (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (C h17 (T (T (T (C (T (T (T (T (T (T (T (T (T (T h362 h333) h309) h159) h158) h28) h96) h91) h66) h57) h38) (T (T (T (T h12 h26) h296) h361) h360)) (S h356)) h345) h358)) h353) h335) h297) h18) h13) h6) h291) h281) h249) h248) h247) h246) h245) h119) h60) h59) h58)
  have h377 := C (T (T (T (T (T (T (T (T (T (T h30 h43) h94) h133) h341) h305) h302) h299) h340) h294) h376) h336
  have h378 := C h22 (T (T (T (T (T (T (T (T (T (T (T h322 h269) h53) h52) h47) h115) h254) h253) h252) h251) h250) (C h22 (T (T (T (T h308 h343) h355) h375) h377)))
  have h379 := C h22 h324
  have h380 := C h22 h326
  have h381 := C h22 h328
  have h382 := C h22 h330
  have h383 := C (T (T (T (T (T h382 h381) h380) h379) h378) h370) h42
  have h384 := C h22 h339
  have h385 := C h22 h298
  have h386 := C h22 h301
  have h387 := C h22 h304
  have h388 := C (T (T (T (T (T (T (T (T (T (T h368 h295) h331) h329) h327) h325) h323) h99) h95) h32) h31) h307
  have h389 := C h22 (T (T (T (T (T (T (T (T (T (T (T (C h22 (T (T (T (T h388 h363) h362) h333) h309)) h249) h248) h247) h246) h245) h119) h60) h59) h58) h272) h306)
  have h390 := R (M v3 v292)
  have h391 := C h390 h349
  have h392 := C (T h391 h383) h349
  have h393 := C h390 h280
  have h394 := C h393 h280
  have h395 := C (T (T (T (T (T (T h290 h289) (C h22 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h276 h104) h18) h13) h6) h291) h281) h249) h248) h247) h246) h245) h119) h60) h59) h58) h272) h306))) h387) h386) h385) h384) h349
  have h396 := C h395 h349
  have h397 := C (T (T (T (T (T (T (T (C h22 h231) (C h22 h150)) (C h22 h149)) (C h22 h112)) (C h22 h226)) (C h22 h224)) (C h22 h214)) h23) h36
  have h398 := C h397 h36
  have h399 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T h398 h396) h394) h392) h388) h374) h373) h372) h371) h369) h389) h387) h386) h385) h384) h349
  have h400 := C h22 h257
  have h401 := C h22 h139
  have h402 := C h22 h192
  have h403 := C h22 h166
  have h404 := C h22 h262
  have h405 := C h22 h264
  have h406 := C h22 h266
  have h407 := C (T (T (T (T (T (T (T h290 h406) h405) h404) h403) h402) h401) h400) h36
  have h408 := C h22 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h322 h269) h53) h52) h47) h115) h254) h253) h252) h251) h250) h279) h278) h7) h12) h26) h103) h288)
  have h409 := C (T (T (T (T (T (T h382 h381) h380) h379) h408) h277) h23) h280
  have h410 := C h409 h280
  have h411 := C h391 h349
  have h412 := C (T (T (T (T (T h369 h389) h387) h386) h385) h384) h42
  have h413 := C (T h412 h393) h280
  have h414 := C h407 h36
  T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h30 h43) h94) h133) h341) h305) h302) h299) h340) h294) h376) h412) h409) h407) (h v5 v3 v2)) (C h22 (C h22 (T (C (T (T (T (T (T (T (T (C (T (T (T (T (T (T (T (T (T (T (T (T (T h397 h395) h383) h368) h295) h331) h329) h327) h325) h323) h99) h95) h32) h31) (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h45 h56) h80) h75) h88) h20) h145) h144) h308) h343) h355) h375) h377) h413) h411) h410) h414)) (C h8 h398)) (C h8 h396)) (C h8 h394)) (C h8 (T (T (T (T h392 h388) h374) h373) h372))) (S (h v101 x y))) h18) h13) (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h45 h56) h80) h75) h88) h20) h145) h144) h308) h343) h355) h375) h374) h373) h372) h371) h369) h389) h408) h277) h406) h405) h404) h403) h402) h401) h400) (h v4 v1 v0)) (C h42 (T (T (T (T (T (T (T (T (C h42 h398) (C h280 h396)) (C h349 h394)) (C h280 (T (T (T (T (T (T (T (T (T (T (T (T h392 h388) h363) h362) h333) h309) h351) h350) h348) (C h349 h359)) (C h280 (R (M (M v293 v2) v2)))) (C h349 h357)) (C h280 (R (M (M v293 v0) v0)))))) (S (h v293 v0 v0))) h294) h376) h412) (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T h382 h381) h380) h379) h378) h370) h367) h366) h365) h364) h377) h413) h411) h410) h414) h280)))) (C h280 (R (M (M v5 v0) v0)))) (C h349 (T (T (T (T h399 h409) h407) (h v5 v2 v0)) (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h45 h56) h80) h75) h88) h20) h145) h144) h308) h343) h355) h375) h377) h413) h411) h410) (C h407 h349)) (T (T (T (T (T (T (T (T (T (T (T (T (T (C h17 (T (T (T h399 h383) h368) h295)) (S (h v0 v2 y))) h6) h291) h281) h249) h248) h247) h246) h245) h119) h60) h59) h58))))) (C h280 (R (M (M v5 v1) v1))))) (S (h v5 v0 v1)))))) (S (h v3 v3 v0))

