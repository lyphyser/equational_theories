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
theorem Equation2944_implies_Equation1507 (G: Type _) [Magma G] (h: Equation2944 G) : Equation1507 G := fun x y z =>
  let v0 := M z y
  let v1 := M z v0
  let v2 := M y x
  let v3 := M v2 v1
  have h4 := R v3
  have h5 := h y z x
  have h6 := S h5
  have h7 := R x
  have h8 := h v1 x v1
  have h9 := S h8
  let v10 := M (M x (M x v1)) v1
  have h11 := R v10
  have h12 := C (C (T (C h11 h9) h9) h7) h7
  have h13 := h v1 v10 x
  have h14 := h v1 v2 v3
  have h15 := S h14
  have h16 := h v2 x v2
  have h17 := S h16
  let v18 := M (M x (M x v2)) v2
  have h19 := R v18
  have h20 := T (C h19 h17) h17
  have h21 := h v2 v18 v3
  have h22 := T h21 (C (C h20 h4) h4)
  have h23 := C h22 h4
  have h24 := T (T (T (T h23 h15) h13) h12) h6
  have h25 := R z
  have h26 := C h25 h24
  have h27 := C h25 h26
  have h28 := T (T (T h27 h13) h12) h6
  have h29 := T h16 (C h19 h16)
  have h30 := T (C (C h29 h4) h4) (S h21)
  have h31 := C h30 h4
  have h32 := S h13
  have h33 := C (C (T h8 (C h11 h8)) h7) h7
  have h34 := T (T (T (T h5 h33) h32) h14) h31
  have h35 := C h25 h34
  have h36 := C h25 h35
  let v37 := M v2 v3
  have h38 := h v37 z v0
  have h39 := S h38
  have h40 := h v37 z z
  have h41 := S h40
  let v42 := M (M x (M x z)) z
  have h43 := h z v42 v0
  have h44 := S h43
  have h45 := R v0
  have h46 := h z x z
  have h47 := R v42
  have h48 := T h46 (C h47 h46)
  have h49 := C (T (T (T h5 h33) h32) (C h48 h45)) h45
  have h50 := T (T (T h5 h33) h32) h36
  have h51 := C h50 (T h49 h44)
  have h52 := C h51 h25
  have h53 := T h52 h41
  have h54 := C h25 h53
  have h55 := C h50 h45
  have h56 := S h46
  have h57 := T (C h47 h56) h56
  have h58 := C (T (T (T (C h57 h45) h13) h12) h6) h45
  have h59 := C (T (T h43 h58) h55) (T h54 h26)
  have h60 := T (T (T (T h59 h39) h23) h15) h36
  have h61 := C h28 (T h43 h58)
  have h62 := C h61 h25
  have h63 := T h40 h62
  have h64 := C h25 h63
  have h65 := C h28 h45
  have h66 := C (T (T h65 h49) h44) (T h35 h64)
  let v67 := M y v0
  let v68 := M y v67
  have h69 := h (M v68 z) z z
  have h70 := S h69
  have h71 := h z v42 y
  have h72 := S h71
  have h73 := R y
  have h74 := C (C h48 h73) h73
  have h75 := C h45 h24
  have h76 := C h45 h53
  have h77 := C (T (T (T h52 h41) h38) h66) h25
  have h78 := h v0 y z
  have h79 := T h78 h77
  have h80 := C h79 (T (T (T h76 h75) h74) h72)
  have h81 := T (T (T (T (T h80 h70) h52) h41) h38) h66
  have h82 := C h45 h63
  have h83 := C h45 h82
  have h84 := C h45 h34
  have h85 := C (C h57 h73) h73
  have h86 := C h45 (T (T (T (T h49 h44) h71) h85) h84)
  have h87 := T (T (T h74 h72) h43) h58
  have h88 := C h45 h87
  have h89 := T h88 h86
  have h90 := T (T (T h49 h44) h71) h85
  have h91 := C h45 h90
  have h92 := C h45 (T (T (T (T h75 h74) h72) h43) h58)
  have h93 := C h45 h76
  have h94 := S h78
  have h95 := C (T (T (T h59 h39) h40) h62) h25
  have h96 := T h95 h94
  have h97 := C h96 (T (T (T h71 h85) h84) h82)
  have h98 := C h60 h25
  have h99 := C h60 h45
  have h100 := C h81 h45
  have h101 := C h83 h45
  have h102 := C h89 h45
  have h103 := T (T (T (T (T (T h102 h101) h100) h99) h65) h49) h44
  have h104 := T (T (T h14 h31) h40) h62
  have h105 := C h104 h103
  let v106 := M v0 y
  let v107 := M v0 v106
  let v108 := M v107 v0
  have h109 := R v108
  have h110 := T (T h5 h33) h32
  have h111 := C h110 h109
  have h112 := T h92 h91
  have h113 := C h112 h45
  have h114 := C h93 h45
  have h115 := T (T (T (T (T h59 h39) h40) h62) h69) h97
  have h116 := C h115 h45
  have h117 := T (T (T (T h27 h14) h31) h38) h66
  have h118 := C h117 h45
  have h119 := T (T (T (T (T (T h43 h58) h55) h118) h116) h114) h113
  have h120 := C (T (T (T (T (T (T (T (T h80 h70) h52) h41) h23) h15) h13) h12) h6) h119
  have h121 := C h83 h25
  have h122 := C h89 h25
  have h123 := C h117 h25
  have h124 := R v67
  have h125 := T (T h13 h12) h6
  have h126 := C h125 h124
  have h127 := T (T (T (T (T (T (T (T h14 h31) h40) h62) h69) h97) h93) h92) h91
  have h128 := C h127 (T (T (T (T h126 h51) h123) h95) h94)
  have h129 := C h110 h87
  have h130 := C h110 h129
  have h131 := R v106
  have h132 := C h125 h131
  have h133 := C h125 h132
  have h134 := T h71 h85
  have h135 := C h110 h134
  have h136 := R v1
  have h137 := C h136 h135
  have h138 := C h127 (T (T (T (T (T (T (T (T (T (T h137 h133) h130) h128) h102) h101) h100) h99) h65) h49) h44)
  have h139 := C (T (T (T (T (T (T (T h138 h122) h121) h120) h111) h105) h77) h98) h25
  have h140 := T h74 h72
  have h141 := C h125 h140
  have h142 := C h136 h141
  have h143 := C h110 h131
  have h144 := C h110 h143
  have h145 := C h125 h90
  have h146 := C h125 h145
  have h147 := C h110 h124
  have h148 := C h110 h147
  have h149 := C h110 (T (T (T h148 h146) h144) h142)
  have h150 := C h149 h25
  have h151 := C h125 h126
  have h152 := C h110 h135
  have h153 := C h73 (T (T (T h152 h133) h130) h151)
  have h154 := C h153 h25
  have h155 := C h125 h141
  have h156 := C h73 (T (T (T h148 h146) h144) h155)
  let v157 := M y z
  let v158 := M y v157
  have h159 := h v158 y v0
  have h160 := S h159
  have h161 := h v157 y v1
  have h162 := S h161
  have h163 := C h125 (T (T (T h137 h133) h130) h151)
  have h164 := T (T (T (T (T (T (T (T h88 h86) h83) h80) h70) h52) h41) h23) h15
  have h165 := C h164 (T (T (T (T h78 h77) h98) h61) h147)
  have h166 := C h164 (T (T (T (T (T (T (T (T (T (T h43 h58) h55) h118) h116) h114) h113) h165) h146) h144) h142)
  have h167 := C h112 h25
  have h168 := C h93 h25
  have h169 := C (T (T (T (T (T (T (T (T h5 h33) h32) h14) h31) h40) h62) h69) h97) h103
  have h170 := C h125 h109
  have h171 := T (T (T h52 h41) h23) h15
  have h172 := C h171 h119
  have h173 := h v157 y y
  have h174 := R (M y (M y v68))
  have h175 := C h45 h134
  have h176 := C h45 h175
  have h177 := C h45 h140
  have h178 := C h45 (T h91 h177)
  let v179 := M v107 z
  have h180 := h v179 z z
  have h181 := S h180
  have h182 := h v108 y v0
  have h183 := S h182
  have h184 := T (T (T (T (T h122 h121) h120) h111) h105) h94
  have h185 := h v37 v0 v0
  have h186 := S h185
  have h187 := T (T (T (T (T h14 h31) h40) h62) h69) h97
  have h188 := C h187 (T h105 h94)
  have h189 := C (T h188 h114) h45
  have h190 := T (T (T (T (T h80 h70) h52) h41) h23) h15
  have h191 := C h190 (T h78 h172)
  have h192 := h v108 v1 y
  have h193 := S h192
  have h194 := R (M v1 (M v1 v108))
  have h195 := C h194 h125
  have h196 := C (T (T (T (T (T h43 h58) h55) h118) h116) h191) h171
  have h197 := C (T (T (T h35 h64) h196) h195) (T (T (T (T (T (T (T (T (C h79 h103) h70) h52) h41) h23) h15) h13) h12) h6)
  have h198 := T (T (T (T h197 h193) h102) h101) h191
  have h199 := C h198 h45
  have h200 := h v108 v0 v0
  have h201 := T (T (T h197 h193) h200) (C (T (T (T (T (T (T (T h199 h189) h186) h23) h15) h13) h12) h6) (T (T h78 h172) h170))
  have h202 := C (T (T (T (T (T h188 h100) h99) h65) h49) h44) h104
  have h203 := C h194 h110
  have h204 := C (T (T (T h203 h202) h54) h26) (T (T (T (T (T (T (T (T h5 h33) h32) h14) h31) h40) h62) h69) (C h96 h119))
  have h205 := T (T (T (T h188 h114) h113) h192) h204
  have h206 := C h205 h45
  have h207 := C (T h101 h191) h45
  have h208 := C (T (T (T (T (T h14 h31) h185) h207) h206) (C h201 h45)) h184
  have h209 := R v179
  have h210 := T (T (T (T (T h78 h172) h170) h169) h168) h167
  have h211 := C h103 h210
  have h212 := h y v0 v0
  have h213 := h v108 y y
  have h214 := S h213
  have h215 := R (M y (M y v108))
  have h216 := R (M v0 (M v0 v108))
  have h217 := C h187 (T (T (T (T (T (T (T (T h208 h183) h102) h101) h100) h99) h65) h49) h44)
  have h218 := C (T (T (T (T (T (T (T (T (T (T (T (T h217 h120) h111) h105) h94) h35) h64) h196) h195) (C h205 h110)) (C h216 h125)) (C h201 h110)) (C h215 h125)) h125
  have h219 := R (M v1 (M v1 v179))
  have h220 := C h219 h110
  have h221 := C (T (T (T (T (T (T (T (T (T h220 h218) h214) h102) h101) h100) h99) h65) h49) h44) (T h212 h211)
  have h222 := h v179 v1 y
  have h223 := T (T (T (T h217 h168) h167) h222) h221
  have h224 := T (T (T (C (T (T (T (T (T (T (T h5 h33) h32) h14) h31) h185) h207) h206) (T (T h111 h105) h94)) (S h200)) h192) h204
  have h225 := C (T (T (T (T (T (C h224 h45) h199) h189) h186) h23) h15) h210
  have h226 := C h190 (T (T (T (T (T (T (T (T h43 h58) h55) h118) h116) h114) h113) h182) h225)
  have h227 := h v37 v0 z
  have h228 := C (T (T (T (T (T (T (T h5 h33) h32) h14) h31) h227) (C (T h121 h226) h25)) (C h223 h25)) (T (T (T (T (T (T (T (T (T (C h110 h209) h208) h183) h102) h101) h100) h99) h65) h49) h44)
  have h229 := C (T (T (T (T (T (T (T h228 h181) h122) h121) h120) h111) h105) h94) (T (T (T (T (T (T (T (T (T (T h5 h33) h32) h14) h31) h40) h62) h69) h97) h93) h92)
  have h230 := R (M y (M y v179))
  have h231 := C h230 h125
  have h232 := S h222
  have h233 := S h212
  have h234 := C h119 h184
  have h235 := C h219 h125
  have h236 := C (T (T (T (T (T (T (T (T (T (T (T (T (C h215 h110) (C h224 h125)) (C h216 h110)) (C h198 h125)) h203) h202) h54) h26) h78) h172) h170) h169) h226) h110
  have h237 := C (T (T (T (T (T (T (T (T (T h43 h58) h55) h118) h116) h114) h113) h213) h236) h235) (T h234 h233)
  have h238 := T (T (T (T h237 h232) h122) h121) h226
  have h239 := C (T (T (T (T (T (T (T (C h238 h25) (C (T h217 h168) h25)) (S h227)) h23) h15) h13) h12) h6) (T (T (T (T (T (T (T (T (T h43 h58) h55) h118) h116) h114) h113) h182) h225) (C h125 h209))
  have h240 := C (T (T (T h237 h232) h180) h239) h110
  have h241 := R (M z (M z v179))
  have h242 := C h241 h125
  have h243 := C h223 h110
  have h244 := C h110 (T (T (T (T (T (T (T (T (T (T (T h153 h149) h138) h122) h121) h120) h111) h105) h77) h98) h61) h147)
  have h245 := R (M y (M y v158))
  have h246 := h v158 y y
  have h247 := C (T (T (T (T (T h148 h146) h144) h155) h246) (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (C h245 h110) (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h244 h128) h213) h236) h235) h243) h242) h240) h231) h229) h178) h176) (C (T (T (T (T (T (T h78 h172) h170) h169) h168) h167) h166) h164)) (C h163 h125)) (C h174 h110)) (C h156 h125)) h125)) (S h173)) h135) h132) h129) h126) h51) h123) h95) h172) h170) h169) h168) h167) h166) h163) h156) h110)) h136
  have h248 := C h151 h110
  have h249 := R (M v1 (M v1 v67))
  have h250 := C h249 h125
  have h251 := C h130 h110
  have h252 := R (M y (M y v106))
  have h253 := C h252 h125
  have h254 := C h133 h110
  have h255 := R (M v1 (M v1 v106))
  have h256 := C h255 h125
  have h257 := C h152 h110
  have h258 := T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h257 h256) h254) h253) h251) h250) h248) h247) h162) h135) h132) h129) h126) h51) h123) h95) h94
  have h259 := h v179 y y
  have h260 := S h259
  have h261 := C (T (T (T (T (T (T (T h78 h172) h170) h169) h168) h167) h180) h239) (T (T (T (T (T (T (T (T (T (T h86 h83) h80) h70) h52) h41) h23) h15) h13) h12) h6)
  have h262 := C h261 h125
  have h263 := C h45 (T h175 h88)
  have h264 := C h45 h177
  have h265 := T h264 h263
  have h266 := C h265 h110
  have h267 := R (M v0 v107)
  have h268 := C h267 h125
  have h269 := C h176 h110
  have h270 := T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h43 h58) h55) h118) h116) h114) h113) h213) h236) h235) h243) h242) h240) h231) h229) h178
  have h271 := C h270 (T (T (T (T (T (T (T (T (T (T (T (T h175 h88) h86) h83) h80) h70) h52) h41) h23) h15) h13) h12) h6)
  have h272 := C h25 h177
  have h273 := C h125 (T (T (T (T (T (T (T (T (T (T (T h126 h51) h123) h95) h172) h170) h169) h168) h167) h166) h163) h156)
  have h274 := T (T (T (T (T (T (T (T h43 h58) h55) h118) h116) h114) h113) h165) h273
  have h275 := C h274 (T (T (T (T (T (T (T (T (T (T (T (T h272 h271) h269) h268) h266) h262) h260) h122) h121) h120) h111) h105) h94)
  have h276 := C h25 h175
  have h277 := C h25 h276
  have h278 := C h238 h125
  have h279 := C h241 h110
  have h280 := C (T (T (T h228 h181) h222) h221) h125
  have h281 := C h230 h110
  have h282 := T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h263 h261) h281) h280) h279) h278) h220) h218) h214) h102) h101) h100) h99) h65) h49) h44
  have h283 := C h282 (T (T (T (T (T (T (T (T (T (T (T (T h5 h33) h32) h14) h31) h40) h62) h69) h97) h93) h92) h91) h177)
  have h284 := C h264 h125
  have h285 := C h267 h110
  have h286 := T h178 h176
  have h287 := C h286 h125
  have h288 := C h229 h110
  have h289 := C h282 (T (T (T (T (T (T (T (T (T (T (T h78 h172) h170) h169) h168) h167) h259) h288) h287) h285) h284) h283)
  have h290 := C h264 h45
  have h291 := C h286 h45
  have h292 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T h43 h58) h55) h118) h116) h114) h113) h213) h236) h235) h243) h242) h240) h231) h229) (T (T (T (T (T (T (T (T (T (T h269 h268) h266) h262) h260) h122) h121) h120) h111) h105) h94)
  have h293 := C h25 (T (T (T (T h259 h288) h287) h285) h284)
  have h294 := C (T (T (T (T (T (T (T (T (T (T (T h13 h12) h6) h212) h211) h293) h292) h291) h290) h289) h277) h275) h258
  have h295 := C h125 (T (T (T (T (T h294 h160) h152) h133) h130) h151)
  have h296 := C (T h295 h156) h25
  have h297 := C h155 h125
  have h298 := C h255 h110
  have h299 := C h144 h125
  have h300 := C h252 h110
  have h301 := C h146 h125
  have h302 := C h249 h110
  have h303 := C h148 h125
  have h304 := C (T (T (T (T (T (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h153 h149) h138) h122) h121) h120) h111) h105) h77) h98) h61) h147) h145) h143) h141) h173) (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (C h153 h110) (C h174 h125)) (C h149 h110)) (C (T (T (T (T (T (T h138 h122) h121) h120) h111) h105) h94) h127)) h264) h263) h261) h281) h280) h279) h278) h220) h218) h214) h165) h273) h110)) (C h245 h125)) h125) (S h246)) h152) h133) h130) h151) h136
  have h305 := T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h78 h77) h98) h61) h147) h145) h143) h141) h161) h304) h303) h302) h301) h300) h299) h298) h297
  have h306 := C h25 (T (T (T (T h269 h268) h266) h262) h260)
  have h307 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T h261 h281) h280) h279) h278) h220) h218) h214) h102) h101) h100) h99) h65) h49) h44) (T (T (T (T (T (T (T (T (T (T h78 h172) h170) h169) h168) h167) h259) h288) h287) h285) h284)
  have h308 := C h265 h45
  have h309 := C h176 h45
  have h310 := C h270 (T (T (T (T (T (T (T (T (T (T (T h271 h269) h268) h266) h262) h260) h122) h121) h120) h111) h105) h94)
  have h311 := C h25 h272
  have h312 := T (T (T (T (T (T (T (T h244 h128) h102) h101) h100) h99) h65) h49) h44
  have h313 := C h312 (T (T (T (T (T (T (T (T (T (T (T (T h78 h172) h170) h169) h168) h167) h259) h288) h287) h285) h284) h283) h276)
  have h314 := C (T (T (T (T (T (T (T (T (T (T (T h313 h311) h310) h309) h308) h307) h306) h234) h233) h5) h33) h32) h305
  have h315 := C h110 (T (T (T (T (T h148 h146) h144) h155) h159) h314)
  let v316 := M v158 y
  have h317 := h v316 v1 y
  have h318 := S h317
  have h319 := C h274 h258
  have h320 := R (M v1 (M v1 v316))
  have h321 := C h320 h125
  have h322 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h256 h254) h253) h251) h250) h248) h247) h162) h135) h132) h129) h126) h51) h123) h95) h172) h170) h169) h168) h167) h166) h163) h315) h136
  have h323 := h v106 v1 v1
  have h324 := C (T (T (T (T h71 h85) h323) h322) h321) (T (T (T (T (T (T (T (T (T h319 h313) h311) h310) h309) h308) h307) h306) h234) h233)
  have h325 := T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h324 h318) h257) h256) h254) h253) h251) h250) h248) h247) h162) h135) h132) h129) h126) h51) h123) h95) h172) h170) h169) h168) h167) h166) h163) h315
  have h326 := C h325 h25
  have h327 := C h312 h305
  have h328 := S h323
  have h329 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h295 h149) h138) h122) h121) h120) h111) h105) h77) h98) h61) h147) h145) h143) h141) h161) h304) h303) h302) h301) h300) h299) h298) h136
  have h330 := C h320 h110
  have h331 := C (T (T (T (T h330 h329) h328) h74) h72) (T (T (T (T (T (T (T (T (T h212 h211) h293) h292) h291) h290) h289) h277) h275) h327)
  have h332 := h v316 z z
  have h333 := S h332
  have h334 := R v316
  have h335 := T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h295 h149) h138) h122) h121) h120) h111) h105) h77) h98) h61) h147) h145) h143) h141) h161) h304) h303) h302) h301) h300) h299) h298) h297) h317) h331
  have h336 := C h335 h25
  have h337 := C (T h153 h315) h25
  have h338 := C h156 h25
  have h339 := C h163 h25
  have h340 := C (T (T (T (T (T (T (T h123 h95) h172) h170) h169) h168) h167) h166) h25
  have h341 := C (T (T (T (T (T (T (T (T (T (T h5 h33) h32) h14) h31) h40) h340) h339) h338) h337) h336) (T (T (T (T (T (T (T (T (T (T (T (T (T (C h110 h334) h294) h160) h152) h133) h130) h128) h102) h101) h100) h99) h65) h49) h44)
  have h342 := T (T (T h341 h333) h317) h331
  have h343 := C h342 h25
  have h344 := h z y y
  have h345 := C (T (T (T (T (T (T (T (T h148 h128) h102) h101) h100) h99) h65) h49) h44) h305
  have h346 := C h151 h45
  have h347 := C h130 h45
  have h348 := C h133 h45
  have h349 := C h152 h45
  have h350 := T (T (T (T (T (T (T (T (T (T (T (T (T (T h349 h348) h347) h346) h345) h319) h313) h311) h310) h309) h308) h307) h306) h234) h233
  have h351 := C (T (T (T (T (T (T (T (T (T (T h326 h296) h154) h150) h139) h41) h23) h15) h13) h12) h6) (T (T (T (T (T (T (T (T (T (T (T (T (T h43 h58) h55) h118) h116) h114) h113) h165) h146) h144) h155) h159) h314) (C h125 h334))
  have h352 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h78 h77) h98) h61) h147) h145) h143) h141) h161) h304) h303) h302) h301) h300) h299) h298) h297) h332) h351) (T (C h305 h350) (S h344))
  have h353 := T (T (T (T (T (T (T (T (T (T (T (T h352 h343) h326) h296) h154) h150) h139) h62) h69) h97) h93) h92) h91
  have h354 := C h155 h45
  have h355 := C h144 h45
  have h356 := C h146 h45
  have h357 := C h148 h45
  have h358 := C (T (T (T (T (T (T (T (T h43 h58) h55) h118) h116) h114) h113) h165) h151) h258
  have h359 := T (T (T (T (T (T (T (T (T (T (T (T (T (T h212 h211) h293) h292) h291) h290) h289) h277) h275) h327) h358) h357) h356) h355) h354
  have h360 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h341 h333) h257) h256) h254) h253) h251) h250) h248) h247) h162) h135) h132) h129) h126) h51) h123) h95) h94) (T h344 (C h258 h359))
  have h361 := T (T (T h324 h318) h332) h351
  have h362 := C h361 h25
  have h363 := h (M v158 v0) v0 v0
  have h364 := S h363
  have h365 := h v316 y y
  have h366 := R (M y (M y v316))
  have h367 := R (M z (M z v316))
  have h368 := h v106 v1 v0
  have h369 := C (T (T (T h71 h85) h368) (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h348 h347) h346) h345) h319) h313) h311) h310) h309) h308) h307) h306) h234) h233) h5) h33) h32) h14) h31) h40) h340) h339) h338) h337) h336) h362) h360) h45)) (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (C (T (T (T (T (T (T (T (T h71 h85) h323) h322) h321) (C h335 h110)) (C h367 h125)) (C h361 h110)) (C h366 h125)) h350) (S h365)) h257) h256) h254) h253) h251) h250) h248) h247) h162) h135) h132) h129) h126) h51) h123) h95) h94)
  have h370 := T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h369 h364) h349) h348) h347) h346) h345) h319) h313) h311) h310) h309) h308) h307) h306) h234) h233) h5) h33) h32) h14) h31) h40) h340) h339) h338) h337) h336) h362) h360
  have h371 := C (T (T (T (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h352 h343) h326) h296) h154) h150) h139) h41) h23) h15) h13) h12) h6) h212) h211) h293) h292) h291) h290) h289) h277) h275) h327) h358) h357) h356) h355) h45) (S h368)) h74) h72) (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h78 h77) h98) h61) h147) h145) h143) h141) h161) h304) h303) h302) h301) h300) h299) h298) h297) h365) (C (T (T (T (T (T (T (T (T (C h366 h110) (C h342 h125)) (C h367 h110)) (C h325 h125)) h330) h329) h328) h74) h72) h359))
  have h372 := h v3 v2 y
  have h373 := S h372
  have h374 := R v2
  have h375 := C h374 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h349 h348) h347) h346) h345) h319) h313) h311) h310) h309) h308) h307) h306) h234) h233) h5) h33) h32) h14) h31)
  have h376 := T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h88 h86) h83) h80) h70) h52) h41) h23) h15) h13) h12) h6) h212) h211) h293) h292) h291) h290) h289) h277) h275) h327) h358) h357) h356) h355) h354
  have h377 := C h374 h376
  have h378 := C h374 h175
  have h379 := T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h309 h308) h307) h306) h234) h233) h5) h33) h32) h14) h31) h40) h62) h69) h97) h93) h92) h91) h177
  have h380 := C h374 h379
  have h381 := T (T (T (T (T (T (T (T (T (T (T (T h52 h41) h23) h15) h13) h12) h6) h212) h211) h293) h292) h291) h290
  have h382 := C h374 h381
  have h383 := C h374 (T (T (T (T (T (T h5 h33) h32) h14) h31) h40) h62)
  have h384 := C h20 h73
  have h385 := h v2 v18 y
  have h386 := T h385 (C (T (T (T (T (T (T h384 h383) h382) h380) h378) h377) h375) h73)
  have h387 := C h386 h24
  have h388 := C h22 (T (T h375 h387) h373)
  have h389 := C h374 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h23 h15) h13) h12) h6) h212) h211) h293) h292) h291) h290) h289) h277) h275) h327) h358) h357) h356) h355) h354)
  have h390 := S h385
  have h391 := C h29 h73
  have h392 := C h374 (T (T (T (T (T (T h52 h41) h23) h15) h13) h12) h6)
  have h393 := T (T (T (T (T (T (T (T (T (T (T (T h309 h308) h307) h306) h234) h233) h5) h33) h32) h14) h31) h40) h62
  have h394 := C h374 h393
  have h395 := T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h175 h88) h86) h83) h80) h70) h52) h41) h23) h15) h13) h12) h6) h212) h211) h293) h292) h291) h290
  have h396 := C h374 h395
  have h397 := C h374 h177
  have h398 := T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h349 h348) h347) h346) h345) h319) h313) h311) h310) h309) h308) h307) h306) h234) h233) h5) h33) h32) h14) h31) h40) h62) h69) h97) h93) h92) h91
  have h399 := C h374 h398
  have h400 := T (C (T (T (T (T (T (T h389 h399) h397) h396) h394) h392) h391) h73) h390
  have h401 := C h400 h34
  have h402 := C h374 h389
  have h403 := C h386 (T (T (T (T (T h402 h388) h15) h13) h12) h6)
  have h404 := C h374 h375
  have h405 := C h374 h377
  have h406 := C h374 h378
  have h407 := C h374 h380
  have h408 := C h374 h382
  have h409 := C h374 h383
  have h410 := C h374 (T (T (T (T (T h409 h408) h407) h406) h405) h404)
  have h411 := C h374 (T (T (T h410 h403) h401) h389)
  have h412 := C h374 h392
  have h413 := C h374 h394
  have h414 := C h374 h396
  have h415 := C h374 h397
  have h416 := C h374 h399
  have h417 := C h374 (T (T (T (T (T h402 h416) h415) h414) h413) h412)
  have h418 := C h30 (T (T h372 h401) h389)
  have h419 := C h400 (T (T (T (T (T h5 h33) h32) h14) h418) h404)
  have h420 := C h374 (T (T (T h375 h387) h419) h417)
  have h421 := T h402 h420
  have h422 := T (T (T (T (T (T (T (T (T h409 h408) h407) h406) h405) h388) h15) h13) h12) h6
  have h423 := T (T (T (T (T (T (T (T h372 h401) h389) h399) h397) h396) h394) h392) h391
  have h424 := C h423 h422
  have h425 := T (T (T (T (T (T (T (T (T h5 h33) h32) h14) h418) h416) h415) h414) h413) h412
  have h426 := C (T (T (T (T (T (T (T (T h384 h383) h382) h380) h378) h377) h375) h387) h373) h425
  have h427 := C h4 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (C h409 h7) (C h408 h7)) (C h407 h7)) (C h406 h7)) (C h405 h7)) (C h404 h7)) (C h421 h7)) (C (T (T (T h411 h388) h15) h36) h7)) (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h27 h13) h12) h6) h212) h211) h293) h292) h291) h290) h289) h277) h275) h327) h358) h357) h356) h355) h354) h363) h371) h7)) (C h370 h7)) (C h353 h7)) (C h89 h7)) (C h83 h7)) (C h81 h7)) (C (T (T (T (T (T (T h59 h39) h23) h15) h13) h12) h6) h7)) h385) h426)
  have h428 := C h412 h7
  have h429 := C h413 h7
  have h430 := C h414 h7
  have h431 := C h415 h7
  have h432 := C h416 h7
  have h433 := C h402 h7
  have h434 := T h411 h404
  have h435 := C h434 h7
  have h436 := C (T (T (T h27 h14) h418) h420) h7
  have h437 := T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h369 h364) h349) h348) h347) h346) h345) h319) h313) h311) h310) h309) h308) h307) h306) h234) h233) h5) h33) h32) h36
  have h438 := C h437 h7
  have h439 := T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h352 h343) h326) h296) h154) h150) h139) h41) h23) h15) h13) h12) h6) h212) h211) h293) h292) h291) h290) h289) h277) h275) h327) h358) h357) h356) h355) h354) h363) h371
  have h440 := C h439 h7
  have h441 := T (T (T (T (T (T (T (T (T (T (T (T h88 h86) h83) h80) h70) h52) h340) h339) h338) h337) h336) h362) h360
  have h442 := C h441 h7
  have h443 := C h112 h7
  have h444 := C h93 h7
  have h445 := C h115 h7
  have h446 := T (T (T (T (T (T h5 h33) h32) h14) h31) h38) h66
  have h447 := C h446 h7
  have h448 := T (T h410 h403) h373
  let v449 := M v2 v37
  T (T (h x y v3) (C (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (C h110 h22) (C h125 (R (M v37 v3)))) (C h446 h30)) (C h115 h374)) (C h93 h374)) (C h112 h374)) (C h441 h374)) (C h439 h374)) (C h437 h374)) (C h27 h386)) (C h125 (R (M v449 y)))) (C (T (T (T (T (T h5 h33) h32) h14) h418) h420) h400)) (C h434 h374)) (C h402 h374)) (C h416 h374)) (C h415 h374)) (C h414 h374)) (C h413 h374)) (C h412 h374)) (C (T (T (T (T (T (T h409 h408) h407) h406) h405) h388) h15) (T (T (T (T (T (T (T (T (T (T (T (T h385 h426) (C (T (T h372 h419) h417) h422)) (C h410 h110)) (C (T h403 h373) (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h13 h12) h6) h212) h211) h293) h292) h291) h290) h289) h277) h275) h327) h358) h357) h356) h355) h354))) (C h4 h398)) (C h4 h177)) (C h4 h395)) (C h4 h393)) (C h4 h53)) (C h4 h24)) (h (M v3 y) v3 v3)) (C (T (C (T (T (C h4 (T (T (T (T (T (T (T (C h4 (C h4 h34)) (C h4 (C h4 h63))) (C h4 (C h4 h381))) (C h4 (C h4 h379))) (C h4 (C h4 h175))) (C h4 (C h4 h376))) (C h4 (T (T (C (T h372 h419) (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h349 h348) h347) h346) h345) h319) h313) h311) h310) h309) h308) h307) h306) h234) h233) h5) h33) h32)) (C h417 h125)) (C h448 h425)))) (C h4 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h424 h390) h447) h445) h444) h443) h442) h440) h438) h436) h435) h433) h432) h431) h430) h429) h428)))) (C h423 (T (T (T (T (T (T (T (T (T (T (T (T h427 (C (T (T (T h372 h401) (h v449 v2 v2)) (C (T (T (C h417 h374) (C h448 (T (T (T (T (T (T (T (T (T (T (T (T (T (T h447 h445) h444) h443) h442) h440) h438) h436) h435) h433) h432) h431) h430) h429) h428))) h427) h374)) (T h424 h390))) (S (h (M v2 (M v2 y)) v3 v2))) h409) h408) h407) h406) h405) h388) h15) h13) h12) h6))) h390) (T (T (T (T (T (T h372 h401) h389) h399) h397) h396) h394)) h412) h4)))) (C h125 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (C h409 h4) (C h408 h4)) (C h407 h4)) (C h406 h4)) (C h405 h4)) (C h404 h4)) (C h421 h4)) (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h411 h388) h15) h13) h12) h6) h212) h211) h293) h292) h291) h290) h289) h277) h275) h327) h358) h357) h356) h355) h354) h363) h371) h4)) (C h370 h4)) (C h353 h4)) (C h89 h4)) (C h83 h4)) (C h81 h4)) (C h60 h4)) (C h28 h4)))) h4) h4)) (S (h v3 y v3))

