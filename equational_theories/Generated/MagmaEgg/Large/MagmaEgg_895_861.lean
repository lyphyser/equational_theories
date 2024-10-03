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
theorem Equation895_implies_Equation861 (G: Type _) [Magma G] (h: Equation895 G) : Equation861 G := fun x y z =>
  let v0 := M z y
  let v1 := M y z
  let v2 := M v1 v0
  let v3 := M x v2
  have h4 := h v3 x x
  have h5 := S h4
  have h6 := R x
  have h7 := h x x v2
  have h8 := S h7
  let v9 := M v3 v3
  have h10 := R v9
  have h11 := h x v0 v2
  have h12 := S h11
  let v13 := M v2 x
  let v14 := M v0 x
  have h15 := h v2 v2 (M v14 v13)
  have h16 := S h15
  have h17 := h v0 v2 x
  have h18 := R v2
  have h19 := C h18 (C h17 h17)
  have h20 := T h19 h16
  have h21 := R v0
  have h22 := C h21 h20
  have h23 := h v1 v0 v0
  have h24 := T h23 h22
  have h25 := R v3
  have h26 := h v0 v2 v2
  have h27 := S h26
  have h28 := C h20 h18
  have h29 := S h17
  have h30 := C h18 (C h29 h29)
  have h31 := S h23
  have h32 := T h15 h30
  have h33 := C h21 h32
  have h34 := T h33 h31
  have h35 := C h34 h21
  have h36 := C (T (T h35 h15) h30) h18
  have h37 := C h24 (T h36 h28)
  let v38 := M v0 v2
  have h39 := h v38 v1 v0
  have h40 := T (T (T h23 h22) h39) h37
  have h41 := C h20 h40
  have h42 := R v1
  have h43 := C h32 h42
  have h44 := T (T h43 h41) h27
  have h45 := C h44 (C h25 h24)
  let v46 := M v3 v1
  let v47 := M v2 v1
  let v48 := M v47 v46
  have h49 := h v48 v2 v2
  have h50 := S h49
  have h51 := S h39
  have h52 := C h24 h21
  have h53 := C (T (T h19 h16) h52) h18
  have h54 := C h32 h18
  have h55 := C h34 (T h54 h53)
  have h56 := T h55 h51
  have h57 := C h56 h21
  have h58 := C h57 h18
  have h59 := T h39 h37
  have h60 := C h59 h21
  let v61 := M v0 v0
  let v62 := M v2 v61
  have h63 := h v62 v3 v1
  have h64 := S h63
  have h65 := R v46
  have h66 := C h20 h42
  have h67 := T (T (T h55 h51) h33) h31
  have h68 := C h32 h67
  have h69 := T (T h26 h68) h66
  have h70 := C h69 (C h25 h34)
  have h71 := C h25 (T (T h11 h70) (C h43 h65))
  have h72 := C (T (T (T (T (T h71 h64) h19) h16) h52) h60) h18
  have h73 := T (T (T h71 h64) h19) h16
  let v74 := M v3 x
  have h75 := R v74
  have h76 := C h75 h73
  have h77 := C (T h11 h70) h18
  have h78 := C h77 (T (T (T (T h76 h72) h58) h36) h28)
  have h79 := h v3 v3 x
  have h80 := C h73 (T h79 h78)
  have h81 := C (T (T (T h80 h50) h45) h12) h10
  have h82 := C h25 (T (T (C h66 h65) h45) h12)
  have h83 := T h63 h82
  have h84 := C h83 h25
  have h85 := C h84 h10
  have h86 := C h32 h25
  have h87 := C h86 h10
  have h88 := T (T (T (T (T h86 h84) h80) h50) h45) h12
  have h89 := C h20 h25
  have h90 := C h89 h10
  have h91 := T h71 h64
  have h92 := C h91 h25
  have h93 := C h92 h10
  have h94 := S h79
  have h95 := T (T (T h15 h30) h63) h82
  have h96 := C h75 h95
  have h97 := C (T (T (T (T (T h57 h35) h15) h30) h63) h82) h18
  have h98 := C h60 h18
  have h99 := C (T h45 h12) h18
  have h100 := C h99 (T (T (T (T h54 h53) h98) h97) h96)
  have h101 := C h95 (T h100 h94)
  have h102 := C (T (T (T h11 h70) h49) h101) h10
  have h103 := C h95 (T (C (T (T (T (T (T (T (T h80 h50) h45) h12) h7) h102) h93) h90) h88) (C (T (T (T h87 h85) h81) h8) h6))
  have h104 := h v74 v2 v3
  have h105 := T (T (T (T (T h15 h30) h63) h82) h104) h103
  have h106 := C h88 h105
  have h107 := h v48 v3 x
  have h108 := S h107
  have h109 := h v2 z v1
  have h110 := S h109
  have h111 := R (M z v1)
  have h112 := h v47 v0 v2
  have h113 := S h112
  have h114 := R v61
  have h115 := C h69 (T (T (T (C h57 h114) (C h35 h114)) h19) h16)
  let v116 := M v2 v2
  let v117 := M v38 v116
  have h118 := h v117 v0 v0
  have h119 := C (T h41 h27) (T (T (C h24 h42) (C h59 h42)) (C (T h118 h115) h24))
  let v120 := M v1 v1
  have h121 := R v120
  have h122 := C h43 h121
  have h123 := h (M v47 v120) v2 v2
  have h124 := S h123
  have h125 := R v116
  have h126 := C h66 h121
  have h127 := S h118
  have h128 := C h44 (T (T (T h15 h30) (C h52 h114)) (C h60 h114))
  have h129 := C (T h26 h68) (T (T (C (T h128 h127) h34) (C h56 h42)) (C h34 h42))
  have h130 := T (T h112 h129) h126
  have h131 := C h130 h18
  have h132 := C h131 h125
  have h133 := C (T (T (T (T (T h23 h22) h39) h37) h118) h115) (T (T h58 h36) h28)
  have h134 := h v117 v1 v0
  have h135 := C h73 (T (T (T (T (T (T h23 h22) h39) h37) h134) h133) h132)
  have h136 := S h104
  have h137 := T (T (T (T (T h11 h70) h49) h101) h92) h89
  have h138 := C h73 (T (C (T (T (T h7 h102) h93) h90) h6) (C (T (T (T (T (T (T (T h87 h85) h81) h8) h11) h70) h49) h101) h137))
  have h139 := T h138 h136
  have h140 := C h139 h42
  have h141 := h v1 v1 (M (M z x) (M v1 x))
  have h142 := S h141
  have h143 := h z v1 x
  have h144 := C h42 (C h143 h143)
  have h145 := T h144 h142
  have h146 := R z
  have h147 := C h146 h145
  have h148 := h y z z
  have h149 := T h148 h147
  have h150 := T h104 h103
  have h151 := C h150 h42
  have h152 := S h134
  have h153 := C (T (T (T (T (T h128 h127) h55) h51) h33) h31) (T (T h54 h53) h98)
  have h154 := T (T h122 h119) h113
  have h155 := C h154 h18
  have h156 := C h155 h125
  have h157 := C h95 (T (T (T (T (T (T h156 h153) h152) h55) h51) h33) h31)
  have h158 := h v0 x v2
  have h159 := S h158
  let v160 := M v2 v3
  have h161 := h (M v160 v9) v2 v2
  have h162 := S h161
  have h163 := C (T (T (T (T (T h45 h12) h7) h102) h93) h90) h18
  have h164 := C h163 h125
  have h165 := T (T (T (T (T h138 h136) h71) h64) h19) h16
  have h166 := C h165 (T (T h79 h78) h164)
  have h167 := C (T (T (T (T (T h166 h162) h87) h85) h81) h8) (T (T (T (C h40 h25) (C (T (T h118 h115) h131) h25)) (C h155 h25)) (C (T (T (T h128 h127) h55) h51) h25))
  let v168 := M v1 v3
  have h169 := R v168
  have h170 := C (T (T (T (T (T h87 h85) h81) h8) h11) h70) h18
  have h171 := C h170 h125
  have h172 := C h105 (T (T h171 h100) h94)
  have h173 := C (T (T (T (T (T (T (T (T (T h80 h50) h45) h12) h7) h102) h93) h90) h161) h172) h169
  have h174 := C h84 h169
  have h175 := C h86 h169
  have h176 := R y
  have h177 := C h89 h169
  have h178 := C h92 h169
  have h179 := C (T (T (T (T (T (T (T (T (T h166 h162) h87) h85) h81) h8) h11) h70) h49) h101) h169
  have h180 := C (T (T (T (T (T h7 h102) h93) h90) h161) h172) (T (T (T (C (T (T (T h39 h37) h118) h115) h25) (C h131 h25)) (C (T (T h155 h128) h127) h25)) (C h67 h25))
  have h181 := T (T (T (T (T (T (T h43 h41) h27) h158) h180) h179) h178) h177
  have h182 := T (T (T (T (T h26 h68) h66) h112) h129) h126
  have h183 := h z v2 v1
  have h184 := S h183
  have h185 := h v2 v1 v3
  have h186 := S h185
  have h187 := C h145 (T (T (T (T h158 h180) h179) h178) h177)
  have h188 := C (T h187 h186) (T (C h149 h21) (C h111 h69))
  let v189 := M y v0
  have h190 := R v189
  have h191 := S h143
  have h192 := C h42 (C h191 h191)
  have h193 := T h141 h192
  have h194 := C h193 (T (T (T (T h175 h174) h173) h167) h159)
  have h195 := C (T (T (T h57 h35) h185) h194) h190
  have h196 := C h60 h190
  have h197 := C h52 h190
  have h198 := h (M v2 v189) v1 v1
  have h199 := S h198
  have h200 := C h35 h190
  have h201 := C h57 h190
  have h202 := C (T (T (T h187 h186) h52) h60) h190
  have h203 := S h148
  have h204 := C h146 h193
  have h205 := T h204 h203
  have h206 := C (T h185 h194) (T (C h111 h44) (C h205 h21))
  have h207 := C (T (T (T (T h183 h206) h202) h201) h200) h145
  have h208 := h y y z
  have h209 := C h145 (T h208 (C (T h148 h207) h121))
  have h210 := C (T (T (T (T (T (T h209 h199) h197) h196) h195) h188) h184) (T (T (T (T (T (C h182 h176) (C h154 h176)) (C h181 h176)) (C (T (T (T (T (T (T (T (T (T (T (T (T (T h175 h174) h173) h167) h159) h26) h68) h66) h112) h129) h126) h123) h157) h151) h149)) (C h140 h111)) (C (T (T (T (T h135 h124) h122) h119) h113) h111))
  let v211 := M v0 y
  have h212 := R v211
  have h213 := C (T (T (T (T (T h55 h51) h33) h31) h141) h192) h176
  have h214 := C h213 h212
  have h215 := C h59 h176
  have h216 := C h215 h212
  have h217 := C h24 h176
  have h218 := C h217 h212
  let v219 := M v1 y
  let v220 := M v219 v211
  have h221 := h v220 v2 z
  have h222 := S h221
  have h223 := T (T (T (T (T (T (T (T (T (T h218 h216) h214) h210) h110) h15) h30) h63) h82) h104) h103
  have h224 := h v219 z v1
  have h225 := S h224
  have h226 := C h34 h176
  have h227 := C h56 h176
  have h228 := C (T (T (T (T (T h144 h142) h23) h22) h39) h37) h176
  have h229 := C (T (T (T (T h197 h196) h195) h188) h184) h193
  have h230 := C h193 (T (C (T h229 h203) h121) (S h208))
  have h231 := C (T (T (T (T h198 h230) h228) h227) h226) h42
  have h232 := C (T (T (T (T (T (T (T (T h215 h213) h209) h199) h197) h196) h195) h188) h184) (C (T (T h148 h207) h231) h149)
  let v233 := M y y
  have h234 := R v233
  have h235 := C h217 h234
  have h236 := h (M v219 v233) v1 y
  have h237 := S h236
  have h238 := C h226 h234
  have h239 := C (T (T (T (T h217 h215) h213) h209) h199) h42
  have h240 := C (T (T (T (T (T (T (T (T h183 h206) h202) h201) h200) h198) h230) h228) h227) (C (T (T h239 h229) h203) h205)
  have h241 := C (T (T (T (T (T (T (T (T (T (T (T (T h183 h206) h202) h201) h200) h198) h230) h228) h227) h226) h224) h240) h238) h176
  have h242 := C h42 (T (T (T (C h182 h146) (C h154 h146)) (C h181 h146)) (C (T (T (T (T (T h175 h174) h173) h167) h159) h241) (T (T (T (T (T (T (T (T (T h183 h206) h202) h201) h200) h198) h230) h228) h227) h226)))
  let v243 := M v1 (M v0 z)
  have h244 := h v243 y y
  have h245 := T (T (T (T (T h122 h119) h113) h43) h41) h27
  have h246 := T (T (T (T (T (T (T h175 h174) h173) h167) h159) h26) h68) h66
  have h247 := C (T (T (T (T (T (T (T (T (T (T (T (T h235 h232) h225) h217) h215) h213) h209) h199) h197) h196) h195) h188) h184) h176
  have h248 := C h42 (T (T (T (C (T (T (T (T (T h247 h158) h180) h179) h178) h177) (T (T (T (T (T (T (T (T (T h217 h215) h213) h209) h199) h197) h196) h195) h188) h184)) (C h246 h146)) (C h130 h146)) (C h245 h146))
  have h249 := T h236 h248
  have h250 := C h249 h176
  have h251 := T h241 h250
  have h252 := h y v0 x
  have h253 := S h252
  have h254 := h v0 v0 (M (M y x) v14)
  have h255 := C (T (T h235 h232) h225) h42
  have h256 := T h242 h237
  have h257 := C h256 h42
  have h258 := T (T (T (T h257 h255) h239) h229) h203
  have h259 := C h226 h212
  have h260 := C h227 h212
  have h261 := C h228 h212
  have h262 := C (T (T (T (T (T (T h183 h206) h202) h201) h200) h198) h230) (T (T (T (T (T (C (T (T (T (T h112 h129) h126) h123) h157) h111) (C h151 h111)) (C (T (T (T (T (T (T (T (T (T (T (T (T (T h140 h135) h124) h122) h119) h113) h43) h41) h27) h158) h180) h179) h178) h177) h205)) (C h246 h176)) (C h130 h176)) (C h245 h176))
  have h263 := T (T (T (T h109 h262) h261) h260) h259
  have h264 := C h263 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (C h258 (T (T (T (T (T h43 h41) h27) h254) (C h21 (C h253 h253))) (C h251 h234))) (S h244)) h242) h237) h235) h232) h225) h217) h215) h213) h209) h199) h197) h196) h195) h188) h184)
  have h265 := h v243 v2 v1
  have h266 := h v243 v0 v2
  have h267 := h v220 y z
  have h268 := C (T h265 h264) h42
  have h269 := C h249 h42
  have h270 := C (T (T h224 h240) h238) h42
  have h271 := h v243 z v1
  have h272 := S h265
  have h273 := C h256 h176
  have h274 := T h273 h247
  have h275 := T (T (T (T h148 h207) h231) h270) h269
  have h276 := T (T (T (T h218 h216) h214) h210) h110
  have h277 := C h276 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h183 h206) h202) h201) h200) h198) h230) h228) h227) h226) h224) h240) h238) h236) h248) h244) (C h275 (T (T (T (T (T (C h274 h234) (C h21 (C h252 h252))) (S h254)) h26) h68) h66)))
  let v278 := M v160 v168
  have h279 := h v278 v2 v2
  have h280 := S h279
  have h281 := C (C (T (T (T (T (T (T (T (T (T (T h122 h119) h113) h43) h41) h27) h158) h180) h179) h178) h177) h18) h125
  have h282 := C h276 (T (T (T (T (T (T (T h23 h22) h39) h37) h134) h133) h132) h281)
  have h283 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h183 h206) h202) h201) h200) h198) h230) h228) h227) h226) h224) h240) h238) h236) h248) h265) h264) (T (T (T (T (T (T (T (C (T (T (T (T (T (T h282 h280) h175) h174) h173) h167) h159) (T (T (T (T (T (T h204 h207) h231) h270) h269) h268) (C (T (T (T h277 h272) h271) (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T h183 h206) h202) h201) h200) h198) h230) h228) h227) h226) h224) h240) h238) h236) h248) (T (T (T (T (T (T (C h258 (T (T (T (T (T h204 h207) h231) h270) h269) h268)) (S h267)) h218) h216) h214) h210) h110))) h24))) (S h266)) h265) h264) (C h223 h146)) (C h139 h146)) (C h91 h146)) (C h20 h146))
  have h284 := h v220 z v1
  have h285 := C h276 (T (T (T (T (T (T h109 h262) h261) h260) h259) h284) h283)
  have h286 := C (T (T (T (T (T (T h187 h186) h109) h262) h261) h260) h259) h18
  have h287 := C (T (T (T (T (T (T (T h138 h136) h71) h64) h19) h16) h185) h194) h18
  have h288 := C h150 h73
  have h289 := T (T (T (T (T (T h285 h222) h218) h216) h214) h210) h110
  have h290 := C h289 (T (T (T (T (T (T (T (T (T (T (T h54 h53) h98) h97) h96) h288) h287) h286) h285) h222) h284) h283)
  have h291 := T h287 h286
  have h292 := C h291 h125
  have h293 := T h96 h288
  have h294 := C h293 h125
  have h295 := T (T h53 h98) h97
  have h296 := C h295 h125
  have h297 := C h54 h125
  have h298 := h (M v116 v116) v0 v2
  have h299 := S h298
  have h300 := C h28 h125
  have h301 := T (T h72 h58) h36
  have h302 := C h301 h125
  have h303 := C h139 h95
  have h304 := T h303 h76
  have h305 := C h304 h125
  have h306 := C (T (T (T (T (T (T (T h187 h186) h15) h30) h63) h82) h104) h103) h18
  have h307 := C (T (T (T (T (T (T h218 h216) h214) h210) h110) h185) h194) h18
  have h308 := T h307 h306
  have h309 := C h308 h125
  have h310 := S h284
  have h311 := C (T h277 h272) h42
  have h312 := C (C (T (T (T (T (T (T (T (T (T (T h175 h174) h173) h167) h159) h26) h68) h66) h112) h129) h126) h18) h125
  have h313 := C h263 (T (T (T (T (T (T (T h312 h156) h153) h152) h55) h51) h33) h31)
  have h314 := T (T (T (T (T (T (T (T (T (T h138 h136) h71) h64) h19) h16) h109) h262) h261) h260) h259
  have h315 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h277 h272) h242) h237) h235) h232) h225) h217) h215) h213) h209) h199) h197) h196) h195) h188) h184) (T (T (T (T (T (T (T (C h32 h146) (C h83 h146)) (C h150 h146)) (C h314 h146)) h277) h272) h266) (C (T (T (T (T (T (T h158 h180) h179) h178) h177) h279) h313) (T (T (T (T (T (T (C (T (T (T (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T h242 h237) h235) h232) h225) h217) h215) h213) h209) h199) h197) h196) h195) h188) h184) (T (T (T (T (T (T h109 h262) h261) h260) h259) h267) (C h275 (T (T (T (T (T h311 h257) h255) h239) h229) h147)))) (S h271)) h265) h264) h34) h311) h257) h255) h239) h229) h147)))
  have h316 := C h263 (T (T (T (T (T (T h315 h310) h218) h216) h214) h210) h110)
  have h317 := T (T (T (T (T (T h109 h262) h261) h260) h259) h221) h316
  have h318 := C h317 (T (T (T (T (T (T (T (T (T (T (T h315 h310) h221) h316) h307) h306) h303) h76) h72) h58) h36) h28)
  have h319 := h v62 v2 v2
  have h320 := C (T (T (T (T (T (T (T (T h218 h216) h214) h210) h110) h15) h30) h319) (C (T (T (T (T (T (T (T (T (T (T h109 h262) h261) h260) h259) h221) h318) h309) h305) h302) h300) (T (T (T (T (T (T (T (T (T h296 h294) h292) h290) h222) h218) h216) h214) h210) h110))) h24
  have h321 := h (M v1 (M z z)) v3 v0
  have h322 := R (M v3 v0)
  have h323 := h v278 v3 v0
  have h324 := C h276 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h158 h180) h179) h178) h177) h323) (C h25 (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (C (T h279 h313) h69) (C (T (T (T (T (T (T (T (T h282 h280) h175) h174) h173) h167) h159) h241) h250) h44)) (C h274 (T (T (T (T (T (T (T h158 h180) h179) h178) h177) h279) h313) h320))) h299) h297) h296) h294) h292) h290) h222) h218) h216) h214) h210) h110) h185) h194) h322))) (S h321)) h144) h142) h23) h22) h39) h37) h134) h133) h132) h281)
  have h325 := C h314 h21
  have h326 := C h150 h21
  have h327 := C h83 h21
  have h328 := C h32 h21
  have h329 := C (T (T (T (T (T (T h324 h280) h175) h174) h173) h167) h159) (T (T (T (T (T (T h328 h327) h326) h325) h324) h313) h320)
  let v330 := M v2 v0
  have h331 := R v330
  have h332 := C h325 h331
  have h333 := C h326 h331
  have h334 := C h327 h331
  have h335 := C h328 h331
  let v336 := M v330 v330
  have h337 := h v336 x v2
  have h338 := S h337
  have h339 := C h20 h21
  have h340 := C h339 h331
  have h341 := C h91 h21
  have h342 := C h341 h331
  have h343 := C h139 h21
  have h344 := C h343 h331
  have h345 := C h223 h21
  have h346 := C h345 h331
  have h347 := C (T (T (T (T (T (T (T (T (C (T (T (T (T (T (T (T (T (T (T h297 h296) h294) h292) h290) h222) h218) h216) h214) h210) h110) (T (T (T (T (T (T (T (T (T h109 h262) h261) h260) h259) h221) h318) h309) h305) h302)) (S h319)) h19) h16) h109) h262) h261) h260) h259) h34
  have h348 := C h263 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h312 h156) h153) h152) h55) h51) h33) h31) h141) h192) h321) (C h25 (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h187 h186) h109) h262) h261) h260) h259) h221) h318) h309) h305) h302) h300) h298) (C h251 (T (T (T (T (T (T (T h347 h282) h280) h175) h174) h173) h167) h159))) (C (T (T (T (T (T (T (T (T h273 h247) h158) h180) h179) h178) h177) h279) h313) h69)) (C (T h282 h280) h44)) h322))) (S h323)) h175) h174) h173) h167) h159)
  have h349 := C (T (T (T (T (T (T h158 h180) h179) h178) h177) h279) h348) (T (T (T (T (T (T h347 h282) h348) h345) h343) h341) h339)
  have h350 := h v62 v2 v0
  have h351 := C (T (T (T (T (T h298 h349) h346) h344) h342) h340) h25
  have h352 := C (T (T (T (T (T h221 h318) h309) h305) h302) h300) h25
  have h353 := T (T (T h106 h5) h77) h163
  have h354 := C h263 (T (T (T (C h353 h125) h171) h100) h94)
  have h355 := h v160 v2 v2
  have h356 := S h355
  have h357 := C h137 h165
  have h358 := T (T (T h170 h99) h4) h357
  have h359 := C h276 (T (T (T h79 h78) h164) (C h358 h125))
  have h360 := C (T (T (T (T (T h297 h296) h294) h292) h290) h222) h25
  have h361 := C (T (T (T (T (T h335 h334) h333) h332) h329) h299) h25
  have h362 := C (T (T (T (T (T (T (T (T (T h361 h360) h359) h356) h86) h84) h80) h50) h45) h12) (T (T (T (T h355 h354) h352) h351) (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h335 h334) h333) h332) h329) h299) h297) h296) h294) h292) h290) h222) h218) h216) h214) h210) h110) h15) h30) h350) (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h109 h262) h261) h260) h259) h221) h318) h309) h305) h302) h300) h298) h349) h346) h344) h342) h340) (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h334 h333) h332) h329) h299) h297) h296) h294) h292) h290) h222) h218) h216) h214) h210) h110))) h25))
  have h363 := R v160
  have h364 := C h351 h363
  have h365 := C h352 h363
  have h366 := C h360 h363
  have h367 := C h361 h363
  have h368 := C (T (T (T (T (T (T (T (T (T h11 h70) h49) h101) h92) h89) h355) h354) h352) h351) (T (T (T (T (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h335 h334) h333) h332) h329) h299) h297) h296) h294) h292) h290) h222) h218) h216) h214) h210) h110) (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h109 h262) h261) h260) h259) h221) h318) h309) h305) h302) h300) h298) h349) h346) h344) h342)) (S h350)) h19) h16) h109) h262) h261) h260) h259) h221) h318) h309) h305) h302) h300) h298) h349) h346) h344) h342) h340) h25) h361) h360) h359) h356)
  have h369 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h109 h262) h261) h260) h259) h221) h318) h309) h305) h302) h300) h298) h349) h346) h344) h342) h340) h337) h368) h367) h366) (C (T (T (T (T (T h359 h356) h86) h84) h80) h50) h88)) (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h365 h364) h362) h338) h335) h334) h333) h332) h329) h299) h297) h296) h294) h292) h290) h222) h218) h216) h214) h210) h110) h15) h30) h63) h82)
  have h370 := h v220 v2 v3
  have h371 := C h25 (T (T (T (T (T (T h109 h262) h261) h260) h259) h370) h369)
  have h372 := C (T (T (T (T (T h371 h108) h49) h101) h92) h89) h18
  let v373 := M v3 v2
  have h374 := h v373 v2 v2
  have h375 := S h374
  have h376 := h v336 v3 v3
  have h377 := h v48 x v2
  have h378 := T (T h372 h106) h5
  have h379 := C (T (T (T (T (T h49 h101) h92) h89) h355) h354) h137
  have h380 := C h25 (T (T (T (T (T (T (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h379 h365) h364) h362) h338) h335) h334) h333) h332) h329) h299) h297) h296) h294) h292) h290) h222) h218) h216) h214) h210) h110) (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h71 h64) h19) h16) h109) h262) h261) h260) h259) h221) h318) h309) h305) h302) h300) h298) h349) h346) h344) h342) h340) h337) h368) h367) h366)) (S h370)) h218) h216) h214) h210) h110)
  have h381 := C (T (T (T (T (T h86 h84) h80) h50) h107) h380) h18
  have h382 := T (T h4 h357) h381
  have h383 := h v373 v3 v2
  have h384 := C h289 (T h383 (C h382 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (C h378 (T (T (T (T (T h371 h108) h377) (C (T (T (T (T (T (T (T h11 h70) h49) h101) h92) h89) h355) h354) (T (T (C (T (T h99 h4) h357) h25) (C h353 h25)) (C (T h170 h99) h25)))) (C h352 h10)) (C h351 h10))) (S h376)) h335) h334) h333) h332) h329) h299) h297) h296) h294) h292) h290) h316) h307) h306) h303) h76) h72) h58) h36) h28)))
  have h385 := R v373
  have h386 := C h291 h385
  have h387 := C h293 h385
  have h388 := C h295 h385
  have h389 := C h54 h385
  have h390 := C (T (T (T (T (T h389 h388) h387) h386) h384) h375) h18
  have h391 := C h28 h385
  have h392 := C h301 h385
  have h393 := C h304 h385
  have h394 := C h308 h385
  have h395 := T (T (T h371 h108) h45) h12
  have h396 := C h317 (T (C h378 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h54 h53) h98) h97) h96) h288) h287) h286) h285) h318) h309) h305) h302) h300) h298) h349) h346) h344) h342) h340) h376) (C h382 (T (T (T (T (T (C h361 h10) (C h360 h10)) (C (T (T (T (T (T (T (T h359 h356) h86) h84) h80) h50) h45) h12) (T (T (C (T h77 h163) h25) (C h358 h25)) (C (T (T h106 h5) h77) h25)))) (S h377)) h107) h380)))) (S h383))
  have h397 := h v62 v3 v2
  T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h11 h70) h107) h380) h374) h396) h394) h393) h392) h391) (h (M v116 v373) v3 v2)) (C h25 (T (T (T (T (T (T (T (T (T (T (T (C (T (T (T h390 h372) h106) h5) (T (T (T (T h374 h396) h394) h393) h392)) (S h397)) h19) h16) h109) h262) h261) h260) h259) h370) h369) (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h379 h365) h364) h362) h338) h335) h334) h333) h332) h329) h299) h297) h296) h294) h292) h290) h222) h218) h216) h214) h210) h110) h15) h30) h397) (C (T (T (T h4 h357) h381) (C (T (T (T (T (T h374 h396) h394) h393) h392) h391) h18)) (T (T (T (T h388 h387) h386) h384) h375))) (C (T (T (C (T (T (T (T h389 h388) h387) h386) (C (T h285 h222) h395)) h95) (C (C h223 h6) h75)) (C (T (T (C h139 h6) (C h91 h6)) (C h20 h6)) h75)) h395)) h75)))) (S (h (M v13 v74) v3 x))) (C (T (T (C h32 h6) (C h83 h6)) (C h150 h6)) h75)) (C (C h314 h6) h75)) (C (T (T (T (T (C (T h221 h316) (T (T (T h11 h70) h107) h380)) h394) h393) h392) h391) h73)) h390) h372) h106) h5

