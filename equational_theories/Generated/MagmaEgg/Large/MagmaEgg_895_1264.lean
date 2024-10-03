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
theorem Equation895_implies_Equation1264 (G: Type _) [Magma G] (h: Equation895 G) : Equation1264 G := fun x y z =>
  let v0 := M y z
  let v1 := M v0 y
  let v2 := M v1 z
  have h3 := R v2
  have h4 := h x v1 v2
  have h5 := S h4
  let v6 := M v0 v2
  have h7 := h v1 v1 v6
  have h8 := S h7
  have h9 := h y v1 z
  have h10 := R v1
  have h11 := C h10 (C h9 h9)
  have h12 := T h11 h8
  have h13 := C h12 h3
  have h14 := h (M v1 (M y y)) z z
  have h15 := S h14
  have h16 := R (M z z)
  have h17 := R z
  have h18 := S h9
  have h19 := C h10 (C h18 h18)
  have h20 := T h7 h19
  have h21 := C h20 h17
  have h22 := C h21 h16
  have h23 := h z v2 x
  have h24 := S h23
  have h25 := C h3 (C h24 h24)
  let v26 := M v2 x
  have h27 := h v2 v2 (M (M z x) v26)
  have h28 := C h17 (T (T h27 h25) h22)
  have h29 := T h28 h15
  have h30 := C h29 h3
  let v31 := M z v2
  have h32 := h v31 v1 z
  have h33 := S h32
  have h34 := S h27
  have h35 := C h3 (C h23 h23)
  have h36 := C h12 h17
  have h37 := C h36 h16
  have h38 := C h17 (T (T h37 h35) h34)
  have h39 := T h14 h38
  have h40 := C h39 h17
  have h41 := C h40 h3
  have h42 := C h21 h3
  have h43 := T (T (T h28 h15) h11) h8
  have h44 := C h43 (T h42 h41)
  have h45 := T h44 h33
  have h46 := C h45 h3
  have h47 := C h36 h3
  have h48 := C h29 h17
  have h49 := C h48 h3
  have h50 := T (T (T h7 h19) h14) h38
  have h51 := C h50 (T h49 h47)
  have h52 := R v6
  let v53 := M v2 v2
  let v54 := M v31 v53
  have h55 := h v54 z z
  have h56 := S h55
  have h57 := T h32 h51
  have h58 := C h57 h17
  have h59 := C h58 h16
  have h60 := C h40 h16
  have h61 := h z v2 v2
  have h62 := S h61
  have h63 := C h3 (T (T (T (T (T h7 h19) h14) h38) h32) h51)
  have h64 := T h63 h62
  have h65 := C h64 (T (T (T (T h27 h25) h22) h60) h59)
  have h66 := T (T (T (T (T (T (T h65 h56) h44) h33) h28) h15) h11) h8
  have h67 := R v0
  have h68 := C h67 (T (C h66 h52) h18)
  let v69 := M v2 v1
  have h70 := h v69 v0 v2
  have h71 := T (T (T (T (T (T (T h70 h68) h7) h19) h14) h38) h32) h51
  have h72 := C h71 h3
  have h73 := C h48 h16
  have h74 := C h45 h17
  have h75 := C h74 h16
  have h76 := C h3 (T (T (T (T (T h44 h33) h28) h15) h11) h8)
  have h77 := T h61 h76
  have h78 := C h77 (T (T (T (T h75 h73) h37) h35) h34)
  have h79 := T (T (T (T (T (T (T (T (T (T (T h7 h19) h14) h38) h32) h51) h55) h78) h72) h46) h30) h13
  let v80 := M x v2
  have h81 := R v80
  have h82 := T h70 h68
  have h83 := C h82 (C h81 h79)
  have h84 := C (T h83 h5) h3
  have h85 := h (M v69 (M v80 v1)) v2 v2
  have h86 := S h85
  have h87 := R v53
  have h88 := S h70
  have h89 := T (T (T (T (T (T (T h7 h19) h14) h38) h32) h51) h55) h78
  have h90 := C h67 (T h9 (C h89 h52))
  have h91 := T (T (T (T (T (T (T h44 h33) h28) h15) h11) h8) h90) h88
  have h92 := C h91 h3
  have h93 := C h57 h3
  have h94 := C h39 h3
  have h95 := C h20 h3
  have h96 := T (T (T (T (T (T (T (T (T (T (T h95 h94) h93) h92) h65) h56) h44) h33) h28) h15) h11) h8
  have h97 := T h90 h88
  have h98 := C h97 (C h81 h96)
  have h99 := C (T h4 h98) h3
  have h100 := C h99 h87
  have h101 := h v2 v80 x
  have h102 := S h101
  have h103 := C h81 (C h102 h102)
  let v104 := M v80 x
  have h105 := h v80 v80 (M v26 v104)
  have h106 := C h3 (T (T h105 h103) h100)
  have h107 := C (T h106 h86) h3
  let v108 := M v2 v80
  have h109 := h v108 x v2
  have h110 := S h109
  have h111 := S h105
  have h112 := C h81 (C h101 h101)
  have h113 := C h84 h87
  have h114 := C h3 (T (T h113 h112) h111)
  have h115 := C (T h85 h114) h3
  have h116 := C (T h99 h115) h81
  have h117 := T (T (T h106 h86) h83) h5
  have h118 := C h117 h116
  have h119 := T h118 h110
  have h120 := C h119 h3
  let v121 := M v80 v80
  let v122 := M v108 v121
  have h123 := h v122 v80 x
  have h124 := S h123
  have h125 := h v104 z v80
  have h126 := S h125
  have h127 := C h91 h81
  have h128 := C (T (T (T h14 h38) h32) h51) h81
  have h129 := C h20 h81
  have h130 := R (M v104 v80)
  have h131 := C h12 h81
  have h132 := C (T (T (T h44 h33) h28) h15) h81
  have h133 := C h71 h81
  have h134 := h v54 v1 z
  have h135 := S h134
  have h136 := C h58 h3
  have h137 := C h66 (T (T h42 h41) h136)
  have h138 := C h92 h87
  have h139 := C h93 h87
  have h140 := C h94 h87
  have h141 := C h95 h87
  have h142 := T (T (T (T (T (T (T (T (T (T (T (T (T h141 h140) h139) h138) h137) h135) h44) h33) h28) h15) h11) h8) h90) h88
  have h143 := C h13 h87
  have h144 := C h30 h87
  have h145 := C h46 h87
  have h146 := C h72 h87
  have h147 := C h74 h3
  have h148 := C h89 (T (T h147 h49) h47)
  have h149 := C h142 h3
  have h150 := T (T (T (T (T (T (T (T h149 h65) h56) h134) h148) h146) h145) h144) h143
  have h151 := T (T (T (T (T (T (T (T (T (T (T (T (T h70 h68) h7) h19) h14) h38) h32) h51) h134) h148) h146) h145) h144) h143
  have h152 := C h151 h3
  have h153 := T (T (T (T (C (T (T (T (T (T (T (T (T (T (T (T h95 h94) h93) h92) h65) h56) h134) h148) h146) h145) h144) h143) h3) h149) h72) h46) h30
  have h154 := C h81 (T (T (T (T (T h118 h110) h106) h86) h83) h5)
  have h155 := h v2 v80 v80
  have h156 := T h155 h154
  have h157 := C h156 (T (T (T (T (C h120 h87) (C h107 h87)) h113) h112) h111)
  have h158 := h v122 v2 v2
  have h159 := C (T h107 h84) h81
  have h160 := T (T (T h4 h98) h85) h114
  have h161 := C h160 h159
  have h162 := T (T (T (T (T (T (T h4 h98) h85) h114) h109) h161) h158) h157
  let v163 := M v1 v2
  have h164 := h v163 x v2
  have h165 := C h64 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h61 h76) h70) h68) h7) h19) h14) h38) h32) h51) h55) h78) h72) h46) h30) h13) h164) (C h162 (T (T (T (T (T (T (T (T (C h153 h81) (C h94 h81)) (C h93 h81)) (C (T h92 h152) h81)) (C h150 h81)) (C h142 h81)) h133) h132) h131))) (C h130 (T (T (T h129 h128) h127) (C h64 h81))))
  have h166 := T (T (T h90 h88) h63) h62
  have h167 := R v69
  have h168 := C h167 h166
  have h169 := C (T (T (T (T (T h28 h15) h11) h8) h90) h88) h96
  have h170 := T (T (T (T (T (T (T h32 h51) h55) h78) h72) h46) h30) h13
  have h171 := T (T (T (T (T (T (T h95 h94) h93) h92) h65) h56) h44) h33
  have h172 := C h171 h170
  have h173 := R v31
  have h174 := C (T (T h46 h30) h13) h173
  have h175 := R (M v54 v2)
  have h176 := C h175 h171
  have h177 := C (T (T (T (T (T (T (T (T h141 h140) h139) h138) h137) h135) h55) h78) h72) (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h61 h76) h70) h68) h7) h19) h14) h38) h32) h51) h55) h78) h72) h46) h30) h13)
  let v178 := M v163 v53
  have h179 := R v178
  have h180 := C h179 h166
  have h181 := C h150 h43
  have h182 := R (M v178 v2)
  have h183 := C h182 h171
  have h184 := C (T (T h55 h78) h152) h79
  have h185 := C h57 h10
  have h186 := C h39 h10
  have h187 := C h20 h10
  let v188 := M v1 v1
  have h189 := h v188 v2 v1
  have h190 := S h189
  have h191 := C h12 h10
  have h192 := C h29 h10
  have h193 := C h45 h10
  have h194 := C (T (T h149 h65) h56) h96
  have h195 := C h182 h170
  have h196 := T (T (T (T (T (T (T (T h141 h140) h139) h138) h137) h135) h55) h78) h152
  have h197 := C h196 h50
  have h198 := T (T (T h61 h76) h70) h68
  have h199 := C h179 h198
  have h200 := C (T (T (T (T (T (T (T (T h92 h65) h56) h134) h148) h146) h145) h144) h143) (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h95 h94) h93) h92) h65) h56) h44) h33) h28) h15) h11) h8) h90) h88) h63) h62)
  have h201 := R v163
  have h202 := C h93 h201
  have h203 := C h94 h201
  have h204 := C h95 h201
  let v205 := M v163 v163
  have h206 := R v205
  have h207 := C h13 h201
  have h208 := C h30 h201
  have h209 := C h46 h201
  have h210 := C h175 h170
  have h211 := C (T (T h95 h94) h93) h173
  have h212 := C h13 h173
  have h213 := C h95 h50
  have h214 := C (T (T (T (T (T (T h213 h212) h211) h210) h209) h208) h207) h64
  have h215 := C h13 h43
  have h216 := C h95 h173
  have h217 := C (T (T (T (T (T (T (T (T (T (T h186 h185) h184) h183) h181) h180) h177) h176) h174) h216) h215) h167
  have h218 := C h187 h167
  have h219 := C (T (T (T (T (T h218 h217) h214) (C h206 h198)) (C (T (T (T (T h204 h203) h202) h200) h199) h97)) (C (T (T (T (T (T h197 h195) h194) h193) h192) h191) h82)) h97
  have h220 := C h191 h167
  have h221 := C (T (T (T (T (T (T (T (T (T (T h213 h212) h211) h210) h200) h199) h197) h195) h194) h193) h192) h167
  have h222 := C (T h216 h215) h97
  have h223 := R (M v163 v31)
  have h224 := C h223 h198
  have h225 := C h170 h171
  have h226 := C h225 h166
  have h227 := R (M v31 v163)
  have h228 := C h227 h198
  have h229 := C (T (T (T (T (T h70 h68) h7) h19) h14) h38) h79
  have h230 := C h229 h64
  have h231 := C h167 h198
  have h232 := T (T (T (T h94 h93) h92) h152) (C (T (T (T (T (T (T (T (T (T (T (T h141 h140) h139) h138) h137) h135) h55) h78) h72) h46) h30) h13) h3)
  have h233 := S h158
  have h234 := T h109 h161
  have h235 := C h234 h3
  have h236 := S h155
  have h237 := C h81 (T (T (T (T (T h4 h98) h85) h114) h109) h161)
  have h238 := T h237 h236
  have h239 := C h238 (T (T (T (T h105 h103) h100) (C h115 h87)) (C h235 h87))
  have h240 := T (T (T (T (T (T (T h239 h233) h118) h110) h106) h86) h83) h5
  have h241 := C h77 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (C h130 (T (T (T (C h77 h81) h133) h132) h131)) (C h240 (T (T (T (T (T (T (T (T h129 h128) h127) (C h151 h81)) (C h196 h81)) (C (T h149 h72) h81)) (C h46 h81)) (C h30 h81)) (C h232 h81)))) (S h164)) h95) h94) h93) h92) h65) h56) h44) h33) h28) h15) h11) h8) h90) h88) h63) h62)
  have h242 := C (T (T (T (T h155 h154) h125) h241) h231) (T (T (T (T (T (T (T (T (T (T (T (T (T (C h153 h87) h140) h139) h138) h137) h135) h44) h33) h28) h15) h11) h8) h90) h88)
  have h243 := h v163 v2 v2
  have h244 := h v178 z z
  have h245 := S h244
  have h246 := C h201 h198
  have h247 := C h201 h166
  have h248 := T (T (T (T (T (T h74 h48) h36) h155) h154) h125) h241
  have h249 := S h243
  have h250 := C (T (T (T (T h168 h165) h126) h237) h236) (T (T (T (T (T (T (T (T (T (T (T (T (T h70 h68) h7) h19) h14) h38) h32) h51) h134) h148) h146) h145) h144) (C h232 h87))
  have h251 := C h169 h77
  have h252 := C h227 h166
  have h253 := C h172 h198
  have h254 := C h223 h166
  have h255 := C (T h213 h212) h82
  have h256 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h218 h217) h255) h254) h253) h252) h251) h250) h249) h95) h94) h93) h92) h65) h56) h44) h33) h28) h15) h11) h8) h90) h88) h63) h62) (T (T (T (T (T (T (T h27 h25) h22) h60) h59) (C h248 h16)) (C (T (T (T (T (T h231 h229) h225) h216) h215) h247) h16)) (C (T (T (T (T (T h246 h213) h212) h211) h210) h200) h16))
  have h257 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h256 h245) h141) h140) h139) h138) h137) h135) h55) h78) h72) h46) h30) h13) h243) h242) h230) h228) h226) h224) h222) h221) h220) h43
  let v258 := M v188 v69
  have h259 := R (M v258 v2)
  have h260 := C h259 h171
  have h261 := C (T (T (T (T (T (T h204 h203) h202) h176) h174) h216) h215) h77
  have h262 := T (T (T (T (T (T h165 h126) h237) h236) h21) h40) h58
  have h263 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h61 h76) h70) h68) h7) h19) h14) h38) h32) h51) h55) h78) h72) h46) h30) h13) h243) h242) h230) h228) h226) h224) h222) h221) h220) (T (T (T (T (T (T (T (C (T (T (T (T (T h177 h176) h174) h216) h215) h247) h16) (C (T (T (T (T (T h246 h213) h212) h172) h169) h168) h16)) (C h262 h16)) h75) h73) h37) h35) h34)
  have h264 := C (T (T (T (T (T (T (T (T (T (T (T (T (T h7 h19) h14) h38) h32) h51) h134) h148) h146) h145) h144) h143) h244) h263) (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (C (T (T h261 h255) h254) h3) (C (T h253 h252) h3)) (C (T (T (T (T (T h228 h226) h224) h222) h221) h220) h3)) h256) h245) h141) h140) h139) h138) h137) h135) h55) h78) h72) h46) h30) h13)
  have h265 := h v205 v1 z
  have h266 := S h265
  have h267 := C (T (T (T (T (T (T (T (T (T (T (T (T (T h256 h245) h141) h140) h139) h138) h137) h135) h44) h33) h28) h15) h11) h8) (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h95 h94) h93) h92) h65) h56) h134) h148) h146) h145) h144) h143) h244) h263) (C (T (T (T (T (T h218 h217) h255) h254) h253) h252) h3)) (C (T h228 h226) h3)) (C (T (T h224 h222) h214) h3))
  have h268 := C h259 h170
  have h269 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h218 h217) h255) h254) h253) h252) h251) h250) h249) h95) h94) h93) h92) h65) h56) h134) h148) h146) h145) h144) h143) h244) h263) h50
  have h270 := R v258
  have h271 := C h270 h198
  have h272 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h271 h269) h268) h267) h266) h204) h203) h202) h176) h174) h172) h169) h168) h165) h126) h237) h236) (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h155 h154) h125) h241) h231) h229) h225) h211) h210) h209) h208) h207) h265) h264) h260) h257) h219)
  have h273 := C h270 h166
  have h274 := C (T (T (T (T (T (T (T (T (T (T (T (T h231 h229) h225) h211) h210) h209) h208) h207) h265) h264) h260) h257) h273) h3
  have h275 := C h248 h3
  have h276 := C (T h169 h168) h3
  have h277 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h276 h274) h272) h190) h187) h186) h185) h184) h183) h181) h180) h177) h176) h174) h172) h169) h168) h165) h126) h237) h236) (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h42 h41) h136) h275) h274) h272) h190) h187) h186) h185) h184) h183) h181) h180) h177) h209) h208) h207) h265) h264) h260) h257) h219)
  have h278 := C (T h231 h229) h3
  have h279 := C (T (T (T (T h42 h41) h136) h275) h278) h87
  have h280 := h (M v53 v53) x v2
  have h281 := S h280
  have h282 := C h262 h3
  have h283 := C (T (T (T (T h276 h282) h147) h49) h47) h87
  have h284 := C (T (T (T (T (T (T (T (T (T (T (T (T h271 h269) h268) h267) h266) h204) h203) h202) h176) h174) h172) h169) h168) h3
  have h285 := C (T (T (T (T (T (C (T (T (T (T (T h187 h186) h185) h184) h183) h181) h97) (C (T (T (T (T h180 h177) h209) h208) h207) h82)) (C h206 h166)) h261) h221) h220) h82
  have h286 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h155 h154) h125) h241) h231) h229) h225) h211) h210) h209) h208) h207) h265) h264) h260) h257) h273) (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h285 h269) h268) h267) h266) h204) h203) h202) h176) h174) h172) h169) h168) h165) h126) h237) h236)
  have h287 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h155 h154) h125) h241) h231) h229) h225) h211) h210) h200) h199) h197) h195) h194) h193) h192) h191) h189) h286) h284) h278) (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h285 h269) h268) h267) h266) h204) h203) h202) h200) h199) h197) h195) h194) h193) h192) h191) h189) h286) h284) h282) h147) h49) h47)
  have h288 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h155 h154) h125) h241) h231) h229) h225) h211) h210) h200) h199) h197) h195) h194) h193) h192) h191) h189) h287) h283) (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (C (T (C (T (T (T (T (T (T h187 h186) h185) h184) h183) h181) h180) h3) (C (T (T (T h177 h209) h208) h207) h3)) h87) (C (C (T (T (T (T h204 h203) h202) h176) h174) h3) h87)) (C (T (C (T (T h216 h215) h247) h3) (C (T (T (T h246 h213) h212) h172) h3)) h87)) h277) h190) h187) h186) h185) h184) h183) h181) h180) h177) h176) h174) h172) h169) h168) h165) h126) h237) h236)
  have h289 := h v188 v2 v2
  have h290 := C (T (T (T (T h279 h277) h190) h289) h288) h81
  have h291 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h125 h241) h231) h229) h225) h211) h210) h200) h199) h197) h195) h194) h193) h192) h191) h189) h287) h283) h81
  have h292 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h279 h277) h190) h187) h186) h185) h184) h183) h181) h180) h177) h176) h174) h172) h169) h168) h165) h126) h81
  have h293 := C (T (T (T (T (T (T (T (T h292 h239) h233) h118) h110) h106) h86) h83) h5) (T (T (T (T (T h109 h161) h158) h157) h291) h290)
  have h294 := R v108
  have h295 := C h291 h294
  have h296 := C (T h239 h233) h117
  have h297 := C h292 h294
  have h298 := S h289
  have h299 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h279 h277) h190) h187) h186) h185) h184) h183) h181) h180) h177) h176) h174) h172) h169) h168) h165) h126) h237) h236) (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h155 h154) h125) h241) h231) h229) h225) h211) h210) h200) h199) h197) h195) h194) h193) h192) h191) h189) h287) (C (T (C (T (T (T h225 h216) h215) h247) h3) (C (T (T h246 h213) h212) h3)) h87)) (C (C (T (T (T (T h211 h210) h209) h208) h207) h3) h87)) (C (T (C (T (T (T h204 h203) h202) h200) h3) (C (T (T (T (T (T (T h199 h197) h195) h194) h193) h192) h191) h3)) h87))
  have h300 := C (T (T (T (T h299 h298) h189) h287) h283) h81
  have h301 := C (T (T (T (T (T (T (T (T h4 h98) h85) h114) h109) h161) h158) h157) h291) (T (T (T (T (T h300 h292) h239) h233) h118) h110)
  have h302 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h155 h154) h125) h241) h231) h229) h225) h211) h210) h200) h199) h197) h195) h194) h193) h192) h191) h189) h287) h283) h280) h301) h297) h296) (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h295 h293) h281) h279) h277) h190) h187) h186) h185) h184) h183) h181) h180) h177) h176) h174) h172) h169) h168) h165) h126)
  have h303 := h v104 v2 v80
  have h304 := C h81 (T (T (T h155 h154) h303) h302)
  have h305 := C (T h304 h124) h3
  let v306 := M v80 v2
  have h307 := h v306 v2 v2
  have h308 := S h307
  have h309 := S h303
  have h310 := C (T h158 h157) h160
  have h311 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h310 h295) h293) h281) h279) h277) h190) h187) h186) h185) h184) h183) h181) h180) h177) h176) h174) h172) h169) h168) h165) h126) h237) h236) (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h125 h241) h231) h229) h225) h211) h210) h200) h199) h197) h195) h194) h193) h192) h191) h189) h287) h283) h280) h301) h297)
  have h312 := R v104
  have h313 := R x
  have h314 := C h234 h313
  have h315 := C h314 h312
  have h316 := C h160 h313
  have h317 := C h316 h312
  let v318 := M x x
  let v319 := M v318 v104
  have h320 := h v319 v80 v80
  have h321 := R v121
  have h322 := C h117 h313
  have h323 := C h322 h312
  have h324 := C h316 h156
  have h325 := C (T h324 h323) h81
  have h326 := C h322 h238
  have h327 := C h119 h313
  have h328 := C h327 h312
  have h329 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h299 h298) h187) h186) h185) h184) h183) h181) h180) h177) h176) h174) h172) h169) h168) h165) h126) h303) h302) h328) h326) h81
  have h330 := h v122 x v2
  have h331 := T (T (T h305 h120) h107) h84
  have h332 := C h81 (T (T (T h311 h309) h237) h236)
  have h333 := T (T (T h99 h115) h235) (C (T h123 h332) h3)
  have h334 := C h333 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (C h331 (T (T (T (T (T h304 h124) h330) (C h162 (T (C h120 h81) h159))) (C h291 h321)) (C (T (T h290 h329) h325) h321))) (S h320)) h317) h315) h311) h309) h125) h241) h231) h229) h225) h211) h210) h200) h199) h197) h195) h194) h193) h192) h191) h189) h286) h284) h282) h147) h49) h47)
  have h335 := h v306 v80 v2
  have h336 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h314 h310) h295) h293) h281) h279) h277) h190) h187) h186) h185) h184) h183) h181) h180) h177) h176) h174) h172) h169) h168) h165) h126) h237) h236) (T (T (T (C h3 (T (T (T (T (T (T (T (T (T h4 h98) h85) h114) h109) h161) h123) h332) h335) h334)) h308) h335) h334)
  have h337 := R v26
  have h338 := C h316 h337
  have h339 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h324 h315) h311) h309) h125) h241) h231) h229) h225) h211) h210) h200) h199) h197) h195) h194) h193) h192) h191) h289) h288) h81
  have h340 := h v318 x v2
  have h341 := C (T h317 h326) h81
  let v342 := M v318 v26
  have h343 := C h322 h337
  have h344 := S h335
  have h345 := C h331 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h42 h41) h136) h275) h274) h272) h190) h187) h186) h185) h184) h183) h181) h180) h177) h176) h174) h172) h169) h168) h165) h126) h303) h302) h328) h323) h320) (C h333 (T (T (T (T (T (C (T (T h341 h339) h300) h321) (C h292 h321)) (C h240 (T h116 (C h235 h81)))) (S h330)) h123) h332)))
  have h346 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h155 h154) h125) h241) h231) h229) h225) h211) h210) h200) h199) h197) h195) h194) h193) h192) h191) h189) h287) h283) h280) h301) h297) h296) h327) (T (T (T h345 h344) h307) (C h3 (T (T (T (T (T (T (T (T (T h345 h344) h304) h124) h118) h110) h106) h86) h83) h5)))
  T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h4 h98) h85) h114) h109) h161) h123) h332) h307) h346) h343) (h v342 x x)) (C (T (T (T (T (T (T (T (T (T (T h4 h98) h85) h114) h109) h161) h123) h332) h307) h346) h343) (T (T (T (T (T (T (T (T (C (R (M v342 x)) (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h316 h314) h310) h295) h293) h281) h279) h277) h190) h187) h186) h185) h184) h183) h181) h180) h177) h176) h174) h172) h169) h168) h165) h126)) (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (C (T (T (T (T (T (T (T (T (T (T h338 h336) h308) h304) h124) h158) h157) h291) h290) h329) h325) h160) (C (T (T (T (T (T (T (T (T (T (T (T h341 h339) h300) h292) h239) h233) h118) h110) h106) h86) h83) h5) (T (T (T (T (T (T h109 h161) h158) h157) h291) h290) h329))) (S h340)) h316) h314) h310) h295) h293) h281) h279) h277) h190) h187) h186) h185) h184) h183) h181) h180) h177) h176) h174) h172) h169) h168) h165) h126) h237) h236) (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h125 h241) h231) h229) h225) h211) h210) h200) h199) h197) h195) h194) h193) h192) h191) h189) h287) h283) h280) h301) h297) h296) h327) h322) h340) (C (T (T (T (T (T (T (T (T (T (T (T h4 h98) h85) h114) h109) h161) h158) h157) h291) h290) h329) h325) (T (T (T (T (T (T h339 h300) h292) h239) h233) h118) h110))))) (S (h v319 v2 v80))) h317) h315) h311) h309) h237) h236))) (C (T (T h338 h336) h308) h3)) h305) h120) h107) h84

