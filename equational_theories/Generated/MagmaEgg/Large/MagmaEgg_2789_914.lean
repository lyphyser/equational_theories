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
theorem Equation2789_implies_Equation914 (G: Type _) [Magma G] (h: Equation2789 G) : Equation914 G := fun x y z =>
  let v0 := M z z
  let v1 := M y x
  let v2 := M v1 v0
  let v3 := M y v2
  have h4 := R x
  let v5 := M y v3
  let v6 := M x z
  let v7 := M x v1
  have h8 := h v1 (M v7 v6) v1
  have h9 := S h8
  have h10 := R v1
  have h11 := h z x v1
  have h12 := C (C h11 h11) h10
  have h13 := h v0 (M (M x v0) v6) v0
  have h14 := S h13
  have h15 := R v0
  have h16 := h z x v0
  have h17 := C (C h16 h16) h15
  have h18 := h v0 v2 v2
  have h19 := S h18
  let v20 := M x v2
  have h21 := h v2 (M v20 v6) v2
  have h22 := S h21
  have h23 := R v2
  have h24 := h z x v2
  have h25 := C (C h24 h24) h23
  have h26 := h v2 v0 y
  have h27 := S h26
  have h28 := R y
  have h29 := S h24
  have h30 := C (C h29 h29) h23
  have h31 := T h21 h30
  have h32 := h z x y
  have h33 := S h32
  have h34 := C (C h33 h33) h28
  have h35 := h y (M (M x y) v6) y
  have h36 := T h35 h34
  have h37 := C h36 h31
  have h38 := C h37 h28
  have h39 := T h38 h27
  have h40 := C h15 h39
  have h41 := T h25 h22
  have h42 := S h35
  have h43 := C (C h32 h32) h28
  have h44 := T h43 h42
  have h45 := C h44 h41
  have h46 := C h45 h28
  have h47 := T (T (T (T h40 h25) h22) h26) h46
  have h48 := T h17 h14
  have h49 := C h48 h47
  have h50 := T h26 h46
  have h51 := C h15 h50
  let v52 := M v3 y
  have h53 := h v52 v0 v0
  have h54 := S h53
  have h55 := T (T (T (T h38 h27) h21) h30) h51
  have h56 := S h16
  have h57 := C (C h56 h56) h15
  have h58 := T h13 h57
  have h59 := C h58 h55
  have h60 := C (T (T (T h21 h30) h51) h59) h15
  have h61 := T (T (T (T (T (T h60 h54) h38) h27) h21) h30) h51
  have h62 := C h58 h61
  have h63 := C (T (T (T h49 h40) h25) h22) h15
  have h64 := T (T (T (T (T (T (T (T h62 h49) h40) h25) h22) h26) h46) h53) h63
  have h65 := C h48 h64
  have h66 := T (T (T (T (T (T h40 h25) h22) h26) h46) h53) h63
  have h67 := C h48 h66
  let v68 := M v2 v0
  have h69 := h v68 v0 v2
  have h70 := S h69
  have h71 := T (T (T h60 h54) h38) h27
  have h72 := T (T (T (T (T (T (T (T h60 h54) h38) h27) h21) h30) h51) h59) h67
  have h73 := C h31 h72
  have h74 := C h41 h66
  have h75 := C h31 h55
  have h76 := C h23 h50
  have h77 := C (T (T (T h76 h75) h74) h73) h71
  have h78 := T (T (T (T (T (T (T (T (T (T h77 h70) h60) h54) h38) h27) h21) h30) h51) h59) h67
  have h79 := C h58 h78
  have h80 := T (T (T h26 h46) h53) h63
  have h81 := C h23 h39
  have h82 := C h41 h47
  have h83 := C h31 h61
  have h84 := C h41 h64
  have h85 := C (T (T (T h84 h83) h82) h81) h80
  have h86 := C (T (T (T (T (T (T (T h25 h22) h26) h46) h53) h63) h69) h85) (T (T (T (T (T (T h79 h65) h62) h49) h40) h25) h22)
  have h87 := T (T (T (T (T (T (T (T (T (T h62 h49) h40) h25) h22) h26) h46) h53) h63) h69) h85
  have h88 := C h48 h87
  have h89 := C h58 h72
  have h90 := T (T (T (T (T (T (T (T (T (T (T (T h77 h70) h60) h54) h38) h27) h21) h30) h51) h59) h67) h89) h88
  have h91 := C h31 h90
  have h92 := C h41 h87
  have h93 := C (T (T (T (T (T (T (T h76 h75) h74) h73) h92) h91) h86) h19) (T (T h91 h86) h19)
  have h94 := T h73 h92
  let v95 := M v2 v2
  have h96 := R v95
  have h97 := C h96 h94
  have h98 := C h96 (T h75 h74)
  have h99 := C h96 h76
  let v100 := M v95 v95
  have h101 := h v100 v0 v1
  have h102 := S h101
  have h103 := C h96 h81
  have h104 := C h96 (T h83 h82)
  have h105 := C h31 h78
  have h106 := T h105 h84
  have h107 := C h96 h106
  have h108 := T (T (T (T (T (T (T (T (T (T (T (T h79 h65) h62) h49) h40) h25) h22) h26) h46) h53) h63) h69) h85
  have h109 := C h41 h108
  have h110 := C (T (T (T (T (T (T (T h77 h70) h60) h54) h38) h27) h21) h30) (T (T (T (T (T (T h21 h30) h51) h59) h67) h89) h88)
  have h111 := C (T (T (T (T (T (T (T h18 h110) h109) h105) h84) h83) h82) h81) (T (T h18 h110) h109)
  have h112 := T (T (T (T (T h13 h57) h111) h107) h104) h103
  have h113 := h v100 v2 v2
  let v114 := M v95 v68
  have h115 := h v114 v0 v0
  have h116 := S h115
  have h117 := T (T (T (T (T h99 h98) h97) h93) h17) h14
  have h118 := C (T (T (T (T (T (T (T h21 h30) h51) h59) h67) h89) h88) (C h58 h90)) h117
  have h119 := T (T (T (T (T (T (T h118 h116) h77) h70) h60) h54) h38) h27
  have h120 := C (T (T (T (T (T (T (T (C h48 h108) h79) h65) h62) h49) h40) h25) h22) h112
  have h121 := T (T (T (T (T (T (T h26 h46) h53) h63) h69) h85) h115) h120
  have h122 := C (T (T (T (T (T (T (T (T (T (T (T (T h98 h97) h93) h17) h14) h18) h110) h109) h105) h84) h83) h82) h81) h121
  have h123 := h v52 v2 v2
  have h124 := C (T (T (T (T (T (T (T (C (T (T (T h60 h54) h123) h122) h119) (S h113)) h99) h98) h97) h93) h17) h14) h112
  have h125 := h v100 v2 v0
  have h126 := S h11
  have h127 := C (C h126 h126) h10
  have h128 := T h8 h127
  have h129 := C h128 (T (T (T (T (T (T (T h13 h57) h111) h107) h104) h103) h125) h124)
  have h130 := C h129 h10
  let v131 := M v2 v1
  have h132 := h v131 v1 v0
  have h133 := h v131 v2 v0
  have h134 := S h133
  have h135 := S h125
  have h136 := S h123
  have h137 := C (T (T (T (T (T (T (T (T (T (T (T (T h76 h75) h74) h73) h92) h91) h86) h19) h13) h57) h111) h107) h104) h119
  have h138 := C (T (T (T (T (T (T (T h13 h57) h111) h107) h104) h103) h113) (C (T (T (T h137 h136) h53) h63) h121)) h117
  have h139 := T h12 h9
  have h140 := C h139 (T (T (T (T (T (T (T h138 h135) h99) h98) h97) h93) h17) h14)
  have h141 := C h140 h10
  have h142 := C h41 (T (T (T h138 h135) h101) h141)
  have h143 := C h31 (T h125 h124)
  have h144 := C h41 (T h138 h135)
  have h145 := C h31 (T (T (T h130 h102) h125) h124)
  have h146 := h v131 v2 v2
  have h147 := C (T (T (T (T (T (T (T (T (T h13 h57) h111) h107) h104) h103) h101) h141) h146) (C (T (T (T (T (C h96 (T h145 h144)) h137) h136) h53) h63) (T (T (T (T (T (T (T (T (T h26 h46) h53) h63) h69) h85) h115) h120) h143) h142))) (T (T (T (T (T (T (T h130 h102) h99) h98) h97) h93) h17) h14)
  have h148 := T h147 h134
  have h149 := C h139 h148
  have h150 := C (T (T (T (T (T (T (T (T (T (C (T (T (T (T h60 h54) h123) h122) (C h96 (T h143 h142))) (T (T (T (T (T (T (T (T (T h145 h144) h118) h116) h77) h70) h60) h54) h38) h27)) (S h146)) h130) h102) h99) h98) h97) h93) h17) h14) (T (T (T (T (T (T (T h13 h57) h111) h107) h104) h103) h101) h141)
  have h151 := R (M v0 v1)
  have h152 := C h151 (T (T (T (T (T h138 h135) h101) h141) h133) h150)
  have h153 := T (T h129 h152) h149
  have h154 := C h41 h148
  have h155 := h v131 v0 v2
  have h156 := R v131
  have h157 := C (T (T (T (T (T (T (T (T (T (T (C h156 h106) (C (T h155 (C (T (T (T (T (T (T (T (T (T (T h154 h145) h144) h118) h116) h77) h70) h60) h54) h38) h27) h153)) (T (T (T (T h73 h92) h91) h86) h19))) (S h132)) h130) h102) h99) h98) h97) h93) h17) h14) h10
  have h158 := h v114 v2 v1
  have h159 := h v131 v2 v3
  have h160 := S h159
  have h161 := R (M v0 y)
  have h162 := C h161 (T (T h62 h49) h40)
  have h163 := C h36 h72
  have h164 := C h44 (T (T (T (T (T (T (T (T (T (T h79 h65) h62) h49) h40) h25) h22) h26) h46) h53) h63)
  have h165 := C h36 h90
  have h166 := S h158
  have h167 := C h151 (T (T (T (T (T h147 h134) h130) h102) h125) h124)
  have h168 := T h133 h150
  have h169 := C h128 h168
  have h170 := T (T h169 h167) h140
  have h171 := C h31 h168
  have h172 := C (T (T (T (T (T (T (T (T (T (T h13 h57) h111) h107) h104) h103) h101) h141) h132) (C (T (C (T (T (T (T (T (T (T (T (T (T h26 h46) h53) h63) h69) h85) h115) h120) h143) h142) h171) h170) (S h155)) (T (T (T (T h18 h110) h109) h105) h84))) (C h156 h94)) h10
  have h173 := h v3 (M (M x v3) v6) v3
  have h174 := S h173
  have h175 := R v3
  have h176 := h z x v3
  have h177 := C (C h176 h176) h175
  have h178 := T h177 h174
  have h179 := C (T (T (T (T (T (T (T h172 h166) h77) h70) h60) h54) h38) h27) h178
  have h180 := h v3 v0 v1
  have h181 := C (T h180 (C h179 (T (T (T (T (T (T (T h8 h127) h172) h166) h115) h120) h143) h142))) (T (T (T (T h165 h164) h163) h162) h45)
  have h182 := C h44 h108
  have h183 := C h36 (T (T (T (T (T (T (T (T (T (T h60 h54) h38) h27) h21) h30) h51) h59) h67) h89) h88)
  have h184 := C h175 (T h183 h182)
  have h185 := C h44 h64
  have h186 := C h161 (T (T h51 h59) h67)
  have h187 := C h175 (T (T h37 h186) h185)
  have h188 := C h31 (T (T (T (T (T h187 h184) h181) h160) h133) h150)
  let v189 := M v3 v3
  have h190 := h v189 v2 v0
  have h191 := T (T (T (T (T (T (T (T (T (T (T h187 h184) h181) h160) h130) h102) h99) h98) h97) h93) h17) h14
  have h192 := C h175 (T (T h163 h162) h45)
  have h193 := C h175 (T h165 h164)
  have h194 := S h180
  have h195 := S h176
  have h196 := C (C h195 h195) h175
  have h197 := T h173 h196
  have h198 := C (T (T (T (T (T (T (T h26 h46) h53) h63) h69) h85) h158) h157) h197
  have h199 := C (T (C h198 (T (T (T (T (T (T (T h145 h144) h118) h116) h158) h157) h12) h9)) h194) (T (T (T (T h37 h186) h185) h183) h182)
  have h200 := C h41 (T (T (T (T (T h147 h134) h159) h199) h193) h192)
  have h201 := T (T (T (T (T (T (T (T (T (T (T h26 h46) h53) h63) h69) h85) h115) h120) h143) h142) h171) h200
  have h202 := h v68 y v2
  have h203 := S h202
  have h204 := T (T (T (T (T (T (T (T (T (T (T h188 h154) h145) h144) h118) h116) h77) h70) h60) h54) h38) h27
  have h205 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h76 h75) h74) h73) h92) h91) h86) h19) h13) h57) h111) h107) h104) h103) h101) h141) h159) h199) h193) h204
  have h206 := h v189 v2 v2
  have h207 := T (C (T (T (T (T (T (T (T (T (T (T (T (T (T h13 h57) h111) h107) h104) h103) h101) h141) h159) h199) h193) h192) h206) (C (T h205 h203) h201)) h191) (S h190)
  have h208 := C h41 h207
  have h209 := R (M v0 v189)
  have h210 := T (T (T (T (T (T (T (T (T h172 h166) h77) h70) h60) h54) h38) h27) h21) h30
  have h211 := C h210 h209
  have h212 := T (T (T (T (T (T (T (T (T (T (T h13 h57) h111) h107) h104) h103) h101) h141) h159) h199) h193) h192
  have h213 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h184 h181) h160) h130) h102) h99) h98) h97) h93) h17) h14) h18) h110) h109) h105) h84) h83) h82) h81) h201
  have h214 := T h190 (C (T (T (T (T (T (T (T (T (T (T (T (T (T (C (T h202 h213) h204) (S h206)) h187) h184) h181) h160) h130) h102) h99) h98) h97) h93) h17) h14) h212)
  have h215 := C h128 h214
  have h216 := h v189 v1 v0
  have h217 := S h216
  have h218 := C h139 h207
  have h219 := T (T (T (T (T (T (T (T (T h25 h22) h26) h46) h53) h63) h69) h85) h158) h157
  have h220 := C h219 h209
  have h221 := C h31 h214
  have h222 := h v189 v0 v1
  have h223 := C (T h222 (C (T (T (T (T (T (T (T (T (T (T (T (T (T h211 h208) h188) h154) h145) h144) h118) h116) h77) h70) h60) h54) h38) h27) (T (T (T (T (T (T (T (T (T (T (T (T h8 h127) h172) h166) h115) h120) h143) h142) h171) h200) h221) h220) h218))) h191
  have h224 := T h223 h217
  have h225 := T (T (T (T (T (T (T (T (T h26 h46) h53) h63) h69) h85) h158) h157) h12) h9
  have h226 := C h225 h224
  let v227 := M v189 v189
  have h228 := h v227 v2 v0
  have h229 := C (T (C (T (T (T (T (T (T (T (T (T (T (T (T (T h26 h46) h53) h63) h69) h85) h115) h120) h143) h142) h171) h200) h221) h220) (T (T (T (T (T (T (T (T (T (T (T (T h215 h211) h208) h188) h154) h145) h144) h118) h116) h158) h157) h12) h9)) (S h222)) h212
  have h230 := T h216 h229
  have h231 := T (T (T (T (T (T (T (T (T h8 h127) h172) h166) h77) h70) h60) h54) h38) h27
  have h232 := C h231 h230
  have h233 := R (M v2 v189)
  have h234 := T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h130 h102) h99) h98) h97) h93) h17) h14) h18) h110) h109) h105) h84) h83) h82) h81
  have h235 := T (T (T h226 h215) h211) h208
  have h236 := T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h76 h75) h74) h73) h92) h91) h86) h19) h13) h57) h111) h107) h104) h103) h101) h141
  have h237 := h v227 v2 v2
  have h238 := T (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h13 h57) h111) h107) h104) h103) h101) h141) h159) h199) h193) h192) h216) h229) h237) (C (T (T (T (C h236 h235) (C h234 h233)) h205) h203) (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h26 h46) h53) h63) h69) h85) h115) h120) h143) h142) h171) h200) h221) h220) h218) h232))) (T (T (T (T (T (T (T (T (T (T (T (T (T h223 h217) h187) h184) h181) h160) h130) h102) h99) h98) h97) h93) h17) h14)) (S h228)
  have h239 := C h41 h238
  have h240 := R (M v0 v227)
  have h241 := C h210 h240
  have h242 := T (T (T h221 h220) h218) h232
  have h243 := T h228 (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (C (T (T (T h202 h213) (C h236 h233)) (C h234 h242)) (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h226 h215) h211) h208) h188) h154) h145) h144) h118) h116) h77) h70) h60) h54) h38) h27)) (S h237)) h223) h217) h187) h184) h181) h160) h130) h102) h99) h98) h97) h93) h17) h14) (T (T (T (T (T (T (T (T (T (T (T (T (T h13 h57) h111) h107) h104) h103) h101) h141) h159) h199) h193) h192) h216) h229))
  have h244 := C h128 h243
  have h245 := C (T (T (T (T (T (T (T h53 h63) h69) h85) h158) h157) h12) h9) h230
  let v246 := M v52 v189
  have h247 := h v246 v2 v3
  have h248 := S h247
  have h249 := C (T (T (T (T (T (T (T h8 h127) h172) h166) h77) h70) h60) h54) h224
  have h250 := C h139 h238
  have h251 := C h219 h240
  have h252 := C h31 h243
  have h253 := T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h8 h127) h172) h166) h115) h120) h143) h142) h171) h200) h221) h220) h218) h232) h252) h251) h250) h249
  have h254 := h v2 (M v20 v7) v2
  have h255 := h v1 x v2
  have h256 := R (M v1 v1)
  have h257 := C (T (T (T (T (C h256 (T (T (T h244 h241) h239) h226)) (C h256 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h215 h211) h208) h188) h154) h145) h144) h118) h116) h77) h70) h60) h54) h38) h27) h129) h152) h149))) (C h256 h170)) (C (C h255 h255) h23)) (S h254)) h253
  have h258 := h v227 v1 v1
  have h259 := h v246 v2 v1
  have h260 := S h259
  have h261 := T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h245 h244) h241) h239) h226) h215) h211) h208) h188) h154) h145) h144) h118) h116) h158) h157) h12) h9
  have h262 := R (M v2 v246)
  have h263 := C h236 h262
  have h264 := T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h187 h184) h181) h160) h130) h102) h99) h98) h97) h93) h17) h14) h18) h110) h109) h105) h84) h83) h82) h81
  have h265 := C h264 (T (T (T h216 h229) h258) h257)
  have h266 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h13 h57) h111) h107) h104) h103) h101) h141) h159) h199) h193) h192) h216) h229) h265) h263) h261
  have h267 := C h44 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h266 h260) h245) h244) h241) h239) h226) h215) h211) h208) h188) h154) h145) h144) h118) h116)
  have h268 := S h258
  have h269 := S h255
  have h270 := C (T (T (T (T h254 (C (C h269 h269) h23)) (C h256 h153)) (C h256 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h169 h167) h140) h26) h46) h53) h63) h69) h85) h115) h120) h143) h142) h171) h200) h221) h220) h218))) (C h256 (T (T (T h232 h252) h251) h250))) h261
  have h271 := T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h76 h75) h74) h73) h92) h91) h86) h19) h13) h57) h111) h107) h104) h103) h101) h141) h159) h199) h193) h192
  have h272 := C h271 (T (T (T h270 h268) h223) h217)
  have h273 := C h234 h262
  have h274 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h273 h272) h223) h217) h187) h184) h181) h160) h130) h102) h99) h98) h97) h93) h17) h14) h253
  have h275 := T h259 h274
  have h276 := C h36 h275
  have h277 := T h266 h260
  have h278 := C h44 h277
  have h279 := C h36 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h115 h120) h143) h142) h171) h200) h221) h220) h218) h232) h252) h251) h250) h249) h259) h274)
  have h280 := h v3 v3 y
  have h281 := T (T (T (T (T (T (T (T (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h26 h46) h53) h63) h69) h85) h115) h120) h143) h142) h171) h200) h221) h220) h218) h232) h252) h251) h250) h249) h28) (S h280)) h37) h186) h185) h183) h182) h279) h278
  have h282 := R (M v2 y)
  have h283 := h y v2 v0
  have h284 := C (T (T (T h43 h42) h283) (C (T (T (T (C h71 h282) (C h225 h281)) (C h128 (T (T (T (T (T (T (T (T h276 h267) h165) h164) h163) h162) h45) h173) h196))) h179) (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h13 h57) h111) h107) h104) h103) h101) h141) h159) h199) h193) h192) h216) h229) h258) h257))) h178
  have h285 := C h36 h197
  have h286 := T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h285 h284) h248) h245) h244) h241) h239) h226) h215) h211) h208) h188) h154) h145) h144) h118) h116) h158) h157) h12) h9
  have h287 := h v5 v2 v1
  have h288 := R (M v2 v5)
  have h289 := C h44 h178
  have h290 := T (T (T (T (T (T (T (T h276 h267) h165) h164) h163) h162) h45) h280) (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h245 h244) h241) h239) h226) h215) h211) h208) h188) h154) h145) h144) h118) h116) h77) h70) h60) h54) h38) h27) h28)
  have h291 := C (T (T (T (C (T (T (T h198 (C h139 (T (T (T (T (T (T (T (T h177 h174) h37) h186) h185) h183) h182) h279) h278))) (C h231 h290)) (C h80 h282)) (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h270 h268) h223) h217) h187) h184) h181) h160) h130) h102) h99) h98) h97) h93) h17) h14)) (S h283)) h35) h34) h197
  have h292 := C h231 (T (T h247 h291) h289)
  have h293 := C h139 h277
  have h294 := R (M v0 v246)
  have h295 := C h219 h294
  have h296 := C h31 h275
  have h297 := h v227 v2 v3
  have h298 := S h297
  have h299 := R (M v2 v3)
  have h300 := C (T (T h180 (C h179 (T (T (T (T (T (T (T (T (T h8 h127) h172) h166) h115) h120) h143) h142) h171) h200))) (C h299 h242)) (T (T (T (T (T (T h276 h267) h165) h164) h163) h162) h45)
  have h301 := C h175 h281
  have h302 := C h175 h290
  have h303 := C (T (T (C h299 h235) (C h198 (T (T (T (T (T (T (T (T (T h188 h154) h145) h144) h118) h116) h158) h157) h12) h9))) h194) (T (T (T (T (T (T h37 h186) h185) h183) h182) h279) h278)
  have h304 := S (h z x x)
  T (T (T (h x (M (M x x) v6) x) (C (C h304 h304) h4)) (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h13 h57) h111) h107) h104) h103) h101) h141) h159) h199) h193) h192) h216) h229) h258) h257) h296) h295) h293) h292) (C h31 (T h287 (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (C h234 h288) (C h271 (T (T (T (T (T (T (T (T (C h225 (T (T h285 h284) h248)) (C h128 h275)) (C h210 h294)) (C h41 h277)) h270) h268) h297) h303) h302))) (C (T (T (T h187 h184) h181) h160) (T (T (T (T h301 h300) h298) h258) h257))) h273) h272) h223) h217) h187) h184) h181) h160) h130) h102) h99) h98) h97) h93) h17) h14) (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h8 h127) h172) h166) h115) h120) h143) h142) h171) h200) h221) h220) h218) h232) h252) h251) h250) h249) h247) h291) h289))))) (C h219 (R (M v0 v5)))) (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h172 h166) h115) h120) h143) h142) h171) h200) h221) h220) h218) h232) h252) h251) h250) h249) h247) h291) h289) (T (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h13 h57) h111) h107) h104) h103) h101) h141) h159) h199) h193) h192) h216) h229) h265) h263) (C (T (T (T h159 h199) h193) h192) (T (T (T (T h270 h268) h297) h303) h302))) (C h264 (T (T (T (T (T (T (T (T h301 h300) h298) h258) h257) h296) h295) h293) h292))) (C h236 h288)) h286) (S h287)))) (C h286 (R v5))) h4)) (S (h v3 y x))

