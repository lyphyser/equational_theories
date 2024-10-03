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
theorem Equation2349_implies_Equation2170 (G: Type _) [Magma G] (h: Equation2349 G) : Equation2170 G := fun x y z =>
  let v0 := M z y
  let v1 := M x (M x (M v0 v0))
  have h2 := h y v1 z
  have h3 := S h2
  have h4 := R z
  have h5 := h v0 x v0
  have h6 := R v1
  have h7 := C (T h5 (C h6 h5)) h4
  let v8 := M y z
  let v9 := M x (M x (M v8 v8))
  have h10 := h z v9 y
  have h11 := S h10
  have h12 := R y
  have h13 := h v8 x v8
  have h14 := R v9
  have h15 := C (T h13 (C h14 h13)) h12
  have h16 := R v0
  have h17 := C h16 (T h15 h11)
  have h18 := T (T h17 h7) h3
  have h19 := C h4 h18
  let v20 := M v8 x
  have h21 := R v20
  have h22 := S h13
  have h23 := C (T (C h14 h22) h22) h12
  have h24 := C h16 (T h10 h23)
  have h25 := S h5
  have h26 := C (T (C h6 h25) h25) h4
  let v27 := M z v8
  let v28 := M z v27
  let v29 := M x (M x (M z z))
  have h30 := h y v29 v28
  have h31 := S h30
  have h32 := R v28
  have h33 := h z z y
  have h34 := R v29
  have h35 := h z x z
  have h36 := C (T h35 (C h34 (T h35 (C h34 h33)))) h32
  have h37 := T (T (T (T h36 h31) h2) h26) h24
  have h38 := C h4 h37
  have h39 := S h35
  have h40 := S h33
  have h41 := C (T (C h34 (T (C h34 h40) h39)) h39) h32
  have h42 := R v8
  have h43 := C h42 h18
  have h44 := C h16 h43
  have h45 := C h42 h37
  have h46 := C h16 h45
  have h47 := T (T (T (T h17 h7) h3) h30) h41
  have h48 := C h42 h47
  have h49 := T (T h2 h26) h24
  have h50 := C h42 h49
  have h51 := T (T (T h10 h23) h50) h48
  have h52 := T h38 h19
  have h53 := C h52 h51
  have h54 := h v27 z z
  have h55 := C h12 (T (T h43 h15) h11)
  have h56 := C h12 h50
  have h57 := C h4 (T h56 h55)
  let v58 := M v20 v0
  have h59 := h v28 v58 z
  have h60 := S h59
  have h61 := R v58
  have h62 := C (C h61 (C h61 (T (T (T (T (T (T (T (T (T h57 h54) h53) h46) h44) h17) h7) h3) h30) h41))) h4
  let v63 := M v8 y
  let v64 := M y v63
  have h65 := h v64 v58 z
  have h66 := C h12 h43
  have h67 := C h12 (T (T h10 h23) h50)
  have h68 := T (T (T (T h67 h66) h65) h62) h60
  have h69 := C h68 (T (T (T (T (T (T (T h57 h54) h53) h46) h44) h17) h7) h3)
  have h70 := T h67 h66
  have h71 := C h4 h70
  have h72 := C h42 h71
  have h73 := C h4 h47
  have h74 := C h4 h49
  have h75 := T h74 h73
  have h76 := C h75 (T (T h72 h69) h40)
  have h77 := C h4 (T (T (T (T (T (T (T (T h76 h53) h46) h44) h17) h7) h3) h30) h41)
  have h78 := C h42 h57
  have h79 := S h54
  have h80 := T (T (T h45 h43) h15) h11
  have h81 := C h75 h80
  have h82 := C h16 h48
  have h83 := C h16 h50
  have h84 := S h65
  have h85 := C (C h61 (C h61 (T (T (T (T (T (T (T (T (T h36 h31) h2) h26) h24) h83) h82) h81) h79) h71))) h4
  have h86 := T (T (T (T h59 h85) h84) h56) h55
  have h87 := C h86 (T (T (T (T (T (T (T h2 h26) h24) h83) h82) h81) h79) h71)
  have h88 := C h52 (T (T h33 h87) h78)
  have h89 := h v64 z z
  have h90 := S h89
  have h91 := C (T (T h30 h41) (C h4 (C h4 h71))) h80
  have h92 := C h12 (T (T (T (T (T (T h72 h69) h40) h10) h23) h50) h48)
  have h93 := C h4 (T (T (T (T (T h92 h91) h90) h65) h62) h60)
  have h94 := C h4 (T (T (T (T (T (T (T (T (T h93 h36) h31) h2) h26) h24) h83) h82) h81) h88)
  have h95 := C h12 (T (T (T (T (T (T h45 h43) h15) h11) h33) h87) h78)
  have h96 := C (T (T (C h4 (C h4 h57)) h36) h31) h51
  have h97 := T (T (T (T (T h59 h85) h84) h89) h96) h95
  have h98 := C h4 h97
  let v99 := M v8 v27
  have h100 := h v99 z y
  have h101 := S h100
  have h102 := h (M z v28) y z
  have h103 := S h102
  have h104 := C h42 (T (T h76 h79) h71)
  have h105 := C h4 (T (T (T (T (T (T (T (T (T h76 h53) h46) h44) h17) h7) h3) h30) h41) h98)
  have h106 := C h4 (T (T (T (T (T (T (T (T h36 h31) h2) h26) h24) h83) h82) h81) h88)
  have h107 := T (T (T h74 h73) h106) h105
  have h108 := C h107 (T (T (T (T (T (T h76 h53) h46) h44) h17) h7) h3)
  have h109 := C h16 (T h108 h101)
  have h110 := h v99 v0 v0
  have h111 := C (T (T (T (T (T h67 h66) h89) h96) h95) (C h12 (T h110 (C (T (T (T (T (T (T (T h109 h76) h53) h46) h44) h17) h7) h3) h75)))) (T (T h104 h69) h40)
  have h112 := C h42 (T (T h57 h54) h88)
  have h113 := C h42 h112
  have h114 := C h42 h72
  have h115 := C h107 (T (T (T (T (T h114 h113) h111) h103) h36) h31)
  have h116 := C h42 h78
  have h117 := C h42 h104
  have h118 := T (T (T h94 h77) h38) h19
  have h119 := C h118 (T (T (T (T (T (T h2 h26) h24) h83) h82) h81) h88)
  have h120 := C h16 (T h100 h119)
  have h121 := C (T (T (T (T (T (C h12 (T (C (T (T (T (T (T (T (T h2 h26) h24) h83) h82) h81) h88) h120) h52) (S h110))) h92) h91) h90) h56) h55) (T (T h33 h87) h112)
  have h122 := C h16 (T h115 h119)
  have h123 := C h118 (T (T (T (T (T h30 h41) h102) h121) h117) h116)
  have h124 := h v99 v0 v8
  have h125 := C h16 (T h108 h123)
  have h126 := T (T (T (T (T (C h16 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (C h16 (T (T (T (C (T (T (T (T (T (T (T (T h2 h26) h24) h83) h82) h81) h88) h120) h125) h86) (S h124)) h100) h123)) h122) h109) h76) h53) h46) h44) h17) h7) h3) h30) h41) h102) h121) h117) h116)) h115) h101) h72) h69) h40
  have h127 := C h126 (T (T h30 h41) h98)
  have h128 := h v27 v0 v8
  have h129 := S h128
  have h130 := h v28 v0 y
  have h131 := S h130
  have h132 := T (T (T (T (T h33 h87) h78) h100) h123) (C h16 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h114 h113) h111) h103) h36) h31) h2) h26) h24) h83) h82) h81) h88) h120) h125) (C h16 (T (T (T h115 h101) h124) (C (T (T (T (T (T (T (T (T h122 h109) h76) h53) h46) h44) h17) h7) h3) h68)))))
  have h133 := C h132 (T (T h93 h36) h31)
  have h134 := C (T (T (T (T h33 h87) h78) h100) h119) (T (T (T (T (T (T (T h105 h133) h131) h59) h85) h84) h56) h55)
  have h135 := C h4 (T h73 h106)
  have h136 := T (T (T (T (T (T (T (T (T h135 h134) h129) h54) h53) h46) h44) h17) h7) h3
  have h137 := C h132 h136
  have h138 := C h4 h74
  have h139 := C h4 h138
  let v140 := M z v0
  let v141 := M z v140
  have h142 := h v141 y y
  have h143 := S h142
  have h144 := C h4 (T (T (T h139 h137) h127) h94)
  have h145 := T (T (T (T (T (T (T (T (T h144 h134) h129) h54) h53) h46) h44) h17) h7) h3
  have h146 := C h4 h19
  have h147 := C h4 h146
  have h148 := C h4 (T h77 h38)
  have h149 := C (T (T (T (T h108 h101) h72) h69) h40) (T (T (T (T (T (T (T h67 h66) h65) h62) h60) h130) h127) h94)
  have h150 := T (T (T (T (T (T (T (T (T h2 h26) h24) h83) h82) h81) h79) h128) h149) h148
  have h151 := C h126 h150
  have h152 := C h136 (T (T (T (T (T (T h74 h73) h106) h105) h133) h151) h147)
  have h153 := h v63 z v0
  have h154 := T (T (T h10 h23) h153) h152
  have h155 := h v64 v8 z
  have h156 := C (T (T (T (T h10 h23) h153) h152) (C h12 (T (T (T (T (T (T (T h139 h137) h131) h59) h85) h84) h155) (C (T (T (T (T h113 h111) h103) h36) h31) h154)))) h145
  let v157 := M z v141
  have h158 := h v157 v8 v8
  have h159 := S h158
  have h160 := R (M v8 v157)
  have h161 := T (T (T (T (T (T (T (T (T (T h74 h73) h106) h105) h133) h131) h59) h85) h84) h56) h55
  have h162 := C h161 h160
  have h163 := C h161 h162
  have h164 := C h4 (T (T (T h105 h133) h151) h147)
  have h165 := h y z z
  have h166 := S h165
  have h167 := h (M v0 v63) z z
  have h168 := S h167
  have h169 := S h153
  have h170 := C h150 (T (T (T (T (T (T h139 h137) h127) h94) h77) h38) h19)
  have h171 := T (T (T h170 h169) h15) h11
  have h172 := C (T (T (T (T (T h74 h73) h106) h105) h133) h151) h171
  have h173 := C h107 (T (T (T (T h172 h168) h17) h7) h3)
  have h174 := R (M y v141)
  have h175 := T (T (T (T (T (T (T (T (T (T h67 h66) h65) h62) h60) h130) h127) h94) h77) h38) h19
  have h176 := C h175 h174
  have h177 := C h175 h176
  have h178 := C h161 h174
  have h179 := C (T (T (T (T (T h137 h127) h94) h77) h38) h19) h154
  have h180 := C h161 (T (T (T (T (T (T (T (T (T h144 h134) h129) h54) h53) h46) h44) h167) h179) h178)
  have h181 := C (T (T (T (T (T (T (T h67 h66) h65) h62) h60) h130) h151) h147) (T (T (T (T (T (T h180 h177) h173) h101) h72) h69) h40)
  have h182 := R (M v0 v157)
  have h183 := C h161 h182
  have h184 := C h161 (T (T (T (T (T (T (T (T (T (T (T (T h183 h181) h166) h2) h26) h24) h83) h82) h81) h79) h128) h149) h164)
  have h185 := C h175 h182
  have h186 := C h175 h185
  have h187 := C h175 (T (T (T (T (T (T (T (T (T h176 h172) h168) h83) h82) h81) h79) h128) h149) h164)
  have h188 := C h161 h178
  have h189 := C h118 (T (T (T (T h2 h26) h24) h167) h179)
  have h190 := C (T (T (T (T (T (T (T h139 h137) h131) h59) h85) h84) h56) h55) (T (T (T (T (T (T h33 h87) h78) h100) h189) h188) h187)
  have h191 := C h161 (T (T (T (T (T (T (T (T (T (T (T h144 h134) h129) h54) h53) h46) h44) h17) h7) h3) h165) h190)
  have h192 := C h16 (T (T h191 h186) h184)
  have h193 := C h175 (T (T (T (T (T (T (T (T (T (T (T (T (T h144 h134) h129) h54) h53) h46) h44) h17) h7) h3) h165) h190) h185) h192)
  have h194 := C (T (T (T (T (T (T (T (T (T (T (T h33 h87) h78) h100) h189) h188) h187) h191) h186) h184) h193) h163) (T (T (T (T (T (T (T (T (T h156 h143) h139) h137) h131) h59) h85) h84) h56) h55)
  have h195 := C h4 (T h194 h159)
  have h196 := T (T (T (T (T (T (T (T (T h2 h26) h24) h83) h82) h81) h79) h128) h149) h164
  have h197 := C (T (T (T (T (C h12 (T (T (T (T (T (T (T (C (T (T (T (T h30 h41) h102) h121) h117) h171) (S h155)) h65) h62) h60) h130) h151) h147)) h170) h169) h15) h11) h196
  have h198 := C h175 (T (T (T (T (T (T (T (T (T (T (T h181 h166) h2) h26) h24) h83) h82) h81) h79) h128) h149) h164)
  have h199 := C h161 h183
  have h200 := C h175 (T (T (T (T (T (T (T (T (T (T (T (T h144 h134) h129) h54) h53) h46) h44) h17) h7) h3) h165) h190) h185)
  have h201 := C h16 (T (T h200 h199) h198)
  have h202 := C h161 (T (T (T (T (T (T (T (T (T (T (T (T (T h201 h183) h181) h166) h2) h26) h24) h83) h82) h81) h79) h128) h149) h164)
  have h203 := C h175 h160
  have h204 := C h175 h203
  have h205 := C (T (T (T (T (T (T (T (T (T (T (T h204 h202) h200) h199) h198) h180) h177) h173) h101) h72) h69) h40) (T (T (T (T (T (T (T (T (T h67 h66) h65) h62) h60) h130) h151) h147) h142) h197)
  have h206 := h v157 z z
  have h207 := S h206
  have h208 := C h161 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h138 h135) h134) h129) h54) h53) h46) h44) h17) h7) h3) h165) h190) h185) h192) h162)
  have h209 := T (T (T (T (T (T (T (T (T (T (T (T h208 h204) h202) h200) h199) h198) h180) h177) h173) h101) h72) h69) h40
  have h210 := C h4 (T h158 h205)
  have h211 := C (T (T (T (T (T (T (T (T (T (T h67 h66) h65) h62) h60) h130) h151) h147) h142) h197) h210) h209
  have h212 := C h4 (T (T (T h211 h207) h158) h205)
  have h213 := C h175 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h203 h201) h183) h181) h166) h2) h26) h24) h83) h82) h81) h79) h128) h149) h148) h146)
  have h214 := T (T (T (T (T (T (T (T (T (T (T (T h33 h87) h78) h100) h189) h188) h187) h191) h186) h184) h193) h163) h213
  have h215 := C (T (T (T (T (T (T (T (T (T (T h195 h156) h143) h139) h137) h131) h59) h85) h84) h56) h55) h214
  have h216 := h v140 v8 v0
  have h217 := S h216
  have h218 := h v0 z z
  have h219 := S h218
  have h220 := C h196 h209
  let v221 := M v0 v140
  have h222 := R (M v8 v221)
  have h223 := C h161 h222
  have h224 := C h16 (T (T (T (T h138 h135) h164) h206) h215)
  have h225 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T h33 h87) h78) h100) h189) h188) h187) h191) h186) h184) h193) h163) h213) h224) h223) (T h220 h219)
  have h226 := C h4 (T (T (T (T (T (T h225 h217) h138) h135) h164) h206) h215)
  have h227 := C h145 h214
  have h228 := C h16 (T (T (T (T h211 h207) h144) h148) h146)
  have h229 := C h175 h222
  have h230 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T h229 h228) h208) h204) h202) h200) h199) h198) h180) h177) h173) h101) h72) h69) h40) (T h218 h227)
  have h231 := C h161 h228
  have h232 := C h175 h229
  have h233 := C h161 (T h224 h223)
  have h234 := C h4 (T (T (T (T (T (T (T (T (T h233 h232) h231) h211) h207) h144) h148) h146) h216) h230)
  let v235 := M v0 v221
  have h236 := h v235 y v8
  have h237 := S h236
  have h238 := C h175 (T h229 h228)
  have h239 := C h161 h223
  have h240 := C h175 h224
  have h241 := T (T (T (T (T (T (T (T (T (T (T (T (T (T h2 h26) h24) h83) h82) h81) h79) h128) h149) h164) h206) h215) h240) h239) h238
  have h242 := h v221 v8 v8
  have h243 := S h242
  have h244 := C (T (T (T (T (T (T (T (T (T (T (T (T (T h2 h26) h24) h83) h82) h81) h79) h128) h149) h164) h206) h215) h240) h239) (T (T (T (T (T (T (T (T (T (T (T (T h220 h219) h74) h73) h106) h105) h133) h131) h59) h85) h84) h56) h55)
  have h245 := C h12 (T h244 h243)
  have h246 := C (T (T (T (T (T (T (T (T (T (T (T (T (T h245 h220) h219) h74) h73) h106) h105) h133) h131) h59) h85) h84) h56) h55) h241
  have h247 := h v221 y y
  have h248 := C h12 (T (T (T h244 h243) h247) h246)
  have h249 := C (T (T (T (T (T (T (T (T (T (T (T (T (T h232 h231) h211) h207) h144) h134) h129) h54) h53) h46) h44) h17) h7) h3) (T (T (T (T (T (T (T (T (T (T (T (T h67 h66) h65) h62) h60) h130) h127) h94) h77) h38) h19) h218) h227)
  have h250 := C h12 (T h242 h249)
  have h251 := S h247
  have h252 := T (T (T (T (T (T (T (T (T (T (T (T (T (T h233 h232) h231) h211) h207) h144) h134) h129) h54) h53) h46) h44) h17) h7) h3
  have h253 := C (T (T (T (T (T (T (T (T (T (T (T (T (T h67 h66) h65) h62) h60) h130) h127) h94) h77) h38) h19) h218) h227) h250) h252
  have h254 := C h16 (T h253 h251)
  have h255 := R (M v8 v235)
  have h256 := C h175 h255
  have h257 := h v221 v8 v0
  have h258 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T h33 h87) h78) h100) h189) h188) h187) h191) h186) h184) h193) h163) h213) h257) (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h256 h254) h233) h232) h231) h211) h207) h144) h134) h129) h54) h53) h46) h44) h17) h7) h3) (T (T (T h218 h227) h250) h248))) (T (T (T (T (T (T (T (T (T (T (T (T (T h234 h226) h212) h195) h156) h143) h139) h137) h131) h59) h85) h84) h56) h55)
  have h259 := C h4 (T (T (T (T (T (T (T (T (T h225 h217) h138) h135) h164) h206) h215) h240) h239) h238)
  have h260 := C h4 (T (T (T (T (T (T h211 h207) h144) h148) h146) h216) h230)
  have h261 := C h4 (T (T (T h194 h159) h206) h215)
  have h262 := C h12 (T (T (T h253 h251) h242) h249)
  have h263 := C h161 h255
  have h264 := C h16 (T h247 h246)
  have h265 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h2 h26) h24) h83) h82) h81) h79) h128) h149) h164) h206) h215) h240) h239) h238) h264) h263) (T (T (T h262 h245) h220) h219)) (S h257)) h208) h204) h202) h200) h199) h198) h180) h177) h173) h101) h72) h69) h40) (T (T (T (T (T (T (T (T (T (T (T (T (T h67 h66) h65) h62) h60) h130) h151) h147) h142) h197) h210) h261) h260) h259)
  have h266 := h v235 y z
  have h267 := S h266
  have h268 := C h161 h254
  have h269 := C h175 h256
  have h270 := C h161 (T h264 h263)
  have h271 := h v221 z v0
  have h272 := C (T (T (T (T h218 h227) h250) h248) (C h12 (T (T (T h253 h251) h271) (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h258 h237) h233) h232) h231) h211) h207) h144) h134) h129) h54) h53) h46) h44) h17) h7) h3) (T (T (T (T (T (T (T (T (T (T (T (T h74 h73) h106) h105) h133) h151) h147) h142) h197) h210) h261) h260) h259))))) (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h270 h269) h268) h253) h251) h208) h204) h202) h200) h199) h198) h180) h177) h173) h101) h72) h69) h40)
  have h273 := R (M v0 v235)
  have h274 := C h175 h273
  have h275 := C h16 (T h272 h267)
  have h276 := C h175 h274
  have h277 := C h161 h273
  have h278 := C h175 (T h256 h254)
  have h279 := C h161 h263
  have h280 := C h175 h264
  have h281 := C (T (T (T (T (C h12 (T (T (T (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h2 h26) h24) h83) h82) h81) h79) h128) h149) h164) h206) h215) h240) h239) h238) h236) h265) (T (T (T (T (T (T (T (T (T (T (T (T h234 h226) h212) h195) h156) h143) h139) h137) h127) h94) h77) h38) h19)) (S h271)) h247) h246)) h262) h245) h220) h219) (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h33 h87) h78) h100) h189) h188) h187) h191) h186) h184) h193) h163) h213) h247) h246) h280) h279) h278)
  have h282 := C h42 (T (T (T (T (T (T (T (T (T (T h138 h135) h164) h206) h215) h240) h239) h238) h266) h281) h277)
  have h283 := C h161 (T (T h282 h276) h275)
  have h284 := C h42 (T (T (T (T (T (T (T (T (T (T h274 h272) h267) h233) h232) h231) h211) h207) h144) h148) h146)
  have h285 := C h161 h277
  have h286 := C h16 (T h266 h281)
  have h287 := C h175 (T (T h286 h285) h284)
  have h288 := h v140 v0 v8
  have h289 := S h288
  have h290 := h v0 v0 z
  have h291 := S h290
  have h292 := C h241 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h282 h276) h275) h270) h269) h268) h253) h251) h208) h204) h202) h200) h199) h198) h180) h177) h173) h101) h72) h69) h40)
  have h293 := R (M v0 (M v8 v140))
  have h294 := C h175 h293
  have h295 := C h42 (T (T (T (T (T (T (T (T (T (T (T h138 h135) h164) h206) h215) h240) h239) h238) h266) h281) h277) h287)
  have h296 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h33 h87) h78) h100) h189) h188) h187) h191) h186) h184) h193) h163) h213) h247) h246) h280) h279) h278) h286) h285) h284) h295) h294) (T (T (T (T (T (T (T (T (T (T (T (T h292 h291) h74) h73) h106) h105) h133) h131) h59) h85) h84) h56) h55)
  have h297 := C h252 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h33 h87) h78) h100) h189) h188) h187) h191) h186) h184) h193) h163) h213) h247) h246) h280) h279) h278) h286) h285) h284)
  have h298 := C h42 (T (T (T (T (T (T (T (T (T (T (T h283 h274) h272) h267) h233) h232) h231) h211) h207) h144) h148) h146)
  have h299 := C h161 h293
  have h300 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h299 h298) h282) h276) h275) h270) h269) h268) h253) h251) h208) h204) h202) h200) h199) h198) h180) h177) h173) h101) h72) h69) h40) (T (T (T (T (T (T (T (T (T (T (T (T h67 h66) h65) h62) h60) h130) h127) h94) h77) h38) h19) h290) h297)
  have h301 := S (h v20 x v20)
  let v302 := M x (M x (M v20 v20))
  T (T (T (T (T (T (T (T (T (T (T (T (T (h x v302 v8) (C (T (C (R v302) h301) h301) h42)) (C h21 h70)) (C h21 (T (T h65 h62) h60))) (C h21 h97)) (C h21 (T (T (T (T (T (T (T (T h92 h91) h90) h65) h62) h60) h130) h151) h147))) (C h21 (T h142 h197))) (C h21 (T (T (T (T (T (T (T (T (T (T h156 h143) h139) h137) h127) h94) h77) h38) h19) h218) h227))) (C h21 (T (T (T (T (T (T (T (T (T (T (T (T (T (T h220 h219) h74) h73) h106) h105) h133) h151) h147) h142) h197) h210) h261) h260) h259))) (C h21 (T (T (T (T (T (T (T (T (T (T (T (T (T (T h234 h226) h212) h195) h156) h143) h139) h137) h127) h94) h77) h38) h19) h290) h297))) (C h21 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h292 h291) h74) h73) h106) h105) h133) h151) h147) h142) h197) h210) h261) h260) h259) (C h4 (T h236 h265))) (C h4 (T (T (T (T (T h258 h237) h266) h281) h277) h287))) (C h4 (T (T (T (T (T (T (T (T (T (T (T (T (T h283 h274) h272) h267) h233) h232) h231) h211) h207) h144) h148) h146) h288) h300))) (C h4 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h296 h289) h138) h135) h164) h206) h215) h240) h239) h238) h266) h281) h277) h287) (C h161 h295)) (C h175 h294)) (C h161 (T h299 h298))))))) (C h21 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (C h4 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (C h175 (T h295 h294)) (C h161 h299)) (C h175 h298)) h283) h274) h272) h267) h233) h232) h231) h211) h207) h144) h148) h146) h288) h300)) (C h4 (T (T (T (T (T (T (T (T (T (T (T (T (T h296 h289) h138) h135) h164) h206) h215) h240) h239) h238) h266) h281) h277) h287))) (C h4 (T (T (T (T (T h283 h274) h272) h267) h236) h265))) (C h4 (T h258 h237))) h234) h226) h212) h195) h156) h143) h139) h137) h127) h94) h77))) (C h21 h38)) (C h21 h19)

