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
theorem Equation4197_implies_Equation3573 (G: Type _) [Magma G] (h: Equation4197 G) : Equation3573 G := fun x y z =>
  let v0 := M z z
  let v1 := M v0 x
  have h2 := h y v1 v0
  have h3 := S h2
  let v4 := M y v1
  let v5 := M v0 y
  let v6 := M v5 v1
  have h7 := h v6 v0 v4
  let v8 := M x y
  have h9 := h y v1 v8
  have h10 := S h9
  let v11 := M v8 y
  have h12 := h (M v11 v1) v8 v1
  have h13 := S h12
  have h14 := R v1
  have h15 := R v8
  have h16 := h v11 v1 v4
  have h17 := R v4
  have h18 := h v8 y v1
  have h19 := R y
  have h20 := h v0 x v0
  have h21 := S h20
  have h22 := R v0
  have h23 := R x
  have h24 := h z z z
  have h25 := C (S h24) h22
  have h26 := h z z v0
  have h27 := T h26 h25
  have h28 := C h27 h23
  have h29 := C h28 h22
  have h30 := C (T (T h29 h21) h28) h22
  have h31 := h x v0 v0
  have h32 := h x v0 x
  have h33 := S h32
  have h34 := S h26
  have h35 := C h24 h22
  have h36 := h v0 v0 x
  have h37 := S h36
  have h38 := S h31
  have h39 := T h35 h34
  have h40 := C h39 h23
  have h41 := C h40 h22
  have h42 := C (T (T h40 h20) h41) h22
  have h43 := C (T h29 (C (T (T (T h40 h20) h42) h38) h22)) h23
  have h44 := C (T h20 h41) h23
  have h45 := h v1 x v4
  have h46 := S h45
  have h47 := h v1 v0 v1
  have h48 := S h47
  have h49 := C (T h30 h21) h14
  have h50 := h v0 v0 v1
  have h51 := C (T (T h26 h25) (C (T (T (T h26 h25) h50) h49) h22)) h14
  have h52 := h v0 v0 y
  have h53 := h y v0 v0
  have h54 := S h53
  have h55 := C h39 h19
  have h56 := h v0 y v0
  have h57 := C (T (T h55 h56) (C h55 h22)) h22
  have h58 := S h56
  have h59 := C h27 h19
  have h60 := C (T (T (C h59 h22) h58) h59) h22
  have h61 := h y v0 v1
  have h62 := S h61
  have h63 := h x y v0
  have h64 := C h63 h14
  have h65 := h v8 v1 v4
  have h66 := h y v1 x
  have h67 := h v1 x v8
  have h68 := C (T h29 h21) h23
  have h69 := C (T (C (T (T (T h31 h30) h21) h28) h22) h41) h23
  have h70 := T (T (T (T (T (T h26 h25) h36) h69) h68) h67) (C (S h66) h15)
  have h71 := S h50
  have h72 := C (T h20 h42) h14
  have h73 := C (T (T (C (T (T (T h72 h71) h35) h34) h22) h35) h34) h14
  have h74 := C (T (T (T (T (C (T (T (T (T (T (T (C (T (T (T (T h20 h41) h47) h73) (C h70 h14)) h17) (S h65)) h64) h62) h53) h60) h58) h19) (C (T h56 (C (T (T (T h55 h56) h57) h54) h22)) h19)) (S h52)) h35) h34) h14
  have h75 := h v4 y v1
  have h76 := T (T (T (T (T h75 h74) h51) h48) h29) h21
  have h77 := C h17 h76
  have h78 := S h75
  have h79 := T (T (T (T (T (T (C h66 h15) (S h67)) h44) h43) h37) h35) h34
  have h80 := C (T (T (T (T h26 h25) h52) (C (T (C (T (T (T h53 h60) h58) h59) h22) h58) h19)) (C (T (T (T (T (T (T h56 h57) h54) h61) (C (S h63) h14)) h65) (C (T (T (T (T (C h79 h14) h51) h48) h29) h21) h17)) h19)) h14
  have h81 := T (T (T (T (T h20 h41) h47) h73) h80) h78
  have h82 := h y v1 v4
  have h83 := S h82
  let v84 := M v4 y
  have h85 := h (M v84 v1) v4 v4
  have h86 := S h85
  have h87 := h v84 v1 v1
  have h88 := S h87
  have h89 := C h14 h81
  have h90 := C (T (T (T (T h20 h41) h47) h73) (C (T (T (T (T h26 h25) h50) h49) h89) h14)) h76
  have h91 := C h17 (T (T (T (T (T (T h26 h25) h50) h49) h89) h90) h88)
  have h92 := C (C h91 h17) h17
  have h93 := h v0 v4 v4
  have h94 := h v0 v4 x
  have h95 := T (T (T (T (T (C (C (T (T h20 h42) h38) h17) h23) (S h94)) h93) h92) h86) h83
  have h96 := C h95 h81
  have h97 := h v4 x v1
  have h98 := T (T h97 h96) h77
  have h99 := C (C h98 h23) h17
  have h100 := h x x v4
  have h101 := T (T (T (T (T (T (T h100 h99) h46) h44) h43) h37) h35) h34
  have h102 := S h100
  have h103 := S h97
  have h104 := S h93
  have h105 := C h14 h76
  have h106 := C (T (T (T (T (C (T (T (T (T h105 h72) h71) h35) h34) h14) h51) h48) h29) h21) h81
  have h107 := C h17 (T (T (T (T (T (T h87 h106) h105) h72) h71) h35) h34)
  have h108 := C (C h107 h17) h17
  have h109 := T (T (T (T (T h82 h85) h108) h104) h94) (C (C (T (T h31 h30) h21) h17) h23)
  have h110 := C h109 h76
  have h111 := C h17 h81
  have h112 := T (T h111 h110) h103
  have h113 := C (C h112 h23) h17
  have h114 := T (T (T (T (T (T (T h26 h25) h36) h69) h68) h45) h113) h102
  have h115 := C (T (T (T (T (T (T (T h100 h99) h46) h44) h43) h37) (C h22 h114)) (C h114 h101)) h23
  have h116 := h v1 x y
  have h117 := T (T (T (T (T (T (C h112 h19) (S h116)) h44) h43) h37) h35) h34
  have h118 := C h117 h17
  have h119 := h v1 y v4
  have h120 := h v4 y v0
  have h121 := S h120
  have h122 := C (T (T (T (T (T (T h20 h41) h47) h73) h80) h78) (C (T (T (T h82 h85) h108) h104) h19)) h101
  have h123 := C (T (T (T (T (T (T (C (T (T (T h93 h92) h86) h83) h19) h75) h74) h51) h48) h29) h21) h114
  have h124 := C (T (T (T (T (T (T (T (C (T (T (T (T (T (T (T (T (T (C h23 h101) h31) h30) h41) h47) h73) h80) h78) h120) h123) h19) (C (T (T (T (T (T (T (T h122 h121) h75) h74) h51) h48) h29) h21) h19)) h119) h118) h93) h92) h86) h83) h23
  let v125 := M x x
  have h126 := h v125 y x
  have h127 := h x y x
  have h128 := T h127 (C (T (T (T (T h126 h124) h97) h96) h77) h23)
  have h129 := C (T (T (C h128 h17) h113) h102) h23
  have h130 := C (T (T (T (T (T h129 h115) h33) h31) h30) h21) h15
  have h131 := h v4 x v8
  have h132 := h v125 y v4
  have h133 := S h132
  have h134 := C h17 (T (T (T (T (T (T (T (T (T (T h87 h106) h105) h72) h71) h36) h69) h68) h45) h113) h102)
  have h135 := h v1 v0 y
  have h136 := C (T (T (T (C (T (T (T (T (T (T h75 h74) h51) h48) h29) h21) h28) h22) h41) h135) (C (T h91 h134) h19)) h17
  have h137 := h y v0 v4
  have h138 := C h19 h101
  have h139 := C h19 h114
  have h140 := h y v0 x
  have h141 := S h127
  have h142 := h (M v125 y) x v4
  have h143 := h v5 x v4
  have h144 := T (T (T h143 (C (C (C h17 (T (T (T (T (T h56 h57) h54) h137) h136) h133)) h23) h17)) (S h142)) h141
  have h145 := C h144 h22
  have h146 := h y x v0
  have h147 := h x x y
  have h148 := h x x v0
  have h149 := h x v0 v1
  have h150 := C h95 (T (T (T (T (T h20 h42) h38) h149) (C (T (T (T (S h148) h147) (C (T (T (C (T h146 h145) h23) (S h140)) h139) h19)) (C (T (T (T (T (T (T (T h138 h137) h136) h133) h126) h124) h131) h130) h19)) h14)) (S h18))
  have h151 := S h131
  have h152 := S h126
  have h153 := T (T (T (T (T (T h26 h25) h36) h69) h68) h116) (C h98 h19)
  have h154 := C h153 h17
  have h155 := C (T (T (T (T (T (T (T h82 h85) h108) h104) h154) (S h119)) (C (T (T (T (T (T (T (T h20 h41) h47) h73) h80) h78) h120) h123) h19)) (C (T (T (T (T (T (T (T (T (T h122 h121) h75) h74) h51) h48) h29) h42) h38) (C h23 h114)) h19)) h23
  have h156 := T (C (T (T (T (T h111 h110) h103) h155) h152) h23) h141
  have h157 := C (T (T h100 h99) (C h156 h17)) h23
  have h158 := C (T (T (T (T (T (T (T (C h101 h114) (C h22 h101)) h36) h69) h68) h45) h113) h102) h23
  have h159 := C (T (T (T (T (T h20 h42) h38) h32) h158) h157) h15
  have h160 := C (T (T (T h159 h151) h97) h150) h14
  have h161 := C (T (T (T h110 h103) h131) h130) h14
  have h162 := C (T h161 h160) h17
  have h163 := h v84 v1 v4
  have h164 := T (T (T (T (T (T (T (T (T (T (T (T (T h100 h99) h46) h44) h43) h37) h50) h49) h89) h90) h88) h163) h162) (S h16)
  have h165 := S h147
  have h166 := S h137
  have h167 := S h135
  have h168 := C (T (T (T (C (T (C h17 (T (T (T (T (T (T (T (T (T (T h100 h99) h46) h44) h43) h37) h50) h49) h89) h90) h88)) h107) h19) h167) h29) (C (T (T (T (T (T (T h40 h20) h41) h47) h73) h80) h78) h22)) h17
  have h169 := T (T (T h127 h142) (C (C (C h17 (T (T (T (T (T h132 h168) h166) h53) h60) h58)) h23) h17)) (S h143)
  have h170 := C (T (T h138 h140) (C (T (C h169 h22) (S h146)) h23)) h19
  have h171 := C (T (T (T (T (T (T (T h159 h151) h155) h152) h132) h168) h166) h139) h19
  have h172 := C h109 (T (T (T (T (T h18 (C (T (T (T h171 h170) h165) h148) h14)) (S h149)) h31) h30) h21)
  have h173 := C (T (T (T h172 h103) h131) (C (T (T (T (T (T (T (T (T (T (T (T (T h129 h115) h33) h31) h30) h41) h47) h73) h80) h78) h120) h123) (C h14 h164)) h15)) h14
  have h174 := C (T (T (T (T (T (T (T (T (T h56 h57) h54) h137) h136) h133) h126) h124) h97) h96) h14
  have h175 := T (T (T (T (T h174 h161) h160) h173) h13) h10
  have h176 := C (T (T (T (T (T (T (T (T (T h110 h103) h155) h152) h132) h168) h166) h53) h60) h58) h14
  have h177 := C (T (T (T h159 h151) h97) h96) h14
  have h178 := C (T (T (T h172 h103) h131) h130) h14
  have h179 := S h163
  have h180 := C (T h178 h177) h17
  have h181 := C (T (T (T (C (T (T (T (T (T (T (T (T (T (T (T (T (C h14 (T (T (T (T (T (T (T (T (T (T (T (T (T h16 h180) h179) h87) h106) h105) h72) h71) h36) h69) h68) h45) h113) h102)) h122) h121) h75) h74) h51) h48) h29) h42) h38) h32) h158) h157) h15) h151) h97) h150) h14
  have h182 := T (T (T (T (T h9 h12) h181) h178) h177) h176
  have h183 := C (T (T (T (T h161 h160) h173) h13) h10) h182
  have h184 := h y v1 z
  have h185 := S h184
  have h186 := h (M (M z y) v1) z v4
  have h187 := S h186
  have h188 := R z
  have h189 := h z y z
  have h190 := C (T (T (C (T (T (T (T h159 h151) h97) h96) h77) h188) (C (T (T (T (T (T (T (T (T (T (T h111 h110) h103) h155) h152) h132) h168) h166) h53) h60) h58) h188)) (S h189)) h14
  have h191 := h v8 z v1
  have h192 := C (C (C h17 (T h191 h190)) h188) h17
  have h193 := h (M v8 z) z v4
  have h194 := T (T (T h193 h192) h187) h185
  have h195 := T (T h9 h12) h181
  have h196 := C h195 h194
  have h197 := S h193
  have h198 := S h191
  have h199 := C (T (T h189 (C (T (T (T (T (T (T (T (T (T (T h56 h57) h54) h137) h136) h133) h126) h124) h97) h96) h77) h188)) (C (T (T (T (T h111 h110) h103) h131) h130) h188)) h14
  have h200 := C (C (C h17 (T h199 h198)) h188) h17
  have h201 := T (T (T h184 h186) h200) h197
  have h202 := C h17 h201
  have h203 := C (T (T (T h202 h196) h180) h183) h22
  have h204 := C h17 h194
  have h205 := T (T h173 h13) h10
  have h206 := C h205 h201
  have h207 := h z z v4
  have h208 := S h207
  let v209 := M v4 z
  let v210 := M v209 z
  have h211 := h v210 v4 v4
  have h212 := h v8 z v4
  have h213 := C h39 h188
  have h214 := h z v0 z
  have h215 := S h214
  have h216 := C h27 h188
  have h217 := h v4 z v4
  have h218 := C (C (C h17 (T (T (T (T (T h217 (C (T (T (T (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T h202 h196) h180) h179) h87) h106) h105) h72) h71) h36) h69) h68) h45) h113) h102) h188) (C h101 h188)) h216) h215) h17)) (C (T (T h214 h213) (C h70 h188)) h17)) (S h212)) h191) h190)) h188) h17
  have h219 := h v209 z v4
  have h220 := T (T (T h219 h218) h187) h185
  have h221 := S h219
  have h222 := C (C (C h17 (T (T (T (T (T h199 h198) h212) (C (T (T (C h79 h188) h216) h215) h17)) (C (T (T (T h214 h213) (C h114 h188)) (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T h100 h99) h46) h44) h43) h37) h50) h49) h89) h90) h88) h163) h162) h206) h204) h188)) h17)) (S h217))) h188) h17
  have h223 := T (T (T h184 h186) h222) h221
  have h224 := T (T (T (T (T (T (T (T (T h26 h25) h50) h49) h89) h90) h88) h163) h162) (C h205 h223)
  have h225 := C h224 h220
  have h226 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (C h225 h17) (S h211)) h208) h26) h25) h50) h49) h89) h90) h88) h163) h162) h206) h204) h22
  have h227 := h v210 v4 v0
  have h228 := h v6 v0 v8
  have h229 := S h228
  have h230 := C h153 h194
  have h231 := T (T (T (T (T (T (T (T (T (C h195 h220) h180) h179) h87) h106) h105) h72) h71) h35) h34
  have h232 := C h231 h201
  have h233 := C h128 h194
  have h234 := C h15 (T (T (T h219 h218) h200) h197)
  have h235 := C (T (T (T (T (T (T (T h234 h233) h46) h44) h43) h37) h35) h34) h223
  have h236 := C h15 (T (T (T h193 h192) h222) h221)
  have h237 := C h156 h201
  have h238 := S h227
  have h239 := C h231 h223
  have h240 := C (T (T (T (T (T (T (T (T (T (T (T (T (T h202 h196) h180) h179) h87) h106) h105) h72) h71) h35) h34) h207) h211) (C h239 h17)) h22
  have h241 := C (T (T (T (T (T (T (T (T (T (T h240 h238) h208) h26) h25) h36) h69) h68) h45) h237) h236) h17
  have h242 := h v4 v0 v4
  have h243 := S h242
  have h244 := C (T (T (T (T (T (T (T (T (T (T h234 h233) h46) h44) h43) h37) h35) h34) h207) h227) h226) h17
  have h245 := C (T (T (T (T (T (T (T h26 h25) h36) h69) h68) h45) h237) h236) h220
  have h246 := C h224 h194
  have h247 := C h117 h201
  have h248 := C (T (T (T (T h9 h12) h181) h178) h177) h175
  have h249 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T h196 h180) h179) h87) h106) h105) h72) h71) h35) h34) h207) h227) h226) h203) (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T h248 h179) h87) h106) h105) h72) h71) h36) h69) h68) h45) h237) h236) (C h15 (T (T (T (T (T (T (T (T (T (T (T (T (T (T h219 h218) h187) h185) h82) h85) h108) h104) h154) h247) h246) h239) h245) h244) h243))) (C h15 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h242 h241) h235) h225) h232) h230) h118) h93) h92) h86) h83) h9) h12) h181) h178) h177) h176))) h22)) h15
  have h250 := C (T (T (T (T (T (T (T (T (T (T (T (T h233 h46) h44) h43) h37) h50) h49) h89) h90) h88) h163) h162) h206) h15
  have h251 := C (T (T (T (T (T (T h26 h25) h36) h69) h68) h45) h237) h15
  have h252 := C (T (T (T (T (T (T h233 h46) h44) h43) h37) h35) h34) h15
  have h253 := C (T (T (T (T (T (T (T (T (T (T (T (T h196 h180) h179) h87) h106) h105) h72) h71) h36) h69) h68) h45) h237) h15
  have h254 := C (T (T (T h248 h162) h206) h204) h22
  have h255 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (C h15 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h174 h161) h160) h173) h13) h10) h82) h85) h108) h104) h154) h247) h246) h239) h245) h244) h243)) (C h15 (T (T (T (T (T (T (T (T (T (T (T (T (T (T h242 h241) h235) h225) h232) h230) h118) h93) h92) h86) h83) h184) h186) h222) h221))) h234) h233) h46) h44) h43) h37) h50) h49) h89) h90) h88) h163) h183) h22) h254) h240) h238) h208) h26) h25) h50) h49) h89) h90) h88) h163) h162) h206) h15
  have h256 := S (h v6 v0 v0)
  have h257 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h251 h250) h249) h229) h3) h82) h85) h108) h104) h154) h247) h246) h239) h245) h244) h243) h91) h134) (C h17 h164)) (C (T (T (T (T (T (T (T (T (T (T h82 h85) h108) h104) h154) h247) h246) h239) h245) h244) h243) (T (T (T (T (T (T (T (T (T h16 h180) h179) h87) h106) h105) h72) h71) h35) h34))) (C (T (T (T (T (T (T (T (T (T (T (T (T (T h242 h241) h235) h225) h232) h230) h118) h93) h92) h86) h83) h2) h7) (C (T (T (T h254 h240) h238) h208) h182)) h22)) h22
  T (T (T (T (T (h x y y) (h (M (M y x) y) y v4)) (C (T (T (T (T (T (T (T (T (T (T (T (C (T (T (T (T (T (T (T (T (T (T (T (C (T (T (T (T h2 h228) h255) h253) h252) (T (T (T (T (T (C (T h146 (C h144 h114)) h19) (C (T (T (T (T (T (T (T (T (T (C h169 h101) h145) (h v8 v0 v0)) (C (T (T (T (T (T h257 h256) h228) h255) h253) h252) h22)) h257) h256) h228) h255) h253) h252) h19)) (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h251 h250) h249) h229) h3) h82) h85) h108) h104) h154) h247) h246) h239) h245) h244) h243) h19)) h167) h29) h21)) (C (T (T (T (T (T (T (T (T h251 h250) h249) h229) h3) h9) h12) h181) h178) h14)) (S (h v8 v1 v1))) h64) h62) h137) h136) h133) h126) h124) h131) h130) h19) h171) h170) h165) h100) h99) h46) h44) h43) h37) h35) h34) h182)) (C (T (T (T h207 h227) h226) h203) h175)) (S h7)) h3

