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
theorem Equation895_implies_Equation4424 (G: Type _) [Magma G] (h: Equation895 G) : Equation4424 G := fun x y z =>
  let v0 := M z x
  have h1 := h y y (M v0 (M y x))
  have h2 := S h1
  have h3 := h z y x
  have h4 := R y
  have h5 := C h4 (C h3 h3)
  let v6 := M z z
  have h7 := R v6
  have h8 := T h5 h2
  have h9 := C h8 h7
  let v10 := M v6 x
  have h11 := h v6 v6 (M v0 v10)
  have h12 := S h11
  have h13 := h z v6 x
  have h14 := C h7 (C h13 h13)
  have h15 := T h14 h12
  have h16 := C h9 h15
  have h17 := C h7 (T (T (T h16 h9) h5) h2)
  have h18 := S h13
  have h19 := C h7 (C h18 h18)
  have h20 := T h11 h19
  have h21 := S h3
  have h22 := C h4 (C h21 h21)
  have h23 := T h1 h22
  have h24 := C h23 h7
  have h25 := C h24 h20
  have h26 := h (M y v6) v6 v6
  have h27 := S h26
  have h28 := C h7 (T (T (T h1 h22) h24) h25)
  have h29 := C h7 (T (T (T h28 h27) h24) h25)
  let v30 := M v6 y
  let v31 := M v6 v30
  have h32 := h v31 y v6
  have h33 := S h32
  let v34 := M v30 x
  have h35 := h v30 v30 (M v0 v34)
  have h36 := S h35
  have h37 := h z v30 x
  have h38 := R v30
  have h39 := C h38 (C h37 h37)
  have h40 := T (T (T h39 h36) h28) h27
  have h41 := R (M v31 v6)
  have h42 := C h41 h40
  have h43 := S h37
  have h44 := C h38 (C h43 h43)
  have h45 := T h35 h44
  have h46 := C h7 (T (T (T h16 h9) h26) h17)
  have h47 := T h28 h46
  have h48 := C h47 h7
  have h49 := T (T (T (T h29 h17) h35) h44) h48
  have h50 := C h49 h45
  have h51 := C h47 h38
  have h52 := C (T (T (T h29 h27) h5) h2) (T (T h51 h50) h42)
  let v53 := M v30 v30
  let v54 := M v31 v53
  have h55 := h v54 v6 v6
  have h56 := S h55
  have h57 := T h29 h17
  have h58 := C h57 h38
  have h59 := T h39 h36
  have h60 := C h57 h7
  have h61 := T (T (T (T h60 h39) h36) h28) h46
  have h62 := C h61 h59
  have h63 := T (T (T h26 h17) h35) h44
  have h64 := C h41 h63
  have h65 := C (T (T (T h1 h22) h26) h46) (T (T h64 h62) h58)
  have h66 := C (T (T (T (T (T (T h60 h39) h36) h28) h46) h32) h65) h15
  have h67 := C h49 h20
  have h68 := T (T (T (T (T (T (T (T h52 h33) h29) h17) h35) h44) h48) h67) h66
  have h69 := h v6 v30 v30
  have h70 := S h69
  have h71 := T (T (T h52 h33) h29) h17
  have h72 := C h71 (T (T (T (T (T h1 h22) h26) h46) h32) h65)
  have h73 := C (T h72 h70) (T (T (T (T (T h35 h44) h48) h67) h66) (C h68 h20))
  have h74 := C h61 h15
  have h75 := C (T (T (T (T (T (T h52 h33) h29) h17) h35) h44) h48) h20
  have h76 := T (T (T (T (T (T (T (T h75 h74) h60) h39) h36) h28) h46) h32) h65
  have h77 := C h76 h8
  have h78 := R (M v54 v6)
  have h79 := C h78 h40
  have h80 := C h68 h45
  have h81 := C (T (T h80 h79) h77) h57
  have h82 := C h76 h59
  have h83 := C h78 h63
  have h84 := C h68 h23
  have h85 := T (T (T h28 h46) h32) h65
  have h86 := C h85 (T (T (T (T (T h52 h33) h29) h27) h5) h2)
  have h87 := R v31
  have h88 := C (T h32 h65) (T (T (T h1 h22) h26) h17)
  have h89 := C h61 h8
  have h90 := C (T (T (T (T h51 h50) h42) h89) h88) h87
  have h91 := C (T (T (T (T (T (T (T h90 h81) h73) h56) h52) h33) h29) h17) h85
  let v92 := M x y
  have h93 := h (M v53 v31) v92 v30
  have h94 := S h93
  let v95 := M v92 v30
  have h96 := R v95
  have h97 := C h49 h23
  have h98 := C (T h52 h33) (T (T (T h28 h27) h5) h2)
  have h99 := C (T (T (T (T h98 h97) h64) h62) h58) h87
  have h100 := C (T (T h84 h83) h82) h47
  have h101 := C (T h69 h86) (T (T (T (T (T (C h76 h15) h75) h74) h60) h39) h36)
  have h102 := C (T (T (T (T (T (T (T h28 h46) h32) h65) h55) h101) h100) h99) h71
  have h103 := T h69 h102
  have h104 := C h103 h96
  have h105 := h x v6 y
  have h106 := R v92
  have h107 := C h106 (T h105 h104)
  have h108 := C (T h107 h94) h38
  let v109 := M v92 x
  have h110 := h v109 v30 v30
  have h111 := S h110
  have h112 := R v53
  have h113 := S h105
  have h114 := T h91 h70
  have h115 := C h114 h96
  have h116 := C h106 (T h115 h113)
  have h117 := C (T h93 h116) h38
  have h118 := C (T (T (T h97 h64) h62) h58) h47
  have h119 := C (T (T h50 h42) h89) h57
  have h120 := h v53 v6 v30
  have h121 := T (T (T (T (T (T (T (T (T h107 h94) h90) h81) h73) h56) h52) h33) h29) h17
  have h122 := C h121 (T (T (T (T (T (T (T (T (T (T (T (T h69 h86) h84) h83) h82) h98) h97) h64) h62) h58) h120) (C h103 (T (T (T (T (T (T (T (T (T (T (C (T (T (C h51 h47) h119) h118) h57) h91) h86) h84) h83) h82) h98) h97) h64) h62) h58))) (C h117 h112))
  have h123 := T h122 h111
  have h124 := C h123 h59
  have h125 := R (M v109 v6)
  have h126 := C h125 h63
  have h127 := C (T (T h97 h64) h62) h47
  have h128 := C (T (T (T h51 h50) h42) h89) h57
  have h129 := T (T (T (T (T (T (T (T (T h28 h46) h32) h65) h55) h101) h100) h99) h93) h116
  have h130 := C h129 (T (T (T (T (T (T (T (T (T (T (T (T (C h108 h112) (C h114 (T (T (T (T (T (T (T (T (T (T h51 h50) h42) h89) h88) h80) h79) h77) h72) h102) (C (T (T h128 h127) (C h58 h57)) h47)))) (S h120)) h51) h50) h42) h89) h88) h80) h79) h77) h72) h70)
  have h131 := T h110 h130
  have h132 := C h131 h23
  have h133 := T (T (T (T (T (T (T (T (T (T (T h107 h94) h90) h81) h73) h56) h52) h33) h29) h27) h5) h2
  have h134 := R v109
  have h135 := C h134 h133
  let v136 := M v109 v109
  have h137 := h v136 v6 y
  have h138 := S h137
  have h139 := h v109 v6 y
  have h140 := S h139
  have h141 := h v109 v30 v6
  have h142 := C h131 h45
  have h143 := C h123 h8
  have h144 := C h125 h40
  have h145 := h v109 v6 v6
  have h146 := T (T (T (T (T (T h135 h132) h126) h124) h108) h91) h70
  have h147 := C h146 (T (T (T (T (T (T (T (T (T (T (T h28 h46) h32) h65) h55) h101) h100) h99) h93) h116) h145) (C (T (T (T (T (T h69 h102) h117) h142) h144) h143) (T (T (T (T (T (T (T (T (T (T (T (C (T (T (T (T (T (T (T (T (T (T (T h122 h111) h107) h94) h90) h81) h73) h56) h52) h33) h29) h17) (T (T (T (T (T h14 h12) h69) h102) h117) h142)) (S h141)) h107) h94) h90) h81) h73) h56) h52) h33) h29) h17)))
  have h148 := h v136 v6 v30
  have h149 := S h148
  have h150 := h v109 y v6
  have h151 := S h150
  have h152 := C (T (T (T (T (T (T (T (T (T (T (T (T (T h147 h140) h107) h94) h90) h81) h73) h56) h52) h33) h29) h27) h5) h2) (T (T (T (T (T (T (T (T (T (T (T (T h51 h50) h42) h89) h88) h80) h79) h77) h72) h102) h117) h142) h144)
  have h153 := T (T (T (T (T (T (T (T (T (T (T h1 h22) h26) h46) h32) h65) h55) h101) h100) h99) h93) h116
  have h154 := C h134 h153
  have h155 := T (T (T (T (T (T h69 h102) h117) h142) h144) h143) h154
  have h156 := C h155 (T (T (T (T (T (T (T (T (T (T (T (C (T (T (T (T (T h132 h126) h124) h108) h91) h70) (T (T (T (T (T (T (T (T (T (T (T h28 h46) h32) h65) h55) h101) h100) h99) h93) h116) h141) (C (T (T (T (T (T (T (T (T (T (T (T h28 h46) h32) h65) h55) h101) h100) h99) h93) h116) h110) h130) (T (T (T (T (T h124 h108) h91) h70) h11) h19)))) (S h145)) h107) h94) h90) h81) h73) h56) h52) h33) h29) h17)
  have h157 := h v136 v30 v30
  have h158 := C h146 (T (T (T (T (T (T (T (T h69 h102) h117) h142) h144) h143) h154) h157) (C (T (T (T (T (T (T (T (T (T (T (T h28 h46) h32) h65) h55) h101) h100) h99) h93) h116) h139) h156) (T (T (T (T (T (T (T (T (T h152 h151) h107) h94) h90) h81) h73) h56) h52) h33)))
  have h159 := T h158 h149
  have h160 := C h159 h59
  have h161 := R (M v136 v6)
  have h162 := C h161 h63
  have h163 := C h161 h40
  have h164 := C (T (T (T (T (T (T (T (T (T (T (T (T (T h1 h22) h26) h46) h32) h65) h55) h101) h100) h99) h93) h116) h139) h156) (T (T (T (T (T (T (T (T (T (T (T (T h126 h124) h108) h91) h86) h84) h83) h82) h98) h97) h64) h62) h58)
  have h165 := C h155 (T (T (T (T (T (T (T (T (C (T (T (T (T (T (T (T (T (T (T (T h147 h140) h107) h94) h90) h81) h73) h56) h52) h33) h29) h17) (T (T (T (T (T (T (T (T (T h32 h65) h55) h101) h100) h99) h93) h116) h150) h164)) (S h157)) h135) h132) h126) h124) h108) h91) h70)
  have h166 := T h148 h165
  have h167 := C h166 h45
  have h168 := h v136 y v6
  have h169 := C (T (T (T (T h80 h79) h77) h72) h70) (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h51 h50) h42) h89) h88) h80) h79) h77) h72) h102) h117) h142) h144) h143) h154) h168) (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h1 h22) h26) h46) h32) h65) h55) h101) h100) h99) h93) h116) h139) h156) h167) h163) (C h159 h8)) (T (T (T (T (T (T (T (T (T (T (T (T (T h162 h160) h147) h140) h107) h94) h90) h81) h73) h56) h52) h33) h29) h17)))
  have h170 := T (T (T h50 h42) h89) h88
  have h171 := C h170 h112
  have h172 := C h51 h112
  let v173 := M v53 v53
  have h174 := h v173 x v30
  have h175 := S h174
  have h176 := C h108 h96
  have h177 := C (T (T (T (T (T h80 h79) h77) h72) h102) h117) h96
  have h178 := C h170 h96
  have h179 := C h51 h96
  have h180 := T (T (T (T (T h179 h178) h177) h176) h115) h113
  have h181 := C h58 h96
  have h182 := T (T (T h98 h97) h64) h62
  have h183 := C h182 h96
  have h184 := C (T (T (T (T (T h108 h91) h86) h84) h83) h82) h96
  have h185 := C h117 h96
  let v186 := M x x
  have h187 := h x x (M v0 v186)
  have h188 := S h187
  have h189 := h z x x
  have h190 := R x
  have h191 := C h190 (C h189 h189)
  have h192 := C h180 h7
  have h193 := T (C (T (T (T (T (T (T (T (T h192 h191) h188) h105) h104) h185) h184) h183) h181) h59) (C h180 h38)
  have h194 := C h58 h112
  have h195 := C h182 h112
  have h196 := C (T (T (T (T h69 h86) h84) h83) h82) (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (C h166 h23) h162) h160) h147) h140) h107) h94) h90) h81) h73) h56) h52) h33) h29) h27) h5) h2) (T (T (T (T (T (T (T (T (T (T (T (T (T h28 h46) h32) h65) h55) h101) h100) h99) h93) h116) h139) h156) h167) h163)) (S h168)) h135) h132) h126) h124) h108) h91) h86) h84) h83) h82) h98) h97) h64) h62) h58)
  have h197 := T (T (T (T (T (T (T (T (T (T h69 h102) h117) h142) h144) h143) h154) h137) h196) h195) h194
  have h198 := h v31 v6 v30
  have h199 := T (T (T h28 h46) h198) (C h197 (T (T (T (T (T (T (T (T (T h119 h118) h90) h81) h73) h56) h52) h33) h29) h17))
  have h200 := h (M v53 v95) v30 v6
  have h201 := C h190 (T (T (T (T (T (T (T h105 h104) h185) h184) h183) h181) h200) (C h199 h193))
  have h202 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h201 h175) h172) h171) h169) h138) h135) h132) h126) h124) h108) h91) h86) h84) h83) h82) h47
  have h203 := R v186
  have h204 := C h203 h121
  let v205 := M v186 v109
  have h206 := h v205 x v6
  have h207 := S h206
  have h208 := S h189
  have h209 := C h190 (C h208 h208)
  have h210 := T h187 h209
  have h211 := T (T (T (T (T (T (T (T (T h51 h50) h42) h89) h88) h80) h79) h77) h72) h70
  have h212 := C h203 h129
  have h213 := C h212 h211
  have h214 := S h200
  have h215 := T (T (T (T (T h105 h104) h185) h184) h183) h181
  have h216 := C h215 h7
  have h217 := T (C h215 h38) (C (T (T (T (T (T (T (T (T h179 h178) h177) h176) h115) h113) h187) h209) h216) h45)
  have h218 := T (T (T (T (T (T (T (T (T (T h172 h171) h169) h138) h135) h132) h126) h124) h108) h91) h70
  have h219 := T (T (T (C h218 (T (T (T (T (T (T (T (T (T h28 h46) h32) h65) h55) h101) h100) h99) h128) h127)) (S h198)) h29) h17
  have h220 := C h190 (T (T (T (T (T (T (T (C h219 h217) h214) h179) h178) h177) h176) h115) h113)
  have h221 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h80 h79) h77) h72) h102) h117) h142) h144) h143) h154) h137) h196) h195) h194) h174) h220) h57
  have h222 := T (T (T (T (T (T (T h28 h46) h32) h65) h55) h101) h100) h221
  have h223 := C h222 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h172 h171) h169) h138) h135) h132) h126) h124) h108) h91) h86) h84) h83) h82) h98) h97) h64) h62) h58)
  have h224 := h v30 v30 v30
  have h225 := T h191 h188
  have h226 := T (T (T (T (T (T (T (T (T h69 h86) h84) h83) h82) h98) h97) h64) h62) h58
  have h227 := C (T (T (T h93 h116) h139) h156) h226
  have h228 := C (T (T (T h147 h140) h107) h94) h211
  have h229 := h v186 v30 v30
  have h230 := S h229
  have h231 := S h224
  have h232 := T (T (T (T (T (T (T h202 h81) h73) h56) h52) h33) h29) h17
  have h233 := C h232 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h51 h50) h42) h89) h88) h80) h79) h77) h72) h102) h117) h142) h144) h143) h154) h137) h196) h195) h194)
  have h234 := C h204 h226
  have h235 := C (T (T h234 h233) h231) (T (T (T h39 h36) h224) h223)
  have h236 := R (M v205 v6)
  have h237 := C h236 h63
  have h238 := C (T (T (T (T (T (T (T (T (T (T h202 h81) h73) h56) h52) h33) h29) h17) h224) h223) h213) (T h29 h27)
  have h239 := C h204 h47
  have h240 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h239 h238) h237) h235) h230) h201) h175) h172) h171) h169) h138) h135) h132) h126) h124) h108) h91) h86) h84) h83) h82) h96
  have h241 := C h106 (T (T (T (T (T (T (T (T h204 h202) h81) h73) h56) h52) h33) h29) h17)
  have h242 := h x v92 x
  have h243 := C h212 h57
  have h244 := C (T (T (T (T (T (T (T (T (T (T h234 h233) h231) h28) h46) h32) h65) h55) h101) h100) h221) (T h26 h46)
  have h245 := C h236 h40
  have h246 := C (T (T h224 h223) h213) (T (T (T h233 h231) h35) h44)
  have h247 := C (T (T (T (T (T (T h174 h220) h229) h246) h245) h244) h243) (T h242 h241)
  have h248 := T (T (T (T (T h247 h240) h177) h176) h115) h113
  have h249 := C h248 (T (T (T (T (T (T (T (T (C (T (T h35 h44) h48) h210) (C h61 h225)) (C (T (T (T (T (T (T h29 h17) h35) h44) h48) h67) h66) h210)) (C h76 h225)) (C (T (T (T (T (T (T (T h55 h101) h100) h99) h93) h116) h110) h130) h210)) (C h123 h225)) (C (T (T h150 h164) h228) h210)) (C (T (T (T (T h227 h152) h151) h107) h94) h225)) (C (T (T (T (T (T (T (T (T (T (T h90 h81) h73) h56) h52) h33) h29) h17) h224) h223) h213) h210))
  have h250 := R v34
  have h251 := h v173 v6 v30
  have h252 := S h251
  have h253 := h v31 v30 v30
  have h254 := h v173 v30 v30
  have h255 := C h218 (T (T (T (T (T (T (T (T (T (T (T (T h69 h102) h117) h142) h144) h143) h154) h137) h196) h195) h194) h254) (C h199 (T (C h219 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h51 h50) h42) h89) h88) h80) h79) h77) h72) h102) h117) h142) h144) h143) h154) h137) h196) h195)) (S h253))))
  have h256 := C (T h255 h252) h225
  have h257 := C h197 (T (T (T (T (T (T (T (T (T (T (T (T (C h219 (T h253 (C h199 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h171 h169) h138) h135) h132) h126) h124) h108) h91) h86) h84) h83) h82) h98) h97) h64) h62) h58)))) (S h254)) h172) h171) h169) h138) h135) h132) h126) h124) h108) h91) h70)
  have h258 := C (T (T (T (T (T h137 h196) h195) h194) h251) h257) h210
  have h259 := T h258 h256
  have h260 := C h259 h250
  have h261 := C h159 h225
  have h262 := C (T (T (T (T (T (T (T (T h69 h102) h117) h142) h144) h143) h154) h148) h165) h210
  have h263 := T h262 h261
  have h264 := C h263 h250
  let v265 := M v10 v34
  have h266 := C (T (T (T (T (T (T (T (T h158 h149) h135) h132) h126) h124) h108) h91) h70) h225
  have h267 := C h166 h210
  have h268 := T h267 h266
  have h269 := C h268 h250
  have h270 := C (T (T (T (T (T h255 h252) h172) h171) h169) h138) h225
  have h271 := C (T h251 h257) h210
  have h272 := T h271 h270
  have h273 := C h272 h250
  have h274 := S h242
  have h275 := C h106 (T (T (T (T (T (T (T (T h28 h46) h32) h65) h55) h101) h100) h221) h212)
  have h276 := C (T (T (T (T (T (T h239 h238) h237) h235) h230) h201) h175) (T h275 h274)
  have h277 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h80 h79) h77) h72) h102) h117) h142) h144) h143) h154) h137) h196) h195) h194) h174) h220) h229) h246) h245) h244) h243) h96
  have h278 := T (T (T (T (T h105 h104) h185) h184) h277) h276
  have h279 := C h278 (T (T (T (T (T (T (T (T (C (T (T (T (T (T (T (T (T (T (T h234 h233) h231) h28) h46) h32) h65) h55) h101) h100) h99) h225) (C (T (T (T (T h93 h116) h150) h164) h228) h210)) (C (T (T h227 h152) h151) h225)) (C h131 h210)) (C (T (T (T (T (T (T (T h122 h111) h107) h94) h90) h81) h73) h56) h225)) (C h68 h210)) (C (T (T (T (T (T (T h75 h74) h60) h39) h36) h28) h46) h225)) (C h49 h210)) (C (T (T h60 h39) h36) h225))
  have h280 := T (T (T (T (T (T (T (T (T (T (T (T h28 h46) h32) h65) h55) h101) h100) h221) h212) h206) h279) h273) h269
  have h281 := C h280 (T (T (T (T (T (T (T (T (T (T (T h260 h249) h207) h204) h202) h81) h73) h56) h52) h33) h29) h17)
  have h282 := h v136 v30 x
  have h283 := T (T (T (T (T (T (T (T (T (T (T (T h239 h238) h237) h235) h230) h201) h175) h172) h171) h169) h138) h282) h281
  have h284 := C h283 h96
  have h285 := T (T (T (T (T (T (T (T (T (T (T (T h201 h175) h172) h171) h169) h138) h135) h132) h126) h124) h108) h91) h70
  have h286 := S h282
  have h287 := T (T (T (T (T (T (T (T (T (T (T (T h264 h260) h249) h207) h204) h202) h81) h73) h56) h52) h33) h29) h17
  have h288 := C h287 (T (T (T (T (T (T (T (T (T (T (T h28 h46) h32) h65) h55) h101) h100) h221) h212) h206) h279) h273)
  have h289 := T (T (T (T (T (T (T (T (T (T (T (T h288 h286) h137) h196) h195) h194) h174) h220) h229) h246) h245) h244) h243
  have h290 := C h289 h96
  have h291 := h v186 x v30
  have h292 := S h291
  have h293 := C h248 (T (T (T (T (T (T (T (T (T h262 h261) h258) h256) h247) h240) h183) h181) h200) (C h222 h193))
  have h294 := R v10
  have h295 := C h259 h294
  have h296 := C h263 h294
  let v297 := M v10 v10
  have h298 := h v297 v6 v30
  have h299 := S h298
  have h300 := h v265 y v6
  have h301 := S h300
  have h302 := R (M v265 v6)
  have h303 := C h302 h40
  have h304 := h v186 v6 v30
  have h305 := C h280 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (C h289 h112) (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h239 h238) h237) h235) h230) h201) h175) h172) h171) h169) h138) h135) h132) h126) h124) h108) h91) h70) (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h51 h50) h42) h89) h88) h80) h79) h77) h72) h102) h117) h142) h144) h143) h154) h137) h196) h195) h194) h174) h220) h229) h246) h245) h244))) (S h304)) h201) h175) h172) h171) h169) h138) h135) h132) h126) h124) h108) h91) h70)
  have h306 := h v265 v30 v30
  have h307 := T h306 h305
  have h308 := C h307 h45
  have h309 := h v265 v6 y
  have h310 := S h309
  have h311 := h v265 v30 v6
  have h312 := S h306
  have h313 := C h287 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h69 h102) h117) h142) h144) h143) h154) h137) h196) h195) h194) h174) h220) h304) (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h69 h102) h117) h142) h144) h143) h154) h137) h196) h195) h194) h174) h220) h229) h246) h245) h244) h243) (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h238 h237) h235) h230) h201) h175) h172) h171) h169) h138) h135) h132) h126) h124) h108) h91) h86) h84) h83) h82) h98) h97) h64) h62) h58))) (C h283 h112))
  have h314 := T h313 h312
  have h315 := h v265 v6 v6
  have h316 := T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h296 h295) h293) h292) h201) h175) h172) h171) h169) h138) h135) h132) h126) h124) h108) h91) h70
  have h317 := C h316 (T (T (T (T (T (T (T (T (T (T (T (T (T (T h28 h46) h32) h65) h55) h101) h100) h221) h212) h206) h279) h273) h269) h315) (C (T (T (T (T (T (T (T (T (T (T (T h69 h102) h117) h142) h144) h143) h154) h282) h281) h308) h303) (C h314 h8)) (T (T (T (T (T (T (T (T (T (T (T (T (T (T (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T h313 h312) h264) h260) h249) h207) h204) h202) h81) h73) h56) h52) h33) h29) h17) (T (T (T (T (T (T (T (T (T (T (T h14 h12) h69) h102) h117) h142) h144) h143) h154) h282) h281) h308)) (S h311)) h264) h260) h249) h207) h204) h202) h81) h73) h56) h52) h33) h29) h17)))
  have h318 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h317 h310) h264) h260) h249) h207) h204) h202) h81) h73) h56) h52) h33) h29) h27) h5) h2) (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h51 h50) h42) h89) h88) h80) h79) h77) h72) h102) h117) h142) h144) h143) h154) h282) h281) h308) h303)
  have h319 := C h314 h59
  have h320 := C h302 h63
  have h321 := C h268 h294
  have h322 := C h272 h294
  have h323 := C h278 (T (T (T (T (T (T (T (T (T (C h232 h217) h214) h179) h178) h277) h276) h271) h270) h267) h266)
  have h324 := T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h69 h102) h117) h142) h144) h143) h154) h137) h196) h195) h194) h174) h220) h291) h323) h322) h321
  have h325 := C h324 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (C (T (T (T (T (T (T (T (T (T (T (T (C h307 h23) h320) h319) h288) h286) h135) h132) h126) h124) h108) h91) h70) (T (T (T (T (T (T (T (T (T (T (T (T (T (T h28 h46) h32) h65) h55) h101) h100) h221) h212) h206) h279) h273) h269) h311) (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T h28 h46) h32) h65) h55) h101) h100) h221) h212) h206) h279) h273) h269) h306) h305) (T (T (T (T (T (T (T (T (T (T (T h319 h288) h286) h135) h132) h126) h124) h108) h91) h70) h11) h19)))) (S h315)) h264) h260) h249) h207) h204) h202) h81) h73) h56) h52) h33) h29) h17)
  have h326 := h v297 v30 v30
  have h327 := C h316 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h69 h102) h117) h142) h144) h143) h154) h137) h196) h195) h194) h174) h220) h291) h323) h322) h321) h326) (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T h28 h46) h32) h65) h55) h101) h100) h221) h212) h206) h279) h273) h269) h309) h325) (T (T (T (T (T (T (T (T (T (T (T (T h318 h301) h264) h260) h249) h207) h204) h202) h81) h73) h56) h52) h33)))
  have h328 := C (T (T (T (T (T (T (T (T (T (T (T (T (T h327 h299) h296) h295) h293) h292) h201) h175) h172) h171) h169) h138) h282) h281) (T (T (T h191 h188) h242) h241)
  have h329 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h1 h22) h26) h46) h32) h65) h55) h101) h100) h221) h212) h206) h279) h273) h269) h309) h325) (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h320 h319) h288) h286) h135) h132) h126) h124) h108) h91) h86) h84) h83) h82) h98) h97) h64) h62) h58)
  have h330 := C h324 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T h317 h310) h264) h260) h249) h207) h204) h202) h81) h73) h56) h52) h33) h29) h17) (T (T (T (T (T (T (T (T (T (T (T (T h32 h65) h55) h101) h100) h221) h212) h206) h279) h273) h269) h300) h329)) (S h326)) h296) h295) h293) h292) h201) h175) h172) h171) h169) h138) h135) h132) h126) h124) h108) h91) h70)
  have h331 := T h298 h330
  have h332 := C h331 h210
  have h333 := C (T (T (T (T (T h332 h328) h290) h240) h183) h181) h285
  have h334 := T h327 h299
  have h335 := C h334 h225
  have h336 := C (T (T (T (T (T (T (T (T (T (T (T (T (T h288 h286) h137) h196) h195) h194) h174) h220) h291) h323) h322) h321) h298) h330) (T (T (T h275 h274) h187) h209)
  have h337 := T (T (T h247 h284) h336) h335
  have h338 := C h337 h203
  have h339 := C h259 h203
  have h340 := C h263 h203
  have h341 := h (M v10 v186) v92 v6
  have h342 := S h341
  have h343 := h z v92 x
  have h344 := S h343
  have h345 := h v92 v92 (M v0 v109)
  have h346 := T h345 (C h106 (C h344 h344))
  have h347 := C h268 h203
  have h348 := C h272 h203
  have h349 := T (T (T (T (T (T (T (T (T (T (T (T h69 h102) h117) h142) h144) h143) h154) h137) h196) h195) h194) h174) h220
  have h350 := C (T (T (T h262 h261) h258) h256) h349
  have h351 := C (T (T h350 h348) h347) h15
  have h352 := C (T (T (T h271 h270) h267) h266) h285
  have h353 := T (T (T h332 h328) h290) h276
  have h354 := C h353 h203
  have h355 := C (T (T (T (T (T h179 h178) h277) h284) h336) h335) h349
  have h356 := C (T (T (T (T (T (T (T (T (T (T (T h247 h240) h177) h176) h115) h113) h187) h209) h216) h355) h354) h352) (T (T (T (T (T (T (T (T (T (T (T (T (T (T h201 h175) h172) h171) h169) h138) h135) h132) h126) h124) h108) h91) h70) h11) h19)
  have h357 := C (T (T (T (T (T (T h187 h209) h216) h355) h354) h356) h351) h346
  have h358 := C h106 h357
  let v359 := M x v92
  let v360 := M v92 v359
  have h361 := h v360 x v92
  have h362 := S h361
  have h363 := R v359
  have h364 := T (C h106 (C h343 h343)) (S h345)
  have h365 := C (T (T (T (T (T (T (T (T (T (T (T h350 h338) h333) h192) h191) h188) h105) h104) h185) h184) h277) h276) (T (T (T (T (T (T (T (T (T (T (T (T (T (T h14 h12) h69) h102) h117) h142) h144) h143) h154) h137) h196) h195) h194) h174) h220)
  have h366 := C (T (T h340 h339) h352) h20
  have h367 := C (T (T (T (T (T (T h366 h365) h338) h333) h192) h191) h188) h364
  have h368 := C h106 h367
  have h369 := R (M v6 v6)
  have h370 := C (T (T h366 h365) h352) h369
  have h371 := C (T (T (T (T (T h358 h342) h340) h339) h356) h351) h20
  have h372 := T (T (T (T (T (T h371 h370) h365) h348) h347) h341) h368
  have h373 := C h372 h364
  have h374 := R (M v92 v6)
  have h375 := C (T (T (T (T (T h366 h365) h348) h347) h341) h368) h15
  have h376 := C (T (T h350 h356) h351) h369
  have h377 := C (T (T h366 h376) h375) h374
  have h378 := C (T (T h357 h377) h373) h363
  have h379 := T (T (T (T (T (T (T (T h358 h342) h340) h339) h338) h333) h192) h191) h188
  have h380 := C h379 h378
  let v381 := M v359 v359
  let v382 := M v360 v381
  have h383 := h v360 x x
  have h384 := S h383
  have h385 := C h372 h225
  have h386 := C (T (T (T (T (T (T (T h187 h209) h216) h355) h354) h356) h376) h375) (T h333 h192)
  have h387 := h v297 x x
  have h388 := h v6 v6 x
  have h389 := T (T (T (T (T (T (T (T (T (T h380 h362) h358) h342) h340) h339) h338) h333) h192) h191) h188
  have h390 := C h389 (T h388 (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h69 h102) h117) h142) h144) h143) h154) h137) h196) h195) h194) h174) h220) h291) h323) h322) h321) h387) h386) h385) (T (T (T h296 h295) h293) h292)))
  have h391 := C (T (T h371 h370) h351) h374
  have h392 := T (T (T (T (T (T h358 h342) h340) h339) h356) h376) h375
  have h393 := C h392 h346
  have h394 := C (T (T h393 h391) h367) h363
  have h395 := C (T (T (T (T (T (T (T (T h187 h209) h216) h355) h354) h348) h347) h341) h368) h394
  have h396 := T (T (T h390 h384) h361) h395
  have h397 := C h396 h225
  have h398 := S h387
  have h399 := C (T (T (T (T (T (T (T h371 h370) h365) h338) h333) h192) h191) h188) (T h216 h355)
  have h400 := C h392 h210
  have h401 := T (T (T (T (T (T (T (T (T (T h187 h209) h216) h355) h354) h348) h347) h341) h368) h361) h395
  have h402 := C h401 (T (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h400 h399) h398) h296) h295) h293) h292) h201) h175) h172) h171) h169) h138) h135) h132) h126) h124) h108) h91) h70) (T (T (T h291 h323) h322) h321)) (S h388))
  have h403 := T h383 h402
  have h404 := C h403 h210
  have h405 := h v297 v359 x
  have h406 := S h405
  have h407 := R (M v359 x)
  have h408 := h v92 v359 v359
  have h409 := C h396 h364
  have h410 := C h403 h346
  have h411 := T h390 h384
  have h412 := C h411 h364
  have h413 := T (T (T h380 h362) h383) h402
  have h414 := C h413 h346
  have h415 := C (T (T (T (T h414 h412) h393) h391) h367) (T (T (T (T (T (T h357 h377) h373) h410) h409) (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h380 h362) h358) h342) h340) h339) h338) h333) h192) h191) h188) h105) h104) h185) h184) h277) h276) (T h408 (C h363 h389)))) (C h337 h407))
  have h416 := C (T h410 h409) h363
  have h417 := h v381 v6 v30
  have h418 := C h334 h59
  have h419 := R (M v297 v6)
  have h420 := C h419 h63
  have h421 := C h331 h23
  have h422 := C (T (T h400 h399) h398) h133
  have h423 := C h411 h225
  have h424 := C h413 h210
  have h425 := C (T h424 h423) h134
  have h426 := C (T (T (T (T (T (T (T (T h378 h416) h415) h406) h387) h386) h385) h404) h397) h129
  have h427 := C (T h414 h412) h363
  have h428 := C (T (T (T (T h357 h377) h373) h410) h409) (T (T (T (T (T (T (C h353 h407) (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h247 h240) h177) h176) h115) h113) h187) h209) h216) h355) h354) h348) h347) h341) h368) h361) h395) (T (C h363 h401) (S h408)))) h414) h412) h393) h391) h367)
  have h429 := C (T (T (T (T (T (T (T (T h424 h423) h400) h399) h398) h405) h428) h427) h394) h121
  have h430 := C (T h404 h397) h134
  have h431 := C (T (T h387 h386) h385) h153
  have h432 := C h334 h8
  have h433 := C h419 h40
  have h434 := C h331 h45
  have h435 := h v381 v30 v30
  T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (h v359 v92 v359) (C h106 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (C (R v381) h379) (C (T h417 (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h69 h102) h117) h142) h144) h143) h154) h137) h196) h195) h194) h174) h220) h291) h323) h322) h321) h405) h428) h427) h394) (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h426 h425) h422) h421) h420) h418) h317) h310) h264) h260) h249) h207) h204) h202) h81) h73) h56) h52) h33) h29) h17) (T (T (T (T (T (T (T (T (T (T (T (T (T h32 h65) h55) h101) h100) h221) h212) h206) h279) h273) h269) h300) h329) (C (T (T (T (T (T h434 h433) h432) h431) h430) h429) h112))) (S h435)) h378) h416) h415) h406) h296) h295) h293) h292) h201) h175) h172) h171) h169) h138) h135) h132) h126) h124) h108) h91) h70))) h210)) (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h378 h416) h415) h406) h296) h295) h293) h292) h201) h175) h172) h171) h169) h138) h135) h132) h126) h124) h108) h91) h70) (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h69 h102) h117) h142) h144) h143) h154) h137) h196) h195) h194) h174) h220) h291) h323) h322) h321) h405) h428) h427) h394) h435) (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h28 h46) h32) h65) h55) h101) h100) h221) h212) h206) h279) h273) h269) h309) h325) h434) h433) h432) h431) h430) h429) (T (T (T (T (T (T (T (T (T (T (T (T (T (C (T (T (T (T (T h426 h425) h422) h421) h420) h418) h112) h318) h301) h264) h260) h249) h207) h204) h202) h81) h73) h56) h52) h33)))) (S h417)) h378) h416) h415) h406) h296) h295) h293) h292) h201) h175) h172) h171) h169) h138) h135) h132) h126) h124) h108) h91) h70) (T (T (T (T (T (T (T (T (T (T h216 h355) h354) h348) h347) h341) h368) h361) h395) (h v382 v6 v6)) (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h69 h102) h117) h142) h144) h143) h154) h137) h196) h195) h194) h174) h220) h291) h323) h322) h321) h387) h386) h385) h404) h397) (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (C h396 h15) h390) h384) h358) h342) h340) h339) h338) h333) h192) h191) h188) h105) h104) h185) h184) h277) h276) h271) h270) h267) h266))))) (S (h v382 v6 x))) h380) h362) h358) h342) h340) h339) h338) h333) h192) h191) h188) h105) h104) h185) h184) h277) h284))) (S (h v265 v92 v30))) h264) h260) h249) h207) h204) h202) h81) h73) h56) h52) h33) h29) h17

