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
theorem Equation2349_implies_Equation1358 (G: Type _) [Magma G] (h: Equation2349 G) : Equation1358 G := fun x y z =>
  let v0 := M z x
  let v1 := M v0 z
  let v2 := M v1 y
  let v3 := M y v2
  let v4 := M x (M x (M v3 v3))
  have h5 := h v2 v4 y
  have h6 := S h5
  have h7 := R y
  have h8 := h v3 x v3
  have h9 := R v4
  have h10 := C (T h8 (C h9 h8)) h7
  have h11 := C h7 (T h10 h6)
  let v12 := M v3 y
  let v13 := M y v12
  have h14 := R z
  have h15 := S h8
  have h16 := C (T (C h9 h15) h15) h7
  have h17 := C h7 (T h5 h16)
  let v18 := M x v0
  let v19 := M x v18
  let v20 := M x (M x (M x x))
  have h21 := h z v20 v19
  have h22 := S h21
  have h23 := R v19
  have h24 := h x x z
  have h25 := R v20
  have h26 := h x x x
  have h27 := C (T h26 (C h25 (T h26 (C h25 h24)))) h23
  have h28 := R v18
  let v29 := M x (M x (M v0 v0))
  have h30 := h x v29 z
  have h31 := S h30
  have h32 := h v0 x v0
  have h33 := R v29
  have h34 := C (T h32 (C h33 h32)) h14
  have h35 := T h34 h31
  have h36 := C h35 h28
  have h37 := R x
  have h38 := C h37 h36
  have h39 := h v18 z x
  have h40 := S h39
  let v41 := M x (M x (M v1 v1))
  have h42 := h z v41 v0
  have h43 := S h42
  have h44 := R v0
  have h45 := h v1 x v1
  have h46 := R v41
  have h47 := C (T h45 (C h46 h45)) h44
  let v48 := M z (M z v1)
  let v49 := M x (M x (M z z))
  have h50 := h v0 v49 v48
  have h51 := S h50
  have h52 := R v48
  have h53 := h z z v0
  have h54 := R v49
  have h55 := h z x z
  have h56 := C (T h55 (C h54 (T h55 (C h54 h53)))) h52
  have h57 := S h32
  have h58 := C (T (C h33 h57) h57) h14
  have h59 := T h30 h58
  have h60 := C h59 (T h56 h51)
  have h61 := C h44 (T (T h60 h47) h43)
  have h62 := h (M z v48) x x
  have h63 := S h62
  have h64 := S h55
  have h65 := C (T (C h54 (T (C h54 (S h53)) h64)) h64) h52
  have h66 := C h35 (T h50 h65)
  have h67 := S h45
  have h68 := C (T (C h46 h67) h67) h44
  have h69 := R (M x (M x v19))
  have h70 := C (T (C h59 h69) (C h35 (C h37 (T (T (T (T h27 h22) h42) h68) h66)))) h37
  have h71 := h v19 x x
  have h72 := C h44 (C h35 (T (T h71 h70) h63))
  have h73 := S h71
  have h74 := S h26
  have h75 := S h24
  have h76 := C (T (C h25 (T (C h25 h75) h74)) h74) h23
  have h77 := C (T (C h59 (C h37 (T (T (T (T h60 h47) h43) h21) h76))) (C h35 h69)) h37
  have h78 := h v0 x x
  have h79 := S h78
  let v80 := M y v3
  let v81 := M x (M x (M y y))
  have h82 := h v1 v81 v80
  have h83 := S h82
  have h84 := R v80
  have h85 := h y y v1
  have h86 := R v81
  have h87 := h y x y
  have h88 := C (T h87 (C h86 (T h87 (C h86 h85)))) h84
  have h89 := C h7 (C h7 h11)
  have h90 := T (T (T (T h89 h88) h83) h34) h31
  have h91 := T h21 h76
  have h92 := C h91 h90
  have h93 := C h7 (C h7 h17)
  have h94 := S h87
  have h95 := C (T (C h86 (T (C h86 (S h85)) h94)) h94) h84
  have h96 := T (T h82 h95) h93
  have h97 := C h14 (C h14 h96)
  have h98 := C (T (T h50 h65) (C h14 (T h97 (C h14 (T (T (T (T (T (T h92 h79) h50) h65) h62) h77) h73))))) (T (T (T h72 h61) h34) h31)
  have h99 := C h44 (C h59 (T (T h62 h77) h73))
  have h100 := C h44 h99
  have h101 := C h44 (T (T h42 h68) h66)
  have h102 := C h44 (T (T (T h89 h88) h83) h101)
  have h103 := C h44 h96
  have h104 := R v1
  have h105 := C h104 (T (T (T (T h103 h102) h100) h98) h40)
  have h106 := C h37 h105
  let v107 := M v0 v1
  let v108 := M v1 v107
  have h109 := R v108
  have h110 := C h35 h109
  let v111 := M v1 v108
  have h112 := h v111 v0 v0
  let v113 := M v1 v18
  have h114 := h v113 z z
  have h115 := S h114
  have h116 := h v111 v3 v1
  have h117 := S h116
  have h118 := R v111
  have h119 := R v3
  have h120 := C h59 h109
  have h121 := C h35 h120
  have h122 := R (M x v108)
  have h123 := C h59 h122
  have h124 := T (T h89 h88) h83
  have h125 := C h44 h124
  have h126 := C h44 (T (T (T h61 h82) h95) h93)
  have h127 := C h44 h72
  have h128 := C h14 (C h14 h124)
  have h129 := T (T (T (T h30 h58) h82) h95) h93
  have h130 := T h27 h22
  have h131 := C h130 h129
  have h132 := C (T (T (C h14 (T (C h14 (T (T (T (T (T (T h71 h70) h63) h56) h51) h78) h131)) h128)) h56) h51) (T (T (T h30 h58) h101) h99)
  have h133 := C h104 (T (T (T (T h39 h132) h127) h126) h125)
  have h134 := C h37 h133
  have h135 := C h35 h134
  have h136 := R (M x v113)
  have h137 := C h59 h136
  have h138 := R v113
  have h139 := C h35 h138
  have h140 := C h37 h139
  have h141 := C h59 h138
  have h142 := C h37 h141
  have h143 := C h35 h136
  have h144 := C h104 h139
  have h145 := C h104 h141
  have h146 := C h59 h28
  have h147 := C h37 h146
  have h148 := C h59 (T (T (T (T h47 h43) h21) h76) h147)
  have h149 := C h35 (T (T (T (T h38 h27) h22) h42) h68)
  have h150 := C h59 h106
  have h151 := C h35 h122
  have h152 := C h59 h110
  have h153 := T (T (T (T h21 h76) h147) h134) h120
  have h154 := h v1 v1 v0
  have h155 := S h154
  have h156 := T (T (T (T h50 h65) h62) h77) h73
  have h157 := C h156 (T (T h38 h27) h22)
  have h158 := C h44 h139
  have h159 := C h91 (T (T h158 h157) h75)
  have h160 := C h44 h141
  have h161 := C h44 h106
  have h162 := C h44 h110
  have h163 := T (T h162 h161) h160
  have h164 := C h14 h163
  have h165 := C h153 (T (T h164 h159) h79)
  have h166 := C h44 h120
  have h167 := C h44 h134
  have h168 := T (T h158 h167) h166
  have h169 := C h14 h168
  have h170 := C h14 h169
  have h171 := C (T (T (T (T h71 h70) h63) h56) h51) (T (T h21 h76) h147)
  have h172 := C h130 (T (T h24 h171) h160)
  have h173 := C h14 (T (C h14 (T (T (T (T (T (T (T h36 h71) h70) h63) h56) h51) h78) h131)) h128)
  have h174 := C h14 (C h14 h105)
  have h175 := C h14 (T (T (T (T (T h174 h173) h56) h51) h78) h172)
  have h176 := C h14 (C h14 h133)
  have h177 := C h14 h176
  have h178 := C (T (T (T (T (T (T h177 h175) h170) h165) h155) h34) h31) h153
  have h179 := C h119 h105
  have h180 := C h119 h133
  have h181 := C (T (T (T (C h119 h180) (C h119 (T (T (T h179 (C h119 (T (T (T (T (T h114 h178) h152) h151) h150) h149))) (C h119 (T h148 h145))) (C h119 (T (T h144 h143) h142))))) (C h119 (C h119 (T (T (T (T h140 h137) h135) h123) h121)))) (C h119 (C h119 (C h59 h118)))) h104
  have h182 := h v18 v3 v1
  have h183 := h v107 z v1
  have h184 := S h183
  have h185 := C h14 (T h97 (C h14 (T (T (T (T (T (T (T h92 h79) h50) h65) h62) h77) h73) h146)))
  have h186 := C (T (T (T h50 h65) h185) h176) (T (T (T h157 h75) h30) h58)
  have h187 := C h44 h161
  have h188 := C h44 h162
  have h189 := C h44 h158
  have h190 := C h44 (T (T (T (T (T (T (T (T (T (T h189 h186) h184) h103) h102) h100) h98) h40) h182) h181) h117)
  have h191 := C h44 h160
  have h192 := C (T (T (T h174 h173) h56) h51) (T (T (T h34 h31) h24) h171)
  have h193 := C h44 (T (T (T (T (T (T (T h39 h132) h127) h126) h125) h183) h192) h191)
  let v194 := M v0 v18
  have h195 := h v194 x v2
  have h196 := R v2
  have h197 := R (M v2 v194)
  have h198 := C h35 h197
  have h199 := C h44 (T (T (T (T (T (T (T h189 h186) h184) h103) h102) h100) h98) h40)
  have h200 := S h182
  have h201 := T (T (T (T h110 h106) h38) h27) h22
  have h202 := C h14 h174
  have h203 := C h14 (T (T (T (T (T h159 h79) h50) h65) h185) h176)
  have h204 := C h14 h164
  have h205 := C h201 (T (T h78 h172) h169)
  have h206 := C (T (T (T (T (T (T h30 h58) h154) h205) h204) h203) h202) h201
  have h207 := C (T (T (T (C h119 (C h119 (C h35 h118))) (C h119 (C h119 (T (T (T (T h152 h151) h150) h143) h142)))) (C h119 (T (T (T (C h119 (T (T h140 h137) h145)) (C h119 (T h144 h149))) (C h119 (T (T (T (T (T h148 h135) h123) h121) h206) h115))) h180))) (C h119 h179)) h104
  have h208 := C h44 (T (T (T (T (T (T (T (T (T (T h116 h207) h200) h39) h132) h127) h126) h125) h183) h192) h191)
  have h209 := h v2 x v2
  have h210 := S h209
  let v211 := M x (M x (M v2 v2))
  have h212 := R v211
  have h213 := h y v211 v1
  let v214 := M v2 v3
  let v215 := M v2 v214
  have h216 := h y v211 v215
  have h217 := S h216
  have h218 := R v215
  have h219 := h v2 v2 y
  have h220 := C (T h209 (C h212 (T h209 (C h212 h219)))) h218
  have h221 := C h59 (T (T (T (T (T (T (T h220 h217) h213) (C (T (C h212 h210) h210) h104)) (C h196 h96)) (C h196 (T (T (T (T (T (T (T h89 h88) h83) h34) h31) h24) h171) h160))) (C h196 h168)) (C h196 (T h208 h199)))
  have h222 := C h37 (T h221 h198)
  have h223 := h v215 x v2
  have h224 := C h44 (T (T (T (T h223 (C h222 h196)) (S h195)) h193) h190)
  have h225 := C (T (T (T (T h154 h205) h204) h203) h202) (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h224 h188) h187) h186) h184) h103) h102) h100) h98) h40) h182) h181) h117) h110) h106) h38) h27) h22)
  have h226 := R (M v0 v215)
  have h227 := C h59 h226
  have h228 := C h44 h166
  have h229 := C h44 h167
  have h230 := C h35 h226
  have h231 := C (T (C h212 (T (C h212 (S h219)) h210)) h210) h218
  have h232 := C h35 (T (T (T (T (T (T (T (C h196 (T h193 h190)) (C h196 h163)) (C h196 (T (T (T (T (T (T (T h158 h157) h75) h30) h58) h82) h95) h93))) (C h196 h124)) (C (T h209 (C h212 h209)) h104)) (S h213)) h216) h231)
  have h233 := C h59 h197
  have h234 := C h37 (T h233 h232)
  have h235 := C h44 (T (T (T (T h208 h199) h195) (C h234 h196)) (S h223))
  have h236 := h (M v1 v113) y v0
  have h237 := C h196 h11
  have h238 := C h196 (C h196 h237)
  have h239 := C h196 h17
  have h240 := h v214 v0 v2
  have h241 := h v12 y y
  have h242 := S h241
  have h243 := C h129 (T h220 h217)
  have h244 := R (M x (M v2 v215))
  have h245 := C h90 (T h216 h231)
  have h246 := h v12 v2 x
  have h247 := h v13 v2 v2
  have h248 := T (T (T h17 h247) (C (T (T h238 h220) h217) (T (T (T h5 h16) h241) h245))) (C h7 (T (T (T (T h243 h242) h246) (C (T (T (T (C h196 (C h196 (T (T (T (T (T (C h59 (T h241 h245)) (C h35 h244)) h222) (C (T (T (T (T (T h24 h171) h167) h166) h208) (C h44 (T (T (T h189 h229) h228) h235))) (T (T (T (T (T h233 h232) h243) h242) h10) h6))) (S h240)) h239))) h238) h220) h217) (T (T (T h24 h171) h167) h166))) (C h7 h163)))
  have h249 := C h248 (T (T (T (T (T (T (T (T (T (T (T h148 h135) h123) h121) h206) h115) h36) h71) h70) h63) h56) h51)
  have h250 := C h104 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h249 (S h236)) h139) h134) h120) h116) h207) h200) h39) h132) h127) h126) h125) h183) h192) h229) h228) h235)
  let v251 := M x (M v1 v0)
  have h252 := R (M v3 v251)
  have h253 := C (T (T (T (T (T (T (T (T (C h59 (T (C h59 h252) h250)) (C h35 h230)) (C (T (T (T (T (T h24 h171) h167) h166) h208) (C h44 (T (T h189 h229) h228))) (T (T (T (T (T (T (T (T h227 h225) h115) h36) h71) h70) h63) h56) h51))) (S h112)) h110) h106) h38) h27) h22) h17
  have h254 := h v251 x v3
  have h255 := C h196 (C h196 h239)
  have h256 := T (T (T (C h7 (T (T (T (T (C h7 h168) (C (T (T (T h216 h231) h255) (C h196 (C h196 (T (T (T (T (T h237 h240) (C (T (T (T (T (T (C h44 (T (T (T h224 h188) h187) h191)) h190) h162) h161) h157) h75) (T (T (T (T (T h5 h16) h241) h245) h221) h198))) h234) (C h59 h244)) (C h35 (T h243 h242)))))) (T (T (T h162 h161) h157) h75))) (S h246)) h241) h245)) (C (T (T h216 h231) h255) (T (T (T h243 h242) h10) h6))) (S h247)) h11
  have h257 := C h256 (T (T (T (T (T (T (T (T (T (T (T h50 h65) h62) h77) h73) h146) h114) h178) h152) h151) h150) h149)
  have h258 := C h104 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h224 h188) h187) h186) h184) h103) h102) h100) h98) h40) h182) h181) h117) h110) h106) h141) h236) h257)
  have h259 := C (T (T (T (T h177 h175) h170) h165) h155) (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h21 h76) h147) h134) h120) h116) h207) h200) h39) h132) h127) h126) h125) h183) h192) h229) h228) h235)
  have h260 := R (M v3 (M z v3))
  T (T (T (h x v2 z) (C (T (T (T (T (T (C h196 (C h196 h156)) (C h196 (C h196 h146))) (C h196 (C h196 h133))) (C h196 (T (C h196 h105) (C h196 (T (T (T (T h114 h259) h258) (C h104 (T (T h249 (C h256 (T (T (T (T (T (T (T (T (T (T (T (T (T h50 h65) h62) h77) h73) h146) h114) h178) h152) h151) h150) h149) h254) h253))) (C h119 (C h14 h11))))) (C h35 h260)))))) (C h196 (C h196 (C h59 h260)))) (C h196 (C h196 (T (T (T (T (T (T (T (T (T (C h104 (T (T (C h119 (C h14 h17)) (C h248 (T (T (T (T (T (T (T (T (T (T (T (T (T (C (T (T (T (T (T (T (T (T h21 h76) h147) h134) h120) h112) (C (T (T (T (T (T (C h44 (T (T h188 h187) h191)) h190) h162) h161) h157) h75) (T (T (T (T (T (T (T (T h50 h65) h62) h77) h73) h146) h114) h259) h230))) (C h59 h227)) (C h35 (T h258 (C h35 h252)))) h11) (S h254)) h148) h135) h123) h121) h206) h115) h36) h71) h70) h63) h56) h51))) h257)) h250) h225) h178) h152) h151) h150) h149) h254) h253)))) h14)) (S (h v13 v2 z))) h11

