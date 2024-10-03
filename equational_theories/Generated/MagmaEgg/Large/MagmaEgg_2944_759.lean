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
theorem Equation2944_implies_Equation759 (G: Type _) [Magma G] (h: Equation2944 G) : Equation759 G := fun x y z =>
  let v0 := M y x
  let v1 := M v0 z
  let v2 := M z v1
  let v3 := M y v2
  have h4 := h v2 y v3
  have h5 := S h4
  have h6 := R v3
  have h7 := h y x y
  have h8 := S h7
  let v9 := M (M x (M x y)) y
  have h10 := R v9
  have h11 := T (C h10 h8) h8
  have h12 := C (C h11 h6) h6
  have h13 := h y v9 v3
  have h14 := T h13 h12
  have h15 := C h14 h6
  have h16 := T h15 h5
  have h17 := R y
  have h18 := C h17 h16
  let v19 := M y v3
  let v20 := M y v19
  have h21 := h v20 y y
  have h22 := S h21
  have h23 := S h13
  have h24 := T h7 (C h10 h7)
  have h25 := C (C h24 h6) h6
  have h26 := T h25 h23
  have h27 := C h26 h6
  have h28 := T h4 h27
  have h29 := C h17 h28
  have h30 := C h26 h29
  have h31 := C h17 (T h15 h30)
  have h32 := h y v9 v2
  have h33 := S h32
  have h34 := R v2
  have h35 := C (C h24 h34) h34
  have h36 := C h6 h16
  have h37 := T h29 h31
  have h38 := C h37 (T (T h36 h35) h33)
  have h39 := C (T (T (C h38 h17) h22) h31) h17
  have h40 := h v19 v3 y
  have h41 := C h14 h18
  have h42 := C (T (T (T h41 h27) h40) h39) h17
  have h43 := T h4 h30
  have h44 := C h43 h26
  have h45 := T (T (T h35 h33) h13) h12
  have h46 := C h34 h45
  have h47 := C (C h11 h34) h34
  have h48 := C h34 (T h32 h47)
  let v49 := M v2 y
  have h50 := h v49 y y
  have h51 := S h50
  have h52 := h (M v19 v3) v2 v3
  have h53 := S h52
  have h54 := T (T (T h44 h42) h22) h18
  have h55 := T h41 h5
  have h56 := C h55 h14
  have h57 := S h40
  have h58 := C h6 h28
  have h59 := C h17 (T h41 h27)
  have h60 := T h59 h18
  have h61 := C h60 (T (T h32 h47) h58)
  have h62 := C (T (T h59 h21) (C h61 h17)) h17
  have h63 := C (T (T (T h62 h57) h15) h30) h17
  have h64 := T (T (T h29 h21) h63) h56
  have h65 := C h55 h64
  have h66 := C h65 h6
  have h67 := h v19 y v3
  have h68 := C (T (T (T h4 h27) h67) h66) h54
  have h69 := C h34 h46
  have h70 := C h34 h48
  have h71 := C h34 (T h35 h33)
  have h72 := T (T (T h25 h23) h32) h47
  have h73 := C h34 h72
  have h74 := T (T (T (T (T h29 h21) h63) h56) h73) h71
  have h75 := C (T (T (T (T h38 h62) h57) h15) h5) h74
  have h76 := T (C h6 h45) (C h6 (T (T (T (T h25 h23) h32) h47) h58))
  have h77 := C h76 h6
  have h78 := T (T (T (T (T (T (T h77 h75) h70) h69) h68) h53) h25) h23
  have h79 := C h43 h18
  have h80 := C h34 h29
  have h81 := T (T (T (T (T (T h80 h79) h65) h68) h53) h25) h23
  let v82 := M v3 v2
  have h83 := h v82 v2 v3
  have h84 := S h83
  have h85 := C h34 h73
  have h86 := C h85 h6
  have h87 := h v19 y y
  have h88 := S h87
  have h89 := C h60 h28
  have h90 := C (T (T (T h4 h27) h40) h39) (T (T (T (T (T h79 h65) h68) h53) h25) h23)
  have h91 := C (T (T h90 h22) h31) h34
  have h92 := C h34 h80
  have h93 := C h92 h34
  have h94 := T (T (T (T (T h93 h91) h89) h36) h35) h33
  have h95 := C (T (T h29 h21) h63) h94
  have h96 := C h34 h18
  have h97 := C h34 h96
  have h98 := C h97 h34
  have h99 := C h55 h29
  have h100 := C h43 h54
  have h101 := S h67
  have h102 := C h100 h6
  have h103 := C (T (T (T h102 h101) h15) h5) h64
  have h104 := C (T (T (T h62 h57) h15) h5) (T (T (T (T (T h13 h12) h52) h103) h100) h99)
  have h105 := C (T (T h59 h21) h104) h34
  have h106 := C h37 h16
  have h107 := T (T (T (T (T h32 h47) h58) h106) h105) h98
  have h108 := T (T h90 h22) h18
  have h109 := C h108 h107
  have h110 := C h92 h17
  have h111 := T (T (T h29 h21) h104) h97
  have h112 := C h111 h81
  have h113 := T (T (T (T (T (T h13 h12) h52) h103) h100) h99) h96
  let v114 := M v2 v3
  have h115 := h v114 v3 v3
  let v116 := M v2 v114
  have h117 := h v116 v2 v2
  have h118 := S h117
  let v119 := M v116 y
  have h120 := h v119 v3 v3
  have h121 := S h120
  have h122 := h v3 v2 v2
  have h123 := S h122
  have h124 := T (T (T (T (T h110 h109) h95) h88) h15) h5
  have h125 := C h107 h124
  have h126 := C h97 h17
  have h127 := T (T h29 h21) h104
  have h128 := C h127 h94
  have h129 := C (T (T h42 h22) h18) h107
  have h130 := T (T (T (T (T h4 h27) h87) h129) h128) h126
  have h131 := h v20 v2 v2
  have h132 := C h127 (T (T (T h95 h88) h15) h5)
  have h133 := C h108 (T (T (T h4 h27) h87) h129)
  let v134 := M v116 v2
  have h135 := h v134 v3 v3
  have h136 := S h135
  have h137 := C (T (T (T (T (T (T (T (T (T (T h65 h68) h53) h25) h23) h32) h47) h58) h106) h105) h133) h6
  have h138 := C (T (T (T h4 h27) h67) h137) (T (T (T (C h34 (T (T (T (T (T (T (T (T (T (T (T h93 h91) h89) h36) h35) h33) h13) h12) h52) h103) h100) h99)) h90) h22) h18)
  have h139 := T (T (T h138 h136) h93) h133
  have h140 := C (T (T (T (C h139 h34) (C h132 h34)) (S h131)) h18) h130
  have h141 := h v134 v2 v2
  have h142 := C h108 (T (T (T (T (T (T (T h32 h47) h58) h106) h105) h98) h141) h140)
  have h143 := C (T (T (T (T (T (T (T (T (T (T h132 h91) h89) h36) h35) h33) h13) h12) h52) h103) h100) h6
  have h144 := C (T (T (T (T (T (T (C h139 h6) h143) h101) h87) h129) h128) h142) h6
  have h145 := h v134 v2 v3
  have h146 := C (T (T (T (T (T (T (T h32 h47) h58) h106) h105) h98) h145) h144) (T h125 h123)
  have h147 := C (T (T (T (T (T (T (T h146 h121) h110) h109) h95) h88) h15) h5) h111
  have h148 := C h94 h130
  have h149 := S h145
  have h150 := C (T (T (T h143 h101) h15) h5) (T (T (T h29 h21) h104) (C h34 (T (T (T (T (T (T (T (T (T (T (T h79 h65) h68) h53) h25) h23) h32) h47) h58) h106) h105) h98)))
  have h151 := T (T (T h132 h98) h135) h150
  have h152 := S h141
  have h153 := C (T (T (T h29 h131) (C h133 h34)) (C h151 h34)) h124
  have h154 := C h127 (T (T (T (T (T (T (T h153 h152) h93) h91) h89) h36) h35) h33)
  have h155 := C (T (T (T (T (T (T h154 h109) h95) h88) h67) h137) (C h151 h6)) h6
  have h156 := C (T (T (T (T (T (T (T h155 h149) h93) h91) h89) h36) h35) h33) (T h122 h148)
  have h157 := T (T (T h154 h126) h120) h156
  have h158 := C h157 h6
  have h159 := T (T (T (T (T (T (T (T (T h32 h47) h58) h106) h105) h98) h145) h144) h158) h147
  have h160 := h v119 y y
  have h161 := h v20 v2 y
  have h162 := h v119 y v3
  have h163 := S h162
  have h164 := T (T (T h92 h90) h22) h18
  have h165 := C (T (T (T (T (T (T (T (T h32 h47) h58) h106) h105) h98) h145) h144) h158) h164
  have h166 := C h17 (T h165 h163)
  have h167 := h v116 y y
  have h168 := T (T (T h146 h121) h110) h142
  have h169 := C h168 h6
  have h170 := C (T (T (T (T (T (T (T (T h169 h155) h149) h93) h91) h89) h36) h35) h33) h111
  have h171 := C h17 (T h162 h170)
  have h172 := C (T (T (T (T (T (T (T h4 h27) h87) h129) h128) h126) h120) h156) h164
  have h173 := C (T (T (T (T (T (T (T h172 h169) h155) h149) h141) h140) (C (T (T h122 h148) h171) h124)) (C (T (T (T (T (T (T (T (T h166 h125) h123) h29) h21) h104) h97) h167) (C (T (T (T (T (T (T (T (C (T (T (T (T (T (T h166 h125) h123) h29) h161) (C h142 h17)) (C h157 h17)) h17) (S h160)) h110) h109) h95) h88) h15) h5) h159)) h34)) h34
  have h174 := C h111 (T (T (T (T (T (T h112 h110) h109) h95) h88) h15) h5)
  have h175 := T (T (T (T h174 h145) h144) h158) h147
  have h176 := C h175 h34
  have h177 := C h164 h113
  have h178 := C h164 (T (T (T (T (T (T h4 h27) h87) h129) h128) h126) h177)
  have h179 := T (T (T (T (T (T (T (T (T (T h68 h53) h25) h23) h32) h47) h58) h106) h105) h98) h178
  have h180 := C h179 h34
  have h181 := C h69 h34
  have h182 := C h70 h34
  have h183 := T (T (T (T (T (T (T (T (T h182 h181) h180) h176) h173) h118) h92) h90) h22) h18
  have h184 := T (T (T (T h172 h169) h155) h149) h178
  have h185 := C h34 (T (C (T (T (T (T (T (T (T (T (T h4 h27) h87) h129) h128) h126) h162) h170) (C h159 h164)) (C h184 h6)) h183) (S h115))
  have h186 := C (T (T (T (T h185 h92) h90) h22) h18) h113
  have h187 := C h34 h71
  have h188 := C h187 h34
  have h189 := C h85 h34
  have h190 := T (T (T (T (T (T (T (T (T (T h174 h93) h91) h89) h36) h35) h33) h13) h12) h52) h103
  have h191 := C h190 h34
  have h192 := C h184 h34
  have h193 := T (T (T (T (T (T (T (T (T h172 h169) h155) h149) h93) h91) h89) h36) h35) h33
  have h194 := C (T (T (T (T (T (T (T (C (T (T (T (T (T (T (T (T (C (T (T (T (T (T (T (T h4 h27) h87) h129) h128) h126) h160) (C (T (T (T (T (T (T (C h168 h17) (C h154 h17)) (S h161)) h18) h122) h148) h171) h17)) h193) (S h167)) h92) h90) h22) h18) h122) h148) h171) h34) (C (T (T h166 h125) h123) h130)) h153) h152) h145) h144) h158) h147) h34
  have h195 := T (T (T (T (T (T (T (T (T h29 h21) h104) h97) h117) h194) h192) h191) h189) h188
  have h196 := C h34 (T h115 (C (T (T (T (T (T (T (T (T (T (C h175 h6) (C h193 h111)) h165) h163) h110) h109) h95) h88) h15) h5) h195))
  let v197 := M v2 v49
  let v198 := M v197 v2
  have h199 := h v198 v2 v2
  have h200 := S h199
  have h201 := h v82 v2 v2
  have h202 := C (T (T (T h32 h47) h201) (C (T (T (T (T (T h181 h180) h176) h173) h118) h196) h34)) (T (T (T (T (C (T (T (T h13 h12) h52) h103) h183) h102) h101) h15) h5)
  have h203 := C (T (T (T (T (T (T (T (T h202 h200) h182) h181) h180) h176) h173) h118) h196) h17
  have h204 := T (T (T (T (T h70 h69) h68) h53) h25) h23
  have h205 := C (T (T (T (C (T (T (T (T (T h185 h117) h194) h192) h191) h189) h34) (S h201)) h35) h33) (T (T (T (T h4 h27) h67) h66) (C (T (T (T h68 h53) h25) h23) h195))
  have h206 := C (T (T (T (T (T (T (T (T (T (T (T h29 h21) h104) h97) h117) h194) h192) h191) h189) h188) h199) h205) h204
  have h207 := T (T (T (T (T h13 h12) h52) h103) h85) h187
  have h208 := h v198 y y
  have h209 := S h208
  have h210 := C (T (T (T (T (T (T (T (T h185 h117) h194) h192) h191) h189) h188) h199) h205) h17
  have h211 := C (T (T (T (T h29 h21) h104) h97) h196) h81
  have h212 := C (T (T (T (T (T (T (T (T h4 h27) h87) h129) h128) h126) h177) h211) h210) h204
  have h213 := T (T (T (T (T (T (T (T (T (T (T h212 h209) h182) h181) h180) h176) h173) h118) h92) h90) h22) h18
  have h214 := C h213 h207
  have h215 := h v197 v2 v2
  have h216 := S h215
  have h217 := C h69 h6
  have h218 := C h70 h6
  have h219 := T (T (T (T (T h218 h217) h102) h101) h15) h5
  have h220 := C (T (T (T (T (T (T (T (T h203 h186) h112) h110) h109) h95) h88) h15) h5) h207
  have h221 := T (T (T (T (T (T (T (T (T (T (T h29 h21) h104) h97) h117) h194) h192) h191) h189) h188) h208) h220
  have h222 := h y v2 v2
  have h223 := T (T (T (T (T (T (C h195 (T (T (T (T (T (T (T (T (T h206 h203) h186) h112) h110) h109) h95) h88) h15) h5)) (S h222)) h13) h12) h52) h103) h85
  have h224 := h v197 v3 v3
  have h225 := h v197 v3 v2
  have h226 := C (T (T (T (T (T (T (T (T (T (T (T h202 h200) h182) h181) h180) h176) h173) h118) h92) h90) h22) h18) h207
  have h227 := T (T (T (T (T (T h69 h68) h53) h25) h23) h222) (C h183 (T (T (T (T (T (T (T (T (T h4 h27) h87) h129) h128) h126) h177) h211) h210) h226))
  have h228 := h v49 v2 v2
  have h229 := C (T (T (T (T (T (T (T h29 h21) h63) h56) h73) h71) h228) (C (T (T (T (C (T (T (T h212 h209) h182) (C h227 h34)) h34) (S h225)) h224) (C (T (T (T (T (T (C h223 h6) h217) h102) h101) h15) h5) h221)) h34)) h219
  have h230 := C h221 (T (T (T (T (T (T (T h229 h216) h70) h69) h68) h53) h25) h23)
  have h231 := C (T (T (T (T (T (T (T (T (T (T (T (T h230 h214) h206) h203) h186) h112) h110) h109) h95) h88) h67) h66) h86) h6
  have h232 := C h187 h6
  have h233 := T (T (T (T (T h4 h27) h67) h66) h86) h232
  have h234 := C (T (T (T (T (T (T (T (C (T (T (T (C (T (T (T (T (T h4 h27) h67) h66) h86) (C h227 h6)) h213) (S h224)) h225) (C (T (T (T (C h223 h34) h188) h208) h220) h34)) h34) (S h228)) h48) h46) h44) h42) h22) h18) h233
  have h235 := C h213 (T (T (T (T (T (T (T h13 h12) h52) h103) h85) h187) h215) h234)
  have h236 := C h221 h204
  let v237 := M v197 v3
  have h238 := h v237 v3 v3
  have h239 := S h238
  have h240 := C h207 h219
  have h241 := C (T (T (T (T (T (T (T (T (T (T (T (T h217 h102) h101) h87) h129) h128) h126) h177) h211) h210) h226) h236) h235) h6
  have h242 := C (T (T (T h32 h47) h83) h241) (T (T (T (T (T (T (T (T (T (T h240 h182) h181) h180) h176) h173) h118) h92) h90) h22) h18)
  have h243 := T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h242 h239) h218) h217) h102) h101) h87) h129) h128) h126) h177) h211) h210) h226) h236) h235
  have h244 := h v237 y v3
  have h245 := C h204 h233
  have h246 := T (T (T (T (T (T (T (T (T (T (T h29 h21) h104) h97) h117) h194) h192) h191) h189) h188) h245) (C h17 (T h244 (C (T (T (T (T (C h243 h6) h231) h84) h35) h33) h74)))
  have h247 := C h246 h81
  have h248 := C (T (T (T (T (T (T (T h4 h27) h87) h129) h128) h126) h177) h247) h78
  let v249 := M v3 v82
  let v250 := M v249 v3
  have h251 := h v250 v2 x
  have h252 := S h251
  have h253 := R x
  have h254 := T (C h6 (T (T (T (T h36 h35) h33) h13) h12)) (C h6 h72)
  have h255 := C h254 h6
  have h256 := T (T (T (T (T h48 h46) h44) h42) h22) h18
  have h257 := C (T (T (T (T h4 h27) h40) h39) h61) h256
  have h258 := T (T (T (T (T (T (T h13 h12) h52) h103) h85) h187) h257) h255
  have h259 := C (T (T (T h231 h84) h35) h33) (T (T (T (T (T (T (T (T (T (T h29 h21) h104) h97) h117) h194) h192) h191) h189) h188) h245)
  have h260 := T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h230 h214) h206) h203) h186) h112) h110) h109) h95) h88) h67) h66) h86) h232) h238) h259
  have h261 := T (T (T (T (T (T (T (T (T (T (T (C h17 (T (C (T (T (T (T h32 h47) h83) h241) (C h260 h6)) h256) (S h244))) h240) h182) h181) h180) h176) h173) h118) h92) h90) h22) h18
  have h262 := C h261 h113
  have h263 := C (T (T (T (T (T (T (T h262 h112) h110) h109) h95) h88) h15) h5) h258
  have h264 := h v19 v3 v3
  have h265 := C h261 h233
  have h266 := C h246 h78
  have h267 := C h246 (T (T (T (T (T (T (T (T h266 h262) h112) h110) h109) h95) h88) h15) h5)
  have h268 := h v250 v3 v3
  have h269 := T (T (T (T (T (T (T h267 h265) h229) h216) h257) h255) h268) (C (T (T (T (C (T (T (T (T h267 h265) h229) h216) h257) h6) (S h264)) h15) h5) (T (T (T (T (T (T (T h29 h21) h63) h56) h73) h71) h50) h263))
  have h270 := C h261 h258
  have h271 := C h261 (T (T (T (T (T (T (T (T h4 h27) h87) h129) h128) h126) h177) h247) h270)
  have h272 := C h246 h219
  let v273 := M (M x (M x v0)) v0
  have h274 := h v0 v273 v1
  have h275 := S h274
  have h276 := R v1
  have h277 := h v0 x v0
  have h278 := R v273
  have h279 := C (C (T h277 (C h278 h277)) h276) h276
  let v280 := M (M x (M x z)) z
  have h281 := h z v280 v1
  have h282 := h z x z
  have h283 := R v280
  have h284 := T (T (T (T (T h154 h109) h95) h88) h15) h30
  have h285 := T (T (T (T (T (T (T h230 h214) h206) h203) h186) h112) h120) h156
  have h286 := C h76 h276
  have h287 := R v0
  have h288 := C h287 (T (T (T (T (T (T (T (T h286 (C (T (T (T (T (T (T (T (T h38 h62) h57) h67) h66) h86) h232) h238) h259) h276)) (C h243 h276)) (C h285 h276)) (C h168 h276)) (C h284 h276)) (C h55 h276)) (C (C (T h282 (C h283 h282)) h276) h276)) (S h281))
  have h289 := C (C h287 h288) h276
  have h290 := C h254 h276
  have h291 := T (T (T (T (T (T (T h146 h121) h177) h211) h210) h226) h236) h235
  have h292 := T (T (T (T (T h41 h27) h87) h129) h128) h142
  have h293 := S h282
  have h294 := C h287 (T (T (T (T (T (T (T (T h281 (C (C (T (C h283 h293) h293) h276) h276)) (C h43 h276)) (C h292 h276)) (C h157 h276)) (C h291 h276)) (C h260 h276)) (C (T (T (T (T (T (T (T (T h242 h239) h218) h217) h102) h101) h40) h39) h61) h276)) h290)
  have h295 := h (M v249 v1) v0 v1
  have h296 := C (T (T h290 h295) (C (T (T h289 h279) h275) h294)) h276
  have h297 := h v19 v3 v1
  have h298 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h242 h239) h218) h217) h102) h101) h297) h296) h289) h279) h275) (C (T (T (T (T (T h32 h47) h58) h106) h105) h133) h253)) (C h151 h253)) (C (T (T (T (T (T h138 h136) h145) h144) h158) h147) h253)) (C h184 h253)) (C h190 h253)) (C h85 h253)) (C h187 h253)) (C (T (T (T h215 h234) h272) h271) h253)) (C h269 h253)) h253
  have h299 := C h260 h253
  have h300 := C h291 h253
  have h301 := C h157 h253
  have h302 := C h292 h253
  have h303 := C h43 h253
  have h304 := T (T (T (T (T (T h303 h302) h301) h300) h299) h298) h252
  have h305 := S h297
  have h306 := C (C h287 h294) h276
  have h307 := S h277
  have h308 := C (C (T (C h278 h307) h307) h276) h276
  have h309 := C (T (T (C (T (T h274 h308) h306) h288) (S h295)) h286) h276
  have h310 := T (T (T (T (T (T h274 h308) h306) h309) h305) h15) h5
  have h311 := C h310 h304
  let v312 := M v2 x
  have h313 := R v312
  have h314 := T (T (T (T (T (T h4 h27) h297) h296) h289) h279) h275
  have h315 := C h314 h313
  let v316 := M v2 v312
  have h317 := C h310 h313
  have h318 := C h55 h253
  have h319 := C h284 h253
  have h320 := C h168 h253
  have h321 := C h285 h253
  have h322 := C h243 h253
  have h323 := S h268
  have h324 := C (T (T (T h4 h27) h264) (C (T (T (T (T h75 h215) h234) h272) h271) h6)) (T (T (T (T (T (T (T h248 h51) h48) h46) h44) h42) h22) h18)
  have h325 := T (T (T (T (T (T (T h324 h323) h77) h75) h215) h234) h272) h271
  have h326 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (C h325 h253) (C (T (T (T h267 h265) h229) h216) h253)) (C h70 h253)) (C h69 h253)) (C h179 h253)) (C h175 h253)) (C (T (T (T (T (T h172 h169) h155) h149) h135) h150) h253)) (C h139 h253)) (C (T (T (T (T (T h132 h91) h89) h36) h35) h33) h253)) h274) h308) h306) h309) h305) h67) h66) h86) h232) h238) h259) h253
  have h327 := T (T (T (T (T (T h251 h326) h322) h321) h320) h319) h318
  have h328 := C h314 h327
  have h329 := T (T (T (T (T (T (T (T (T h29 h21) h63) h56) h73) h71) h50) h263) h328) h317
  have h330 := h v312 v0 v3
  have h331 := S h330
  have h332 := T (T (T (T (T (T (T (T (T h315 h311) h248) h51) h48) h46) h44) h42) h22) h18
  have h333 := h v2 v3 v3
  have h334 := S h333
  have h335 := h v250 v2 v2
  have h336 := S h335
  have h337 := C h269 h34
  have h338 := C h271 h34
  have h339 := h v49 y v2
  have h340 := C (T (T (T (T (T (T (T (T h29 h21) h63) h56) h73) h71) h339) h338) h337) (T (T (T (T (T (T (T (T (T (C h6 h304) h266) h262) h112) h110) h109) h95) h88) h15) h5)
  have h341 := C (T h340 h336) h6
  have h342 := h v312 v3 v3
  have h343 := T (T (T (T (T (T (T (T (T (T h340 h336) h251) h326) h322) h321) h320) h319) h318) h342) (C (T (T (T (T (T (T (T (T h341 h334) h4) h27) h297) h296) h289) h279) h275) (T (T (T (T (T (T (T (T h29 h21) h63) h56) h73) h71) h50) h263) h328))
  have h344 := C h343 h6
  have h345 := C h6 h327
  have h346 := C (T (T (T (T (T (T (T (T (C h325 h34) (C h267 h34)) (S h339)) h48) h46) h44) h42) h22) h18) (T (T (T (T (T (T (T (T (T h4 h27) h87) h129) h128) h126) h177) h247) h270) h345)
  have h347 := C (T h335 h346) h6
  have h348 := C (T (T h333 h347) h344) h332
  have h349 := S h342
  have h350 := C (T (T (T (T (T (T (T (T h274 h308) h306) h309) h305) h15) h5) h333) h347) (T (T (T (T (T (T (T (T h311 h248) h51) h48) h46) h44) h42) h22) h18)
  have h351 := C (T (T (C (T (T (T (T (T (T (T (T (T (T h350 h349) h303) h302) h301) h300) h299) h298) h252) h335) h346) h6) h341) h334) h329
  have h352 := T (T (T h350 h349) h330) h351
  have h353 := C h352 h6
  let v354 := M v2 v316
  have h355 := C h34 (T h330 h351)
  T (T (T (T (T (T (T (T (T (T (T (T (h x v2 v3) (C (C (T (h v316 v0 v0) (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (C (R (M v0 (M v0 v316))) h310) (C (T (T (C (T (T (T (T (T (T (T (T (T (T (T (T (T h274 h308) h306) h309) h305) h87) h129) h128) h126) h177) h247) h270) h345) (C (T (T (T (T (T (T (T (T (T (T h29 h21) h63) h56) h73) h71) h50) h263) h328) h317) h355) (T (T (T (T (T (T (T (T (T (T (T (T (T (T h303 h302) h301) h300) h299) h298) h252) h77) h75) h70) h69) h68) h53) h25) h23))) (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (C (T (T (T (T (T (T (T (T (T (T h274 h308) h306) h309) h305) h15) h5) h333) h347) h344) h353) h332) (S (h v312 v2 v3))) h303) h302) h301) h300) h299) h298) h252) h77) h75) h70) h69) h68) h53) h25) h23)) (S (h v316 v2 y))) h355) h314)) (C (R (M v2 v354)) h310)) (C (T (T (T (T (T (T (T (T (T (T (T (T (T (C h34 (T h348 h331)) h315) h311) h248) h51) h339) h338) h337) (C (T (T (T h324 h323) h335) h346) h34)) (C (R (M v3 (M v3 v312))) h314)) (C h343 h310)) (C (R (M v0 (M v0 v312))) h314)) (C h352 h310)) (C (R v354) h314)) h314)) (S (h v312 v2 v0))) h303) h302) h301) h300) h299) h298) h252) h77) h75) h70) h69) h68) h53) h25) h23) (T (T (T (T (T (T (T (T (T (T (T h274 h308) h306) h309) h305) h15) h5) h333) h347) h344) h353) (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h348 h331) h303) h302) h301) h300) h299) h298) h252) h77) h75) h70) h69) h68) h53) h25) h23) h329)))) h6) h6)) (S (h v316 y v3))) h315) h311) h248) h51) h48) h46) h44) h42) h22) h18

