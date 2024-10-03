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
theorem Equation1571_implies_Equation2132 (G: Type _) [Magma G] (h: Equation1571 G) : Equation2132 G := fun x y z =>
  let v0 := M z z
  let v1 := M y y
  let v2 := M v1 x
  let v3 := M v2 v0
  have h4 := h v3 v3 (M v2 (M z v0))
  have h5 := S h4
  have h6 := h z v2 v0
  have h7 := R v3
  have h8 := C h6 (C h7 h6)
  have h9 := h z v2 z
  have h10 := h v3 v2 z
  have h11 := S h10
  let v12 := M v2 z
  have h13 := R v12
  have h14 := h v12 v12 (M v2 (M v3 z))
  have h15 := h z v1 x
  have h16 := S h15
  have h17 := R v2
  have h18 := C h16 (T (T (C h17 h16) h14) (C h11 (T (C h13 h11) (S h9))))
  have h19 := h v2 v2 (M v1 (M z x))
  let v20 := M v1 v2
  have h21 := h v2 v2 v20
  have h22 := S h21
  have h23 := h v1 v1 x
  have h24 := C h23 (C h17 h23)
  let v25 := M v2 v1
  let v26 := M v1 v25
  have h27 := h v26 v2 v3
  have h28 := S h27
  have h29 := R (M v26 v3)
  have h30 := S h19
  have h31 := C h15 (T (T (C h10 (T h9 (C h13 h10))) (S h14)) (C h17 h15))
  have h32 := S h6
  have h33 := C h32 (C h7 h32)
  have h34 := T (T (T h4 h33) h31) h30
  have h35 := C h34 h29
  have h36 := h v2 v1 v1
  have h37 := S h36
  have h38 := S h23
  have h39 := C h38 (C h17 h38)
  have h40 := T h21 h39
  have h41 := h v1 v2 v2
  have h42 := S h41
  let v43 := M v2 v2
  have h44 := R v43
  have h45 := C h44 h23
  have h46 := h v43 v43 v1
  have h47 := C (T h46 (C (T h45 h42) (T (C h44 (T (T h45 h42) h23)) h42))) h40
  have h48 := C h40 (T (T (T (T (T h47 h37) h19) h18) h8) h5)
  have h49 := R (M v43 v2)
  have h50 := C h34 h49
  have h51 := T h24 h22
  have h52 := C h44 h38
  have h53 := C (T (C (T h41 h52) (T h41 (C h44 (T (T h38 h41) h52)))) (S h46)) h51
  have h54 := T h36 h53
  have h55 := T (T (T h19 h18) h8) h5
  have h56 := C h55 h54
  have h57 := C h55 (T (T h56 h50) h48)
  have h58 := h v2 v1 x
  have h59 := S h58
  have h60 := C h59 (C h17 h59)
  let v61 := M v2 x
  have h62 := h v2 v2 (M v1 v61)
  let v63 := M v2 v3
  have h64 := R v63
  have h65 := C h64 (T (T (T (T (T (T (T h4 h33) h31) h30) h62) h60) h57) h35)
  have h66 := h v63 v0 v3
  have h67 := S h66
  have h68 := S h62
  have h69 := C h58 (C h17 h58)
  have h70 := T h47 h37
  have h71 := C h34 h70
  have h72 := C h55 h49
  have h73 := C h51 (T (T (T (T (T h4 h33) h31) h30) h36) h53)
  have h74 := C h34 (T (T h73 h72) h71)
  have h75 := C h55 h29
  have h76 := C h64 (T (T (T (T (T (T (T h75 h74) h69) h68) h19) h18) h8) h5)
  have h77 := R v0
  have h78 := C h77 (T (T (T (T (T h47 h37) h21) h39) h27) h76)
  have h79 := C h77 h54
  have h80 := h v0 v1 x
  have h81 := S h80
  let v82 := M v0 x
  have h83 := h v2 v2 (M v1 v82)
  have h84 := T h83 (C h81 (C h17 h81))
  have h85 := C h84 (T h79 h78)
  have h86 := h v2 z z
  have h87 := S h86
  have h88 := C h87 (C h77 h87)
  have h89 := h v0 v0 (M z v12)
  have h90 := T (T (T h89 h88) h85) h67
  have h91 := C h90 (T (T (T (T (T (T (T h65 h28) h24) h22) h62) h60) h57) h35)
  let v92 := M v0 v2
  have h93 := h v92 v3 v0
  have h94 := S h93
  have h95 := S h89
  have h96 := C h86 (C h77 h86)
  have h97 := C h77 h70
  have h98 := C h77 (T (T (T (T (T h65 h28) h24) h22) h36) h53)
  have h99 := T (C h80 (C h17 h80)) (S h83)
  have h100 := C h99 (T h98 h97)
  have h101 := h v63 v3 v2
  have h102 := S h101
  have h103 := C h64 (T (T (T h75 h74) h69) h68)
  have h104 := C (T (T (T (T (T h24 h22) h19) h18) h8) h5) (T (T (T (T (T (T (T h4 h33) h31) h30) h21) h39) h27) h103)
  let v105 := M v3 v2
  have h106 := R v105
  have h107 := C h106 (T (T h50 h48) h104)
  have h108 := h v43 v3 v2
  have h109 := h v43 v0 v2
  have h110 := S h109
  have h111 := T (T (T h66 h100) h96) h95
  have h112 := C h111 (T (T (T (T (T (T (T h75 h74) h69) h68) h21) h39) h27) h76)
  have h113 := R v92
  have h114 := C h113 (T (T (T (T (T (T (T (T h4 h33) h31) h30) h21) h39) h27) h112) h98)
  have h115 := T (T (T (T (T (T (T (T h114 h110) h108) h107) h102) h66) h100) h96) h95
  have h116 := C (T (T (T (T (T h21 h39) h27) h112) h98) h97) h115
  have h117 := C h113 (T (T (T (T (T (T (T (T h78 h91) h28) h24) h22) h19) h18) h8) h5)
  have h118 := S h108
  have h119 := C h64 (T (T (T h62 h60) h57) h35)
  have h120 := C (T (T (T (T (T h4 h33) h31) h30) h21) h39) (T (T (T (T (T (T (T h119 h28) h24) h22) h19) h18) h8) h5)
  have h121 := C h106 (T (T h120 h73) h72)
  have h122 := h v63 v3 v3
  let v123 := M v3 v3
  have h124 := h v123 v123 v2
  have h125 := h v2 v2 v0
  have h126 := S h125
  have h127 := R v123
  have h128 := C h127 h126
  have h129 := h v2 v3 v3
  have h130 := T (T (T (T (T (T (T (T h89 h88) h85) h67) h101) h121) h118) (C (T h129 h128) (T h129 (C h127 (T (T h126 h129) h128))))) (S h124)
  have h131 := C h99 (T (T (T (T (T (T (C h130 (T (T (T (T (T (T h114 h110) h56) h50) h48) h104) (C h7 (T h119 h76)))) (S h122)) h101) h121) h118) h109) h117)
  have h132 := h v92 v0 v3
  have h133 := C (T (T (T (T (T (T (T (T (T h79 h78) h91) h28) h24) h22) h19) h18) h8) h5) (T (T (T (T (T (T (T (T (T (T (T (T h4 h33) h31) h30) h21) h39) h27) h112) h98) h97) h132) h131) h116)
  let v134 := M v3 v0
  have h135 := R v134
  have h136 := C h135 (T (T (T (T (T (T (T (T (T h89 h88) h85) h67) h101) h121) h118) h109) h117) h133)
  have h137 := C h7 (T (T (T (T h136 h94) h132) h131) h116)
  have h138 := C h135 h137
  have h139 := h v134 v3 v0
  have h140 := C h135 h55
  have h141 := h v134 v3 v2
  have h142 := S h141
  have h143 := C h135 h34
  have h144 := S h139
  have h145 := S h132
  have h146 := S h129
  have h147 := C h127 h125
  have h148 := T (T (T (T (T (T (T (T h124 (C (T h147 h146) (T (C h127 (T (T h147 h146) h125)) h146))) h108) h107) h102) h66) h100) h96) h95
  have h149 := C h84 (T (T (T (T (T (T h114 h110) h108) h107) h102) h122) (C h148 (T (T (T (T (T (T (C h7 (T h65 h103)) h120) h73) h72) h71) h109) h117)))
  have h150 := T (T (T (T (T (T (T (T h89 h88) h85) h67) h101) h121) h118) h109) h117
  have h151 := C (T (T (T (T (T h79 h78) h91) h28) h24) h22) h150
  have h152 := C (T (T (T (T (T (T (T (T (T h4 h33) h31) h30) h21) h39) h27) h112) h98) h97) (T (T (T (T (T (T (T (T (T (T (T (T h151 h149) h145) h79) h78) h91) h28) h24) h22) h19) h18) h8) h5)
  have h153 := C h135 (T (T (T (T (T (T (T (T (T h152 h114) h110) h108) h107) h102) h66) h100) h96) h95)
  have h154 := C h7 (T (T (T (T h151 h149) h145) h93) h153)
  have h155 := C h135 h154
  have h156 := T (T (T (T (T (T (T (T (T (T (T (T h4 h33) h31) h30) h21) h39) h27) h112) h98) h97) h93) h155) h144
  have h157 := C h156 (T (T (T (T (T (T (T (T (T (T (T h136 h94) h79) h78) h91) h28) h24) h22) h19) h18) h8) h5)
  have h158 := T (T (T (T (T (T (T (T (T (T (T (T h139 h138) h94) h79) h78) h91) h28) h24) h22) h19) h18) h8) h5
  have h159 := C h158 (T (T (T (T (T (T (T (T (T (T (T (T h89 h88) h85) h67) h101) h121) h118) h109) h117) h133) h154) h157) h143)
  have h160 := C h106 (T (T (T (T (T (T (T (T h21 h39) h27) h112) h98) h97) h93) h153) h159)
  have h161 := C h156 (T (T (T (T (T (T (T (T (T (T h160 h142) h139) h138) h94) h79) h78) h91) h28) h24) h22)
  have h162 := C h158 (T (T (T (T (T (T (T (T (T (T (T h4 h33) h31) h30) h21) h39) h27) h112) h98) h97) h93) h153)
  have h163 := C h156 (T (T (T (T (T (T (T (T (T (T (T (T h140 h162) h137) h152) h114) h110) h108) h107) h102) h66) h100) h96) h95)
  have h164 := C h106 (T (T (T (T (T (T (T (T h163 h136) h94) h79) h78) h91) h28) h24) h22)
  have h165 := h v3 v3 v63
  have h166 := S h165
  have h167 := C h125 (C h7 h125)
  have h168 := h v105 v3 v2
  have h169 := S h168
  have h170 := C h158 (T (T (T (T (T (T (T (T (T (T h21 h39) h27) h112) h98) h97) h93) h155) h144) h141) h164)
  have h171 := C h106 (T (T (T (T (T (T (T (T (T (T (T (T (T h89 h88) h85) h67) h101) h121) h118) h109) h117) h133) h154) h157) h143) h170)
  have h172 := C h34 (T h171 h169)
  have h173 := C h158 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h172 h167) h166) h4) h33) h31) h30) h21) h39) h27) h112) h98) h97) h93) h155) h144) h141) h164)
  have h174 := h v105 v3 v0
  have h175 := T (T (T (T (T h171 h169) h174) h173) h161) h140
  have h176 := R v1
  have h177 := C h106 (T (T (T (T (T (T (T (T (T (T (T (T (T h161 h140) h162) h137) h152) h114) h110) h108) h107) h102) h66) h100) h96) h95)
  have h178 := h v105 x v0
  have h179 := S h178
  have h180 := S h174
  have h181 := C h55 (T h168 h177)
  have h182 := C h126 (C h7 h126)
  have h183 := C h156 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h160 h142) h139) h138) h94) h79) h78) h91) h28) h24) h22) h19) h18) h8) h5) h165) h182) h181)
  have h184 := h v43 x v2
  have h185 := S h184
  have h186 := C h106 (T (T (T (T (T (T (T (T (T (T (T (T h4 h33) h31) h30) h21) h39) h27) h112) h98) h97) h93) h153) h159)
  have h187 := T (T (T (T (T (T (T (T (T (T (T (T h186 h142) h139) h138) h94) h79) h78) h91) h28) h24) h22) h36) h53
  have h188 := R x
  have h189 := C h188 h187
  have h190 := C h106 (T (T (T (T (T (T (T (T (T (T (T (T h163 h136) h94) h79) h78) h91) h28) h24) h22) h19) h18) h8) h5)
  have h191 := T (T (T (T (T (T (T (T (T (T (T (T (T (T h4 h33) h31) h30) h21) h39) h27) h112) h98) h97) h93) h155) h144) h141) h190
  have h192 := h x z v3
  have h193 := S h192
  let v194 := M x v3
  have h195 := h v194 v3 v1
  have h196 := S h195
  have h197 := h v1 v1 (M y (M x y))
  have h198 := S h197
  have h199 := h x y y
  have h200 := C h199 (C h176 h199)
  have h201 := C h188 h70
  have h202 := R v194
  have h203 := C h202 (T (T (T h189 h201) h200) h198)
  have h204 := h v105 x v3
  have h205 := C h55 (T (T (T h171 h169) h204) h203)
  have h206 := R (M v105 v0)
  have h207 := C h34 h206
  let v208 := M v3 v1
  have h209 := R v208
  have h210 := C h209 (T (T (T (T (T (T (T (T h19 h18) h8) h5) h165) h182) h181) h207) h205)
  have h211 := R z
  have h212 := C h55 h206
  have h213 := S h204
  have h214 := T (T (T (T (T (T (T (T (T (T (T (T h47 h37) h21) h39) h27) h112) h98) h97) h93) h155) h144) h141) h190
  have h215 := C h188 h214
  have h216 := C h188 h54
  have h217 := S h199
  have h218 := C h217 (C h176 h217)
  have h219 := C h202 (T (T (T h197 h218) h216) h215)
  have h220 := C h34 (T (T (T h219 h213) h168) h177)
  have h221 := C h209 (T (T (T (T (T (T (T (T h220 h212) h172) h167) h166) h4) h33) h31) h30)
  have h222 := h v194 v0 v1
  have h223 := S h222
  have h224 := h v105 v0 v3
  have h225 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h174 h173) h161) h140) h162) h137) h152) h114) h110) h108) h107) h102) h66) h100) h96) h95) h191
  have h226 := h v105 v2 v3
  let v227 := M v0 v1
  have h228 := R v227
  have h229 := C h228 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h89 h88) h85) h67) h101) h121) h118) h109) h117) h133) h154) h157) h143) h170) h183) h180) h226) (C h111 (T (T (T (C h84 h225) (S h224)) h204) h203)))
  have h230 := T (T (T h229 h223) h195) h221
  have h231 := T (T (T (T (T (T (T (T (T (T (T (T (T (T h186 h142) h139) h138) h94) h79) h78) h91) h28) h24) h22) h19) h18) h8) h5
  have h232 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h89 h88) h85) h67) h101) h121) h118) h109) h117) h133) h154) h157) h143) h170) h183) h180) h231
  have h233 := C h228 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (C h90 (T (T (T h219 h213) h224) (C h99 h232))) (S h226)) h174) h173) h161) h140) h162) h137) h152) h114) h110) h108) h107) h102) h66) h100) h96) h95)
  have h234 := h v208 v2 v2
  have h235 := R (M v227 v0)
  have h236 := h v194 v2 v1
  have h237 := R (M v194 v1)
  have h238 := R v25
  have h239 := h v25 v3 v2
  have h240 := R (M z v3)
  have h241 := C h240 (T (T (C h211 (T (T (T (C (T (T h239 (C (T (T (T (T (T (T (T (T h174 h173) h161) h140) h162) h137) h152) h114) h110) (T (T (C h34 (T (T (T (C h238 (T (T (T (T (T (T (T (T (T h19 h18) h8) h5) h165) h182) h181) h207) h205) (C h34 h237))) (S h236)) h222) h233)) (C h55 h235)) (C h34 h230)))) (S h234)) (T (T (T (T h165 h182) h181) h207) h205)) h196) h222) h233)) (C h211 h230)) (C h211 (T h210 h196)))
  have h242 := h v25 z v3
  have h243 := C (T (T h242 h241) h193) h191
  have h244 := h v25 v3 v3
  have h245 := S h244
  have h246 := S h242
  have h247 := T (T (T h210 h196) h222) h233
  have h248 := C h240 (T (T (C h211 (T h195 h221)) (C h211 h247)) (C h211 (T (T (T h229 h223) h195) (C (T (T h234 (C (T (T (T (T (T (T (T (T h109 h117) h133) h154) h157) h143) h170) h183) h180) (T (T (C h55 h247) (C h34 h235)) (C h55 (T (T (T h229 h223) h236) (C h238 (T (T (T (T (T (T (T (T (T (C h55 h237) h220) h212) h172) h167) h166) h4) h33) h31) h30))))))) (S h239)) (T (T (T (T h220 h212) h172) h167) h166)))))
  have h249 := C (T (T h192 h248) h246) h231
  have h250 := C h55 (T (T (T (T h197 h218) h216) h215) h249)
  have h251 := C h130 (T (T (T h192 h248) h246) h250)
  have h252 := C (T h251 h245) h7
  have h253 := h v82 v0 v3
  have h254 := S h253
  have h255 := C h34 (T (T (T (T h243 h189) h201) h200) h198)
  have h256 := C h148 (T (T (T h255 h242) h241) h193)
  have h257 := C (T h244 h256) h7
  have h258 := C h84 (C h77 (T (T (T (T (T h197 h218) h216) h215) h249) h257))
  have h259 := C (T h258 h254) h7
  have h260 := C (T h197 h218) (T (T (T h259 h252) h243) h189)
  let v261 := M v2 v227
  have h262 := h v261 v2 v3
  have h263 := S h262
  have h264 := R (M v261 v3)
  have h265 := C h99 (C h77 (T (T (T (T (T h252 h243) h189) h201) h200) h198))
  have h266 := C (T h253 h265) h7
  have h267 := h v261 v1 v3
  have h268 := S h267
  have h269 := C (T h200 h198) (T (T (T h215 h249) h257) h266)
  have h270 := T (T (T (T (T (T (T (T h89 h88) h85) h67) h101) h121) h118) h184) h269
  let v271 := M v1 v3
  have h272 := h v271 v3 v0
  have h273 := S h272
  have h274 := T (T (T (T (T (T (T (T h260 h185) h108) h107) h102) h66) h100) h96) h95
  have h275 := R v271
  have h276 := C (T (T (T (T (T (T (T (T h21 h39) h27) h112) h98) h97) h93) h155) h144) (C h55 (T (T (T (T (T (T (T (T h192 h248) h246) h244) h256) h253) h265) h267) (C h275 h274)))
  have h277 := C (T h276 h273) h270
  have h278 := C h90 (T (T (T (T (T (T (T (T (T h277 h268) h258) h254) h251) h245) h250) (C h7 h257)) (C h7 h266)) (C h34 h264))
  have h279 := C (T (T (T (T (T (T (T (T h139 h138) h94) h79) h78) h91) h28) h24) h22) (C h34 (T (T (T (T (T (T (T (T (C h275 h270) h268) h258) h254) h251) h245) h242) h241) h193))
  have h280 := C (T h272 h279) h274
  have h281 := h z v0 v0
  have h282 := S h281
  have h283 := h z z z
  let v284 := M v0 v0
  have h285 := R v284
  have h286 := C h285 h283
  have h287 := h v284 v284 z
  have h288 := C (T h287 (C (T h286 h282) (T (C h285 (T (T h286 h282) h283)) h282))) (T (T (T h278 h263) h267) h280)
  let v289 := M v2 v61
  have h290 := h v289 v0 v0
  have h291 := C h176 (C (T (T (T h290 h288) h278) h263) h7)
  have h292 := T (T (T (T (T (T (T (T (T (T (T (T h272 h279) h290) h288) h278) h263) h258) h254) h251) h245) h242) h241) h193
  have h293 := C h292 (T (T (T (T (T (T (T (T (T (T (T (T (T h291 h260) h185) h109) h117) h133) h154) h157) h143) h170) h183) h180) h168) h177)
  have h294 := h v289 v1 v3
  have h295 := S h290
  have h296 := C h111 (T (T (T (T (T (T (T (T (T (C h55 h264) (C h7 h259)) (C h7 h252)) h255) h244) h256) h253) h265) h267) h280)
  have h297 := S h283
  have h298 := C h285 h297
  have h299 := C (T (C (T h281 h298) (T h281 (C h285 (T (T h297 h281) h298)))) (S h287)) (T (T (T h277 h268) h262) h296)
  have h300 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h192 h248) h246) h244) h256) h253) h265) h262) h296) h299) h295) h294) h293) (C h188 h175)) (C h188 (T (T h162 h137) h152))) (C h188 h115)) (T (T (T (T (T (T (T (T (T (T (T (T h192 h248) h246) h244) h256) h253) h265) h262) h296) h299) h295) h294) h293)
  have h301 := h (M x x) v1 v3
  have h302 := S h301
  have h303 := S h294
  have h304 := T (T (T (T (T (T (T (T (T (T (T (T h192 h248) h246) h244) h256) h253) h265) h262) h296) h299) h295) h276) h273
  have h305 := C h304 (T (T (T (T (T (T (T (T (T (T (T (T (T h171 h169) h174) h173) h161) h140) h162) h137) h152) h114) h110) h184) h269) (C h176 (C (T (T (T h262 h296) h299) h295) h7)))
  have h306 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (C h188 h150) (C h188 (T (T h133 h154) h157))) (C h188 (T (T (T (T (T h143 h170) h183) h180) h168) h177))) h305) h303) h290) h288) h278) h263) h258) h254) h251) h245) h242) h241) h193) (T (T (T (T (T (T (T (T (T (T (T (T h305 h303) h290) h288) h278) h263) h258) h254) h251) h245) h242) h241) h193)
  have h307 := T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h89 h88) h85) h67) h101) h121) h118) h109) h117) h133) h154) h157) h143) h170) h183) h180) h178) h306
  have h308 := C h307 h231
  have h309 := C h304 (T (T (C h176 h54) (C h176 h214)) (C h176 (T h225 h308)))
  let v310 := M x v20
  have h311 := h v310 v2 v3
  have h312 := S h311
  have h313 := T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h300 h179) h174) h173) h161) h140) h162) h137) h152) h114) h110) h108) h107) h102) h66) h100) h96) h95
  have h314 := C h313 h191
  have h315 := T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h314 h232) h186) h142) h139) h138) h94) h79) h78) h91) h28) h24) h22) h19) h18) h8) h5
  have h316 := T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h4 h33) h31) h30) h21) h39) h27) h112) h98) h97) h93) h155) h144) h141) h190) h225) h308
  have h317 := T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h309 h302) h300) h179) h174) h173) h161) h140) h162) h137) h152) h114) h110) h108) h107) h102) h66) h100) h96) h95
  have h318 := C h292 (T (T (C h176 (T h314 h232)) (C h176 h187)) (C h176 h70))
  have h319 := T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h89 h88) h85) h67) h101) h121) h118) h109) h117) h133) h154) h157) h143) h170) h183) h180) h178) h306) h301) h318
  have h320 := h v310 v0 v3
  have h321 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h309 h302) h300) h179) h174) h173) h161) h140) h162) h137) h152) h114) h110) h108) h107) h102) (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h89 h88) h85) h67) h101) h121) h118) h109) h117) h133) h154) h157) h143) h170) h183) h180) h178) h306) h301) h318) h320) (C h99 (C h319 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (C h317 h316) (C h307 h315)) h314) h232) h186) h142) h139) h138) h94) h79) h78) h91) h28) h24) h22) h19) h18) h8) h5))))
  have h322 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h101 h121) h118) h109) h117) h133) h154) h157) h143) h170) h183) h180) h178) h306) h301) h318) (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (C h84 (C h317 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h4 h33) h31) h30) h21) h39) h27) h112) h98) h97) h93) h155) h144) h141) h190) h225) h308) (C h313 h316)) (C h319 h315)))) (S h320)) h309) h302) h300) h179) h174) h173) h161) h140) h162) h137) h152) h114) h110) h108) h107) h102) h66) h100) h96) h95)
  have h323 := h y z z
  have h324 := R y
  T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h192 h248) h246) h244) h256) h253) h265) h262) h296) h299) h295) h294) (C h292 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h291 h260) h185) h109) h117) h133) h154) h157) h143) h170) h183) h180) h178) h306) h301) h318) h311) h322))) (C h304 (T (T (T (T (T h321 h312) (h v310 y y)) (C h176 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (C h324 (C h317 h324)) (C h323 (C h77 h323))) (S (h v0 v0 (M z (M y z))))) h89) h88) h85) h67) h101) h121) h118) h109) h117) h133) h154) h157) h143) h170) h183) h180) h178) h306) h301) h318) h311) h322))) (C h176 (T (T (T (T (T (T (T h321 h312) h309) h302) h300) h179) h168) h177))) (C h176 h175)))) (S (h v134 v1 v3))) h139) h138) h94) h79) h78) h91) h28) h24) h22) h19) h18) h8) h5

