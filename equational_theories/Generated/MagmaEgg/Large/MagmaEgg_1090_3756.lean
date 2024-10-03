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
theorem Equation1090_implies_Equation3756 (G: Type _) [Magma G] (h: Equation1090 G) : Equation3756 G := fun x y z =>
  let v0 := M z z
  let v1 := M y x
  let v2 := M v1 v0
  have h3 := h v2 z z
  have h4 := S h3
  let v5 := M (M z (M v0 x)) x
  have h6 := h z v0 v5
  have h7 := S h6
  have h8 := R v5
  have h9 := h z v0 x
  have h10 := h z v2 z
  have h11 := S h10
  have h12 := R z
  have h13 := h v1 z z
  have h14 := C h13 h12
  have h15 := R v2
  have h16 := C h15 h14
  have h17 := T h16 h11
  have h18 := C (S h13) h12
  have h19 := C h15 h18
  have h20 := T h10 h19
  have h21 := C h20 h12
  have h22 := R v0
  have h23 := C h22 (T h9 (C (T h21 (C h17 h9)) h8))
  have h24 := T h23 h7
  let v25 := M x y
  let v26 := M v2 v0
  have h27 := h v26 v25 y
  have h28 := S h27
  have h29 := R y
  have h30 := h y v25 x
  have h31 := S h30
  let v32 := M v25 x
  let v33 := M (M y v32) x
  have h34 := R v33
  have h35 := R x
  have h36 := R v25
  have h37 := C h36 (T (C (C h35 h31) h34) h31)
  have h38 := h x v25 v33
  have h39 := T h38 h37
  have h40 := h v0 v2 x
  have h41 := S h40
  let v42 := M (M v0 (M v2 x)) x
  have h43 := R v42
  have h44 := h v2 v1 z
  have h45 := S h44
  have h46 := R v1
  have h47 := C h15 (T (C (T (C h46 (T h41 h21)) h45) h43) h41)
  have h48 := h v1 v2 v42
  have h49 := T h48 h47
  have h50 := C h49 h39
  have h51 := h x v1 x
  have h52 := S h51
  let v53 := M v1 x
  let v54 := M (M x v53) x
  have h55 := R v54
  have h56 := C h46 (T (C (C h29 h52) h55) h52)
  have h57 := h y v1 v54
  have h58 := C (T (T h57 h56) h50) h29
  have h59 := C h36 h58
  let v60 := M y y
  let v61 := M v25 v60
  have h62 := h v61 x x
  have h63 := S h62
  have h64 := S h38
  have h65 := C h36 (T h30 (C (C h35 h30) h34))
  have h66 := S h57
  have h67 := C h46 (T h51 (C (C h29 h51) h55))
  have h68 := T h67 h66
  have h69 := h v25 y y
  have h70 := S h69
  have h71 := R v61
  have h72 := C h71 h68
  have h73 := R v53
  have h74 := T h65 h64
  have h75 := S h48
  have h76 := C h17 h12
  have h77 := C h15 (T h40 (C (T h44 (C h46 (T h76 h40))) h43))
  have h78 := T h77 h75
  have h79 := C h78 h74
  have h80 := C (T (T h79 h67) h66) h29
  have h81 := C h36 h80
  have h82 := T h27 h81
  have h83 := C h82 h73
  have h84 := T h57 h56
  have h85 := C h49 h84
  have h86 := T (T h85 h83) h72
  have h87 := C h29 h86
  have h88 := T h87 h70
  have h89 := C h88 h68
  have h90 := C (T (T h89 h65) h64) h35
  have h91 := T (T (T h48 h47) h27) h81
  have h92 := C h91 h90
  let v93 := M v1 y
  let v94 := M y v93
  have h95 := h v94 v1 x
  have h96 := C h78 h68
  have h97 := T h59 h28
  have h98 := C h97 h73
  have h99 := C h71 h84
  have h100 := T (T h99 h98) h96
  have h101 := C h29 h100
  have h102 := C (T (T (T h69 h101) h95) h92) h35
  have h103 := C h35 h102
  let v104 := M x v32
  have h105 := h v104 v25 x
  have h106 := S h105
  have h107 := S h95
  have h108 := T h69 h101
  have h109 := C h108 h84
  have h110 := C (T (T h38 h37) h109) h35
  have h111 := T (T (T h59 h28) h77) h75
  have h112 := C h111 h110
  have h113 := C (T (T (T h112 h107) h87) h70) h35
  have h114 := T (T (T (T (T h103 h63) h59) h28) h77) h75
  have h115 := C h114 h110
  have h116 := C h35 h113
  have h117 := T (T (T (T (T h48 h47) h27) h81) h62) h116
  have h118 := C h117 h90
  have h119 := R (M v25 y)
  have h120 := C h97 h119
  have h121 := T h103 h63
  have h122 := C h121 h119
  have h123 := R v104
  have h124 := C h123 h39
  have h125 := T (T (T (T (T h124 h122) h120) h79) h67) h66
  have h126 := C h125 h86
  have h127 := C (T h126 h101) h84
  have h128 := C h123 h74
  have h129 := T h62 h116
  have h130 := C h129 h119
  have h131 := C h82 h119
  have h132 := T (T (T (T (T h57 h56) h50) h131) h130) h128
  have h133 := C h132 h100
  have h134 := h v94 v1 y
  have h135 := S h134
  have h136 := C h125 h74
  have h137 := C h108 (T (T (T (T (C (T (T (T (T (T (T h136 h48) h47) h27) h81) h62) h116) h84) (C h121 h68)) h99) h98) h96)
  let v138 := M v104 x
  have h139 := h v138 v25 y
  have h140 := C (T h139 h137) h68
  have h141 := C h128 h84
  have h142 := C h130 h29
  have h143 := C h131 h29
  have h144 := T (T (T (T h58 h143) h142) h141) h140
  have h145 := C h114 h144
  have h146 := C (T (T (T h145 h135) h87) h133) h29
  have h147 := R v60
  have h148 := C h129 h147
  have h149 := C h148 h29
  have h150 := C h91 h147
  have h151 := C h150 h29
  have h152 := h (M (M v1 v60) y) v1 x
  have h153 := C h111 h147
  have h154 := C h153 h29
  have h155 := C h121 h147
  have h156 := C h155 h29
  have h157 := C h120 h29
  have h158 := C h122 h29
  have h159 := C h124 h68
  have h160 := S h139
  have h161 := C (T (T (T (T (T (T h103 h63) h59) h28) h77) h75) (C h132 h39)) h68
  have h162 := C h129 h84
  have h163 := C h88 (T (T (T (T h85 h83) h72) h162) h161)
  have h164 := C (T h163 h160) h84
  have h165 := T (T (T (T h164 h159) h158) h157) h80
  have h166 := C h117 h165
  have h167 := C (T (T (T h126 h101) h134) h166) h29
  have h168 := C (T h87 h133) h68
  have h169 := C h36 (T h110 (C (T (T (T (T (T h168 h167) h156) h154) h152) (C h117 (T (T (C (T (T (T (T (C (T (T (T (T (T (T h151 h149) h146) h127) h89) h65) h64) h68) h69) h101) h95) h118) h35) (C (T h115 h92) h35)) h113))) h35))
  have h170 := R (M v0 z)
  have h171 := C h36 (T (C (T (T (T (T (T (C h114 (T (T h102 (C (T h112 h118) h35)) (C (T (T (T (T h115 h107) h87) h70) (C (T (T (T (T (T (T h38 h37) h109) h168) h167) h156) h154) h84)) h35))) (S h152)) h151) h149) h146) h127) h35) h90)
  have h172 := T h105 h171
  have h173 := S h9
  have h174 := C h22 (T (C (T (C h20 h173) h76) h8) h173)
  have h175 := T h6 h174
  have h176 := C h12 (T (T (T (T (C h49 h175) (C h82 h170)) (C h129 h170)) (C h172 h170)) (C (T (T (T (T (T h169 h106) h103) h63) h59) h28) h24))
  let v177 := M z (M v1 z)
  have h178 := T h176 h4
  have h179 := C h178 h14
  have h180 := C (T h179 h19) h12
  have h181 := T h169 h106
  have h182 := C h12 (T (T (T (T (C (T (T (T (T (T h27 h81) h62) h116) h105) h171) h175) (C h181 h170)) (C h121 h170)) (C h97 h170)) (C h78 h24))
  have h183 := T h3 h182
  have h184 := C h183 h18
  have h185 := h z v1 z
  have h186 := S h185
  have h187 := R v177
  have h188 := C h78 h21
  have h189 := C h97 h22
  have h190 := C h121 h22
  have h191 := C h181 h22
  have h192 := C h172 h22
  have h193 := C h129 h22
  have h194 := C h82 h22
  have h195 := C h49 h76
  have h196 := T (T (T (T (T (T (T h169 h106) h103) h63) h59) h28) h77) h75
  have h197 := C h196 (T (T (T (T (T (C (T h44 h195) h12) (C h194 h12)) (C h193 h12)) (C h192 h12)) (C (T (T (T (T (T (T h191 h190) h189) h188) h45) h3) h182) h175)) (C h187 h24))
  have h198 := C (T (T (T h197 h186) h10) h184) h12
  have h199 := T (T (T (T (T (T (T h48 h47) h27) h81) h62) h116) h105) h171
  have h200 := C h199 (T (T (T (T (T (C h187 h175) (C (T (T (T (T (T (T h176 h4) h44) h195) h194) h193) h192) h24)) (C h191 h12)) (C h190 h12)) (C h189 h12)) (C (T h188 h45) h12))
  let v201 := M v2 z
  have h202 := R v201
  have h203 := C (C h172 h202) h12
  have h204 := C (C h129 h202) h12
  have h205 := C (C h82 h202) h12
  have h206 := C (C h49 h202) h12
  have h207 := T (T (T (T (T (T h206 h205) h204) h203) h198) h180) h76
  have h208 := T (T (T (C (T (T (T (T (C h207 h24) h23) h7) h185) h200) h12) h198) h180) h76
  have h209 := h v177 v1 z
  have h210 := S h209
  let v211 := M (M v1 v201) z
  have h212 := h v211 v0 z
  have h213 := S h212
  have h214 := C (C h78 h202) h12
  have h215 := C (C h97 h202) h12
  have h216 := C (C h121 h202) h12
  have h217 := C (C h181 h202) h12
  have h218 := C (T (T (T h179 h11) h185) h200) h12
  have h219 := C (T h16 h184) h12
  have h220 := T (T (T (T (T (T h21 h219) h218) h217) h216) h215) h214
  have h221 := T (T (T h21 h219) h218) (C (T (T (T (T h197 h186) h6) h174) (C h220 h175)) h12)
  have h222 := C h22 h221
  have h223 := C h114 (T (T (T (T (T (T h222 h213) h206) h205) h204) h203) h198)
  have h224 := C h22 h208
  let v225 := M x x
  let v226 := M v25 v225
  have h227 := h v226 v0 v0
  have h228 := S h227
  have h229 := R (M v0 v0)
  have h230 := C h117 (T (T (T (T (T (T h218 h217) h216) h215) h214) h212) h224)
  have h231 := h v26 v2 z
  have h232 := T h231 (C (T (T (T (T h3 h182) h209) h230) (C h172 h229)) (T (T (T (T (T h205 h204) h203) h198) h180) h76))
  have h233 := T (T (T (T (C (T (T (T (C h207 h232) h228) h169) h106) (T (T (T (T (T (T (T (T h21 h219) h218) h217) h216) h215) h214) h212) h224)) h223) h210) h176) h4
  have h234 := C h183 h233
  have h235 := h v211 v2 v0
  have h236 := C (T (T (T (T (T (T (T (T h21 h219) h218) h217) h216) h215) h214) h235) h234) h208
  have h237 := S h235
  have h238 := T (C (T (T (T (T (C h181 h229) h223) h210) h176) h4) (T (T (T (T (T h21 h219) h218) h217) h216) h215)) (S h231)
  have h239 := T (T (T (T h3 h182) h209) h230) (C (T (T (T h105 h171) h227) (C h220 h238)) (T (T (T (T (T (T (T (T h222 h213) h206) h205) h204) h203) h198) h180) h76))
  have h240 := h v177 v0 v2
  have h241 := C h178 h239
  have h242 := C (T (T (T (T (T (T (T (T h241 h237) h206) h205) h204) h203) h198) h180) h76) h221
  have h243 := C h183 h15
  have h244 := C h243 h22
  have h245 := C (T (T (T (T h244 h242) h213) h235) h234) (T (T (T (T (T (T (T (T (T h243 h241) h237) h206) h205) h204) h203) h198) h180) h76)
  have h246 := C (T (T (T (T (T (T (T (T (T h245 h242) h213) h206) h205) h204) h203) h198) h180) h76) h15
  have h247 := h (M (M v2 v2) v0) v2 v2
  have h248 := C h178 h15
  have h249 := C h248 h22
  have h250 := C (T (T (T (T h241 h237) h212) h236) h249) (T (T (T (T (T (T (T (T (T h21 h219) h218) h217) h216) h215) h214) h235) h234) h248)
  have h251 := C (T (T (T (T (T (T (T (T (T h21 h219) h218) h217) h216) h215) h214) h212) h236) h250) h15
  have h252 := C (T (T (T (C h207 (T h251 (C (T (T (T h245 h249) h247) (C h183 h246)) h15))) (S h240)) h176) h4) h239
  let v253 := M v0 v2
  have h254 := R v253
  have h255 := C (C h220 h254) h15
  let v256 := M (M v0 v253) v2
  have h257 := R v225
  have h258 := T (T (T (T (C h91 h257) h112) h107) h87) h70
  have h259 := C h111 h257
  have h260 := C (T (T (T (T (T (T (T (T (T h21 h219) h218) h217) h216) h215) h214) h235) (C (T (T (T h3 h182) h240) (C h220 (T (C (T (T (T (C h178 h251) (S h247)) h244) h250) h15) h246))) h233)) (C (C h207 h254) h15)) h238
  have h261 := R v93
  have h262 := h v226 v25 y
  have h263 := C h199 (T h127 h89)
  have h264 := h v138 v1 y
  have h265 := S h264
  have h266 := C h196 (T h109 h168)
  have h267 := h v226 y y
  have h268 := R v226
  T (T (T (T (T (T (T (T (T (T h69 h101) h95) h92) h259) (h (M v1 v225) v1 y)) (C (T (T (T (T (T (T (T (T (T h48 h47) h27) h81) h62) h116) h105) h171) h227) h260) (T (T (T (T (T (T (T (T (T (T (T (C (T (T (T (T (T (T (T (T (T (T (C h258 (T (T (T (T (T (T (T (T h85 h83) h72) h162) h161) (C (T (T (T (T (T (T (T (T h136 h48) h47) h27) h81) h62) h116) h105) h171) h84)) (C (T h267 (C (T (T (T (T (T (T (T (T h57 h56) h50) h131) h130) h128) h264) h263) (C h268 h74)) (T (T (T (C (T (C h196 h144) h166) h29) h146) h127) h89))) h68)) (C (T (T (T (C (T (T (T (T (T (T (T (T (C h268 h39) h266) h265) h124) h122) h120) h79) h67) h66) (T (T (T h109 h168) h167) (C (T h145 (C h199 h165)) h29))) (S h267)) h262) (C (T (T (T (T (T h69 h101) h134) h166) h155) h153) (T (T (T (T (T (C (T (T (T h266 h265) h139) h137) h29) h164) h159) h158) h157) h80))) h29)) (C (T (T (T (T (T (T (T (T (T (T (T (C (T (T (T (T (T h150 h148) h145) h135) h87) h70) (T (T (T (T (T h58 h143) h142) h141) h140) (C (T (T (T h163 h160) h264) h263) h29))) (S h262)) h169) h106) h103) h63) h59) h28) h77) h75) (h v1 y y)) (C (T (T (T (T (T (T (T (T h57 h56) h50) h131) h130) h128) h139) h137) (C h88 h261)) (T (T (T (T h151 h149) h146) h127) h89))) h29))) (S (h (M v25 v93) v25 y))) (C h108 h261)) h163) h160) h124) h122) h120) h79) h67) h66) (T (h y v1 y) (C (T (T (T (T (T (T (T (T (T (T h48 h47) h27) h81) h62) h116) h105) h171) h227) h260) (C (R v256) h78)) (T (T (C (T (T h95 h92) h259) h84) (C h258 (T (T (T h50 h131) h130) h128))) (S (h x v25 x)))))) (S (h v256 y x))) h255) h252) h237) h206) h205) h204) h203) h198) h180) h76))) (C (T (T (T (T (T (T (T (T (T (C (T (T (T (T (T (T (T (T (T h255 h252) h237) h206) h205) h204) h203) h198) h180) h76) h232) h228) h169) h106) h103) h63) h59) h28) h77) h75) (T (T (T (T (T (T (T (T h21 h219) h218) h217) h216) h215) h214) h212) h236))) (S (h v177 v1 v0))) h176) h4

