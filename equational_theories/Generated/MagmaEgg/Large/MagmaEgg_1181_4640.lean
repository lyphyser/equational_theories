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
theorem Equation1181_implies_Equation4640 (G: Type _) [Magma G] (h: Equation1181 G) : Equation4640 G := fun x y z =>
  let v0 := M y z
  have h1 := h z x v0
  have h2 := S h1
  have h3 := R x
  let v4 := M v0 z
  have h5 := h v4 v0 y
  have h6 := R v0
  have h7 := C h3 (C (C h6 (S h5)) h3)
  let v8 := M (M y (M y v4)) v0
  have h9 := h v8 x v0
  have h10 := h v8 x z
  have h11 := S h10
  have h12 := S h9
  have h13 := C h3 (C (C h6 h5) h3)
  have h14 := R z
  have h15 := C h14 (C h14 (T (T h1 h13) h12))
  have h16 := h z v0 x
  have h17 := S h16
  let v18 := M x (M x z)
  have h19 := h (M v18 v0) v0 v0
  have h20 := T (C h6 (T (C h6 (C (C h6 h16) h6)) (S h19))) h17
  have h21 := C h14 (C h20 h14)
  let v22 := M v4 v0
  have h23 := h v22 z v0
  let v24 := M x y
  have h25 := h v0 v4 v24
  have h26 := R v4
  have h27 := C h26 (S h25)
  have h28 := C h3 (C (T (T (T h27 h23) h21) h15) h3)
  have h29 := C h26 h25
  have h30 := h v22 x v0
  have h31 := S h30
  have h32 := T h16 (C h6 (T h19 (C h6 (C (C h6 h17) h6))))
  have h33 := C h3 (C h32 h3)
  have h34 := h z y z
  have h35 := S h34
  let v36 := M z (M z z)
  let v37 := M v36 y
  have h38 := h v37 y y
  have h39 := S h38
  have h40 := R y
  have h41 := C h40 h34
  have h42 := C h41 h40
  have h43 := C h3 (C (T (C h40 (T (C h40 h42) h39)) h35) h3)
  let v44 := M v0 y
  have h45 := h v44 x y
  let v46 := M v24 x
  have h47 := h y v0 v46
  have h48 := S h47
  have h49 := C h3 (C (T (T (T (T (T (C h6 h48) h45) h43) h33) h31) h29) h3)
  have h50 := h (M (M v46 (M v46 y)) v0) x v0
  have h51 := T (T (T (T (T (T h50 h49) h28) h11) h9) h7) h2
  have h52 := C h6 h51
  have h53 := h y v0 x
  have h54 := S h53
  let v55 := M x v24
  let v56 := M v55 v0
  have h57 := h v56 v4 v0
  have h58 := S h57
  have h59 := T h47 h52
  have h60 := C h6 h53
  have h61 := S h45
  have h62 := C h40 h35
  have h63 := C h62 h40
  have h64 := C h3 (C (T h34 (C h40 (T h38 (C h40 h63)))) h3)
  have h65 := C h3 (C h20 h3)
  have h66 := S h23
  have h67 := C h14 (C h32 h14)
  have h68 := C h14 (C h14 (T (T h9 h7) h2))
  have h69 := C h14 (C h14 (T (T (T h50 h49) h28) h11))
  have h70 := S h50
  have h71 := C h3 (C (T (T (T (T (T h27 h30) h65) h64) h61) (C h6 h47)) h3)
  let v72 := M (M v24 (M v24 v0)) v4
  have h73 := h v72 x v4
  have h74 := h v72 y v4
  have h75 := S h74
  have h76 := C h3 (C (T (T (T h68 h67) h66) h29) h3)
  have h77 := T (T (T (T (T (T h1 h13) h12) h10) h76) h71) h70
  have h78 := C h6 h77
  have h79 := T h78 h48
  have h80 := h v22 v4 v0
  have h81 := S h80
  have h82 := h v37 z y
  have h83 := C h26 (T (T h82 (C h14 (C h62 h14))) (C h32 h26))
  have h84 := h v37 v4 y
  have h85 := S h84
  have h86 := C h41 h26
  have h87 := C h26 (T (C h26 h86) h85)
  have h88 := C (T (T (T h87 h83) h81) h29) h79
  have h89 := C h79 h88
  let v90 := M v0 v4
  have h91 := h v90 v4 v4
  have h92 := T (T (T (T (T h91 h89) h75) h73) h71) h70
  have h93 := C h14 (C h14 h92)
  have h94 := C (T (T (T (T (T (T (T (T (T h93 h69) h68) h67) h66) h30) h65) h64) h61) h60) h59
  have h95 := R (M z (M z v90))
  have h96 := C h95 h79
  have h97 := S h91
  have h98 := C h62 h26
  have h99 := C h26 (T h84 (C h26 h98))
  have h100 := C h26 (T (T (C h20 h26) (C h14 (C h41 h14))) (S h82))
  have h101 := C (T (T (T h27 h80) h100) h99) h59
  have h102 := C h59 h101
  have h103 := S h73
  have h104 := T (T (T (T (T h50 h49) h103) h74) h102) h97
  have h105 := C h14 (C h14 h104)
  have h106 := C h14 (C h14 (T (T (T h10 h76) h71) h70))
  have h107 := C h59 (T (T (T h101 (C (T (T (T (T (T (T (T h87 h83) h81) h23) h21) h15) h106) h105) h26)) h96) h94)
  have h108 := h v90 y x
  have h109 := S h108
  have h110 := R (M x (M x v90))
  have h111 := C h110 h79
  have h112 := C (T (C h3 (C h3 h77)) (C h3 (C h3 h104))) h59
  have h113 := h (M v18 y) x y
  have h114 := S h113
  have h115 := h z y x
  have h116 := C h62 h3
  have h117 := C h3 (T h116 (C (C h40 h115) h3))
  have h118 := C h41 h3
  have h119 := h z y y
  have h120 := C h3 (T (C (C h40 (S h119)) h3) h118)
  have h121 := h (M (M y v0) y) x y
  have h122 := C h40 h51
  have h123 := C h40 h92
  have h124 := C (T (C h40 h123) (C h40 h122)) h79
  have h125 := C h79 h98
  have h126 := h v37 x y
  have h127 := S h126
  have h128 := C h3 (T (C (C h40 (S h115)) h3) h118)
  have h129 := C (T (C h3 (C h3 h92)) (C h3 (C h3 h51))) h79
  have h130 := C h110 h59
  have h131 := C h40 (T (T (T (T (T (T h130 h129) h113) h128) h127) h84) h125)
  have h132 := C (T (T (T (T (T (T (T (T (T (T h1 h13) h12) h10) h76) h103) h74) h102) h97) h108) h131) h59
  have h133 := C h79 (T (T (T (T (T (T (T h132 h124) h121) h120) h117) h114) h112) h111)
  let v134 := M z y
  have h135 := h v134 v4 v4
  have h136 := S h135
  have h137 := C h59 h86
  have h138 := C h40 (T (T (T (T (T (T h137 h85) h126) h117) h114) h112) h111)
  have h139 := C (T (T (T (T (T (T (T (T (T (T h138 h109) h91) h89) h75) h73) h28) h11) h9) h7) h2) h79
  have h140 := C h40 h104
  have h141 := C h40 h77
  have h142 := C (T (C h40 h141) (C h40 h140)) h59
  have h143 := S h121
  have h144 := C h3 (T h116 (C (C h40 h119) h3))
  have h145 := C h59 (T (T (T (T (T (T (T h130 h129) h113) h128) h144) h143) h142) h139)
  have h146 := T (T (T h141 h140) h137) (C h26 (T (T h98 h108) h145))
  have h147 := C h146 h59
  have h148 := C h26 (T (T (T (T (T (T h67 h66) h30) h65) h64) h61) h147)
  have h149 := C h26 (T h148 h136)
  have h150 := T (T (T (C h26 (T (T h133 h109) h86)) h125) h123) h122
  have h151 := C h150 h79
  have h152 := C h26 (T (T (T (T (T (T h151 h45) h43) h33) h31) h23) h21)
  have h153 := C (T (T h149 h133) h131) h26
  have h154 := C h26 (T (T (T h153 h139) h135) h152)
  have h155 := h v36 v4 v4
  have h156 := C h6 (T (T (T (T (T (T (T (T (T (T (T (T (T (T h45 h43) h33) h31) h23) h21) h155) h154) h149) h133) h109) h91) h89) h107) h58)
  let v157 := M v0 v44
  have h158 := h v157 z v4
  have h159 := S h158
  have h160 := C h95 h59
  have h161 := C h6 h54
  have h162 := C (T (T (T (T (T (T (T (T (T h161 h45) h43) h33) h31) h23) h21) h15) h106) h105) h79
  have h163 := C h79 (T (T (T h162 h160) (C (T (T (T (T (T (T (T h93 h69) h68) h67) h66) h80) h100) h99) h26)) h88)
  have h164 := T (T (T (T (T (T (T (T h57 h163) h75) h73) h28) h11) h9) h7) h2
  have h165 := R v157
  have h166 := C h59 h165
  have h167 := C h59 h166
  have h168 := C h79 h165
  have h169 := S h155
  have h170 := C h26 (T h135 h152)
  have h171 := C (T (T h138 h145) h170) h26
  have h172 := C h26 (T (T (T h148 h136) h132) h171)
  have h173 := C h6 (T (T (T (T (T (T (T (T (T (T (T (T (T (T h57 h163) h102) h97) h108) h145) h170) h172) h169) h67) h66) h30) h65) h64) h61)
  have h174 := T (T (T h78 h48) h53) h173
  have h175 := h v157 v0 y
  have h176 := S h175
  have h177 := C h79 h168
  have h178 := C h59 (T h53 h173)
  have h179 := C h26 h178
  let v180 := M y y
  have h181 := R v180
  have h182 := C h59 h181
  have h183 := h (M (M y v180) v0) x v0
  have h184 := S h183
  have h185 := h y v0 y
  have h186 := C h3 (C (T h161 (C h6 h185)) h3)
  have h187 := h v56 x v0
  have h188 := T (T (T h156 h54) h47) h52
  have h189 := C h6 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (C h146 h188) h151) h45) h43) h33) h31) h23) h21) h155) h154) h149) h133) h109) h91) h89) h107) h58) h187) h186) h184) (C (T h182 h179) h6)) (C h177 h6))
  have h190 := C (T (T (T (T (T h189 h176) h156) h54) h47) h52) h174
  have h191 := C h79 (T h190 h168)
  have h192 := h v157 v4 v0
  have h193 := R v56
  have h194 := C h79 h193
  have h195 := S h187
  have h196 := h y v0 z
  have h197 := C h3 (C (T (C h6 (S h196)) h60) h3)
  have h198 := h (M (M z v134) v0) x v0
  have h199 := T (T h198 h197) h195
  have h200 := C h59 h199
  have h201 := S h198
  have h202 := C h3 (C (T h161 (C h6 h196)) h3)
  have h203 := C h3 (C (T (C h6 (S h185)) h60) h3)
  have h204 := T (T (T h183 h203) h202) h201
  have h205 := C h40 h204
  have h206 := h y v0 v0
  have h207 := C h3 (C (T (C h6 (S h206)) h60) h3)
  have h208 := h (M v157 v0) x v0
  have h209 := T (T (T h208 h207) h186) h184
  have h210 := C h40 h209
  have h211 := S h208
  have h212 := C h3 (C (T h161 (C h6 h206)) h3)
  have h213 := h y v0 v24
  have h214 := C h3 (C (T (C h6 (S h213)) h60) h3)
  let v215 := M v24 y
  have h216 := h (M (M v24 v215) v0) x v0
  have h217 := T (T (T h216 h214) h212) h211
  have h218 := C h40 h217
  have h219 := S h216
  have h220 := C h3 (C (T h161 (C h6 h213)) h3)
  have h221 := C h40 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h63 h45) h43) h33) h31) h23) h21) h155) h154) h149) h133) h109) h91) h89) h107) h58) h187) h220) h219)
  have h222 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h161 h45) h43) h33) h31) h23) h21) h155) h154) h149) h133) h109) h91) h89) h75) h73) h28) h11) h9) h7) h2) (T (T (T (T (T (T (T (T (T (T (T h141 h140) h137) h85) h38) h221) h218) h210) h205) h200) h194) (C (T (T (T (T h53 h173) h192) h191) h167) h164))
  have h223 := h v56 y v24
  have h224 := S h223
  have h225 := R (M v24 (M v24 v56))
  have h226 := R v24
  have h227 := R (M v24 (M v24 v90))
  have h228 := h (M (M v24 (M v24 z)) y) x y
  have h229 := h z y v24
  have h230 := C h40 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h216 h214) h195) h57) h163) h102) h97) h108) h145) h170) h172) h169) h67) h66) h30) h65) h64) h61) h42)
  have h231 := T (T (T h208 h207) h220) h219
  have h232 := C h40 h231
  have h233 := T (T (T h183 h203) h212) h211
  have h234 := C h40 h233
  have h235 := T (T (T h198 h197) h186) h184
  have h236 := C h40 h235
  have h237 := T (T h187 h202) h201
  have h238 := C h79 h237
  have h239 := C h59 h193
  have h240 := C h40 (T (T (T (T (T (T (T (T (T (T (T (T (T h239 h238) h236) h234) h232) h230) h39) h126) (C h3 (T h116 (C (C h40 h229) h3)))) (S h228)) (C (T (C h226 (C h226 h77)) (C h226 (C h226 h104))) h59)) (C h227 h79)) (C (T (T (T (T (C h226 (C h226 (T (T (T (T (T (T h91 h89) h107) h58) h187) h220) h219))) (C h226 (C h226 h217))) (C h226 (C h226 h209))) (C h226 (C h226 h204))) (C h226 (C h226 h199))) h59)) (C h225 h79))
  have h241 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h240 h224) h57) h163) h102) h97) h108) h145) h170) h172) h169) h67) h66) h30) h65) h64) h61) h60) h6
  have h242 := C h40 (T (T (T (T (T (T (T (T (T (T (T (T (T (C h225 h59) (C (T (T (T (T (C h226 (C h226 h237)) (C h226 (C h226 h235))) (C h226 (C h226 h233))) (C h226 (C h226 h231))) (C h226 (C h226 (T (T (T (T (T (T h216 h214) h195) h57) h163) h102) h97)))) h79)) (C h227 h59)) (C (T (C h226 (C h226 h92)) (C h226 (C h226 h51))) h79)) h228) (C h3 (T (C (C h40 (S h229)) h3) h118))) h127) h38) h221) h218) h210) h205) h200) h194)
  have h243 := h v56 z v4
  have h244 := S h243
  have h245 := C h59 h200
  have h246 := C h40 h205
  have h247 := C h40 h210
  have h248 := C h40 h218
  have h249 := C h79 (T (T (T (T (T (T (T (T (T h162 h160) (C (T (T (T (T h93 h69) h68) h155) h154) h26)) h153) h124) h121) h120) h127) h38) h221)
  have h250 := C h14 (C (T (T (T (T (T (T (T (T (T (T (T (T h1 h13) h12) h10) h76) h103) h74) h107) h249) h248) h247) h246) h245) h164)
  have h251 := C (T (T (T h250 h244) h223) h242) h6
  have h252 := T (T (T (T (T (T (T (T h1 h13) h12) h10) h76) h103) h74) h107) h58
  have h253 := C h59 (T (T (T (T (T (T (T (T (T h230 h39) h126) h144) h143) h142) h171) (C (T (T (T (T h172 h169) h15) h106) h105) h26)) h96) h94)
  have h254 := C h40 h232
  have h255 := C h40 h234
  have h256 := C h40 h236
  have h257 := C h79 h238
  have h258 := C h14 (C (T (T (T (T (T (T (T (T (T (T (T (T h257 h256) h255) h254) h253) h163) h75) h73) h28) h11) h9) h7) h2) h252)
  have h259 := C (T (T (T (T (T (T (T h257 h256) h255) h254) h253) h58) h243) h258) h6
  have h260 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h93 h69) h68) h155) h154) h149) h133) h109) h91) h89) h107) h249) h248) h247) h246) h245) h6
  have h261 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h1 h13) h12) h10) h76) h103) h74) h102) h97) h108) h145) h170) h172) h169) h15) h106) h105) h6
  let v262 := M z v0
  have h263 := h v262 v24 y
  have h264 := R v262
  have h265 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h93 h69) h68) h155) h154) h149) h133) h109) h91) h89) h75) h73) h28) h11) h9) h7) h2) h6
  have h266 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h257 h256) h255) h254) h253) h163) h102) h97) h108) h145) h170) h172) h169) h15) h106) h105) h6
  have h267 := C (T (T (T (T (T (T (T h250 h244) h57) h249) h248) h247) h246) h245) h6
  have h268 := C (T (T (T h240 h224) h243) h258) h6
  have h269 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h161 h45) h43) h33) h31) h23) h21) h155) h154) h149) h133) h109) h91) h89) h107) h58) h223) h242) h6
  have h270 := S h192
  have h271 := C h79 h181
  have h272 := C h79 (T h156 h54)
  have h273 := C h26 h272
  have h274 := C h6 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (C h167 h6) (C (T h273 h271) h6)) h183) h203) h195) h57) h163) h102) h97) h108) h145) h170) h172) h169) h67) h66) h30) h65) h64) h61) h147) (C h150 h174))
  have h275 := C (T (T (T (T (T h78 h48) h53) h173) h175) h274) h188
  have h276 := C h59 (T h166 h275)
  have h277 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h1 h13) h12) h10) h76) h103) h74) h102) h97) h108) h145) h170) h172) h169) h67) h66) h30) h65) h64) h61) h60) (T (T (T (T (T (T (T (T (T (T (T (C (T (T (T (T h177 h276) h270) h156) h54) h252) h239) h238) h236) h234) h232) h230) h39) h84) h125) h123) h122)
  have h278 := T (T (T (T (T (T (T h53 h173) h192) h191) h167) h273) h271) (C h59 (T (T (T h178 h275) (C (T (T (T (T h189 h176) h192) h191) h167) h26)) (C (T (T (T (T (T (T h177 h276) h270) h156) h54) h47) h52) (T (T (T (T (T (T (T (T (T (T h78 h48) h53) h173) h158) h277) h269) h268) h267) h266) h265))))
  have h279 := C h278 h226
  have h280 := h (M y v24) v24 v24
  have h281 := C h79 (T (T (T (C (T (T (T (T (T (T h78 h48) h53) h173) h192) h191) h167) (T (T (T (T (T (T (T (T (T (T h261 h260) h259) h251) h241) h222) h159) h156) h54) h47) h52)) (C (T (T (T (T h177 h276) h270) h175) h274) h26)) h190) h272)
  have h282 := T (T (T (T (T (T (T h281 h182) h179) h177) h276) h270) h156) h54
  have h283 := C h282 h226
  have h284 := C h226 h283
  have h285 := h v262 v24 v4
  have h286 := C h226 (T (T (T (T (T (T (T (T (T (T h53 h173) h158) h277) h269) h268) h267) h266) h265) h285) h284)
  have h287 := h v215 v4 v4
  have h288 := S h287
  have h289 := R (M v4 (M v4 v215))
  have h290 := C h289 h59
  have h291 := S h285
  have h292 := C h226 h279
  have h293 := C h226 (T (T (T (T (T (T (T (T (T (T h292 h291) h261) h260) h259) h251) h241) h222) h159) h156) h54)
  have h294 := h v262 x v4
  have h295 := C h3 (T (T (T (T (T (T (T (T (T (T (C h3 (C h278 h3)) (S h294)) h261) h260) h259) h251) h241) h222) h159) h156) h54)
  have h296 := C h295 (T (T (T (T (T (T (T (T (T (T (T (T h78 h48) h53) h173) h158) h277) h269) h268) h267) h266) h265) h285) h284)
  have h297 := C h26 (T h296 h293)
  let v298 := M y x
  have h299 := h v298 v4 x
  have h300 := R v298
  have h301 := C (T (C h59 h300) (C h26 (T h299 h297))) h79
  have h302 := h (M (M y v298) v4) x v4
  have h303 := S h302
  have h304 := h x v4 y
  have h305 := h x v4 v46
  have h306 := C h26 (S h305)
  have h307 := C h3 (C (T h306 (C h26 h304)) h3)
  have h308 := C h26 h305
  have h309 := h x v4 x
  have h310 := C h3 (C (T (C h26 (S h309)) h308) h3)
  let v311 := M (M x (M x x)) v4
  have h312 := h v311 x v4
  have h313 := h v311 v4 y
  have h314 := S h312
  have h315 := C h3 (C (T h306 (C h26 h309)) h3)
  have h316 := C h3 (C (T (C h26 (S h304)) h308) h3)
  have h317 := S h299
  have h318 := C (C h3 (T (T (T (T (T (T (T (T (T (T h53 h173) h158) h277) h269) h268) h267) h266) h265) h294) (C h3 (C h282 h3)))) (T (T (T (T (T (T (T (T (T (T (T (T h292 h291) h261) h260) h259) h251) h241) h222) h159) h156) h54) h47) h52)
  have h319 := C h26 (T h286 h318)
  have h320 := C (T (C h26 (T h319 h317)) (C h79 h300)) h59
  have h321 := C h289 h79
  have h322 := h x y z
  have h323 := S h322
  have h324 := C h40 h323
  let v325 := M (M z (M z x)) y
  have h326 := h v325 y y
  have h327 := h v325 v4 y
  have h328 := S h327
  have h329 := C h40 h322
  have h330 := h y x v0
  have h331 := C h3 (S h330)
  let v332 := M v157 x
  have h333 := h v332 y x
  have h334 := h v332 x x
  have h335 := C h3 h330
  have h336 := h v46 x x
  have h337 := C h59 (C (T (T (T (T (T (T (T (C h3 (S h336)) (C h3 (C h335 h3))) (S h334)) h333) (C h59 (C h331 h40))) h319) h317) h329) h59)
  have h338 := h (M (M x (M x v46)) x) y x
  have h339 := C h26 (T (T (T (T (T (T (T (T (T (T (T h338 h337) h328) h326) (C h59 (C (T (T h324 h299) (C h79 (T (T (T h296 h293) h287) (C h79 (T (T (T (T (T h321 h320) h302) h316) h315) h314))))) h59))) (S h313)) h312) h310) h307) h303) h301) h290)
  have h340 := S h338
  have h341 := C h79 (C (T (T (T (T (T (T (T h324 h299) h297) (C h79 (C h335 h40))) (S h333)) h334) (C h3 (C h331 h3))) (C h3 h336)) h79)
  have h342 := C h59 (T (T h327 h341) h340)
  have h343 := C (T (T (T (T h322 h342) h339) h288) h286) h226
  have h344 := C h226 (C (T (T (T (T h293 h287) (C h26 (T (T (T (T (T (T (T (T (T (T (T h321 h320) h302) h316) h315) h314) h313) (C h79 (C (T (T (C h59 (T (T (T (C h59 (T (T (T (T (T h312 h310) h307) h303) h301) h290)) h288) h286) h318)) h317) h329) h79))) (S h326)) h327) h341) h340))) (C h79 (T (T h338 h337) h328))) h323) h226)
  have h345 := C h59 (C h59 h264)
  T (T (T (T (T (T (T (T (T (T (T (T (T (C h226 (T (T (T (T (T (T (T h322 h342) h339) h288) h286) h318) (C h295 (T (T (T (T (T (T (T (T (T (T (T (T (T (T h78 h48) h53) h173) h158) h277) h269) h268) h267) h266) h265) (h v262 y y)) (C h59 (T (T (T (C (R (M y (M y v262))) h59) (C h345 h26)) (C (R (M v4 (M v4 v262))) h79)) (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T h281 h182) h179) h177) h276) h270) h158) h277) h269) h268) h267) h266) h265) h263) (C h226 (T (T (T (C h345 h226) h283) h280) h344))) h59)))) (S (h v55 v4 v24))) h343))) h344)) (C h226 (T (T (T (C h226 h343) (S h280)) h279) (C (C h79 (C h79 h264)) h226)))) (S h263)) h261) h260) h259) h251) h241) h222) h159) h156) h54) h47) h52

