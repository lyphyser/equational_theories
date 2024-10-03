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
theorem Equation4197_implies_Equation4358 (G: Type _) [Magma G] (h: Equation4197 G) : Equation4358 G := fun x y z =>
  let v0 := M z y
  have h1 := h x v0 x
  have h2 := S h1
  let v3 := M x v0
  let v4 := M x x
  have h5 := h (M v4 v0) x v3
  have h6 := S h5
  have h7 := R v3
  have h8 := R x
  have h9 := h v4 v0 v3
  have h10 := S h9
  have h11 := R v0
  have h12 := h x x y
  have h13 := S h12
  have h14 := R y
  have h15 := h y x v3
  have h16 := h v0 y x
  have h17 := h z y x
  let v18 := M x z
  have h19 := h (M v18 y) x v3
  have h20 := h v18 y v3
  have h21 := S h20
  have h22 := h x z v0
  have h23 := h y x z
  have h24 := C (C (C h7 (T (C h23 h11) (S h22))) h14) h7
  have h25 := h (M (M y x) v0) y v3
  have h26 := h x v0 y
  have h27 := h v3 x v3
  have h28 := T (T (T h27 (C (C (C h7 (T (T (T h26 h25) h24) h21)) h8) h7)) (S h19)) (S h17)
  have h29 := C h28 h14
  have h30 := h x y v3
  have h31 := T (T h30 (C (T h29 h16) h7)) (S h15)
  have h32 := C h31 h8
  have h33 := h x y z
  have h34 := S h33
  have h35 := R z
  have h36 := h z x v3
  have h37 := S h36
  have h38 := h v0 z x
  have h39 := C (T (C h28 h35) h38) h7
  have h40 := h x z v3
  have h41 := C (T (T h40 h39) h37) h14
  have h42 := C (T (T (T (T h26 h25) h24) h21) h41) h35
  have h43 := T h42 h34
  have h44 := C h43 h8
  have h45 := C (T (T h38 h44) h32) h14
  have h46 := C h7 (T h45 h13)
  have h47 := C (C h46 h11) h7
  have h48 := h (M (M v0 z) y) v0 v3
  have h49 := h z y v0
  have h50 := T (T (T h49 h48) h47) h10
  have h51 := C (C (C h7 h50) h8) h7
  have h52 := h v0 x v3
  let v53 := M y z
  let v54 := M x v53
  have h55 := R v54
  have h56 := S h49
  have h57 := S h48
  have h58 := S h38
  have h59 := S h26
  have h60 := S h25
  have h61 := C (C (C h7 (T h22 (C (S h23) h11))) h14) h7
  have h62 := S h40
  have h63 := T (T (T h17 h19) (C (C (C h7 (T (T (T h20 h61) h60) h59)) h8) h7)) (S h27)
  have h64 := C (T h58 (C h63 h35)) h7
  have h65 := C (T (T h36 h64) h62) h14
  have h66 := C (T (T (T (T h65 h20) h61) h60) h59) h35
  have h67 := T h33 h66
  have h68 := S h30
  have h69 := C h63 h14
  have h70 := T (T h15 (C (T (S h16) h69) h7)) h68
  have h71 := C (T (T (C h70 h8) (C h67 h8)) h58) h14
  have h72 := C h7 (T h12 h71)
  have h73 := C (C h72 h11) h7
  have h74 := T (T (T h9 h73) h57) h56
  have h75 := C h55 h74
  have h76 := h x v53 v0
  have h77 := S h76
  let v78 := M v0 x
  have h79 := h v78 v53 v3
  have h80 := S h79
  have h81 := T (T (T h52 h51) h6) h2
  have h82 := R v53
  have h83 := S h52
  have h84 := C (C (C h7 h74) h8) h7
  have h85 := T (T (T h1 h5) h84) h83
  have h86 := h v0 x x
  have h87 := C (T (T (T (T (S h86) h52) h51) h6) h2) h85
  have h88 := h x x v3
  have h89 := T h88 h87
  have h90 := C h89 h82
  have h91 := h v4 v53 v3
  have h92 := S h91
  have h93 := h x x z
  have h94 := h x z y
  let v95 := M x y
  have h96 := h v95 z v3
  have h97 := S h96
  have h98 := h x y v53
  have h99 := h z x y
  have h100 := C (C (T (C h7 (T (T (T (C h99 h82) (S h98)) h33) h66)) (C h7 h43)) h35) h7
  have h101 := h (M (M z x) v53) z v3
  have h102 := h x v53 z
  have h103 := T (T (T (T (C (T (T (T (T h102 h101) h100) h97) (C h31 h35)) h14) (S h94)) h40) h39) h37
  have h104 := h v53 y x
  have h105 := C (C (T (C h7 (T (T (T (C (T h104 (C h103 h8)) h35) (S h93)) h12) h71)) h46) h82) h7
  have h106 := h (M (M v53 y) z) v53 v3
  have h107 := h y z v53
  have h108 := C (T (T (T (T h107 h106) h105) h92) h90) h81
  have h109 := C (T h108 h80) h11
  have h110 := S h107
  have h111 := S h106
  have h112 := S h102
  have h113 := S h101
  have h114 := C (C (T (C h7 h67) (C h7 (T (T (T h42 h34) h98) (C (S h99) h82)))) h35) h7
  have h115 := T (T (T (T h36 h64) h62) h94) (C (T (T (T (T (C h70 h35) h96) h114) h113) h112) h14)
  have h116 := C (C (T h72 (C h7 (T (T (T h45 h13) h93) (C (T (C h115 h8) (S h104)) h35)))) h82) h7
  have h117 := S h88
  have h118 := C (T (T (T (T h1 h5) h84) h83) h86) h81
  have h119 := T h118 h117
  have h120 := C h119 h82
  have h121 := C (T (T (T (T h120 h91) h116) h111) h110) h85
  have h122 := h v78 v53 v54
  have h123 := S h122
  have h124 := h x v53 x
  have h125 := S h124
  let v126 := M v4 v53
  have h127 := h v126 x v3
  have h128 := S h127
  have h129 := T (T (T h107 h106) h105) h92
  have h130 := C h81 h129
  have h131 := C h82 h85
  have h132 := C h82 h81
  have h133 := C h43 h35
  have h134 := C (T (T (T (T h133 h96) h114) h113) h112) h85
  have h135 := h z z v3
  have h136 := h z z y
  have h137 := S h136
  have h138 := C (T (T h137 h135) h134) h82
  have h139 := h z y v53
  have h140 := T h139 h138
  have h141 := C h140 h55
  have h142 := S h139
  have h143 := S h135
  have h144 := C h67 h35
  have h145 := C (T (T (T (T h102 h101) h100) h97) h144) h81
  have h146 := C (T (T h145 h143) h136) h82
  have h147 := T h146 h142
  have h148 := C h147 h55
  have h149 := C (T (T (C (T (T (C h85 h82) h122) h148) h8) (C (T (T (T (T h141 h123) h79) h121) h132) h8)) (C (T (T (T h131 h108) h80) h130) h8)) h7
  have h150 := h v53 x v3
  have h151 := T (T (T h150 h149) h128) h125
  have h152 := C h140 h151
  have h153 := C (T (T (T h152 h123) h79) h121) h11
  have h154 := C (T (T h153 h109) h77) h50
  let v155 := M v53 x
  have h156 := h v155 v0 v0
  have h157 := S h150
  have h158 := T (T (T h91 h116) h111) h110
  have h159 := C h85 h158
  have h160 := C (T (T (T h159 h79) h121) h132) h8
  have h161 := C (T (T h160 (C (T (T (T (T h131 h108) h80) h122) h148) h8)) (C (T (T h141 h123) (C h81 h82)) h8)) h7
  have h162 := C h8 h158
  have h163 := h y z x
  have h164 := S h163
  let v165 := M v95 z
  have h166 := h v165 x v3
  have h167 := S h166
  have h168 := C h7 (T (T (T (T (T (T (T h150 h149) h128) h125) h102) h101) h100) h97)
  have h169 := T (T (T h124 h127) h161) h157
  have h170 := T (T (T (T (T (C h103 h14) h65) h20) h61) h60) h59
  have h171 := C h170 h169
  have h172 := h y y v54
  have h173 := h y y v53
  have h174 := S h173
  have h175 := h z y y
  have h176 := C h175 h82
  have h177 := C h11 h158
  have h178 := C h11 h129
  have h179 := C (S h175) h82
  have h180 := S h172
  have h181 := T (T (T (T (T h26 h25) h24) h21) h41) (C h115 h14)
  have h182 := C (T (C (T (T (T (T (C h181 h55) h180) h173) h179) h178) h8) (C (T (T (T (T (T h177 h176) h174) h172) h171) h168) h8)) h7
  have h183 := h v54 x v3
  have h184 := T (T (T (T (T (T (T h183 h182) h167) h164) h107) h106) h105) h92
  have h185 := C h8 h184
  have h186 := C (T (T (T (C (T (T (T (T (T h185 h162) h124) h127) h161) h157) h11) h156) h154) h75) h8
  let v187 := M v54 x
  have h188 := h v187 v0 x
  have h189 := h v187 v0 v3
  have h190 := S h189
  have h191 := S h183
  have h192 := C h181 h151
  have h193 := C h7 (T (T (T (T (T (T (T h96 h114) h113) h112) h124) h127) h161) h157)
  have h194 := C (T (C (T (T (T (T (T h193 h192) h180) h173) h179) h178) h8) (C (T (T (T (T h177 h176) h174) h172) (C h170 h55)) h8)) h7
  have h195 := T (T (T h163 h166) h194) h191
  have h196 := h x v0 v0
  have h197 := S h196
  have h198 := h v78 v0 v3
  have h199 := S h198
  have h200 := C (T (T (T (T h49 h48) h47) h10) (C h89 h11)) h81
  have h201 := C (T h200 h199) h11
  have h202 := C (T (T (T (T (C h119 h11) h9) h73) h57) h56) h85
  have h203 := h x v0 v53
  have h204 := S h203
  have h205 := h v155 v0 v3
  have h206 := S h205
  have h207 := h y y z
  have h208 := C (T (T (S h207) h172) h171) h11
  have h209 := h y z v0
  have h210 := C (T (T (T (T (T (T h120 h91) h116) h111) h110) h209) h208) h7
  have h211 := C (T (T (T (T h152 h123) h79) h210) h206) h82
  have h212 := C (T (T (T (T (T h211 h204) h1) h5) h84) h83) h11
  have h213 := h v155 v53 v0
  have h214 := h v155 v53 v54
  have h215 := S h214
  have h216 := h v53 x x
  have h217 := h x x v54
  have h218 := T (T (T (T (T h107 h106) h105) h92) h90) (C (T (T (T h118 h117) h217) (C (T (T (T (T (S h216) h150) h149) h128) h125) h169)) h82)
  have h219 := C h218 h151
  have h220 := C (T (T (T (T (T h219 h215) h213) h212) h198) h202) h11
  have h221 := h v155 v0 v53
  have h222 := C (T (T (T (T (T (T h152 h123) h79) h210) h206) h221) (C (T (T h220 h201) h197) h195)) h11
  have h223 := C h147 h169
  have h224 := C (T (T (T h108 h80) h122) h223) h11
  have h225 := C (T h79 h121) h11
  have h226 := C (T (T (T (T (T (T (T (T h133 h96) h114) h113) h112) h76) h225) h224) h222) h7
  let v227 := M z z
  have h228 := S h209
  have h229 := C (T (T h192 h180) h207) h11
  have h230 := C (T (T (T (T (T (T h229 h228) h107) h106) h105) h92) h90) h7
  have h231 := T (T (T h183 h182) h167) h164
  have h232 := T (T (T (T (T (C (T (T (T (C (T (T (T (T h124 h127) h161) h157) h216) h151) (S h217)) h88) h87) h82) h120) h91) h116) h111) h110
  have h233 := C h232 h169
  have h234 := S h213
  have h235 := C (T (T (T (T h205 h230) h80) h122) h223) h82
  have h236 := C (T (T (T (T (T h52 h51) h6) h2) h203) h235) h11
  have h237 := C (T (T (T (T (T h200 h199) h236) h234) h214) h233) h11
  have h238 := C (T h198 h202) h11
  have h239 := C (T (T (T (T (T (T (C (T (T h196 h238) h237) h231) (S h221)) h205) h230) h80) h122) h223) h11
  have h240 := C (T (T (T (T (T (T (T (T h239 h153) h109) h77) h102) h101) h100) h97) h144) h7
  have h241 := h z z v0
  have h242 := h y z z
  have h243 := C (S h242) h11
  have h244 := h x x v53
  let v245 := M v0 y
  have h246 := S h156
  have h247 := C (T (T h76 h225) h224) h74
  have h248 := C h55 h50
  have h249 := h x v53 v53
  have h250 := C h169 h158
  have h251 := C h55 h184
  have h252 := T (T (T h251 h250) h214) h233
  have h253 := T (T (T (T (T (T (T h91 h116) h111) h110) h163) h166) h194) h191
  have h254 := C h55 h253
  have h255 := C h151 h129
  let v256 := M v3 x
  have h257 := h v256 v53 v3
  have h258 := h v256 v53 v0
  have h259 := h v187 v0 v54
  have h260 := S h259
  have h261 := T (T (T h96 h114) h113) h112
  have h262 := T (T (T h219 h215) h255) h254
  have h263 := C (T (T (T h196 h238) h237) (C h262 h11)) h261
  have h264 := C h11 h184
  have h265 := T (T (T (T (T (T (T (T (T (T (T h264 h177) h176) h174) h172) h171) h168) h263) h260) h189) h240) h134
  have h266 := h v187 v53 v0
  have h267 := h v187 v53 x
  have h268 := S h267
  have h269 := C h8 h253
  have h270 := C h8 h129
  have h271 := C (T h270 h269) h231
  have h272 := h v78 v0 v54
  have h273 := S h272
  have h274 := C h265 h11
  have h275 := C h11 h253
  have h276 := C (T (T (T (T (T h192 h180) h173) h179) h178) h275) h11
  have h277 := h v165 x v53
  have h278 := T (T (T h102 h101) h100) h97
  have h279 := T (T (T (T (T (T (T (T (T (T (T h145 h226) h190) h259) (C (T (T (T (C h252 h11) h220) h201) h197) h278)) h193) h192) h180) h173) h179) h178) h275
  T (T (T (T (T (T (T (T (T h124 (h v126 x x)) (C (T (T (T (T (C (T (T (T h162 h124) (h v126 x v54)) (C (T (T (T (C (T h254 h271) h8) h268) (C (C h169 h8) h82)) (S h244)) h55)) h8) (S (h x v54 x))) (h x v54 v54)) (C (T (T (T (T (T (C (T (T (T (T (T (T (T h183 h182) h167) h164) h209) h208) h276) h274) h55) h273) h236) h234) h214) (C h232 h55)) h55)) (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (C h218 h55) h215) h213) h212) (h v78 v0 v53)) (C (T (T (T (T h109 h77) h124) h127) (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (C (T (T (T (T (T h159 h79) h210) h206) h156) h154) h8) (C h75 h8)) (C (T (T (T h248 h247) h246) (C (T (T (T (T (T h150 h149) h128) h125) h270) h269) h11)) h8)) (S h188)) h189) h240) h143) h241) h243) (h v53 v0 y)) (C (T (T (T (T (C (T (T (h y v53 y) (C (T (T (C (T (T (T (T (T (T (T (T (T h172 h171) h168) h263) h260) h189) (C (T (T (T (T (T (T (T h239 h153) h109) h77) h249) (C (T h214 h233) h82)) (C h262 h82)) (C (T (T (T h251 h250) h213) (C (T h211 h204) h63)) h82)) h7)) (S h257)) h258) (C (T (T (C (T (T (T (C (T (T h139 h138) (C h279 h82)) h28) (S h266)) h267) (C (T (T (T (T (T (T (C (T h185 h162) h195) h251) h250) h213) h212) h272) (C (T (T (T (C h279 h11) (C (T (T (T (T (T h264 h177) h176) h174) h172) h171) h11)) h229) h228) h278)) h8)) h82) (S h277)) h164) h63)) h82) (C (T (T (T (T (T (T (T (T (T (C (T (T h163 h277) (C (T (T (T (C (T (T (T (T (T (T (C (T (T (T h209 h208) h276) h274) h261) h273) h236) h234) h255) h254) h271) h8) h268) h266) (C (T (T (C h265 h82) h146) h142) h63)) h82)) h28) (S h258)) h257) (C (T (T (T (T (T (T (T (C (T (T (T (C (T h203 h235) h28) h234) h255) h254) h82) (C h252 h82)) (C (T h219 h215) h82)) (S h249)) h76) h225) h224) h222) h7)) h190) h188) h186) (C h248 h8)) (C (T (T (T (T (T h247 h246) h205) h230) h80) h130) h8)) h160) h82)) (S (h v3 x v53))) h14)) h29) h11) (h v245 v0 x)) (C (T (T (T (T (T (C (T (h x v245 v3) (C (C h28 (R v245)) h7)) h11) (S (h v245 v3 v0))) (C h69 h7)) h68) h33) h66) h8)) h44) h32) h14)) h13) h244) (C (T (T (T (T (C h151 h8) h183) h182) h167) h164) h129)) (C h82 h158)) h7)) h82)) (S (h v53 v3 v53))) (h v53 v3 x)) (C (T (T (T (T (T (C h55 h85) h145) h143) h241) h243) (C h82 h50)) h8)) (C (C h82 h74) h8)) (C (T (C h242 h11) (S h241)) h8)) (h v227 x v54)) (C (T (T (S (h v53 v227 x)) (C h82 h136)) (C h82 (T (T (T h137 h135) h226) h190))) h55)) (C (T (T (C h82 (T (T (T h189 h240) h143) h136)) (C h82 h137)) (C h195 (R v227))) h55)) (S (h x v227 v54))) h55)) h8)) (S (h v227 v54 x))) (C (T (T (T (T h135 h226) h190) h188) h186) h55)) (S (h v0 x v54))) h52) h51) h6) h2

