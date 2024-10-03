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
theorem Equation2519_implies_Equation1699 (G: Type _) [Magma G] (h: Equation2519 G) : Equation1699 G := fun x y z =>
  let v0 := M y z
  let v1 := M v0 z
  let v2 := M y x
  let v3 := M v2 v1
  have h4 := h v3 v0 y
  have h5 := S h4
  have h6 := R y
  let v7 := M v3 y
  have h8 := h (M v0 (M v7 v0)) x y
  have h9 := S h8
  have h10 := R x
  let v11 := M v3 x
  have h12 := h (M x v11) x x
  have h13 := h v3 v3 x
  have h14 := S h13
  have h15 := C h10 (C h14 h10)
  let v16 := M v3 (M v11 v3)
  have h17 := h v16 x x
  have h18 := h v16 y x
  have h19 := S h18
  have h20 := C (C h6 (C h13 h6)) h10
  let v21 := M y v7
  have h22 := h v21 x x
  have h23 := h v3 v3 y
  have h24 := S h23
  have h25 := C h6 (C h24 h6)
  have h26 := C (T (T (T (T h25 h22) (C (C h10 (C (T (T (T h20 h19) h17) (C h15 h10)) h10)) h10)) (S h12)) (C h10 (C h4 h10))) h6
  have h27 := C h6 (C h23 h6)
  have h28 := h v21 x y
  have h29 := S h28
  let v30 := M v3 (M v7 v3)
  have h31 := h v30 y y
  have h32 := C (T h31 (C h25 h6)) h10
  have h33 := h v30 v2 y
  have h34 := R v2
  have h35 := C (C h10 (T (C (T (C (C h34 (C h23 h34)) h6) (S h33)) h10) h32)) h6
  let v36 := M v3 v2
  have h37 := h (M v2 v36) x y
  have h38 := h v36 v3 v2
  have h39 := R v3
  have h40 := h v2 v3 v3
  have h41 := S h40
  let v42 := M v2 v3
  have h43 := h (M v3 (M v42 v3)) x v3
  have h44 := S h43
  have h45 := h (M x (M v2 x)) x x
  have h46 := S h45
  have h47 := h x v3 y
  have h48 := h y v1 x
  have h49 := S h48
  have h50 := h v1 x v3
  have h51 := T (C (C h39 (T h50 (C (C h10 h49) h39))) h6) (S h47)
  have h52 := h y x x
  have h53 := S h50
  have h54 := C (C h10 h48) h39
  have h55 := T h47 (C (C h39 (T h54 h53)) h6)
  have h56 := C h6 h55
  have h57 := C (C h10 (T h56 (C h52 h51))) h10
  have h58 := C h6 h51
  have h59 := h y v2 x
  have h60 := S h59
  have h61 := C (C h10 (T (C h60 h55) h58)) h10
  let v62 := M v2 (M v2 v2)
  have h63 := h v62 x x
  have h64 := h v2 y v3
  have h65 := S h64
  have h66 := C h34 (C h65 h34)
  have h67 := C (T (T (T (T (T h66 h63) h61) h57) h46) (C h10 (C h40 h10))) h39
  have h68 := C h34 (C h64 h34)
  have h69 := S h63
  have h70 := C (C h10 (T h56 (C h59 h51))) h10
  have h71 := C (C h10 (T (C h49 h55) h58)) h10
  have h72 := h (M v1 v3) x x
  let v73 := M v2 (M (M y v1) v2)
  have h74 := h v1 v0 v73
  have h75 := h v73 z v1
  have h76 := R v1
  have h77 := h z v1 y
  have h78 := S h77
  have h79 := h y z z
  have h80 := R z
  have h81 := h z z v1
  have h82 := C (C h76 (T h81 (C (C h80 (S h79)) h76))) h6
  have h83 := T h82 h78
  have h84 := h y v2 v1
  have h85 := C (C h76 (T (C (C h80 h79) h76) (S h81))) h6
  have h86 := T h77 h85
  have h87 := C h6 h86
  have h88 := T (C (C h80 (T h87 (C h84 h83))) h76) (S h75)
  have h89 := R v0
  have h90 := h z v1 v0
  have h91 := C h6 h83
  have h92 := h v1 y z
  let v93 := M z v0
  have h94 := h v93 v3 v3
  have h95 := S h94
  have h96 := h y v2 v3
  have h97 := S h96
  have h98 := C (C h80 (T (C h97 h86) h91)) h39
  have h99 := h (M v2 (M (M y v3) v2)) z v3
  have h100 := C (C h39 (T h96 (C (T h99 h98) h39))) h39
  have h101 := T h100 h95
  have h102 := C (T (T (C h76 (C h101 h76)) (C (T h92 (C h91 (T h90 (C (C h76 h88) h89)))) h88)) (S h74)) h39
  have h103 := h v7 v1 v3
  have h104 := h v7 v2 v3
  have h105 := S h104
  have h106 := S h99
  have h107 := C (C h80 (T h87 (C h96 h83))) h39
  have h108 := C (C h39 (T (C (T h107 h106) h39) h97)) h39
  have h109 := T h94 h108
  have h110 := C (C h34 (C h109 h34)) h39
  have h111 := C (T (T (T (T (T (T (T (T h110 h105) h103) h102) h72) h71) h70) h69) h68) h39
  have h112 := C (C h34 (C h101 h34)) h39
  have h113 := h v93 v2 v2
  have h114 := S h113
  have h115 := h v93 x x
  have h116 := C (C h80 (T (C h60 h86) h91)) h10
  have h117 := h v62 z x
  have h118 := h (M x v2) x x
  have h119 := h y y v2
  have h120 := S h119
  have h121 := h (M y (M (M y v2) y)) x v2
  have h122 := C (C h34 (T h119 (C (T h121 (C (T (T (T (T (C h10 (T (C h120 h55) h58)) h118) (C (C h10 (T (C (T h70 h69) h10) h60)) h10)) (C (C h10 (T h59 (C (T h117 h116) h10))) h10)) (S h115)) h34)) h34))) h34
  have h123 := C h39 (T (C (T (T (C (T h122 h114) h39) h107) h106) h39) h97)
  have h124 := C (T (T h123 h104) h112) h39
  let v125 := M v2 y
  let v126 := M v125 v2
  have h127 := h v126 v3 v3
  have h128 := h v125 v3 v2
  have h129 := h (M v3 (M v125 v3)) x y
  have h130 := h v2 v3 y
  have h131 := h v2 v0 y
  have h132 := S h131
  let v133 := M v0 (M v125 v0)
  have h134 := h v133 x y
  have h135 := h v133 v2 y
  have h136 := C h34 (C h131 h34)
  have h137 := C h34 (T (T (C (T (C h136 h6) (S h135)) h34) (C (T (T (T h134 (C (T (C h10 (C h132 h10)) (C h10 (C h130 h10))) h6)) (S h129)) (C h39 (C (T h128 (C (C h39 (T (C (T (T (T (T h127 h124) h111) h67) h44) h39) h41)) h34)) h39))) h34)) (S h38))
  have h138 := C (T (T (T (T h137 h37) h35) h29) h27) h6
  have h139 := h v62 v2 y
  have h140 := S h117
  have h141 := C (C h80 (T h87 (C h59 h83))) h10
  have h142 := C (C h34 (T (C (T (C (T (T (T (T h115 (C (C h10 (T (C (T h141 h140) h10) h60)) h10)) (C (C h10 (T h59 (C (T h63 h61) h10))) h10)) (S h118)) (C h10 (T h56 (C h119 h51)))) h34) (S h121)) h34) h120)) h34
  have h143 := T h96 (C (T (T h99 h98) (C (T h113 h142) h39)) h39)
  have h144 := C h34 (C h132 h34)
  have h145 := C (T (T (T (T h144 h139) h138) h26) h9) h6
  have h146 := C (C h10 (T (C (S h52) h55) h58)) h10
  have h147 := h v2 v2 y
  have h148 := C (T (T (T (T (T (C h10 (C (S h147) h10)) h45) h146) h70) h69) h136) h6
  let v149 := M v2 v126
  have h150 := h v149 x y
  have h151 := h v149 x x
  have h152 := S h151
  have h153 := S h150
  have h154 := C (T (T (T (T (T h144 h63) h61) h57) h46) (C h10 (C h147 h10))) h6
  have h155 := S h139
  have h156 := S h127
  have h157 := C h39 h143
  have h158 := C (T (T h110 h105) h157) h39
  have h159 := S h103
  have h160 := T h75 (C (C h80 (T (C (S h84) h86) h91)) h76)
  have h161 := C (T (T h74 (C (T (C h87 (T (C (C h76 h160) h89) (S h90))) (S h92)) h160)) (C h76 (C h109 h76))) h39
  have h162 := S h72
  have h163 := C (C h10 (T h56 (C h48 h51))) h10
  have h164 := C (T (T (T (T (T (T (T (T h66 h63) h61) h163) h162) h161) h159) h104) h112) h39
  have h165 := C (T (T (T (T (T (C h10 (C h41 h10)) h45) h146) h70) h69) h68) h39
  have h166 := C h34 (T (T h38 (C (T (T (T (C h39 (C (T (C (C h39 (T h40 (C (T (T (T (T h43 h165) h164) h158) h156) h39))) h34) (S h128)) h39)) h129) (C (T (C h10 (C (S h130) h10)) (C h10 (C h131 h10))) h6)) (S h134)) h34)) (C (T h135 (C h144 h6)) h34))
  have h167 := S h37
  have h168 := C (T (C h27 h6) (S h31)) h10
  have h169 := C (C h10 (T h168 (C (T h33 (C (C h34 (C h24 h34)) h6)) h10))) h6
  have h170 := S h22
  have h171 := C (C h6 (C h14 h6)) h10
  have h172 := S h17
  have h173 := C h10 (C h13 h10)
  have h174 := C (T (T (T (T h8 (C (T (T (T (T (C h10 (C h5 h10)) h12) (C (C h10 (C (T (T (T (C h173 h10) h172) h18) h171) h10)) h10)) h170) h27) h6)) (C (T (T (T (T h25 h28) h169) h167) h166) h6)) h155) h136) h6
  have h175 := C h10 (C (C (T (T (T h4 h174) h154) h153) h10) h10)
  have h176 := h (M x (M v11 x)) x x
  have h177 := S h176
  have h178 := h v3 x x
  have h179 := C (T h15 (C h10 (C h178 h10))) h10
  have h180 := C (T (T (T (T (T h20 h19) h17) h179) h177) h175) h10
  have h181 := T (T (T (T (T h180 h152) h150) h148) h145) h5
  have h182 := h y v3 z
  have h183 := S h182
  have h184 := h (M v3 (M v0 v3)) x y
  have h185 := h v0 v3 y
  have h186 := S h185
  let v187 := M v3 (M (M v0 y) v3)
  have h188 := h v187 v3 y
  have h189 := h v187 v2 y
  let v190 := M v2 (M v0 v2)
  have h191 := h v190 x y
  have h192 := h v190 x x
  have h193 := h v0 v3 x
  have h194 := S h193
  let v195 := M v0 x
  let v196 := M v3 (M v195 v3)
  have h197 := h v196 v2 x
  have h198 := h v196 x x
  have h199 := h (M x v195) x x
  let v200 := M (M z y) v0
  have h201 := h v0 y v200
  have h202 := R v200
  have h203 := h z v0 y
  have h204 := h (M v0 v200) x y
  have h205 := h z z z
  have h206 := C (S h205) h10
  have h207 := C h205 h10
  have h208 := h z y y
  have h209 := C h10 (T (C (S h208) h10) h207)
  have h210 := C h10 (T h206 (C h208 h10))
  have h211 := h (M v1 z) x y
  have h212 := h v1 v3 v3
  have h213 := S h212
  have h214 := h v3 y v1
  let v215 := M y (M v42 y)
  have h216 := h v215 v1 v3
  have h217 := h v215 v2 v3
  have h218 := C (C h39 (T (T (T h111 (S h217)) h216) (C (C h76 (T (C (T h65 h56) h76) (S h214))) h39))) h39
  let v219 := M v2 (M v93 v2)
  have h220 := h v219 v3 v3
  have h221 := h v219 x v0
  have h222 := S h221
  have h223 := h z v2 v0
  have h224 := h z v3 v0
  have h225 := C (T (C h10 (T (C (S h224) h10) h207)) (C h10 (T h206 (C h223 h10)))) h89
  let v226 := M v3 (M v93 v3)
  have h227 := h v226 x v0
  have h228 := C (T (T (T (T (T (T (T (C h10 (C (T (T (T (T (T (T (C (T (T (T (T (T h227 h225) h222) h220) h218) h213) h80) h211) (C (T (C h10 (T (C h83 h10) h207)) h210) h6)) (C (T h209 (C h10 (T h206 (C h203 h10)))) h6)) (S h204)) (C (T h87 (C h6 (T (T h82 h78) h203))) h202)) (S h201)) h10)) h199) (C (C h10 (T (C (T (C (C h10 (C h193 h10)) h10) (S h198)) h10) h194)) h10)) (C (C h10 (T h193 (C (T h197 (C (C h34 (C h194 h34)) h10)) h10))) h10)) (S h192)) h191) (C (C h10 (T (C (T (C (C h34 (C h185 h34)) h6) (S h189)) h10) (C (T h188 (C (C h39 (C h186 h39)) h6)) h10))) h6)) (S h184)) h80
  have h229 := h v226 x z
  have h230 := S h227
  have h231 := C (T (C h10 (T (C (S h223) h10) h207)) (C h10 (T h206 (C h224 h10)))) h89
  have h232 := S h220
  have h233 := C (C h39 (T (T (T (C (C h76 (T h214 (C (T h58 h64) h76))) h39) (S h216)) h217) h164)) h39
  have h234 := T (T (T (T (T (T (T (T h212 h233) h232) h221) h231) h230) h229) h228) h183
  have h235 := h x x v3
  have h236 := S h235
  let v237 := M x v3
  let v238 := M v237 x
  let v239 := M x v238
  have h240 := h v239 v3 x
  have h241 := h v239 x v3
  have h242 := h x v3 x
  have h243 := C (S h242) h10
  have h244 := C h242 h10
  have h245 := h x v1 v3
  have h246 := C h10 (T (C (S h245) h10) h244)
  have h247 := C h10 (T h243 (C h245 h10))
  have h248 := h x v3 v3
  let v249 := M v237 v3
  have h250 := h (M v3 v249) x v3
  have h251 := C h10 h181
  have h252 := C (T (C h10 (C (S h178) h10)) h173) h10
  have h253 := C h10 (C (C (T (T (T h150 h148) h145) h5) h10) h10)
  have h254 := C (T (T (T (T (T h253 h176) h252) h172) h18) h171) h10
  have h255 := T (T (T (T (T h4 h174) h154) h153) h151) h254
  have h256 := C h10 h255
  have h257 := C h256 h10
  have h258 := C (T (C h39 (T (C (T (T (T (T (T (T (T (T (C (T (T (T (T (T h257 h170) h28) h169) h167) h166) h234) h155) h63) h61) h163) h162) h161) h159) h157) h39) h124)) (C h39 (T (T (T (T (T h158 h156) h122) h114) h94) h108))) h234
  have h259 := h v238 v3 v1
  have h260 := C h251 h10
  have h261 := h v237 v3 x
  have h262 := S h261
  have h263 := h v3 z v3
  have h264 := S h263
  let v265 := M v3 v3
  have h266 := h (M z (M v265 z)) y v3
  have h267 := T (C (T (C (T (T h257 h170) (C h6 (C h263 h6))) h39) (S h266)) h39) h264
  have h268 := S h259
  have h269 := S h203
  have h270 := T (T (T (T (T (T (T (T h182 (C (T (T (T (T (T (T (T h184 (C (C h10 (T (C (T (C (C h39 (C h185 h39)) h6) (S h188)) h10) (C (T h189 (C (C h34 (C h186 h34)) h6)) h10))) h6)) (S h191)) h192) (C (C h10 (T (C (T (C (C h34 (C h193 h34)) h10) (S h197)) h10) h194)) h10)) (C (C h10 (T h193 (C (T h198 (C (C h10 (C h194 h10)) h10)) h10))) h10)) (S h199)) (C h10 (C (T (T (T (T (T (T h201 (C (T (C h6 (T (T h269 h77) h85)) h91) h202)) h204) (C (T (C h10 (T (C h269 h10) h207)) h210) h6)) (C (T h209 (C h10 (T h206 (C h86 h10)))) h6)) (S h211)) (C (T (T (T (T (T h212 h233) h232) h221) h231) h230) h80)) h10))) h80)) (S h229)) h227) h225) h222) h220) h218) h213
  have h271 := C (T (C h39 (T (T (T (T (T h100 h95) h113) h142) h127) h124)) (C h39 (T h158 (C (T (T (T (T (T (T (T (T h123 h103) h102) h72) h71) h70) h69) h139) (C (T (T (T (T (T h137 h37) h35) h29) h22) h260) h270)) h39)))) h270
  have h272 := C (T (T h23 h271) h268) h267
  have h273 := T h263 (C (T h266 (C (T (T (C h6 (C h264 h6)) h22) h260) h39)) h39)
  have h274 := C h181 h273
  have h275 := C h39 (T h274 h272)
  have h276 := h (M v3 v265) x y
  have h277 := h v30 v3 y
  have h278 := h v21 v3 x
  have h279 := C h255 h267
  have h280 := C (T (T h259 h258) h24) h273
  have h281 := C h39 (T h280 h279)
  T (T (T (T h235 (C (T (T h240 (C (T (C h39 (T (T (C (T (T (T (C (T (T (T (T h241 (C (T (C h10 (T (C h236 h10) h244)) h247) h39)) (C (T h246 (C h10 (T h243 (C h248 h10)))) h39)) (S h250)) (C h39 (C (T (T (T (T (T (T (T h256 (C h10 (T (T (T (T (T (T (T (T (T (T h180 h152) h150) h148) h145) h5) h23) h271) h268) h257) (C (T (T h251 h261) (C (T (T (T (T (T (T (T (T (T (T (T (T (T h281 (C h39 (C h181 h39))) h276) (C (C h10 (T (C (T (C (C h39 (C h23 h39)) h6) (S h277)) h10) h32)) h6)) h29) h22) h260) h259) h258) h24) h4) h174) h154) h153) h10)) h10)))) h253) h176) h252) h172) h18) h171) h39))) h10) (S h278)) h22) h260) h39) h280) h279)) h275) h10)) h262) h39)) (h v249 v3 y)) (C (T (T (T (T (T (T (T (T (T (T (T (T (T (C h255 (T (T (C (T (T (C (R v249) h270) (C (T (C (T (T h261 (C (T h281 (C h39 (T (T h274 h272) (C (T (T (T h257 h170) h278) (C (T (T (T (T (C h39 (C (T (T (T (T (T (T (T h20 h19) h17) h179) h177) h175) (C h10 (T (T (T (T (T (T (T (T (T (T (C (T (T (C (T (T (T (T (T (T (T (T (T (T (T (T (T h150 h148) h145) h5) h23) h271) h268) h257) h170) h28) (C (C h10 (T h168 (C (T h277 (C (C h39 (C h24 h39)) h6)) h10))) h6)) (S h276)) (C h39 (C h255 h39))) h275) h10) h262) h256) h10) h260) h259) h258) h24) h4) h174) h154) h153) h151) h254))) h251) h39)) h250) (C (T (C h10 (T (C (S h248) h10) h244)) h247) h39)) (C (T h246 (C h10 (T h243 (C h235 h10)))) h39)) (S h241)) h10)) h39)))) h10)) (S h240)) h39) h236) (T (T (T (T (T (T (T (T (T (T h212 h233) h232) h221) h231) h230) h229) h228) h183) h59) (C (T (T h117 h116) (C (T (T (T (T (T (T h113 h142) h127) h124) h111) h67) h44) h10)) h10)))) (C h10 (T (C (T (T (C (T (T (T (T (T (T h43 h165) h164) h158) h156) h122) h114) h10) h141) h140) h10) h60))) h39) h54) h53)) (C (R (M (M v21 x) x)) h234)) (C h181 h143)) h123) h103) h102) h72) h71) h70) h69) h139) h138) h26) h9) h6)) h5

