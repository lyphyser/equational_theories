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
theorem Equation2519_implies_Equation1876 (G: Type _) [Magma G] (h: Equation2519 G) : Equation1876 G := fun x y z =>
  let v0 := M z y
  let v1 := M y z
  let v2 := M x v1
  let v3 := M v2 v0
  have h4 := R z
  have h5 := R v3
  have h6 := h z z v3
  have h7 := S h6
  let v8 := M z v3
  let v9 := M z (M v8 z)
  have h10 := h v9 y v3
  have h11 := S h10
  have h12 := R y
  have h13 := C (C h12 (C h6 h12)) h5
  have h14 := C (C h5 (T (C (T h13 h11) h5) h7)) h5
  let v15 := M y v0
  have h16 := h v15 v3 v3
  have h17 := h v15 v3 v1
  have h18 := S h17
  have h19 := R v1
  have h20 := h z v2 v1
  have h21 := S h20
  have h22 := C (C h12 (C h21 h12)) h19
  let v23 := M z v1
  let v24 := M v2 (M v23 v2)
  have h25 := h v24 y v1
  have h26 := h v24 x v1
  have h27 := S h26
  have h28 := R x
  have h29 := h z v1 x
  have h30 := S h29
  have h31 := C h30 h28
  have h32 := C h28 (T h31 (C h20 h28))
  have h33 := C h29 h28
  have h34 := h z v1 v1
  have h35 := C (T (C h28 (T (C (S h34) h28) h33)) h32) h19
  let v36 := M v23 v1
  have h37 := h (M v1 v36) x v1
  have h38 := h v23 v3 v3
  have h39 := h y x v3
  have h40 := S h39
  have h41 := h (M x (M (M y v3) x)) z v3
  have h42 := T (C (C h5 (T h39 (C (T h41 (C (C h4 (C h40 h4)) h5)) h5))) h5) (S h38)
  let v43 := M v3 y
  have h44 := h v43 v1 v3
  have h45 := h v43 x v3
  have h46 := T h38 (C (C h5 (T (C (T (C (C h4 (C h39 h4)) h5) (S h41)) h5) h40)) h5)
  let v47 := M x (M v23 x)
  have h48 := R v47
  have h49 := h v47 x v1
  have h50 := S h49
  have h51 := h z x v1
  have h52 := C h28 (T (C h21 h28) h33)
  have h53 := C (T h52 (C h28 (T h31 (C h51 h28)))) h19
  have h54 := h v24 y v0
  have h55 := S h54
  have h56 := h v0 v3 v2
  have h57 := S h56
  have h58 := R v2
  let v59 := M v0 v2
  let v60 := M v59 v3
  have h61 := R v60
  have h62 := h v3 x v0
  have h63 := S h62
  have h64 := h v0 v1 v3
  have h65 := h x v0 v1
  have h66 := h v1 v3 x
  have h67 := T h66 (C (C h5 (T (C (C h19 h65) h5) (S h64))) h28)
  have h68 := C h28 h67
  have h69 := C (T (C h68 h57) h63) h61
  have h70 := h v3 v2 v60
  have h71 := T h70 h69
  have h72 := C h71 h58
  have h73 := h v0 z v2
  have h74 := S h73
  have h75 := h (M z (M v59 z)) v3 v2
  have h76 := S h75
  have h77 := C h5 (C h73 h5)
  have h78 := C (T (C h68 (T (C (T (C h77 h58) h76) h58) h74)) h63) h58
  let v79 := M v3 (M v0 v3)
  have h80 := h v79 v2 v2
  have h81 := h v79 x x
  have h82 := S h81
  have h83 := h v79 x y
  have h84 := h z v3 y
  have h85 := h z v2 y
  have h86 := h (M v2 v59) x y
  have h87 := h v0 z x
  have h88 := S h87
  have h89 := C (T (T (T (C h58 (C h88 h58)) h86) (C (T (C h28 (T (C (S h85) h28) h33)) (C h28 (T h31 (C h84 h28)))) h12)) (S h83)) h28
  let v90 := M v0 x
  let v91 := M z (M v90 z)
  have h92 := h v91 v2 x
  have h93 := h v91 v1 x
  have h94 := C (C h28 (C (T (T (T (C (C h19 (C h87 h19)) h28) (S h93)) h92) h89) h28)) h28
  let v95 := M v0 v1
  have h96 := h (M v1 v95) x x
  have h97 := R v95
  have h98 := h z v1 y
  have h99 := C (C h12 (S h98)) h97
  have h100 := h v1 y v95
  have h101 := T (T (T (T (T (T (T (T h100 h99) h96) h94) h82) h80) h78) h72) h57
  have h102 := R v0
  have h103 := h v23 v0 v0
  have h104 := h y z v0
  have h105 := S h104
  have h106 := h (M z (M v15 z)) z v0
  have h107 := T (C (C h102 (T h104 (C (T h106 (C (C h4 (C h105 h4)) h102)) h102))) h102) (S h103)
  have h108 := C (T (T (T (C h19 (C h107 h19)) h37) h35) h27) h102
  let v109 := M v0 y
  have h110 := h v109 v1 v0
  have h111 := h v109 x v0
  have h112 := S h111
  have h113 := T h103 (C (C h102 (T (C (T (C (C h4 (C h104 h4)) h102) (S h106)) h102) h105)) h102)
  have h114 := C (T (T (T (T h26 h53) h50) h48) (C h28 (C h113 h28))) h101
  have h115 := T (T (T (T h20 h114) h112) h110) h108
  have h116 := C h12 (T (T (T (T (T (T (T (T (T h100 h99) h96) h94) h82) h80) h78) h72) h57) (C h115 h12))
  have h117 := C (C h5 (T (T (T (T (C (T (T (T (T (T (T (C h116 h101) h55) h26) h53) h50) h48) (C h28 (C h46 h28))) h5) (S h45)) h44) (C (T (T (T (C h19 (C h42 h19)) h37) h35) h27) h5)) (C (T h25 h22) h5))) h19
  let v118 := M y v1
  have h119 := h v118 v3 v1
  have h120 := h v118 v3 v3
  have h121 := S h120
  have h122 := S h100
  have h123 := C (C h12 h98) h97
  have h124 := S h96
  have h125 := S h92
  have h126 := C (T (T (T h83 (C (T (C h28 (T (C (S h84) h28) h33)) (C h28 (T h31 (C h85 h28)))) h12)) (S h86)) (C h58 (C h87 h58))) h28
  have h127 := C (C h28 (C (T (T (T h126 h125) h93) (C (C h19 (C h88 h19)) h28)) h28)) h28
  have h128 := S h80
  have h129 := C h5 (C h74 h5)
  have h130 := T (C (C h5 (T h64 (C (C h19 (S h65)) h5))) h28) (S h66)
  have h131 := C h28 h130
  have h132 := C (T h62 (C h131 (T h73 (C (T h75 (C h129 h58)) h58)))) h58
  have h133 := S h70
  have h134 := C (T h62 (C h131 h56)) h61
  have h135 := T h134 h133
  have h136 := C h135 h58
  have h137 := T (T (T (T (T (T (T (T h56 h136) h132) h128) h81) h127) h124) h123) h122
  have h138 := C (T (C h28 (T (C (S h51) h28) h33)) h32) h19
  have h139 := C (T (T (T (T (C h28 (C h107 h28)) h48) h49) h138) h27) h137
  have h140 := S h110
  have h141 := S h37
  have h142 := C (T h52 (C h28 (T h31 (C h34 h28)))) h19
  have h143 := C (T (T (T h26 h142) h141) (C h19 (C h113 h19))) h102
  have h144 := T (T (T (T h143 h140) h111) h139) h21
  have h145 := C h12 (T (T (T (T (T (T (T (T (T (C h144 h12) h56) h136) h132) h128) h81) h127) h124) h123) h122)
  have h146 := S h25
  have h147 := C (C h12 (C h20 h12)) h19
  have h148 := C (T (T h17 (C (C h5 (T (T (T (T (C (T h147 h146) h5) (C (T (T (T h26 h142) h141) (C h19 (C h46 h19))) h5)) (S h44)) h45) (C (T (T (T (T (T (T (C h28 (C h42 h28)) h48) h49) h138) h27) h54) (C h145 h137)) h5))) h19)) (S h119)) h5
  have h149 := C (C h12 (C h7 h12)) h5
  have h150 := C (T (T h10 h149) h148) h5
  have h151 := T h6 h150
  have h152 := C h135 h151
  have h153 := C h71 h4
  let v154 := M v3 z
  have h155 := h v154 v3 v3
  have h156 := S h155
  have h157 := T h16 h14
  have h158 := C h5 (C h157 h5)
  have h159 := C (T (T h119 h117) h18) h5
  have h160 := C h5 h159
  let v161 := M v118 v3
  have h162 := h (M v3 v161) x v1
  have h163 := S h162
  have h164 := h y v3 v1
  have h165 := h y v1 y
  have h166 := C (S h165) h28
  have h167 := C h165 h28
  have h168 := h y x v1
  have h169 := S h168
  have h170 := C (T (C h28 (T (C h169 h28) h167)) (C h28 (T h166 (C h164 h28)))) h19
  let v171 := M x (M v118 x)
  have h172 := h v171 x v1
  have h173 := h v171 z v1
  have h174 := S h173
  have h175 := C (C h4 (C h168 h4)) h19
  have h176 := C (T (T (T (T (T (T h175 h174) h172) h170) h163) h160) h158) h5
  have h177 := C (T (T (T h176 h156) h153) h152) h5
  have h178 := C (C h4 (C h169 h4)) h19
  have h179 := S h172
  have h180 := C (T (C h28 (T (C (S h164) h28) h167)) (C h28 (T h166 (C h168 h28)))) h19
  have h181 := C h5 h148
  have h182 := T (C (C h5 (T h6 (C (T h10 h149) h5))) h5) (S h16)
  have h183 := C h5 (C h182 h5)
  have h184 := C (T (T (T (T (T (T h183 h181) h162) h180) h179) h173) h178) h5
  have h185 := C h135 h4
  have h186 := C (T (T h159 h13) h11) h5
  have h187 := T h186 h7
  have h188 := C h71 h187
  have h189 := h v118 z v3
  have h190 := S h189
  have h191 := h v9 x v3
  have h192 := h z v3 v3
  let v193 := M v8 v3
  have h194 := h (M v3 v193) x v3
  have h195 := C h144 h5
  have h196 := T (T (T (T (T (T h186 h7) h20) h114) h112) h110) h108
  have h197 := C h196 h5
  have h198 := h (M v3 v60) x v2
  have h199 := h (M x v90) x x
  have h200 := h v91 x x
  let v201 := M v1 v2
  have h202 := h v201 x z
  have h203 := S h202
  have h204 := h x z z
  have h205 := S h204
  let v206 := M x z
  let v207 := M z (M v206 z)
  have h208 := h v207 v1 z
  have h209 := T h208 (C (C h19 (T (C h205 h67) h131)) h4)
  have h210 := h v207 x z
  have h211 := S h210
  have h212 := h x v2 v2
  have h213 := C (S h212) h28
  have h214 := C h28 (T h213 (C h204 h28))
  have h215 := C h212 h28
  have h216 := h x v3 z
  have h217 := h (M v3 (M v206 v3)) x z
  have h218 := h v206 v3 x
  let v219 := M z x
  let v220 := M v1 (M v219 v1)
  have h221 := h v220 y x
  have h222 := h v15 x x
  have h223 := h v36 y v3
  have h224 := S h223
  have h225 := h (M y (M v154 y)) x z
  have h226 := h v3 y z
  let v227 := M v3 x
  have h228 := h (M x v227) x x
  have h229 := h v3 v0 x
  have h230 := S h229
  let v231 := M v0 (M v227 v0)
  have h232 := h v231 x x
  have h233 := h v231 v0 x
  have h234 := h (M v0 (M v3 v0)) x x
  have h235 := h v3 x z
  have h236 := h (M x (M v154 x)) v0 z
  have h237 := C (T (T (T (T h236 (C (T (T (C h102 (C (S h235) h102)) h234) (C (C h28 (T (C (T (C (C h102 (C h229 h102)) h28) (S h233)) h28) h230)) h28)) h4)) (C (T (T (C (C h28 (T h229 (C (T h232 (C (C h28 (C h230 h28)) h28)) h28))) h28) (S h228)) (C h28 (C h226 h28))) h4)) (S h225)) (C h12 (C (T h155 h184) h12))) h5
  have h238 := C (T (T (T (T (C h12 (C (T h176 h156) h12)) h225) (C (T (T (C h28 (C (S h226) h28)) h228) (C (C h28 (T (C (T (C (C h28 (C h229 h28)) h28) (S h232)) h28) h230)) h28)) h4)) (C (T (T (C (C h28 (T h229 (C (T h233 (C (C h102 (C h230 h102)) h28)) h28))) h28) (S h234)) (C h102 (C h235 h102))) h4)) (S h236)) h5
  have h239 := T (T (C (T h223 h238) h28) (C (T (T (T (T (T (T (T (T h237 h224) h175) h174) h172) h170) h163) h160) (C h5 (C (T h222 (C (C h28 (T (C (T (C (C h12 (C h29 h12)) h28) (S h221)) h28) h30)) h28)) h5))) h28)) (S h218)
  have h240 := C (T (T (T (C h5 (C h239 h5)) h217) (C (T (C h28 (T (C (S h216) h28) h215)) h214) h4)) h211) h28
  have h241 := h v36 v3 x
  have h242 := h v36 y x
  have h243 := S h242
  have h244 := T (T h218 (C (T (T (T (T (T (T (T (T (C h5 (C (T (C (C h28 (T h29 (C (T h221 (C (C h12 (C h30 h12)) h28)) h28))) h28) (S h222)) h5)) h181) h162) h180) h179) h173) h178) h223) h238) h28)) (C (T h237 h224) h28)
  have h245 := h (M y (M v206 y)) x z
  have h246 := h x y z
  have h247 := C h28 (T (C h205 h28) h215)
  have h248 := h v207 z x
  have h249 := h v15 z z
  have h250 := h z v0 z
  have h251 := S h250
  let v252 := M z z
  have h253 := h (M v0 (M v252 v0)) y z
  have h254 := h v252 v3 z
  have h255 := C h144 h4
  have h256 := C h196 h4
  have h257 := T (T (T (T (T (T h143 h140) h111) h139) h21) h6) h150
  have h258 := C h257 h4
  have h259 := C h115 h4
  have h260 := h v220 z x
  have h261 := h v220 x x
  have h262 := h z v2 x
  have h263 := S h262
  have h264 := h (M v2 (M v219 v2)) x x
  have h265 := C (T (T (T (T (T (T (T (T (T h264 (C (C h28 (T (C h263 h28) h33)) h28)) (S h261)) h260) (C (T (T (C h4 (T (C h30 h4) h259)) (C h4 h258)) (C h4 (T (T (T h256 h255) h254) (C (T (T (T (T (T (T (T (T (C h5 (C (T (C (C h4 (T h250 (C (T h253 (C (C h12 (C h251 h12)) h4)) h4))) h4) (S h249)) h5)) h181) h162) h180) h179) h173) h178) h241) h240) h4)))) h28)) (S h248)) h210) (C (T h247 (C h28 (T h213 (C h246 h28)))) h4)) (S h245)) (C h12 (C h244 h12))) h28
  have h266 := C (C h28 (T (T (T (T (T h262 h265) h243) h241) h240) (C h209 h28))) h4
  have h267 := C h239 h4
  have h268 := C h151 (T (T (T (T (T (T (T (T (T h267 h266) h203) (C (T (T (T (T (T h100 h99) h96) h94) h82) h77) h58)) h76) h75) (C (T (T (T (T h129 h81) (C (C h28 (C (T (T (T h126 h125) h200) (C (C h28 (C h88 h28)) h28)) h28)) h28)) (S h199)) (C h28 (C h56 h28))) h58)) (S h198)) h134) h133)
  have h269 := C h244 h4
  have h270 := C h4 h269
  have h271 := C (T (T (T h270 h268) h197) h195) h5
  have h272 := T (C (C h19 (T h68 (C h204 h130))) h4) (S h208)
  have h273 := h v201 v3 z
  have h274 := S h241
  have h275 := C (T (T (T h210 (C (T h247 (C h28 (T h213 (C h216 h28)))) h4)) (S h217)) (C h5 (C h244 h5))) h28
  have h276 := C (T (T (T (T (T (T (T (T (T (C h12 (C h239 h12)) h245) (C (T (C h28 (T (C (S h246) h28) h215)) h214) h4)) h211) h248) (C (T (T (C h4 (T (T (T (C (T (T (T (T (T (T (T (T h275 h274) h175) h174) h172) h170) h163) h160) (C h5 (C (T h249 (C (C h4 (T (C (T (C (C h12 (C h250 h12)) h4) (S h253)) h4) h251)) h4)) h5))) h4) (S h254)) h259) h258)) (C h4 h256)) (C h4 (T h255 (C h29 h4)))) h28)) (S h260)) h261) (C (C h28 (T h31 (C h262 h28))) h28)) (S h264)) h28
  have h277 := C (C h28 (T (T (T (T (T (C h272 h28) h275) h274) h242) h276) h263)) h4
  have h278 := C h187 (T (T (T (T (T (T (T (T (T h70 h69) h198) (C (T (T (T (T (C h28 (C h57 h28)) h199) (C (C h28 (C (T (T (T (C (C h28 (C h87 h28)) h28) (S h200)) h92) h89) h28)) h28)) h82) h77) h58)) h76) h75) (C (T (T (T (T (T h129 h81) h127) h124) h123) h122) h58)) h202) h277) h269)
  have h279 := C h257 h5
  have h280 := C h115 h5
  have h281 := C (T (T (T h280 h279) h278) (C h4 (T (T (T (T h267 h266) h203) h273) (C (T (T (T (T (T (T (C h5 (T (C h272 h5) h271)) h194) (C (T (C h28 (T (C (S h192) h28) h33)) (C h28 (T h31 (C h6 h28)))) h5)) (S h191)) h10) h149) h148) h4)))) h5
  have h282 := h v193 v3 v3
  have h283 := S h282
  have h284 := C h4 h267
  have h285 := C (T (T (T h280 h279) h278) h284) h5
  have h286 := C (T (T (T (C h4 (T (T (T (T (C (T (T (T (T (T (T h159 h13) h11) h191) (C (T (C h28 (T (C h7 h28) h33)) (C h28 (T h31 (C h192 h28)))) h5)) (S h194)) (C h5 (T h285 (C h209 h5)))) h4) (S h273)) h202) h277) h269)) h268) h197) h195) h5
  have h287 := C (T (T (T (C h12 (C h196 h12)) h145) h189) h286) h5
  have h288 := h v161 y v3
  have h289 := C h5 (C (T h288 h287) h5)
  have h290 := h v154 v1 v3
  have h291 := S h290
  have h292 := C (T (T h281 h190) h116) h102
  have h293 := R v193
  have h294 := C h293 h101
  have h295 := C (T (C h19 (T (T (T (T h294 h292) h55) h25) h22)) (C h19 (C h157 h19))) h5
  have h296 := h v8 v1 v3
  have h297 := h v207 v3 x
  have h298 := S h297
  have h299 := C (T (T (T h237 h224) h241) h240) h5
  have h300 := C (T (T (T (T (T (T (T (T h183 h181) h162) h180) h179) h173) h178) h223) h238) h5
  have h301 := C h293 h137
  have h302 := C (T (T h145 h189) h286) h102
  have h303 := h v24 v3 v0
  have h304 := C h30 h5
  have h305 := C h29 h5
  have h306 := S h296
  have h307 := C (T (C h19 (C h182 h19)) (C h19 (T (T (T (T h147 h146) h54) h302) h301))) h5
  have h308 := C (T (T (T (T (T (T (T (T h237 h224) h175) h174) h172) h170) h163) h160) h158) h5
  have h309 := C (T (T (T h275 h274) h223) h238) h5
  have h310 := h v23 v3 v1
  have h311 := R (M v24 v0)
  have h312 := R (M v161 v3)
  have h313 := C (C h19 (T (T (T (T (T (T (T (T (T (C h312 h101) (C h196 h137)) (C h311 h101)) (C h144 h137)) h310) (C (T (T (C h5 (T (T h176 h300) h299)) (C h5 (T (T (T (T (T (T h309 h308) h156) h290) h307) h306) h305))) (C h5 (T h304 h280))) h101)) (S h303)) h54) h302) h301)) h5
  have h314 := h v161 v1 v3
  have h315 := S h288
  have h316 := C (T (T (T h281 h190) h116) (C h12 (C h257 h12))) h5
  have h317 := C h271 h5
  have h318 := C h285 h5
  have h319 := C (T (T (T (T (T (T (T (T (T (T (T h186 h7) h262) h265) h243) h175) h174) h172) h170) h163) (C h5 (T (T h288 h287) h318))) (C h5 (T (T (T (T (T (T (T (T (T h317 h316) h315) h314) h313) h295) h291) h155) h300) h299))) h28
  have h320 := C h151 h28
  have h321 := C (T (T (T (T (T (T (T (T (T (T (T (T h320 h319) h298) h270) h268) h197) h195) h296) h295) h291) h153) h152) h289) h5
  have h322 := C h187 h28
  have h323 := S h314
  have h324 := C (C h19 (T (T (T (T (T (T (T (T (T h294 h292) h55) h303) (C (T (T (C h5 (T h195 h305)) (C h5 (T (T (T (T (T (T h304 h296) h295) h291) h155) h300) h299))) (C h5 (T (T h309 h308) h184))) h137)) (S h310)) (C h115 h101)) (C h311 h137)) (C h257 h101)) (C h312 h137))) h5
  have h325 := C (T (T (T (T (T (T (T (T (T (T (T (C h5 (T (T (T (T (T (T (T (T (T h309 h308) h156) h290) h307) h324) h323) h288) h287) h318)) (C h5 (T (T h317 h316) h315))) h162) h180) h179) h173) h178) h242) h276) h263) h6) h150) h28
  have h326 := C (T h316 h315) h5
  have h327 := C (T (T (T (T (T (T (T (T (T (T (T (T (C h5 h326) h188) h185) h290) h307) h306) h280) h279) h278) h284) h297) h325) h322) h5
  have h328 := C (T (T (T (T (T (T (T (T (T (T (T (T h320 h319) h298) h270) h268) h197) h195) h296) h324) h323) h288) h287) (C (T h282 h327) h5)) h5
  T (T h204 (C (T (T (T (T (T (T (T (T (T (T (T (T h270 h268) h197) h195) h296) h295) h291) h153) h152) h289) (C h5 (T (T (T (T (T (T (T (T (T h326 h186) h7) h262) h265) h243) (h v36 v3 v3)) (C (C h5 (T (T (T (T (T (T h177 h121) h189) h286) h282) h327) h328)) h5)) (S (h (M v219 v3) v3 v3))) h328))) (C h5 (T (T (T (T (T (T (C (T (T (T (T (T (T (T (T (T (T (T (T (C (T h321 h283) h5) h316) h315) h314) h313) h306) h280) h279) h278) h284) h297) h325) h322) h5) h321) h283) h281) h190) h120) (C (T (T (T h188 h185) h155) h184) h5)))) (C h5 (T (T (T (T (T (T h177 h121) h119) h117) h18) h16) h14))) h4)) (S (h v3 v3 z))

