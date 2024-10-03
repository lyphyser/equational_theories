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
theorem Equation2925_implies_Equation2349 (G: Type _) [Magma G] (h: Equation2925 G) : Equation2349 G := fun x y z =>
  have h0 := R z
  let v1 := M z x
  let v2 := M y v1
  let v3 := M y v2
  have h4 := h v3 x z
  have h5 := S h4
  let v6 := M v3 z
  let v7 := M x v6
  let v8 := M v7 x
  have h9 := h v8 v3 z
  have h10 := S h9
  have h11 := R v3
  let v12 := M (M v3 v3) v3
  have h13 := h v12 v2 v2
  have h14 := S h13
  have h15 := R v2
  have h16 := h y v3 v2
  have h17 := h y x v3
  have h18 := S h17
  have h19 := C h15 h18
  have h20 := C h15 h17
  have h21 := R y
  have h22 := h v1 z v2
  have h23 := S h22
  have h24 := C (T (C (C h21 h23) h21) h20) h15
  let v25 := M v1 v2
  let v26 := M (M z v25) z
  have h27 := h v26 y v2
  have h28 := C (T (T h27 h24) (C (T h19 (C h15 h16)) h15)) h15
  have h29 := C (T (T (T h22 h28) h14) (C (C h11 h4) h11)) h0
  have h30 := h x y z
  let v31 := M x z
  let v32 := M (M y v31) y
  have h33 := R x
  have h34 := h x v6 x
  have h35 := S h34
  have h36 := C h33 h35
  have h37 := C h33 h34
  have h38 := R v6
  have h39 := h x y v2
  have h40 := S h39
  let v41 := M x v2
  let v42 := M (M y v41) y
  have h43 := h v42 x v2
  have h44 := S h43
  have h45 := h x v1 v2
  have h46 := S h45
  have h47 := C (T (C (T (C h33 h46) h37) h33) (C (T h36 (C h33 h39)) h33)) h15
  let v48 := M (M v1 v41) v1
  have h49 := h v48 x v2
  have h50 := h v48 z v2
  have h51 := S h50
  have h52 := S h27
  have h53 := C (T h19 (C (C h21 h22) h21)) h15
  have h54 := C (T (T (C (T (C h15 (S h16)) h20) h15) h53) h52) h15
  have h55 := C (T (T (T (C (C h11 h5) h11) h13) h54) h23) h0
  have h56 := C (T (T h9 h55) (C (C h0 h45) h0)) h15
  have h57 := h v8 x x
  have h58 := S h57
  have h59 := h v6 v1 x
  have h60 := S h59
  have h61 := C (C (C h33 h60) h33) h33
  let v62 := M (M v1 (M v6 x)) v1
  have h63 := h v62 x x
  have h64 := h v62 v2 x
  have h65 := C (C (C h33 (T (T (T (C (C (C h15 h59) h15) h33) (S h64)) h63) h61)) h33) h33
  let v66 := M v2 v6
  have h67 := h (M v66 v2) x x
  have h68 := h v2 v6 v3
  have h69 := S h68
  let v70 := M v2 v3
  have h71 := h (M (M v6 v70) v6) x v3
  have h72 := h v2 v2 v3
  have h73 := S h72
  have h74 := C (C h33 h73) h33
  let v75 := M (M v2 v70) v2
  have h76 := h v75 x v3
  have h77 := h v75 y v3
  have h78 := S h77
  have h79 := C h11 h18
  have h80 := C (T h79 (C (C h21 h72) h21)) h11
  have h81 := C (T (T (T (T h80 h78) h76) (C (T h74 (C (C h33 h68) h33)) h11)) (S h71)) h11
  let v82 := M y v3
  let v83 := M (M x v82) x
  have h84 := h v83 v3 v3
  have h85 := h v83 x v3
  have h86 := S h85
  have h87 := h y v3 v3
  have h88 := C (C (T (C h33 (S h87)) (C h33 h17)) h33) h11
  let v89 := M (M v3 v82) v3
  have h90 := h v89 x v3
  have h91 := h v89 x v1
  have h92 := S h91
  have h93 := R v1
  have h94 := S h90
  have h95 := C (C (T (C h33 h18) (C h33 h87)) h33) h11
  have h96 := S h84
  have h97 := C h11 h17
  have h98 := C (T (C (C h21 h73) h21) h97) h11
  have h99 := S h76
  have h100 := C (C h33 h72) h33
  have h101 := C (T (T (T (T h71 (C (T (C (C h33 h69) h33) h100) h11)) h99) h77) h98) h11
  have h102 := h v2 z v2
  have h103 := S h102
  let v104 := M v2 v2
  have h105 := h (M (M z v104) z) x v2
  have h106 := h v2 v6 v2
  have h107 := h (M (M v6 v104) v6) x v2
  have h108 := h v104 y v2
  have h109 := h (M v104 v2) x z
  have h110 := h v2 z z
  have h111 := S h110
  let v112 := M (M z (M v2 z)) z
  have h113 := h v112 v2 z
  have h114 := h v112 x z
  have h115 := S h114
  have h116 := C (C (C h33 h110) h33) h0
  let v117 := M v41 x
  have h118 := h v117 x z
  have h119 := h v117 v2 v1
  have h120 := S h119
  have h121 := h y x v1
  have h122 := C (T (T h27 h24) (C (T h19 (C h15 h121)) h15)) h93
  have h123 := S h121
  have h124 := C (T (T (C (T (C h15 h123) h20) h15) h53) h52) h93
  have h125 := h v1 z y
  have h126 := R v117
  have h127 := C (C (T (C h126 (S h125)) h123) (T h119 h124)) h21
  let v128 := M (M z (M v1 y)) z
  have h129 := h v128 v117 y
  have h130 := C (T (T (T (C (C h38 (T (C (T (T h129 h127) (C (C h21 (T (T (T (T h122 h120) h118) (C (C (C h33 (T (T (T h116 h115) h113) (C (C (C h15 h111) h15) h0))) h33) h0)) (S h109))) h21)) h15) (S h108))) h38) h107) (C (T (C (C h33 (S h106)) h33) (C (C h33 h102) h33)) h15)) (S h105)) h15
  have h131 := h v128 v6 v2
  have h132 := S h129
  have h133 := C (C (T h121 (C h126 h125)) (T h122 h120)) h21
  have h134 := h v26 v1 v2
  have h135 := S h134
  have h136 := C (C (C h93 h22) h93) h15
  have h137 := h (M (M v1 v1) v1) x x
  have h138 := S h137
  have h139 := h z v1 x
  have h140 := C h33 h139
  have h141 := h z v6 x
  have h142 := h (M (M v6 v1) v6) x x
  have h143 := h v12 x x
  have h144 := S h143
  have h145 := h v3 v2 x
  have h146 := S h145
  have h147 := C (C (C h11 h146) h11) h33
  let v148 := M (M v2 (M v3 x)) v2
  have h149 := h v148 v3 x
  have h150 := h v148 v2 x
  have h151 := h (M v70 v2) x x
  have h152 := S h118
  have h153 := C (C (C h33 h111) h33) h0
  have h154 := h v112 v3 z
  let v155 := M v3 v2
  have h156 := h (M v155 v3) x z
  have h157 := h v155 y v3
  have h158 := C (T (T (T (C (C h38 (T (T (T (T (T (T (C (T h157 (C (T (T (T (T (T (C (C h21 (T (T (T (T h156 (C (C (C h33 (T (T (T (C (C (C h11 h110) h11) h0) (S h154)) h114) h153)) h33) h0)) h152) h119) h124)) h21) h133) h132) h131) h130) h103) h11)) h15) h151) (C (C (C h33 (T (T (T (C (C (C h15 h145) h15) h33) (S h150)) h149) h147)) h33) h33)) h144) h13) h54) h23)) h38) h142) (C (C (T (C h33 (S h141)) h140) h33) h33)) h138) h15
  have h159 := h v155 v6 v2
  have h160 := C (C h21 (C (T (T (T h159 h158) h136) h135) h93)) h21
  have h161 := h v155 y v1
  have h162 := S h161
  have h163 := S h159
  have h164 := S h131
  have h165 := C (T (T (T h105 (C (T (C (C h33 h103) h33) (C (C h33 h106) h33)) h15)) (S h107)) (C (C h38 (T h108 (C (T (T (C (C h21 (T (T (T (T h109 (C (C (C h33 (T (T (T (C (C (C h15 h110) h15) h0) (S h113)) h114) h153)) h33) h0)) h152) h119) h124)) h21) h133) h132) h15))) h38)) h15
  have h166 := S h149
  have h167 := C (C (C h11 h145) h11) h33
  have h168 := C h33 (S h139)
  have h169 := C (T (T (T h137 (C (C (T h168 (C h33 h141)) h33) h33)) (S h142)) (C (C h38 (T (T (T (T (T (T h22 h28) h14) h143) (C (C (C h33 (T (T (T h167 h166) h150) (C (C (C h15 h146) h15) h33))) h33) h33)) (S h151)) (C (T (C (T (T (T (T (T h102 h165) h164) h129) h127) (C (C h21 (T (T (T (T h122 h120) h118) (C (C (C h33 (T (T (T h116 h115) h154) (C (C (C h11 h111) h11) h0))) h33) h0)) (S h156))) h21)) h11) (S h157)) h15))) h38)) h15
  have h170 := C (C (C h93 h23) h93) h15
  have h171 := C (C h21 (C (T (T (T h134 h170) h169) h163) h93)) h21
  have h172 := C (T (T (T (T (T h102 h165) h164) h129) h127) h171) h93
  let v173 := M v2 v1
  have h174 := h v173 y v1
  have h175 := h v173 v6 y
  have h176 := S h175
  have h177 := C (T (T (T (T (T h160 h133) h132) h131) h130) h103) h93
  have h178 := T (T (T (T (T h134 h170) h169) h163) h161) h177
  have h179 := h y v2 y
  have h180 := S h179
  let v181 := M (M v2 (M y y)) v2
  have h182 := h v181 v2 y
  have h183 := h v181 v3 y
  have h184 := C (C (C h38 (T (T (T (T (C (T (T h77 h98) (C (T h79 (C h11 h179)) h11)) h21) (S h183)) h182) (C (T (T (C (T (C h15 h180) h20) h15) h53) h52) h21)) (C h178 h21))) h38) h21
  have h185 := h v75 v6 y
  have h186 := C h100 h11
  have h187 := C h74 h11
  have h188 := h v2 v1 v3
  let v189 := M v1 v70
  have h190 := h (M v189 v1) x v3
  have h191 := T (T h190 (C (T (C (C h33 (S h188)) h33) h100) h11)) h187
  have h192 := C (T (C (C h33 h191) h33) (C (C h33 (T (T (T (T (T (T h186 h99) h185) h184) h176) h174) (C (T (T (T (T (T (T (T (T (T (T (T (T (C (C h21 (C (T h172 h162) h93)) h21) h160) h133) h132) h131) h130) h103) h68) h101) h96) h85) h95) h94) h93))) h33)) h93
  have h193 := h v189 x v1
  have h194 := C (T (T (T (T (T (T (T (T h193 h192) h92) h90) h88) h86) h84) h81) h69) h38
  have h195 := h v189 v6 v3
  have h196 := S h195
  have h197 := S h193
  have h198 := T (T h186 (C (T h74 (C (C h33 h188) h33)) h11)) (S h190)
  have h199 := S h185
  have h200 := T (T (T (T (T h172 h162) h159) h158) h136) h135
  have h201 := C (C (C h38 (T (T (T (T (C h200 h21) (C (T (T h27 h24) (C (T h19 (C h15 h179)) h15)) h21)) (S h182)) h183) (C (T (T (C (T (C h11 h180) h97) h11) h80) h78) h21))) h38) h21
  have h202 := C (T (C (C h33 (T (T (T (T (T (T (C (T (T (T (T (T (T (T (T (T (T (T (T h90 h88) h86) h84) h81) h69) h102) h165) h164) h129) h127) h171) (C (C h21 (C (T h161 h177) h93)) h21)) h93) (S h174)) h175) h201) h199) h76) h187)) h33) (C (C h33 h198) h33)) h93
  have h203 := h y y v2
  have h204 := h v3 z v2
  have h205 := S h204
  let v206 := M (M z v155) z
  have h207 := h v206 y v2
  have h208 := h v206 x v2
  have h209 := h (M (M x v3) x) x x
  have h210 := h v148 x x
  have h211 := h v2 z v3
  have h212 := S h211
  have h213 := h (M (M z v70) z) x v3
  have h214 := S h213
  have h215 := C (T h74 (C (C h33 h211) h33)) h11
  have h216 := C (T (T (T (T (T h175 h201) h199) h76) h215) h214) h11
  have h217 := T h216 h212
  have h218 := C h178 h11
  have h219 := h v26 v1 v3
  have h220 := C (C (C h38 (T (T (T (T (T (T (T (T (T (T (T (T h186 h99) h185) h184) h176) h172) h162) h159) h158) h136) h135) h219) (C (T (T (T (T (T (T (T (T (T (T (C (C h93 h218) h93) (C (T (T (T (T (T (C h93 h217) (C (T (T (T (T (T (T h22 h28) h14) h143) (C (C (C h33 (T (T (T h167 h166) h210) (C (C (C h33 h146) h33) h33))) h33) h33)) (S h209)) (C (C h33 h204) h33)) h15)) (S h208)) h207) (C (C (C h21 h205) h21) h15)) (S h203)) h93)) h68) h101) h96) h85) h95) h94) h91) h202) h197) h11))) h38) h11
  have h221 := h v117 v6 v3
  have h222 := h v117 x v6
  have h223 := S h222
  have h224 := h v2 v2 v6
  have h225 := C (C h33 (S h224)) h33
  have h226 := C h225 h38
  have h227 := C (C h33 h224) h33
  have h228 := h v2 v6 v6
  let v229 := M v6 v66
  have h230 := h (M v229 v6) x v6
  have h231 := C (C (C h33 (T (T h230 (C (T (C (C h33 (S h228)) h33) h227) h38)) h226)) h33) h38
  have h232 := h v229 x v6
  have h233 := C h38 h194
  have h234 := C (T (T (T (T (T (T h233 h232) h231) h223) h221) h220) h196) h38
  have h235 := C (T (T (T (T (T (T (T (T h68 h101) h96) h85) h95) h94) h91) h202) h197) h38
  have h236 := C h38 h235
  have h237 := S h232
  have h238 := C h227 h38
  have h239 := C (C (C h33 (T (T h238 (C (T h225 (C (C h33 h228) h33)) h38)) (S h230))) h33) h38
  have h240 := C (T (T (T (T h225 h222) h239) h237) h236) h38
  have h241 := h v2 x v6
  have h242 := C (T (C (C h33 (S h241)) h33) h227) h38
  have h243 := h (M (M x v66) x) x v6
  have h244 := C (C h33 h194) h33
  have h245 := h v189 v6 v1
  have h246 := h v2 x v3
  have h247 := C (T (C (C h33 (S h246)) h33) h100) h11
  have h248 := h (M (M x v70) x) x v3
  have h249 := S h248
  have h250 := C (T h74 (C (C h33 h246) h33)) h11
  have h251 := C (T (C (C h33 h212) h33) h100) h11
  have h252 := h z x x
  have h253 := h (M (M x v1) x) x x
  have h254 := h v1 v1 v2
  let v255 := M v1 v25
  have h256 := h (M v255 v1) x v2
  have h257 := h v255 v6 v1
  have h258 := C (T (T h257 (C (T (T (T (T (C (C h38 (T (T (T h256 (C (T (T (T (C (C h33 (S h254)) h33) h253) (C (C (T (C h33 (S h252)) h140) h33) h33)) h138) h15)) h136) h135)) h38) (C (C h38 (T (T (T (T (T (T (T (T (T (T (T h134 h170) h169) h163) h161) h177) h175) h201) h199) h76) h215) h214)) h38)) (C (C h38 (T (T (T h213 h251) h250) h249)) h38)) (C (C h38 (T (T h248 h247) h187)) h38)) (C (C h38 h198) h38)) h93)) (S h245)) h38
  have h259 := C h33 h258
  have h260 := C h259 h33
  have h261 := C (T (T h245 (C (T (T (T (T (C (C h38 h191) h38) (C (C h38 (T (T h186 h250) h249)) h38)) (C (C h38 (T (T (T h248 h247) h215) h214)) h38)) (C (C h38 (T (T (T (T (T (T (T (T (T (T (T h213 h251) h99) h185) h184) h176) h172) h162) h159) h158) h136) h135)) h38)) (C (C h38 (T (T (T h134 h170) (C (T (T (T h137 (C (C (T h168 (C h33 h252)) h33) h33)) (S h253)) (C (C h33 h254) h33)) h15)) (S h256))) h38)) h93)) (S h257)) h38
  have h262 := C h33 h261
  have h263 := T (T h238 h240) h234
  have h264 := C (T (C h33 h263) h262) h33
  let v265 := M v2 v66
  have h266 := h (M v265 v2) x v6
  have h267 := C (T (T (T (T (T (T (T (T (C (C h33 (T h266 h226)) h33) h264) h260) h244) h243) h242) h240) h234) h194) h15
  have h268 := h v265 x v2
  have h269 := C h15 h194
  have h270 := C h15 h263
  have h271 := C (T (T (T (T (T (T h270 h269) h268) h267) h67) h65) h58) h15
  have h272 := C (T (T (T (T h233 h232) h231) h223) h227) h38
  have h273 := S h221
  have h274 := C h200 h11
  have h275 := C (T (T (T (T (T h213 h251) h99) h185) h184) h176) h11
  have h276 := T h211 h275
  have h277 := C (C (C h38 (T (T (T (T (T (T (T (T (T (T (T (T (C (T (T (T (T (T (T (T (T (T (T h193 h192) h92) h90) h88) h86) h84) h81) h69) (C (T (T (T (T (T h203 (C (C (C h21 h204) h21) h15)) (S h207)) h208) (C (T (T (T (T (T (T (C (C h33 h205) h33) h209) (C (C (C h33 (T (T (T (C (C (C h33 h145) h33) h33) (S h210)) h149) h147)) h33) h33)) h144) h13) h54) h23) h15)) (C h93 h276)) h93)) (C (C h93 h274) h93)) h11) (S h219)) h134) h170) h169) h163) h161) h177) h175) h201) h199) h76) h187)) h38) h11
  have h278 := C (T (T (T (T (T (T h195 h277) h273) h222) h239) h237) h236) h38
  have h279 := T (T h278 h272) h226
  have h280 := C h15 h279
  have h281 := C h15 h258
  have h282 := C h15 h261
  have h283 := C h15 h235
  have h284 := S h266
  have h285 := T (T (T (T (T (T (T (T (T (T (T (T h235 h278) h272) h284) (C h283 h15)) (C h282 h15)) (C (T h281 h280) h15)) h271) h56) h51) h49) h47) h44
  have h286 := C h285 h15
  have h287 := S h67
  have h288 := S h63
  have h289 := C (C (C h33 h59) h33) h33
  have h290 := C (C (C h33 (T (T (T h289 h288) h64) (C (C (C h15 h60) h15) h33))) h33) h33
  have h291 := h v8 v6 v6
  have h292 := h v6 z v6
  have h293 := S h292
  have h294 := C (C h33 h293) h33
  let v295 := M (M z (M v6 v6)) z
  have h296 := h v295 x v6
  have h297 := h v295 v6 x
  have h298 := S h296
  have h299 := C (C h33 h292) h33
  have h300 := h x x v6
  have h301 := S h300
  have h302 := C (T (T (T (C (C h0 h301) h0) h29) h10) h299) h38
  let v303 := M (M x v7) x
  have h304 := h v303 z v6
  have h305 := h v303 x v6
  have h306 := S h305
  have h307 := h x v3 v6
  have h308 := S h307
  have h309 := C (T (C (T (C h33 h308) h37) h33) (C (T h36 (C h33 h300)) h33)) h38
  let v310 := M (M v3 v7) v3
  have h311 := h v310 x v6
  have h312 := h v310 v2 v6
  have h313 := S h312
  have h314 := C h15 h35
  have h315 := C h15 h34
  have h316 := C (C h33 h217) h33
  have h317 := C (C h33 h218) h33
  have h318 := C (T h259 (C h33 h279)) h33
  have h319 := C h262 h33
  have h320 := C (C h33 h235) h33
  have h321 := S h243
  have h322 := C (T h225 (C (C h33 h241) h33)) h38
  have h323 := C (T (T (T (T (T (T (T h235 h278) h272) h322) h321) h320) h319) h318) h38
  have h324 := C (C h33 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h323 h223) h221) h220) h196) h193) h192) h92) h90) h88) h86) h84) h81) h69) h211) h275) h274)) h33
  have h325 := C (T (T (T (T (T (T (T h264 h260) h244) h243) h242) h240) h234) h194) h38
  have h326 := S h268
  have h327 := C (T (T (T (T (T (T (T (T h235 h278) h272) h322) h321) h320) h319) h318) (C (C h33 (T h238 h284)) h33)) h15
  have h328 := C (T (T (T (T (T (T h57 h290) h287) h327) h326) h283) h280) h15
  have h329 := C (T (T (C (C h0 h46) h0) h29) h10) h15
  have h330 := S h49
  have h331 := C (T (C (T (C h33 h40) h37) h33) (C (T h36 (C h33 h45)) h33)) h15
  have h332 := T (T (T (T (T (T (T (T (T (T (T (T h43 h331) h330) h50) h329) h328) (C (T h270 h282) h15)) (C h281 h15)) (C h269 h15)) h266) h240) h234) h194
  have h333 := C h15 h332
  have h334 := T (T (T (T h333 h268) h267) h286) h40
  have h335 := C h334 (T (T (T (T (T (T (T (T (T (T (T (T (T h68 h101) h96) h85) h95) h94) h91) h202) h197) h195) h277) h273) h222) h325)
  have h336 := C h15 h285
  have h337 := C h332 h15
  have h338 := T (T (T (T h39 h337) h327) h326) h336
  have h339 := h v42 x x
  have h340 := C (T (T h339 (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (C (T (C h338 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (C (T (T (T (T (T (T (T h43 h331) h330) h50) h329) h328) (C (T (T h270 h269) h336) h15)) h335) h33) h324) h317) h316) h221) h220) h196) h193) h192) h92) h90) h88) h86) h84) h81) h69)) h335) h33) h324) h317) h316) h221) h220) h196) h193) h192) h92) h90) h88) h86) h84) h81) h69) h33)) h315) h15
  have h341 := C (T (T h39 h340) (C (T h314 (C h15 h307)) h15)) h38
  have h342 := h v7 y v6
  have h343 := S h342
  have h344 := T (C (T (T (T (T (T (T (T h341 h313) h311) h309) h306) h304) h302) h298) h38) h293
  have h345 := C h338 (T (T (T (T (T (T (T (T (T (T (T (T (T h323 h223) h221) h220) h196) h193) h192) h92) h90) h88) h86) h84) h81) h69)
  have h346 := C (C h33 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h218 h216) h212) h68) h101) h96) h85) h95) h94) h91) h202) h197) h195) h277) h273) h222) h325)) h33
  have h347 := C (C h33 h274) h33
  have h348 := C (C h33 h276) h33
  have h349 := C (T (T h314 (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h68 h101) h96) h85) h95) h94) h91) h202) h197) h195) h277) h273) h348) h347) h346) (C (T h345 (C h334 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h68 h101) h96) h85) h95) h94) h91) h202) h197) h195) h277) h273) h348) h347) h346) (C (T (T (T (T (T (T (T h345 (C (T (T h333 h283) h280) h15)) h271) h56) h51) h49) h47) h44) h33)))) h33)) h33)) (S h339)) h15
  have h350 := C (T (T (C (T (C h15 h308) h315) h15) h349) h40) h38
  have h351 := S h311
  have h352 := C (T (C (T (C h33 h301) h37) h33) (C (T h36 (C h33 h307)) h33)) h38
  have h353 := S h304
  have h354 := C (T (T (T h294 h9) h55) (C (C h0 h300) h0)) h38
  have h355 := T h292 (C (T (T (T (T (T (T (T h296 h354) h353) h305) h352) h351) h312) h350) h38)
  have h356 := h (M (M y v6) y) x x
  have h357 := h v62 y x
  have h358 := C (T (T (T (T (T (T h39 h337) h67) h65) (C (C (C h33 (T (T (T h289 h288) h357) (C (C (C h21 h60) h21) h33))) h33) h33)) (S h356)) (C (C h21 h355) h21)) h344
  have h359 := C (T (T (T (T (T (T (C (C h21 h344) h21) h356) (C (C (C h33 (T (T (T (C (C (C h21 h59) h21) h33) (S h357)) h63) h61)) h33) h33)) h290) h287) h286) h40) h355
  have h360 := C h315 h15
  have h361 := C h314 h15
  let v362 := M x x
  let v363 := M v6 v362
  let v364 := M v363 v6
  have h365 := h v364 v6 x
  have h366 := h v364 x x
  have h367 := S h366
  have h368 := h x v2 x
  have h369 := C (C (T (C h33 (S h368)) h37) h33) h33
  have h370 := h (M (M v2 v362) v2) x x
  have h371 := S h370
  have h372 := C (C (T h36 (C h33 h368)) h33) h33
  have h373 := h x x x
  have h374 := C (C (T (C h33 (S h373)) h37) h33) h33
  have h375 := h (M (M x v362) x) x x
  have h376 := S h375
  have h377 := C (C (T h36 (C h33 h373)) h33) h33
  have h378 := h x z x
  have h379 := C (C (T (C h33 (S h378)) h37) h33) h33
  have h380 := h (M (M z v362) z) x x
  have h381 := S h380
  have h382 := C (C (T h36 (C h33 h378)) h33) h33
  have h383 := h v363 v6 v6
  T (T (T (T (T (T (T (T (T h39 h337) h67) h65) h58) h291) (C (T (T (T (C (C h38 (T (T (T (T (T (T (T (C h299 h38) h298) h297) (C (T (C (C h38 (T (T (T (T (T (T (T (C (T (T (T (T (T (T (T (T (T h296 h354) h353) h305) h352) h351) h312) h350) h342) h359) h33) (C (T h358 h343) h33)) h57) h290) h287) h286) h340) h361)) h38) (C (T (C h38 (T (T h360 h349) h40)) (C h38 h34)) h38)) h33)) (S h365)) h366) h372) h371)) h38) (C (C h38 (T (T (T h370 h369) h377) h376)) h38)) (C (C h38 (T (T (T h375 h374) h382) h381)) h38)) (C (C h38 (T (T h380 h379) h367)) h38)) h38)) (S h383)) (h v363 v6 z)) (C (T (T (T (T (T (T (C (C h38 (C (T (T (T (T (T (T (T h383 (C (T (T (T (C (C h38 (T (T h366 h382) h381)) h38) (C (C h38 (T (T (T h380 h379) h377) h376)) h38)) (C (C h38 (T (T (T h375 h374) h372) h371)) h38)) (C (C h38 (T (T (T (T (T (T (T h370 h369) h367) h365) (C (T (C (T (C h38 h35) (C h38 (T (T h39 h340) h361))) h38) (C (C h38 (T (T (T (T (T (T (T h360 h349) h337) h67) h65) h58) (C (T h342 h359) h33)) (C (T (T (T (T (T (T (T (T (T h358 h343) h341) h313) h311) h309) h306) h304) h302) h298) h33))) h38)) h33)) (S h297)) h296) (C h294 h38))) h38)) h38)) (S h291)) h57) h290) h287) h286) h40) h0)) h38) (h (M (M v6 v31) v6) x z)) (C (T (C (T (C h33 (S (h x v6 z))) h37) h33) (C (T h36 (C h33 h30)) h33)) h0)) (S (h v32 x z))) (h v32 z z)) (C (T (T (C (C h0 (S h30)) h0) h29) h10) h0)) h5) h0)

