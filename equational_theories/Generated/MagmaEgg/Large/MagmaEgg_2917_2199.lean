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
theorem Equation2917_implies_Equation2199 (G: Type _) [Magma G] (h: Equation2917 G) : Equation2199 G := fun x y z =>
  let v0 := M y x
  let v1 := M y z
  let v2 := M v1 z
  let v3 := M v2 v0
  have h4 := h v3 v0 v3
  have h5 := S h4
  have h6 := R v3
  have h7 := R v0
  have h8 := h z v2 v1
  have h9 := S h8
  have h10 := R v1
  have h11 := C h10 h9
  have h12 := C (C h11 h7) h7
  let v13 := M z v2
  let v14 := M v2 v13
  let v15 := M v14 v1
  have h16 := h v15 v1 v0
  have h17 := h v15 v1 v3
  have h18 := S h17
  have h19 := C h10 h8
  have h20 := h v3 v3 v2
  have h21 := R v2
  have h22 := C h21 (S h20)
  have h23 := C (T h22 (C h19 h6)) h6
  have h24 := C h21 h20
  have h25 := h z v0 x
  have h26 := S h25
  have h27 := R x
  have h28 := h (M (M v0 (M z v0)) x) x x
  have h29 := h z y x
  let v30 := M y (M z y)
  have h31 := h (M v30 x) x x
  have h32 := h v30 y x
  have h33 := h (M v30 y) y x
  have h34 := h z y y
  have h35 := R y
  have h36 := h z v2 y
  have h37 := C h35 (S h36)
  let v38 := M v14 y
  have h39 := h v38 y x
  have h40 := h v38 y y
  have h41 := C h35 h36
  let v42 := M v1 y
  have h43 := h v42 y x
  have h44 := h y x v1
  let v45 := M x v0
  have h46 := h (M v45 v1) v1 x
  have h47 := h v45 z v3
  have h48 := S h47
  have h49 := h (M v45 z) z x
  have h50 := h y x z
  have h51 := R z
  have h52 := h y v2 z
  have h53 := C h51 (S h52)
  have h54 := C h51 h52
  have h55 := h y z z
  let v56 := M z v1
  have h57 := h (M v56 z) z x
  have h58 := C (C (C h51 (T (T (T h57 (C (C (T (C h51 (S h55)) h54) h27) h27)) (C (C (T h53 (C h51 h50)) h27) h27)) (S h49))) h6) h6
  have h59 := h v56 z v3
  have h60 := S h16
  have h61 := C (C h19 h7) h7
  have h62 := h v0 v2 v3
  have h63 := T (T (C h6 (S h62)) h61) h60
  have h64 := C (T (C h63 h10) h9) h10
  let v65 := M v0 v2
  let v66 := M v2 v65
  let v67 := M v66 v3
  have h68 := h v67 v3 v1
  have h69 := h v67 v3 x
  have h70 := S h69
  have h71 := T (T h16 h12) (C h6 h62)
  have h72 := h v15 v1 x
  have h73 := h x v0 v2
  have h74 := C (T (C (T (C h21 (S h73)) (C h19 h27)) h27) (S h72)) h27
  let v75 := M v0 v45
  have h76 := h (M v75 v2) v2 x
  have h77 := C (T (T h76 h74) (C h71 h27)) h27
  have h78 := S h76
  have h79 := C (T h72 (C (T (C h11 h27) (C h21 h73)) h27)) h27
  have h80 := h v0 y v3
  have h81 := C (T (T (C (T (T (C h6 (S h80)) h61) h60) h27) h79) h78) h27
  let v82 := M v0 y
  let v83 := M y v82
  have h84 := h (M v83 v3) v3 x
  have h85 := h v83 y x
  have h86 := h (M v83 y) y x
  have h87 := h v0 y y
  have h88 := h v0 v0 y
  have h89 := C h35 (S h88)
  let v90 := M v0 (M v0 v0)
  let v91 := M v90 y
  have h92 := h v91 y x
  have h93 := S h92
  have h94 := C h35 h88
  have h95 := h v0 z y
  have h96 := C (C (T (C h35 (S h95)) h94) h27) h27
  let v97 := M z (M v0 z)
  have h98 := h (M v97 y) y x
  have h99 := C (C (C h35 (T (T h98 h96) h93)) h27) h27
  have h100 := h v97 y x
  have h101 := h v97 v2 v3
  have h102 := S h101
  let v103 := M v97 v2
  have h104 := h v103 v2 x
  have h105 := S h104
  have h106 := h v0 z v2
  have h107 := h x v3 v3
  have h108 := C h6 (S h107)
  have h109 := C (T h108 (C (C h21 h106) h27)) h27
  have h110 := C h6 h107
  have h111 := h v0 v2 v2
  have h112 := C h21 (S h111)
  have h113 := C (T (C h112 h27) h110) h27
  let v114 := M v66 v2
  have h115 := h v114 v2 x
  have h116 := h v114 v2 v2
  have h117 := S h116
  have h118 := C h21 h111
  have h119 := C h118 h21
  have h120 := C (C (C h21 (T (T (T (T (T (C h119 h21) h117) h115) h113) h109) h105)) h6) h6
  let v121 := M v3 v2
  have h122 := h v121 v2 v3
  have h123 := C (T (T (T (T (T (T h122 h120) h102) h100) h99) (C (C (C h35 (T (T h92 (C (C (T h89 (C h35 h87)) h27) h27)) (S h86))) h27) h27)) (S h85)) h6
  have h124 := S h122
  have h125 := C h112 h21
  have h126 := S h115
  have h127 := C (T h108 (C h118 h27)) h27
  have h128 := C (T (C (C h21 (S h106)) h27) h110) h27
  have h129 := C (C (C h21 (T (T (T (T (T h104 h128) h127) h126) h116) (C h125 h21))) h6) h6
  have h130 := T (T h101 h129) h124
  have h131 := C h130 h6
  have h132 := T (T (T (T (T (T (T (T (T (T h131 h123) h84) h81) h77) h70) h68) h64) h59) h58) h48
  have h133 := C (T (C (C h10 (T (T (T (C h132 h10) h46) (C (T (T (T (C (T (T (T (T (C h10 (S h44)) h43) (C (C (C h35 (T (C (C h41 h35) h35) (S h40))) h27) h27)) (C (C (C h35 (T (T h39 (C (T (C h37 h27) (C (C h35 h34) h27)) h27)) (S h33))) h27) h27)) (S h32)) h27) h31) (C (C (T (C h27 (S h29)) (C h27 h25)) h27) h27)) (S h28)) h27)) h26)) h6) h24) h6
  let v134 := M v97 v3
  have h135 := h v134 v1 v3
  have h136 := T (T h122 h120) h102
  have h137 := C h136 h6
  have h138 := S h100
  have h139 := S h98
  have h140 := C (C (T h89 (C h35 h95)) h27) h27
  have h141 := C (C (C h35 (T (T h92 h140) h139)) h27) h27
  have h142 := C (T (T (T (T (T (T h85 (C (C (C h35 (T (T h86 (C (C (T (C h35 (S h87)) h94) h27) h27)) h93)) h27) h27)) h141) h138) h101) h129) h124) h6
  have h143 := S h84
  have h144 := C (T (T h76 h74) (C (T (T h16 h12) (C h6 h80)) h27)) h27
  have h145 := C (T (T (C h63 h27) h79) h78) h27
  have h146 := S h68
  have h147 := C (T h8 (C h71 h10)) h10
  have h148 := S h59
  have h149 := C (C (C h51 (T (T (T h49 (C (C (T (C h51 (S h50)) h54) h27) h27)) (C (C (T h53 (C h51 h55)) h27) h27)) (S h57))) h6) h6
  have h150 := C h7 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h47 h149) h148) h147) h146) h69) h145) h144) h143) h142) h137) h135) h133) h23) h18) h16) h12)
  have h151 := h v75 y x
  have h152 := S h151
  have h153 := h (M v75 y) y x
  have h154 := h x v0 y
  have h155 := h x v3 y
  have h156 := C h35 (S h155)
  let v157 := M v3 (M x v3)
  let v158 := M v157 y
  have h159 := h v158 y x
  have h160 := C (C (C h35 (T (T h159 (C (T (C h156 h27) (C (C h35 h154) h27)) h27)) (S h153))) h27) h27
  have h161 := h v158 y y
  have h162 := C h35 h155
  have h163 := h y v3 v0
  have h164 := C h7 (S h163)
  have h165 := C h7 h163
  have h166 := C (C (C h35 (T (T (C h165 h35) (C (T h164 (C h162 h35)) h35)) (S h161))) h27) h27
  have h167 := h v82 y x
  have h168 := C (C (T (T (T (T (T h164 h167) h166) h160) h152) h150) h6) h6
  let v169 := M y v3
  let v170 := M v3 v169
  let v171 := M v170 v0
  have h172 := h v171 v0 v3
  have h173 := h v171 v0 x
  have h174 := S h173
  have h175 := h y x v0
  have h176 := C (C (T (C h7 (S h175)) h165) h27) h27
  have h177 := h (M v45 v0) v0 x
  have h178 := C h132 h7
  have h179 := S h135
  have h180 := T (T (T (T (T (T (T (T (T (T h47 h149) h148) h147) h146) h69) h145) h144) h143) h142) h137
  have h181 := C (T h22 (C (C h10 (T (T (T h25 (C (T (T (T h28 (C (C (T (C h27 h26) (C h27 h29)) h27) h27)) (S h31)) (C (T (T (T (T h32 (C (C (C h35 (T (T h33 (C (T (C (C h35 (S h34)) h27) (C h41 h27)) h27)) (S h39))) h27) h27)) (C (C (C h35 (T h40 (C (C h37 h35) h35))) h27) h27)) (S h43)) (C h10 h44)) h27)) h27)) (S h46)) (C h180 h10))) h6)) h6
  have h182 := C (T (C h11 h6) h24) h6
  have h183 := h v0 v3 v0
  have h184 := S h183
  let v185 := M v0 v3
  have h186 := h (M (M v3 v185) v0) v0 x
  have h187 := h v0 z v0
  have h188 := h (M v97 v0) v0 x
  have h189 := h v121 x v3
  have h190 := S h189
  have h191 := h v2 z v3
  have h192 := C h6 (S h191)
  have h193 := C h6 h191
  have h194 := T (T (T h101 h129) h124) h193
  have h195 := h (M v97 x) x x
  have h196 := h v0 z x
  have h197 := h y x x
  have h198 := h y v3 x
  have h199 := S h198
  have h200 := C h27 h199
  have h201 := C (C (T h200 (C h27 (T (T (T (T h197 (C (C (C h27 h196) h27) h27)) (S h195)) (C h194 h27)) (C h192 h27)))) h6) h6
  let v202 := M v170 x
  have h203 := h v202 x v3
  have h204 := h v202 v3 v3
  have h205 := S h204
  have h206 := S h203
  have h207 := C h27 h198
  have h208 := T (T (T h192 h122) h120) h102
  have h209 := C (C (T (C h27 (T (T (T (T (C h193 h27) (C h208 h27)) h195) (C (C (C h27 (S h196)) h27) h27)) (S h197))) h207) h6) h6
  have h210 := h v134 v0 v3
  have h211 := S h210
  have h212 := C h180 h7
  have h213 := S h177
  have h214 := C (C (T h164 (C h7 h175)) h27) h27
  have h215 := S h172
  have h216 := S h167
  have h217 := C (C (C h35 (T (T h161 (C (T (C h156 h35) h165) h35)) (C h164 h35))) h27) h27
  have h218 := S h159
  have h219 := C h162 h27
  have h220 := C (T (T (T (T (T (C h7 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h61 h60) h17) h182) h181) h179) h131) h123) h84) h81) h77) h70) h68) h64) h59) h58) h48)) h151) (C (C (C h35 (T (T h153 (C (T (C (C h35 (S h154)) h27) h219) h27)) h218)) h27) h27)) h217) h216) h165) h6
  have h221 := C h220 h6
  have h222 := T (T (T (T (T (T h4 h221) h215) h173) h214) h213) h212
  have h223 := C h7 h222
  have h224 := h v185 z x
  have h225 := S h224
  have h226 := h (M v185 z) z x
  have h227 := h v2 v0 z
  have h228 := h (M v13 x) x x
  have h229 := h v1 z x
  have h230 := h v1 y x
  have h231 := S h230
  have h232 := h (M (M y v42) x) x x
  have h233 := h (M v56 x) x x
  have h234 := h y z x
  have h235 := h v202 x x
  have h236 := C (T (T (T h235 (C (C (T h200 (C h27 h234)) h27) h27)) (S h233)) (C (C h51 (T (T h230 (C (T (T (T h232 (C (T (C (C h27 h231) h27) (C (C h27 h229) h27)) h27)) (S h228)) (C (C h51 h227) h27)) h27)) (S h226))) h27)) h27
  have h237 := h v3 v2 y
  have h238 := C h35 (S h237)
  have h239 := C (T h238 (C (T (T (T h198 h236) h225) h223) h6)) h6
  have h240 := C h35 h237
  have h241 := C (C (T (T (C h6 (T (T (C h240 h6) h239) h211)) (C h6 h131)) (C h6 (C (T (T h189 h209) h206) h6))) h6) h6
  have h242 := h v169 v3 v3
  have h243 := C (T (T (T (T (C (T (T (T (T (T (T h238 h242) h241) h205) h203) h201) h190) h7) (C h136 h7)) h188) (C (C (T (C h7 (S h187)) (C h7 h183)) h27) h27)) (S h186)) h7
  have h244 := S h242
  have h245 := C (T (T (T (C (C h51 (T (T h226 (C (T (T (T (C (C h51 (S h227)) h27) h228) (C (T (C (C h27 (S h229)) h27) (C (C h27 h230) h27)) h27)) (S h232)) h27)) h231)) h27) h233) (C (C (T (C h27 (S h234)) h207) h27) h27)) (S h235)) h27
  have h246 := T (T (T (T (T (T h178 h177) h176) h174) h172) h168) h5
  have h247 := C h7 h246
  have h248 := C (T (C (T (T (T h247 h224) h245) h199) h6) h240) h6
  have h249 := C (C (T (T (C h6 (C (T (T h203 h201) h190) h6)) (C h6 h137)) (C h6 (T (T h210 h248) (C h238 h6)))) h6) h6
  have h250 := h v202 y v3
  have h251 := S h250
  have h252 := h v91 y v3
  let v253 := M (M v2 v121) y
  have h254 := h v253 y v0
  have h255 := h v253 y x
  have h256 := S h255
  have h257 := h v3 y y
  have h258 := C (C (T (C h35 (S h257)) h240) h27) h27
  let v259 := M v3 y
  let v260 := M y v259
  have h261 := h (M v260 y) y x
  have h262 := h v260 v3 v3
  have h263 := S h262
  have h264 := h (M v260 v3) v3 x
  have h265 := h v3 y v3
  have h266 := h v3 v3 v3
  have h267 := C h6 (S h266)
  let v268 := M v3 (M v3 v3)
  let v269 := M v268 v3
  have h270 := h v269 v3 x
  have h271 := h v269 v3 v3
  have h272 := C h6 h266
  have h273 := h v114 v2 v3
  have h274 := C (C (C h6 (T (T (T (T (C (T h273 (C (T (C h112 h6) h272) h6)) h6) (S h271)) h270) (C (T (C h267 h27) (C (C h6 h265) h27)) h27)) (S h264))) h6) h6
  have h275 := h v114 v3 v3
  have h276 := T (T (T (T (T (T (C (T (T (T (T (T (T h104 h128) h127) h126) h275) h274) h263) h35) h261) h258) h256) h254) h243) h184
  have h277 := C h35 h276
  have h278 := h v103 y v3
  have h279 := h v114 v2 y
  have h280 := h y v0 v3
  have h281 := C h6 (S h280)
  have h282 := C h6 h280
  have h283 := C (C (C h35 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (C h282 h35) (C (T h281 (C h118 h35)) h35)) (S h279)) h115) h113) h109) h105) h278) (C (C (T h277 h94) h6) h6)) (S h252)) h92) h140) h139) (C h194 h35)) (C (T (T (T h192 h189) h209) h206) h35))) h6) h6
  have h284 := h v259 y v3
  have h285 := T (T (T (T (T (T (T h281 h284) h283) h251) h204) h249) h244) h240
  have h286 := C (C h285 h7) h7
  let v287 := M y v0
  let v288 := M (M v0 v287) v3
  have h289 := h v288 v3 v0
  have h290 := h v288 v3 x
  have h291 := S h290
  have h292 := h y y v3
  have h293 := C (C (T (C h6 (S h292)) h282) h27) h27
  let v294 := M (M y (M y y)) v3
  have h295 := h v294 v3 x
  have h296 := h v294 v0 v2
  have h297 := S h296
  have h298 := S h295
  have h299 := C (C (T h281 (C h6 h292)) h27) h27
  have h300 := S h289
  have h301 := S h284
  have h302 := S h275
  have h303 := C (C (C h6 (T (T (T (T h264 (C (T (C (C h6 (S h265)) h27) (C h272 h27)) h27)) (S h270)) h271) (C (T (C (T h267 (C h118 h6)) h6) (S h273)) h6))) h6) h6
  have h304 := S h261
  have h305 := C (C (T h238 (C h35 h257)) h27) h27
  have h306 := C (T (T (T (T h186 (C (C (T (C h7 h184) (C h7 h187)) h27) h27)) (S h188)) (C h130 h7)) (C (T (T (T (T (T (T h189 h209) h206) h204) h249) h244) h240) h7)) h7
  have h307 := T (T (T (T (T (T h183 h306) (S h254)) h255) h305) h304) (C (T (T (T (T (T (T h262 h303) h302) h115) h113) h109) h105) h35)
  have h308 := C h35 h307
  have h309 := C (C (C h35 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (C (T (T (T h203 h201) h190) h193) h35) (C h208 h35)) h98) h96) h93) h252) (C (C (T h89 h308) h6) h6)) (S h278)) h104) h128) h127) h126) h279) (C (T (C h112 h35) h282) h35)) (C h281 h35))) h6) h6
  have h310 := T (T (T (T (T (T (T h238 h242) h241) h205) h250) h309) h301) h282
  have h311 := C (C h310 h7) h7
  have h312 := C h7 (C (T (T (T (T (T (T h183 h306) h311) h300) h290) h299) h298) h7)
  have h313 := h v90 y x
  have h314 := S h313
  have h315 := C (T (T (T (T (T (T (T h125 h122) h120) h102) h100) h99) h314) h312) h21
  have h316 := C h21 (T (T (T (T (T (T (T (T (C (T (T (T (T h262 h303) h302) h116) h315) h21) h297) h295) h293) h291) h289) h286) h243) h184)
  have h317 := C h316 h7
  have h318 := C (T (T (T (T (T (T h317 h61) h60) h17) h182) h181) h179) h7
  have h319 := C h7 (C (T (T (T (T (T (T h295 h293) h291) h289) h286) h243) h184) h7)
  have h320 := C (T (T (T (T (T (T (T h319 h313) h141) h138) h101) h129) h124) h119) h21
  have h321 := C h21 (T (T (T (T (T (T (T (T h183 h306) h311) h300) h290) h299) h298) h296) (C (T (T (T (T h320 h117) h275) h274) h263) h21))
  have h322 := C h321 h7
  have h323 := h v260 v2 v0
  have h324 := C (T (T (T (T (T (T (T (T (T (T (T (T (T h320 h117) h275) h274) h263) h323) h318) h178) h177) h176) h174) h172) h168) h5) h21
  have h325 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h198 h236) h225) h223) (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h183 h306) h311) h300) h290) h299) h298) h296) h324) h122) h120) h102) h100) h99) h314) h312) h246)) (C (T (T (T (T (T (T (T (T (T (T (T (T (T h319 h313) h141) h138) h101) h129) h124) h189) h209) h206) h250) h309) h301) h282) h6)) (C h285 h6)) h239) h211) h135) h133) h23) h18) h16) h12) h322) h276
  have h326 := h v287 v3 v2
  have h327 := S h326
  have h328 := C h89 h6
  have h329 := S h323
  have h330 := C (T (T (T (T (T (T h135 h133) h23) h18) h16) h12) h322) h7
  have h331 := C (T (T (T (T (T (T (T (T (T (T (T (T (T h4 h221) h215) h173) h214) h213) h212) h330) h329) h262) h303) h302) h116) h315) h21
  have h332 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h317 h61) h60) h17) h182) h181) h179) h210) h248) (C h310 h6)) (C (T (T (T (T (T (T (T (T (T (T (T (T (T h281 h284) h283) h251) h203) h201) h190) h122) h120) h102) h100) h99) h314) h312) h6)) (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h319 h313) h141) h138) h101) h129) h124) h331) h297) h295) h293) h291) h289) h286) h243) h184) h222)) h247) h224) h245) h199) h307
  have h333 := C h6 (T (T (C h321 h6) (C (T (T (T (T (T (T (T (T (T (T (T h316 h4) h221) h215) h173) h214) h213) h212) h330) h332) h277) h94) h6)) h328)
  have h334 := h v268 y x
  have h335 := S h334
  have h336 := h (M v268 y) y x
  have h337 := h v3 v3 y
  have h338 := C (C (C h35 (T (T h255 (C (C (T h238 (C h35 h337)) h27) h27)) (S h336))) h27) h27
  have h339 := C (C (C h35 (T (T h261 h258) h256)) h27) h27
  have h340 := h v260 y x
  have h341 := C (T (T (T (T (T (T (T (T h183 h306) h311) h300) h290) h299) h298) h296) (C (T (T (T (T (T (T (T (T (T h320 h117) h275) h274) h263) h340) h339) h338) h335) h333) h21)) h21
  have h342 := h v65 v3 y
  have h343 := S h342
  have h344 := h v2 v0 v0
  have h345 := C h7 (S h344)
  have h346 := C h7 h344
  have h347 := S h340
  have h348 := C (C (C h35 (T (T h255 h305) h304)) h27) h27
  have h349 := C (C (C h35 (T (T h336 (C (C (T (C h35 (S h337)) h240) h27) h27)) h256)) h27) h27
  have h350 := C h94 h6
  have h351 := C h6 (T (T h350 (C (T (T (T (T (T (T (T (T (T (T (T h89 h308) h325) h318) h178) h177) h176) h174) h172) h168) h5) h321) h6)) (C h316 h6))
  have h352 := C (T (T (T (T (T (T (T (T (C (T (T (T (T (T (T (T (T (T h351 h334) h349) h348) h347) h262) h303) h302) h116) h315) h21) h297) h295) h293) h291) h289) h286) h243) h184) h21
  have h353 := C h6 (T (T (T h350 (C (T (T (T (T (T (T (T (T h89 h308) h325) h329) h340) h339) h338) h335) h333) h6)) (C (T (T (T (T (T (T (T (T (T (T h351 h334) h349) h348) h347) h323) h332) h277) h326) h352) h346) h6)) (C h345 h6))
  have h354 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h183 h306) h311) h300) h290) h299) h298) h296) h324) h189) h209) h206) h250) h309) h301) (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T h4 h221) h215) h173) h214) h213) h212) h330) h329) h340) h339) h338) h335) h333) h353) h35)) h35
  have h355 := C h346 h6
  have h356 := C h6 (T (T (T h355 (C (T (T (T (T (T (T (T (T (T (T h345 h341) h327) h308) h325) h329) h340) h339) h338) h335) h333) h6)) (C (T (T (T (T (T (T (T (T h351 h334) h349) h348) h347) h323) h332) h277) h94) h6)) h328)
  let v357 := M v2 (M x v2)
  let v358 := M y (M x y)
  have h359 := h x v0 v3
  let v360 := M v75 v3
  let v361 := M v157 v3
  have h362 := h x v1 v3
  T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h362 (C (T (T (T (T (T (T (T (T (T (T (h (M (M v1 (M x v1)) v3) v3 x) (C (C (T (C h6 (S h362)) h110) h27) h27)) (S (h v361 v3 x))) (h v361 v3 y)) (C (C (T h108 (C h6 h359)) h35) h35)) (S (h v360 v3 y))) (h v360 v3 x)) (C (T (T (C (T (C h6 (S h359)) h110) h27) h127) h126) h27)) (C (T (T h115 h113) (C (T h108 (C h6 (h x y v3))) h27)) h27)) (S (h (M v358 v3) v3 x))) (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (h v358 x x) (C (C (C h27 (T (T (h (M v358 x) x x) (C (T (C (C h27 (S (h x y x))) h27) (C (C h27 (h x v2 x)) h27)) h27)) (S (h (M v357 x) x x)))) h27) h27)) (S (h v357 x x))) (h v357 y x)) (C (C (C h35 (T (T (h (M v357 y) y x) (C (T (C (C h35 (S (h x v2 y))) h27) h219) h27)) h218)) h27) h27)) h217) h216) h354) h343) h341) h327) h308) h325) h329) h340) h339) h338) h335) h333) h353) (C h6 (T (T (T (T h355 (C (T (T (T (T (T (T (T (T (T (T (T h345 h341) h327) h308) h325) h329) h340) h339) h338) h335) h333) h353) h6)) (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h356 h351) h334) h349) h348) h347) h323) h332) h277) h326) h352) h342) (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T h356 h351) h334) h349) h348) h347) h323) h318) h178) h177) h176) h174) h172) h168) h5) h35) h284) h283) h251) h203) h201) h190) h331) h297) h295) h293) h291) h289) h286) h243) h184) h35)) h167) h166) h160) h152) h150) h6)) h220) (C h164 h6)))) h6)) h6)) (S (h v82 v3 v3))) h354) h343) h341) h327) h308) h325) h318) h178) h177) h176) h174) h172) h168) h5

