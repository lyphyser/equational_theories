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
theorem Equation725_implies_Equation3120 (G: Type _) [Magma G] (h: Equation725 G) : Equation3120 G := fun x y z =>
  let v0 := M y x
  let v1 := M v0 y
  let v2 := M v1 z
  have h3 := h z v2 v1
  have h4 := S h3
  have h5 := h x v2 y
  have h6 := R v2
  have h7 := C h6 h5
  have h8 := R x
  have h9 := h v2 z y
  have h10 := S h9
  let v11 := M (M y v2) y
  let v12 := M z v11
  have h13 := h v12 z z
  have h14 := S h13
  have h15 := R z
  have h16 := C h9 h15
  have h17 := C h15 h16
  let v18 := M v2 z
  have h19 := R v18
  have h20 := h z v18 v1
  have h21 := C (S h20) h19
  let v22 := M v2 v1
  let v23 := M v18 v22
  have h24 := h v23 z v18
  have h25 := h v23 x v18
  have h26 := C h20 h19
  have h27 := h z v18 v0
  let v28 := M (M v0 z) v0
  have h29 := h (M v18 v28) x v18
  have h30 := h v28 x y
  have h31 := R y
  have h32 := h (M y v28) x y
  have h33 := h z y v0
  have h34 := h z y v2
  have h35 := C (S h34) h31
  let v36 := M v18 v2
  have h37 := h (M y v36) x y
  have h38 := S h37
  have h39 := C h34 h31
  have h40 := h z y z
  let v41 := M (M z z) z
  have h42 := h (M y v41) x y
  have h43 := h v41 x y
  have h44 := h v41 x x
  have h45 := h (M x v41) x x
  have h46 := S h45
  have h47 := h z x z
  have h48 := h z x v0
  have h49 := C h8 (C (S h48) h8)
  have h50 := C h8 (T h49 (C h8 (C h47 h8)))
  have h51 := C h8 (C h48 h8)
  have h52 := h z x y
  have h53 := C h8 (T (C h8 (C (S h52) h8)) h51)
  let v54 := M (M y z) y
  have h55 := h (M x v54) x x
  have h56 := h v54 x x
  have h57 := h v54 x z
  have h58 := h (M z v54) x z
  have h59 := h z z y
  have h60 := h z z v1
  have h61 := h (M z v22) x z
  have h62 := h v22 x z
  have h63 := h v22 x v2
  have h64 := S h63
  have h65 := h v1 z v1
  have h66 := S h65
  have h67 := C h66 h15
  have h68 := C h8 (C h8 h67)
  let v69 := M z (M (M v1 v1) v1)
  have h70 := h v69 x z
  have h71 := C h8 (T (T h70 h68) (C h8 (C h5 h6)))
  have h72 := S h70
  have h73 := C h65 h15
  have h74 := C h8 (C h8 h73)
  have h75 := h x v2 v0
  have h76 := S h75
  have h77 := C h8 (T (T (C h8 (C h76 h6)) h74) h72)
  let v78 := M (M v0 x) v0
  have h79 := h (M v2 v78) x v2
  have h80 := h v78 v18 v18
  let v81 := M v18 v78
  have h82 := h v81 v18 v18
  have h83 := h x v18 v0
  have h84 := C h83 h19
  have h85 := h v18 v1 v0
  have h86 := S h85
  let v87 := M (M v0 v18) v0
  let v88 := M v1 v87
  have h89 := h v88 x v1
  have h90 := S h89
  have h91 := R v1
  have h92 := h (M v18 v1) x v18
  have h93 := S h92
  have h94 := h x v18 y
  have h95 := C h10 h15
  have h96 := C h8 h95
  have h97 := h v12 x z
  have h98 := C h8 (T h97 (C h8 (T h96 (C h94 h19))))
  have h99 := S h97
  have h100 := C h8 h16
  have h101 := S h83
  have h102 := C h101 h19
  have h103 := C h8 (T (C h8 (T h102 h100)) h99)
  have h104 := h v81 x v18
  have h105 := S h104
  have h106 := C h8 (T h97 (C h8 (T h96 h84)))
  have h107 := C h8 (T (C h8 (T (C (S h94) h19) h100)) h99)
  have h108 := h v18 v1 v2
  have h109 := T (T (T (T (C (S h108) h91) h92) h107) h106) h105
  have h110 := C h8 (T (C h8 h109) (C h8 (T (T (T (T h104 h103) h98) h93) (C h85 h91))))
  let v111 := M v1 (M (M v2 v18) v2)
  have h112 := h v111 x v1
  have h113 := h v111 v18 v1
  have h114 := S h113
  have h115 := T (T (T (T h104 h103) h98) h93) (C h108 h91)
  have h116 := C h19 (T h83 (C h19 h115))
  have h117 := h x x v18
  have h118 := S h117
  have h119 := h (M x (M (M v18 x) v18)) x x
  have h120 := h x x v2
  have h121 := S h120
  let v122 := M (M v2 x) v2
  have h123 := h (M x v122) x x
  have h124 := h v122 x y
  have h125 := h (M y v122) x y
  have h126 := h x y v2
  have h127 := h (M x y) y x
  have h128 := S h127
  have h129 := h x y v18
  have h130 := C (S h129) h31
  have h131 := C h129 h31
  have h132 := h y x z
  have h133 := S h132
  let v134 := M x (M (M z y) z)
  have h135 := h v134 x x
  have h136 := C h132 h8
  have h137 := R v0
  have h138 := h x v0 z
  have h139 := C (S h138) h137
  have h140 := C h138 h137
  have h141 := h x v0 y
  have h142 := S h141
  have h143 := C h8 (T (T (C h8 (T (C h142 h137) h140)) (C h8 (T h139 (C h8 h136)))) (S h135))
  have h144 := h (M v0 v1) x v0
  have h145 := h v0 v1 z
  have h146 := T (T (T (C (S h145) h91) h144) h143) h133
  let v147 := M v1 (M (M z v0) z)
  have h148 := h v147 x v1
  have h149 := h v147 v0 v1
  have h150 := S h144
  have h151 := C h133 h8
  have h152 := C h8 (T (T h135 (C h8 (T (C h8 h151) h140))) (C h8 (T h139 (C h141 h137))))
  have h153 := T (T (T h132 h152) h150) (C h145 h91)
  have h154 := h y v0 x
  have h155 := C (S h154) h137
  have h156 := C h31 (T h155 (C h31 (C (T (T (T (T (T (T (T h132 h152) h150) (C h137 (C h137 h153))) (S h149)) h148) (C h8 (T (C h8 h146) h131))) (C h8 h130)) h8)))
  have h157 := C h154 h137
  have h158 := h v134 y x
  have h159 := h (M y v0) x y
  have h160 := h v69 v18 v2
  have h161 := S h160
  have h162 := h v69 v2 z
  have h163 := h v2 v2 y
  have h164 := C (S h163) h6
  let v165 := M v2 v11
  have h166 := h v165 v2 v2
  have h167 := h v165 x v2
  have h168 := C h163 h6
  have h169 := h v2 v2 v0
  let v170 := M (M v0 v2) v0
  have h171 := h (M v2 v170) x v2
  have h172 := h v170 x y
  have h173 := S h172
  have h174 := h (M y v170) x y
  have h175 := h v2 y v0
  have h176 := h v2 y v2
  have h177 := C (S h176) h31
  have h178 := h (M y (M (M v2 v2) v2)) x y
  have h179 := C h8 (C h8 (C (T (T h178 (C h8 (C h8 (T h177 (C h175 h31))))) (S h174)) h31))
  have h180 := S h178
  have h181 := C h176 h31
  have h182 := h v2 y x
  let v183 := M x v2
  let v184 := M v183 x
  have h185 := h (M y v184) x y
  have h186 := C h8 (C h8 (C (T (T h185 (C h8 (C h8 (T (C (S h182) h31) h181)))) h180) h31))
  have h187 := h v184 x y
  have h188 := h v184 v18 v18
  have h189 := S h188
  have h190 := h (M v18 v184) x v18
  have h191 := h v2 v18 x
  have h192 := h v2 x v1
  have h193 := S h192
  have h194 := T (T (C h193 h8) h7) h4
  have h195 := C h6 (C h6 h194)
  let v196 := M x (M (M v1 v2) v1)
  have h197 := h v196 v2 x
  have h198 := S h197
  have h199 := S h5
  have h200 := C h6 h199
  have h201 := T (T h3 h200) (C h192 h8)
  have h202 := C h6 (C h6 h201)
  have h203 := h v2 v18 z
  let v204 := M (M z v2) z
  have h205 := h (M v18 v204) x v18
  have h206 := h v204 x x
  have h207 := h (M x v204) x x
  have h208 := h v2 x z
  have h209 := C h8 h194
  have h210 := C h8 h201
  let v211 := M x z
  have h212 := h v211 x x
  have h213 := C h19 (C h19 (C (T (T (T (T (C h19 (T (T h212 (C h8 (C h8 (C (T (T (C h8 h210) (C h8 (T h209 (C h8 (T (T h3 h200) (C h208 h8)))))) (S h207)) h8)))) (S h206))) h205) (C h8 (T (C h8 (T (T (C (S h203) h19) h202) h198)) h193))) (C h8 (T h192 (C h8 (T (T h197 h195) (C h191 h19)))))) (S h190)) h19))
  have h214 := h v211 v18 v18
  have h215 := C h19 (C h19 (C (T (T (T (T (T (C h6 (T (T (T (T (T (T h214 h213) h189) h187) h186) h179) h173)) h171) (C h8 (C h8 (T (C (S h169) h6) h168)))) (S h167)) h166) (C h6 (T (C h6 (T h164 (C h6 h73))) (S h162)))) h6))
  have h216 := h v211 v18 v2
  have h217 := S h214
  have h218 := C h19 (C h19 (C (T (T (T (T h190 (C h8 (T (C h8 (T (T (C (S h191) h19) h202) h198)) h193))) (C h8 (T h192 (C h8 (T (T h197 h195) (C h203 h19)))))) (S h205)) (C h19 (T (T h206 (C h8 (C h8 (C (T (T h207 (C h8 (T (C h8 (T (T (C (S h208) h8) h7) h4)) h210))) (C h8 h209)) h8)))) (S h212)))) h19))
  have h219 := S h187
  have h220 := C h8 (C h8 (C (T (T h178 (C h8 (C h8 (T h177 (C h182 h31))))) (S h185)) h31))
  have h221 := C h8 (C h8 (C (T (T h174 (C h8 (C h8 (T (C (S h175) h31) h181)))) h180) h31))
  have h222 := T (T (T (T (T (T (T (T (T h172 h221) h220) h219) h188) h218) h217) h216) h215) h161
  have h223 := C h15 h222
  have h224 := h (M z v170) x z
  have h225 := S h224
  have h226 := h v2 z v0
  have h227 := C h8 (T h96 (C h8 (C h226 h15)))
  have h228 := h v2 z v18
  have h229 := C h8 (T (C h8 (C (S h228) h15)) h100)
  let v230 := M z (M v36 v18)
  have h231 := h v230 x z
  have h232 := C h137 (T (T (T (T (T h231 h229) h227) h225) h223) h66)
  have h233 := C h8 (T (T (T (C h8 (T (T (T (C (T (T (T h232 h144) h143) h133) h137) h159) (C h8 (C h8 (C (T (T (T (T (C h31 h157) h156) h128) (C h8 (T h132 (C h8 (T (T (T (T h158 (C h31 (T (C h31 h151) h157))) h156) h128) (C h126 h31)))))) (S h125)) h31)))) (S h124))) h123) (C h8 (C h8 (T (C h121 h8) (C h117 h8))))) (S h119))
  have h234 := h v230 x v0
  have h235 := S h231
  have h236 := C h8 (T h96 (C h8 (C h228 h15)))
  have h237 := h v12 v18 v0
  have h238 := h v12 v0 z
  have h239 := h v0 v18 v2
  have h240 := C (S h239) h19
  let v241 := M v18 (M (M v2 v0) v2)
  have h242 := h v241 v0 v18
  have h243 := h v241 x v18
  have h244 := C h239 h19
  have h245 := h v0 v18 v0
  let v246 := M (M v0 v0) v0
  have h247 := h (M v18 v246) x v18
  have h248 := h v246 v18 v1
  have h249 := S h234
  have h250 := C h8 (T (C h8 (C (S h226) h15)) h100)
  have h251 := S h216
  have h252 := C h19 (C h19 (C (T (T (T (T (T (C h6 (T h162 (C h6 (T (C h6 h67) h168)))) (S h166)) h167) (C h8 (C h8 (T h164 (C h169 h6))))) (S h171)) (C h6 (T (T (T (T (T (T h172 h221) h220) h219) h188) h218) h217))) h6))
  have h253 := T (T (T (T (T (T (T (T (T h160 h252) h251) h214) h213) h189) h187) h186) h179) h173
  have h254 := C h15 h253
  have h255 := C h137 (T (T (T (T (T h65 h254) h224) h250) h236) h235)
  have h256 := C h31 (T (C h31 (C (T (T (T (T (T (T (T (C h8 h131) (C h8 (T h130 (C h8 h153)))) (S h148)) h149) (C h137 (C h137 h146))) h144) h143) h133) h8)) h157)
  have h257 := C h8 (T (T (T h119 (C h8 (C h8 (T (C h118 h8) (C h120 h8))))) (S h123)) (C h8 (T (T (T h124 (C h8 (C h8 (C (T (T (T (T h125 (C h8 (T (C h8 (T (T (T (T (C (S h126) h31) h127) h256) (C h31 (T h155 (C h31 h136)))) (S h158))) h133))) h127) h256) (C h31 h155)) h31)))) (S h159)) (C (T (T (T h132 h152) h150) h255) h137))))
  have h258 := T (T (T (T (T (T (T (T h117 h257) h249) h231) h229) h227) h225) h223) h66
  have h259 := h (M v1 v246) v0 v1
  have h260 := h v0 v1 v0
  have h261 := C h19 h151
  have h262 := h v134 v18 x
  have h263 := S h262
  have h264 := C h19 h136
  have h265 := h v18 v0 v18
  have h266 := C (S h265) h137
  let v267 := M (M v18 v18) v18
  let v268 := M v0 v267
  have h269 := h v268 v18 v0
  have h270 := h v268 x v0
  have h271 := C h265 h137
  have h272 := h v18 v0 z
  have h273 := C h8 (C h8 (T (C (S h272) h137) h271))
  let v274 := M z v18
  let v275 := M v274 z
  have h276 := h (M v0 v275) x v0
  have h277 := S h276
  have h278 := C h8 (C h8 (T h266 (C h272 h137)))
  have h279 := h v18 v0 v0
  have h280 := h (M v0 v87) x v0
  have h281 := h v87 v18 v0
  have h282 := T (T (T (T (T (T (T (T h281 (C h19 (C h19 (T (C (T (T (T h280 (C h8 (C h8 (T (C (S h279) h137) h271)))) h278) h277) h137) (C (T (T (T (T (T (T (T (T (T (T h276 h273) (S h270)) h269) (C h19 (T (C h19 (T h266 h264)) h263))) (C h19 (T (T h262 (C h19 (T h261 (C h19 (C (T (T (T (T (T (T h132 h152) h150) h255) (C h137 (T (T h234 h233) h118))) (C h137 (T h141 (C h137 (C h260 h91))))) (S h259)) h258))))) (S h248)))) h247) (C h8 (C h8 (T (C (S h245) h19) h244)))) (S h243)) h242) (C h137 (T (C h137 (T h240 (C h137 h16))) (S h238)))) h137))))) (S h237)) h97) h236) h235) h234) h233) h118
  have h283 := C h19 h282
  have h284 := T (T (T (T (T (T (T (T h65 h254) h224) h250) h236) h235) h234) h233) h118
  have h285 := T (T (T (T (T (T (T (T h117 h257) h249) h231) h229) h99) h237) (C h19 (C h19 (T (C (T (T (T (T (T (T (T (T (T (T (C h137 (T h238 (C h137 (T (C h137 h95) h244)))) (S h242)) h243) (C h8 (C h8 (T h240 (C h245 h19))))) (S h247)) (C h19 (T (T h248 (C h19 (T (C h19 (C (T (T (T (T (T (T h259 (C h137 (T (C h137 (C (S h260) h91)) h142))) (C h137 (T (T h117 h257) h249))) h232) h144) h143) h133) h284)) h264))) h263))) (C h19 (T h262 (C h19 (T h261 h271))))) (S h269)) h270) h278) h277) h137) (C (T (T (T h276 h273) (C h8 (C h8 (T h266 (C h279 h137))))) (S h280)) h137))))) (S h281)
  have h286 := R v88
  have h287 := h v88 x x
  have h288 := C h19 (T (T (T (T (T (T (T (T h283 h116) h114) h112) h110) h90) h287) (C h8 (T (C h258 (T (T (T (T (T (T (C (T (C h258 h286) h86) h285) h283) h116) h114) h112) h110) h90)) h86))) h84)
  have h289 := h v18 v18 v0
  have h290 := S h289
  have h291 := C h19 h285
  have h292 := C h19 (T (C h19 h109) h101)
  have h293 := S h112
  have h294 := C h8 (T (C h8 (T (T (T (T (C h86 h91) h92) h107) h106) h105)) (C h8 h115))
  have h295 := C h19 (T (T (T (T (T (T (T (T h102 (C h8 (T h85 (C h284 (T (T (T (T (T (T h89 h294) h293) h113) h292) h291) (C (T h85 (C h284 h286)) h282)))))) (S h287)) h89) h294) h293) h113) h292) h291)
  have h296 := T (T (C h19 h84) h295) h290
  have h297 := T (T h289 h288) (C h19 h102)
  have h298 := C h297 h19
  have h299 := h v267 x v1
  have h300 := h (M v1 v267) x v1
  have h301 := h v18 v1 v18
  have h302 := h v18 v1 z
  have h303 := h (M v1 v275) x v1
  have h304 := h v275 x v1
  have h305 := h v275 x v2
  have h306 := h (M v2 v275) x v2
  have h307 := h v18 v2 z
  have h308 := h z x v2
  have h309 := h v12 v18 z
  have h310 := C h296 h19
  have h311 := h (M x v18) v18 v18
  have h312 := C h6 (T (T (T h289 h288) (C h19 (T (T h102 h311) (C h19 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (C h19 (T h310 (C h19 h16))) (S h309)) h97) h236) h235) h234) h233) h118) h120) (C h8 (C h8 (C (T (T (T (T h7 h4) h308) (C h8 (C h8 (C h307 h6)))) (S h306)) h6)))) (S h305)) h304) (C h8 (C h8 (C (T (T h303 (C h8 (C h8 (T (C (S h302) h91) (C h301 h91))))) (S h300)) h91)))) (S h299)) (C (T (T h298 (C h296 (T h289 h288))) (S h82)) h19)))))) (S h80))
  have h313 := h v196 v18 x
  have h314 := S h313
  have h315 := C h19 (C h19 h201)
  have h316 := S h79
  have h317 := C h8 (T (T h70 h68) (C h8 (C h75 h6)))
  have h318 := C h8 (T (T (C h8 (C h199 h6)) h74) h72)
  have h319 := h v2 v1 v0
  have h320 := T (T (T (T (C (S h319) h91) h63) h318) h317) h316
  have h321 := C h6 (T (C h6 h320) h76)
  let v322 := M v1 v170
  have h323 := h v322 v2 v1
  have h324 := h v322 x v1
  have h325 := S h324
  have h326 := T (T (T (T h79 h77) h71) h64) (C h319 h91)
  have h327 := h v196 x x
  have h328 := S h327
  have h329 := h v2 x v0
  have h330 := S h329
  have h331 := C h8 (T (C h8 (T (T (C h330 h8) h7) h4)) h210)
  have h332 := h (M x v170) x x
  have h333 := C h8 (T (T h329 (C h8 (T (T (T (T (T h332 h331) h328) h197) h195) h312))) (C h8 h326))
  have h334 := h v2 v18 y
  have h335 := C h8 (T (C h8 (T (T (C (S h334) h19) h202) h198)) h193)
  have h336 := h (M v18 v11) x v18
  have h337 := h v11 x z
  have h338 := h v274 x z
  have h339 := h v2 v18 v0
  have h340 := C h8 (T (C h8 (T (T (C (S h339) h19) h202) h198)) h193)
  have h341 := h (M v18 v170) x v18
  have h342 := C h19 (T (T (T (C (T (T (T (T (T (T (T (T (C h19 h253) h341) h340) h333) h325) h323) h321) h7) h4) h19) h338) (C h8 (C h8 (C (T (C h15 h17) h14) h15)))) (S h337))
  have h343 := h v69 v18 v18
  have h344 := C h19 (T (T (T (T (T (T (T (T (T (T (T h172 h221) h220) h219) h188) h218) h217) h216) h215) h161) h343) (C h19 (T (T (T (T (T (T (T (T h342 h336) h335) h333) h325) h323) h321) h7) h4)))
  have h345 := S h341
  have h346 := C h8 (T h192 (C h8 (T (T h197 h195) (C h339 h19))))
  have h347 := h v170 x x
  have h348 := S h347
  have h349 := S h332
  have h350 := C h8 (T h209 (C h8 (T (T h3 h200) (C h329 h8))))
  have h351 := C h6 (T (T (T h80 (C h19 (T (T (C h19 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (C (T (T h82 (C h297 (T h295 h290))) h310) h19) h299) (C h8 (C h8 (C (T (T h300 (C h8 (C h8 (T (C (S h301) h91) (C h302 h91))))) (S h303)) h91)))) (S h304)) h305) (C h8 (C h8 (C (T (T (T (T h306 (C h8 (C h8 (C (S h307) h6)))) (S h308)) h3) h200) h6)))) h121) h117) h257) h249) h231) h229) h99) h309) (C h19 (T (C h19 h95) h298)))) (S h311)) h84))) h295) h290)
  have h352 := C h8 (T (T (C h8 h320) (C h8 (T (T (T (T (T h351 h202) h198) h327) h350) h349))) h330)
  have h353 := S h323
  have h354 := C h6 (T h75 (C h6 h326))
  have h355 := C h8 (T h49 (C h8 (C (T (T (T (T (T (T (T (T (T (T (T (T (T h3 h200) h354) h353) h324) h352) h346) h345) h344) h315) h314) h327) h350) h349) h8)))
  have h356 := S h55
  have h357 := C h8 (T h49 (C h8 (C h52 h8)))
  have h358 := S h343
  have h359 := C h15 h95
  have h360 := C h19 (T (T (T h337 (C h8 (C h8 (C (T h13 (C h15 h359)) h15)))) (S h338)) (C (T (T (T (T (T (T (T (T h3 h200) h354) h353) h324) h352) h346) h345) (C h19 h222)) h19))
  have h361 := S h336
  have h362 := C h8 (T h192 (C h8 (T (T h197 h195) (C h334 h19))))
  have h363 := C h19 (T (T (T (T (T (T (T (T (T (T (T (C h19 (T (T (T (T (T (T (T (T h3 h200) h354) h353) h324) h352) h362) h361) h360)) h358) h160) h252) h251) h214) h213) h189) h187) h186) h179) h173)
  have h364 := C h19 (C h19 h194)
  have h365 := C h8 (T (C h8 (C (T (T (T (T (T (T (T (T (T (T (T (T (T h332 h331) h328) h313) h364) h363) h341) h340) h333) h325) h323) h321) h7) h4) h8)) h51)
  have h366 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h55 h53) h355) h348) h172) h221) h220) h219) h188) h218) h217) h216) h215) h161) h70) h68) h8
  have h367 := C (T (T (T h45 (C h8 (T (C h8 (C (S h47) h8)) h51))) h357) h356) h8
  have h368 := h z x x
  have h369 := h (M x (M v211 x)) x x
  have h370 := h z x v1
  have h371 := h (M x v22) x x
  let v372 := M (M v18 z) v18
  T (T (T (T h120 (C h8 (C h8 (C (T (T h7 h4) (h z v2 v18)) h6)))) (S (h (M v2 v372) x v2))) (C h6 (T (T (T (T (T (T (T (T (h v372 v18 x) (C h19 (C h19 (T (T (T (T (C (T (T (T (h (M x v372) x x) (C h8 (T (C h8 (C (S (h z x v18)) h8)) h51))) (C h8 (T h49 (C h8 (C h370 h8))))) (S h371)) h8) (C (T (T (T h371 (C h8 (T (C h8 (C (S h370) h8)) h51))) (C h8 (T h49 (C h8 (C h368 h8))))) (S h369)) h8)) (C (T (T (T h369 (C h8 (T (C h8 (C (S h368) h8)) h51))) h50) h46) h8)) h367) h366)))) (S (h v183 v18 x))) h333) h325) h323) h321) (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h9 (C h15 (T h13 (C h15 (T h359 h26))))) (S h24)) h25) (C h8 (T (C h8 h21) (C h8 (C h27 h19))))) (S h29)) (C h19 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h30 (C h8 (C h8 (C (T (T h32 (C h8 (C h8 (T (C (S h33) h31) h39)))) h38) h31)))) (C h8 (C h8 (C (T (T h37 (C h8 (C h8 (T h35 (C h40 h31))))) (S h42)) h31)))) (S h43)) h44) (C h8 (C h8 h367))) (S h56)) h57) (C h8 (C h8 (C (T (T h58 (C h8 (C h8 (T (C (S h59) h15) (C h60 h15))))) (S h61)) h15)))) (S h62)) h63) h318) h317) h316) h351) h202) h198) h313) h364) h363) h341) h340) h362) h361) h360))) h358) h160) h252) h251) h214) h213) h189) h187) h186) h179) h173) h347) h365) h357) h356) h8)) h366))) (C h6 (T (T (T (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h74 h72) h160) h252) h251) h214) h213) h189) h187) h186) h179) h173) h347) h365) h357) h356) h8) (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h55 h53) h355) h348) h172) h221) h220) h219) h188) h218) h217) h216) h215) h161) h343) (C h19 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h342 h336) h335) h346) h345) h344) h315) h314) h197) h195) h312) h79) h77) h71) h64) h62) (C h8 (C h8 (C (T (T h61 (C h8 (C h8 (T (C (S h60) h15) (C h59 h15))))) (S h58)) h15)))) (S h57)) h56) (C h8 (C h8 (C (T (T (T h55 h53) h50) h46) h8)))) (S h44)) h43) (C h8 (C h8 (C (T (T h42 (C h8 (C h8 (T (C (S h40) h31) h39)))) h38) h31)))) (C h8 (C h8 (C (T (T h37 (C h8 (C h8 (T h35 (C h33 h31))))) (S h32)) h31)))) (S h30)))) h29) (C h8 (T (C h8 (C (S h27) h19)) (C h8 h26)))) (S h25)) h24) (C h15 (T (C h15 (T h21 h17)) h14))) h10) h8)) h7) h4))

