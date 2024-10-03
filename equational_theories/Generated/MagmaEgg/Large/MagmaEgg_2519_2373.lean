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
theorem Equation2519_implies_Equation2373 (G: Type _) [Magma G] (h: Equation2519 G) : Equation2373 G := fun x y z =>
  let v0 := M x z
  let v1 := M z v0
  let v2 := M y v1
  let v3 := M v2 y
  let v4 := M y v2
  let v5 := M v4 v3
  have h6 := h v3 v2 v5
  have h7 := S h6
  have h8 := R v5
  have h9 := h y v3 v2
  have h10 := h v1 v3 y
  have h11 := S h10
  have h12 := R y
  have h13 := R v3
  have h14 := h y y v1
  have h15 := R v1
  have h16 := h y v1 v3
  have h17 := C (C h13 (T h16 (C (C h15 (S h14)) h13))) h12
  have h18 := T h17 h11
  have h19 := C h12 h18
  have h20 := h v3 y y
  have h21 := C (T h20 (C h19 h9)) h8
  have h22 := h (M v3 v5) x v2
  have h23 := S h22
  have h24 := R v2
  have h25 := R x
  have h26 := h y v1 v0
  have h27 := C (S h26) h25
  have h28 := C h26 h25
  have h29 := h y v1 v2
  have h30 := C h25 (T (C (S h29) h25) h28)
  have h31 := C (T h30 (C h25 (T h27 (C h9 h25)))) h24
  let v32 := M v1 (M v4 v1)
  have h33 := C (C h13 (T (C (C h15 h14) h13) (S h16))) h12
  have h34 := T h10 h33
  have h35 := C h12 h34
  have h36 := R z
  have h37 := h x x z
  have h38 := S h37
  have h39 := h v0 v1 z
  have h40 := S h39
  have h41 := C (C h25 (C h40 h25)) h36
  let v42 := M v0 z
  let v43 := M v42 v1
  have h44 := h (M v1 v43) x z
  have h45 := R v43
  have h46 := C (C h36 h40) h45
  have h47 := h v1 z v43
  have h48 := h v1 v2 v3
  have h49 := S h48
  let v50 := M v1 v3
  have h51 := h (M v2 (M v50 v2)) x v3
  let v52 := M v1 x
  have h53 := h (M x v52) x x
  have h54 := S h53
  have h55 := h v1 y x
  have h56 := S h55
  let v57 := M y (M v52 y)
  have h58 := h v57 x x
  have h59 := C (C h25 (T h55 (C (T h58 (C (C h25 (C h56 h25)) h25)) h25))) h25
  have h60 := h v57 v0 x
  have h61 := R v0
  have h62 := C (C h25 (T (C (T (C (C h61 (C h55 h61)) h25) (S h60)) h25) h56)) h25
  have h63 := h (M v0 (M v1 v0)) x x
  have h64 := h v1 x v3
  have h65 := S h64
  let v66 := M v50 x
  let v67 := M x v66
  have h68 := h v67 v0 v3
  have h69 := h v67 x v3
  have h70 := h v1 v3 v3
  have h71 := h (M v3 (M v50 v3)) x v3
  have h72 := h v50 v3 x
  have h73 := S h72
  have h74 := h v66 v2 v3
  have h75 := S h74
  have h76 := T (T (T (T h47 h46) h44) h41) h38
  have h77 := h x y v3
  have h78 := S h77
  have h79 := C (C h36 (C h78 h36)) h13
  let v80 := M x v3
  let v81 := M y (M v80 y)
  have h82 := h v81 z v3
  have h83 := h v81 x v3
  have h84 := S h83
  have h85 := h x v1 v1
  have h86 := C (S h85) h25
  have h87 := C h25 (T h86 (C h77 h25))
  have h88 := C h85 h25
  have h89 := h x x v3
  let v90 := M v80 x
  have h91 := h (M x v90) x v3
  have h92 := h v3 v0 x
  have h93 := S h92
  let v94 := M v3 x
  have h95 := h (M v0 (M v94 v0)) x x
  have h96 := S h95
  have h97 := h (M x v94) x x
  have h98 := S h97
  have h99 := h v3 v2 x
  have h100 := S h99
  let v101 := M v2 (M v94 v2)
  have h102 := h v101 x x
  have h103 := C (C h25 (T h99 (C (T h102 (C (C h25 (C h100 h25)) h25)) h25))) h25
  have h104 := C (T (T h103 h98) (C h25 (C h92 h25))) h25
  have h105 := h v90 v3 v0
  have h106 := S h105
  have h107 := h v101 v2 x
  have h108 := h (M v2 (M v3 v2)) x x
  have h109 := C h25 (T h27 (C h29 h25))
  have h110 := h y x v2
  have h111 := C (T (C h25 (T (C (S h110) h25) h28)) h109) h24
  let v112 := M v4 x
  let v113 := M x v112
  have h114 := h v113 x v2
  have h115 := h v113 x v0
  have h116 := S h115
  have h117 := S h114
  have h118 := C (T h30 (C h25 (T h27 (C h110 h25)))) h24
  have h119 := S h9
  have h120 := C (T (C h25 (T (C h119 h25) h28)) h109) h24
  have h121 := C (T (C h35 h119) (S h20)) h8
  have h122 := C (T (T (T (T (T h6 h121) h22) h120) h118) h117) h61
  let v123 := M v3 v0
  let v124 := M x (M v123 x)
  have h125 := h v124 v3 v0
  have h126 := S h125
  have h127 := h v3 x v0
  let v128 := M v3 v3
  have h129 := h (M v3 v128) x y
  have h130 := S h129
  have h131 := h v2 v3 y
  have h132 := C (C h25 (C h131 h25)) h12
  have h133 := C (T (T h132 h130) (C h13 (C h127 h13))) h61
  have h134 := C (T (T h133 h126) (C h25 (C h122 h25))) h61
  have h135 := T (T (T (T (T (T (T h134 h116) h114) h111) h31) h23) h21) h7
  have h136 := C (T (T (C h24 (C h135 h24)) h108) (C (C h25 (T (C (T (C (C h24 (C h99 h24)) h25) (S h107)) h25) h100)) h25)) h61
  let v137 := M (M x (M v2 x)) y
  let v138 := M v137 v0
  have h139 := h v138 v2 v0
  have h140 := C (C h13 (C (T h139 h136) h13)) h61
  have h141 := h v137 v3 v0
  have h142 := C (C h25 (C (S h131) h25)) h12
  have h143 := C (T (T (T (T h129 h142) h141) h140) h106) h25
  have h144 := h v3 x v1
  have h145 := C (C h13 (C (S h144) h13)) h76
  let v146 := M x (M (M v3 v1) x)
  have h147 := h v146 v3 v1
  have h148 := h v146 y x
  have h149 := S h147
  have h150 := S h47
  have h151 := C (C h36 h39) h45
  have h152 := S h44
  have h153 := C (C h25 (C h39 h25)) h36
  have h154 := T (T (T (T h37 h153) h152) h151) h150
  have h155 := C (C h13 (C h144 h13)) h154
  have h156 := C (T h155 h149) h25
  have h157 := S h141
  have h158 := S h139
  have h159 := S h127
  have h160 := C (T (T (C h13 (C h159 h13)) h129) h142) h61
  have h161 := C (T (T (T (T (T h114 h111) h31) h23) h21) h7) h61
  have h162 := C (T (T (C h25 (C h161 h25)) h125) h160) h61
  have h163 := T (T (T (T (T (T (T h6 h121) h22) h120) h118) h117) h115) h162
  have h164 := C (T (T (C (C h25 (T h99 (C (T h107 (C (C h24 (C h100 h24)) h25)) h25))) h25) (S h108)) (C h24 (C h163 h24))) h61
  have h165 := C (C h13 (C (T h164 h158) h13)) h61
  have h166 := C (T (T (T (T h105 h165) h157) h132) h130) h25
  have h167 := C (C h25 (T (C (T (C (C h25 (C h99 h25)) h25) (S h102)) h25) h100)) h25
  have h168 := C (T (T (C h25 (C h93 h25)) h97) h167) h25
  have h169 := C (T (T h95 h168) h166) h25
  have h170 := h (M v3 y) x y
  have h171 := h v1 v0 y
  have h172 := S h171
  let v173 := M v1 y
  let v174 := M v0 (M v173 v0)
  have h175 := h v174 v0 y
  have h176 := h v174 x y
  have h177 := h v1 v2 y
  have h178 := S h177
  let v179 := M v173 v2
  have h180 := h (M v2 v179) x y
  have h181 := R v179
  have h182 := h v2 y v179
  have h183 := C h12 (T (T (T (T (T (T (T (T (T h182 (C (T (C h12 (T (T h178 h10) h33)) h19) h181)) h180) (C (T (C h25 (C h178 h25)) (C h25 (C h171 h25))) h12)) (S h176)) h175) (C (C h61 (C h172 h61)) h12)) (C (T (T (T (T h63 h62) h59) h54) (C h25 (C h34 h25))) h12)) (S h170)) (C (T (T h92 h169) h156) h12))
  have h184 := C (T (T (T (T (T (T (C h183 h25) (S h148)) h147) h145) h143) h104) h96) h76
  have h185 := C h76 (T h184 h93)
  have h186 := C h185 h25
  have h187 := S h63
  have h188 := C (C h25 (T h55 (C (T h60 (C (C h61 (C h56 h61)) h25)) h25))) h25
  have h189 := C (C h25 (T (C (T (C (C h25 (C h55 h25)) h25) (S h58)) h25) h56)) h25
  have h190 := C (T (T h143 h104) h96) h25
  have h191 := C (T h147 h145) h25
  have h192 := C h12 (T (T (T (T (T (T (T (T (T (C (T (T h191 h190) h93) h12) h170) (C (T (T (T (T (C h25 (C h18 h25)) h53) h189) h188) h187) h12)) (C (C h61 (C h171 h61)) h12)) (S h175)) h176) (C (T (C h25 (C h172 h25)) (C h25 (C h177 h25))) h12)) (S h180)) (C (T h35 (C h12 (T (T h17 h11) h177))) h181)) (S h182))
  have h193 := C (T (T (T (T (T (T h95 h168) h166) h155) h149) h148) (C h192 h25)) h154
  have h194 := C h154 (T h92 h193)
  have h195 := h v80 v3 x
  have h196 := S h195
  have h197 := h v4 v1 x
  have h198 := C (T h197 h186) h13
  have h199 := C h13 h198
  have h200 := R (M v112 v1)
  have h201 := T (T h191 h190) h193
  have h202 := T (T (T (T (T (T (T (T h114 h111) h31) h23) h21) h7) h92) h169) h156
  have h203 := C (T (T (T (T (T (C h25 (T (C (T (T (T (T (T (C h202 h15) (C h201 h15)) (C h200 h76)) (C (T (T (T (T h184 h93) h6) h121) h199) h25)) h196) h194) h25) h186)) h91) (C (T (C h25 (T (C (S h89) h25) h88)) h87) h13)) h84) h82) h79) h76
  have h204 := h v113 x v1
  have h205 := C (T (T (T (T (T (T (T (T (T h184 h93) h6) h121) h22) h120) h118) h117) h204) h203) h13
  have h206 := C h201 h13
  have h207 := C (T (T (T (T (T (T (T (T (T (T h134 h116) h114) h111) h31) h23) h21) h7) h92) h169) h156) h13
  have h208 := C h163 h13
  have h209 := T (T (T h208 h207) h206) h205
  have h210 := h (M v2 (M v128 v2)) x v3
  have h211 := h v3 v2 v3
  have h212 := C (T (T (T h198 (C (T (T h103 h98) (C h25 (C h211 h25))) h13)) (S h210)) (C h24 (C h209 h24))) h13
  have h213 := S h197
  have h214 := C h194 h25
  have h215 := C (T h214 h213) h13
  have h216 := C h215 h13
  have h217 := C (T (T h216 h212) h75) h13
  have h218 := C h198 h13
  have h219 := C h218 h13
  have h220 := C h216 h13
  have h221 := C h135 h13
  have h222 := C (T (T (T (T (T (T (T (T (T (T h191 h190) h93) h6) h121) h22) h120) h118) h117) h115) h162) h13
  have h223 := T (T h184 h169) h156
  have h224 := C h223 h13
  have h225 := S h204
  have h226 := T (T (T (T (T (T (T (T h191 h190) h93) h6) h121) h22) h120) h118) h117
  have h227 := C h13 h215
  have h228 := C h25 (T (C h78 h25) h88)
  have h229 := S h82
  have h230 := C (C h36 (C h77 h36)) h13
  have h231 := C (T (T (T (T (T h230 h229) h83) (C (T h228 (C h25 (T h86 (C h89 h25)))) h13)) (S h91)) (C h25 (T h214 (C (T (T (T (T (T h185 h195) (C (T (T (T (T h227 h21) h7) h92) h193) h25)) (C h200 h154)) (C h223 h15)) (C h226 h15)) h25)))) h154
  have h232 := C (T (T (T (T (T (T (T (T (T h231 h225) h114) h111) h31) h23) h21) h7) h92) h193) h13
  have h233 := T (T (T h232 h224) h222) h221
  have h234 := C (T (T (T (C h24 (C h233 h24)) h210) (C (T (T (C h25 (C (S h211) h25)) h97) h167) h13)) h215) h13
  have h235 := C (T (T h74 h234) h218) h13
  have h236 := C (T (C h166 h25) h156) h13
  have h237 := C (T h191 (C h143 h25)) h13
  have h238 := C h13 h208
  have h239 := h v90 v3 v3
  have h240 := S h239
  have h241 := T (T (T (T (T (T (T (T (T (T h6 h121) h22) h120) h118) h117) h204) h203) h74) h234) h218
  have h242 := T (T (T (T (T (T (T (T (T (T h216 h212) h75) h231) h225) h114) h111) h31) h23) h21) h7
  have h243 := C (T h235 (C h242 h241)) h13
  have h244 := C h209 h13
  have h245 := h (M v128 v3) v0 v0
  have h246 := S h245
  have h247 := C h233 h13
  have h248 := C (T (C h241 h242) h217) h13
  have h249 := C h13 h221
  have h250 := C (T (T (T (T (T (T (T (T h249 h129) h142) h141) h140) h106) h239) h248) h247) h61
  have h251 := h v138 v3 v0
  have h252 := h v3 y v0
  have h253 := S h252
  have h254 := h (M y (M v123 y)) x v0
  have h255 := C (T (T (T (T (T h254 (C (T (T (C h25 (C h253 h25)) h97) h167) h61)) h164) h158) h251) h250) h61
  have h256 := C h61 (T h252 h255)
  let v257 := M v0 v3
  have h258 := h v257 v3 v0
  have h259 := S h258
  have h260 := S h251
  have h261 := C (T (T (T (T (T (T (T (T h244 h243) h240) h105) h165) h157) h132) h130) h238) h61
  have h262 := C (T (T (T (T (T h261 h260) h139) h136) (C (T (T h103 h98) (C h25 (C h252 h25))) h61)) (S h254)) h61
  have h263 := C h61 (T h262 h253)
  have h264 := C h263 h61
  have h265 := C h13 (C (T h245 h264) h13)
  have h266 := T (T (T (T (T (T (T (T (T (T (T (T h216 h212) h75) h231) h225) h114) h111) h31) h23) h21) h7) h92) h193
  have h267 := h v5 y v3
  have h268 := C h13 (T h267 (C (T (T (T (T (T (T (T (T (C h12 (C h218 h12)) (C h12 (C h266 h12))) (C h12 (C h223 h12))) h192) h197) h186) h239) h248) h247) h13))
  have h269 := C (T (T (T (T (T (T (T (T (T (T h216 h212) h75) h231) h225) h114) h111) h31) h23) h268) h265) h61
  have h270 := T (T (T (T (T (T (T (T (T (T (T (T h184 h93) h6) h121) h22) h120) h118) h117) h204) h203) h74) h234) h218
  have h271 := C h270 h61
  have h272 := C h201 h61
  have h273 := C h202 h61
  have h274 := C (T (T (T (T (T (T h122 h273) h272) h271) h269) h259) h256) h61
  have h275 := h (M v123 v0) v3 v0
  have h276 := C h226 h61
  have h277 := C h223 h61
  have h278 := C h266 h61
  have h279 := C h13 (T (C (T (T (T (T (T (T (T (T h244 h243) h240) h214) h213) h183) (C h12 (C h201 h12))) (C h12 (C h270 h12))) (C h12 (C h216 h12))) h13) (S h267))
  have h280 := C h256 h61
  have h281 := C h13 (C (T h280 h246) h13)
  have h282 := C (T (T (T (T (T (T (T (T (T (T h281 h279) h22) h120) h118) h117) h204) h203) h74) h234) h218) h61
  have h283 := C (T (T (T (T (T (T h263 h258) h282) h278) h277) h276) h161) h61
  have h284 := C (T h245 h283) h61
  have h285 := h v124 x v0
  have h286 := S h285
  have h287 := h v3 v3 v0
  have h288 := C (T (C h25 (C (S h287) h25)) (C h25 (C h127 h25))) h61
  have h289 := h (M v3 (M v123 v3)) x v0
  have h290 := C h13 (C (T (T (T (T (T h258 h282) h278) h277) h276) h161) h13)
  have h291 := h (M v3 (M v257 v3)) x v3
  have h292 := S h291
  have h293 := h v0 v3 v3
  have h294 := h v0 v1 v3
  have h295 := S h294
  have h296 := C (T (C h25 (C h295 h25)) (C h25 (C h293 h25))) h13
  let v297 := M v1 (M v257 v1)
  have h298 := h v297 x v3
  have h299 := h v297 z v3
  have h300 := S h299
  let v301 := M z v42
  have h302 := h v301 z z
  have h303 := S h302
  have h304 := h x z z
  have h305 := C (C h36 (C h304 h36)) h36
  have h306 := C (T (T h305 h303) (C h36 (C h294 h36))) h13
  have h307 := S h304
  have h308 := C (C h36 (C h307 h36)) h36
  have h309 := h v301 x z
  have h310 := S h309
  have h311 := h x v1 z
  have h312 := C (T (C h25 (T (C (S h311) h25) h88)) (C h25 (T h86 (C h304 h25)))) h36
  let v313 := M v0 v1
  let v314 := M v1 v313
  have h315 := h v314 x z
  have h316 := h v314 x y
  have h317 := S h316
  have h318 := h v0 x y
  have h319 := S h318
  let v320 := M v0 y
  let v321 := M x (M v320 x)
  have h322 := h v321 v1 y
  have h323 := h v321 v3 y
  have h324 := C (C h25 (T (C (T (C (C h13 (C h318 h13)) h12) (S h323)) h25) (C (T h322 (C (C h15 (C h319 h15)) h12)) h25))) h12
  let v325 := M v3 v257
  have h326 := h v325 x y
  have h327 := h v325 x x
  have h328 := S h327
  have h329 := h v0 x x
  have h330 := S h329
  let v331 := M x (M (M v0 x) x)
  have h332 := h v331 v3 x
  have h333 := C (C h25 (T h329 (C (T h332 (C (C h13 (C h330 h13)) h25)) h25))) h25
  have h334 := h v331 y x
  have h335 := h (M y v320) x x
  have h336 := h v0 v2 v3
  have h337 := S h336
  have h338 := C (T (T (T (T (T (T (T (T (T (T (T (T (C h12 (C h337 h12)) h335) (C (C h25 (T (C (T (C (C h12 (C h329 h12)) h25) (S h334)) h25) h330)) h25)) h333) h328) h326) h324) h317) h315) h312) h310) h302) h308) h13
  let v339 := M v2 (M v257 v2)
  have h340 := h v339 y v3
  have h341 := h v339 x v3
  have h342 := S h341
  have h343 := h v0 v3 x
  have h344 := C (S h343) h25
  have h345 := C h343 h25
  have h346 := h v0 z v3
  have h347 := S h346
  have h348 := C (T (C h25 (T (C h347 h25) h345)) (C h25 (T h344 (C h336 h25)))) h13
  have h349 := h (M z (M v257 z)) x v3
  have h350 := T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h349 h348) h342) h340) h338) h306) h300) h298) h296) h292) h290) h289) h288) h286) h125) h160) h251) h250) h284
  have h351 := C h350 h13
  have h352 := h v123 v3 v0
  have h353 := C (T h274 h246) h61
  have h354 := C h353 h61
  have h355 := C h284 h61
  have h356 := S h349
  have h357 := C (T (C h25 (T (C h337 h25) h345)) (C h25 (T h344 (C h346 h25)))) h13
  have h358 := S h340
  have h359 := C (C h25 (T (C (T (C (C h13 (C h329 h13)) h25) (S h332)) h25) h330)) h25
  have h360 := S h326
  have h361 := C (C h25 (T (C (T (C (C h15 (C h318 h15)) h12) (S h322)) h25) (C (T h323 (C (C h13 (C h319 h13)) h12)) h25))) h12
  have h362 := S h315
  have h363 := C (T (C h25 (T (C h307 h25) h88)) (C h25 (T h86 (C h311 h25)))) h36
  have h364 := C (T (T (T (T (T (T (T (T (T (T (T (T h305 h303) h309) h363) h362) h316) h361) h360) h327) h359) (C (C h25 (T h329 (C (T h334 (C (C h12 (C h330 h12)) h25)) h25))) h25)) (S h335)) (C h12 (C h336 h12))) h13
  have h365 := C (T (T (C h36 (C h295 h36)) h302) h308) h13
  have h366 := S h298
  have h367 := C (T (C h25 (C (S h293) h25)) (C h25 (C h294 h25))) h13
  have h368 := C h13 (C (T (T (T (T (T h122 h273) h272) h271) h269) h259) h13)
  have h369 := S h289
  have h370 := C (T (C h25 (C h159 h25)) (C h25 (C h287 h25))) h61
  have h371 := T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h353 h261) h260) h133) h126) h285) h370) h369) h368) h291) h367) h366) h299) h365) h364) h358) h341) h357) h356
  have h372 := C h371 h13
  have h373 := C h284 h13
  have h374 := C (T (T (T h164 h158) h251) h250) h13
  have h375 := T (T (T h374 h373) h372) h347
  have h376 := C (T (T (T h261 h260) h139) h136) h13
  have h377 := C h353 h13
  have h378 := h v331 z x
  have h379 := h v313 v1 v1
  have h380 := h z x v1
  have h381 := S h380
  have h382 := h (M x (M (M z v1) x)) v0 v1
  have h383 := h (M x v0) v1 x
  have h384 := h v331 v2 x
  have h385 := h (M v2 (M v0 v2)) x x
  have h386 := h (M v90 v0) v2 v3
  have h387 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h349 h348) h342) h340) h338) h306) h300) h298) h296) h292) h290) h289) h288) h286) h125) h160) h139) h136) h386) (C (T (T (T (T (T (T (T (C h24 (C h375 h24)) h385) (C (T (T (T (T (C h25 (T (C (T (C (C h24 (C h329 h24)) h25) (S h384)) h25) h330)) h383) (C (T (T (T (T (T (C h15 (T (T (C (T (T (T (T (T (T (T (T (T h333 h328) h326) h324) h317) h315) h312) h310) h302) h308) h15) (C (C h15 (T h380 (C (T h382 (C (C h61 (C h381 h61)) h15)) h15))) h15)) (S h379))) h315) h312) h310) h302) h308) h25)) (C (T (T h305 h303) (C h36 (C h329 h36))) h25)) (S h378)) h25)) h330) h346) h351) h377) h376) h13)) (C h375 (T (T h252 h255) h355))) (C h61 h354)) h263) h258) h282) h278) h277) h276) h161) h352) (C (T (T (T (T (C h13 (C (T h274 h264) h13)) h281) h279) h21) h7) (T h346 h351))) h61) (S h275)) h274) h246) h244) h243) h240) h105) h165) h157) h132) h130) h238) (C h13 h207)) (C h13 h237)) (C h13 (T h236 h206))) (C h13 (T h205 h235))) (C h13 h220)) (C h13 (T h219 h217))) h25
  have h388 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T h216 h212) h75) h231) h225) h114) h111) h31) h23) h21) h7) h252) h255) h355) (C h371 h61)) h76
  have h389 := C (T (T (T (T (T (T (T (T (T h227 h22) h120) h118) h117) h204) h203) h74) h234) h218) h154
  let v390 := M v80 v3
  have h391 := h (M v3 v390) x v3
  have h392 := h x v3 v3
  have h393 := C (T (T (T (T (T (T (T (T (T h216 h212) h75) h231) h225) h114) h111) h31) h23) h199) h76
  have h394 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (C h350 h61) h354) h262) h253) h6) h121) h22) h120) h118) h117) h204) h203) h74) h234) h218) h154
  have h395 := T (T (T h346 h351) h377) h376
  have h396 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (C h13 (T h235 h220)) (C h13 h219)) (C h13 (T h217 h232))) (C h13 (T h224 h237))) (C h13 h236)) (C h13 h222)) h249) h129) h142) h141) h140) h106) h239) h248) h247) h245) h283) h275) (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (C (T (T (T (T h6 h121) h268) h265) (C h13 (C (T h280 h283) h13))) (T h372 h347)) (S h352)) h122) h273) h272) h271) h269) h259) h256) (C h61 h355)) (C h395 (T (T h354 h262) h253))) (C (T (T (T (T (T (T (T h374 h373) h372) h347) h329) (C (T (T (T (T h378 (C (T (T (C h36 (C h330 h36)) h302) h308) h25)) (C (T (T (T (T (T h305 h303) h309) h363) h362) (C h15 (T (T h379 (C (C h15 (T (C (T (C (C h61 (C h380 h61)) h15) (S h382)) h15) h381)) h15)) (C (T (T (T (T (T (T (T (T (T h305 h303) h309) h363) h362) h316) h361) h360) h327) h359) h15)))) h25)) (S h383)) (C h25 (T h329 (C (T h384 (C (C h24 (C h330 h24)) h25)) h25)))) h25)) (S h385)) (C h24 (C h395 h24))) h13)) (S h386)) h164) h158) h133) h126) h285) h370) h369) h368) h291) h367) h366) h299) h365) h364) h358) h341) h357) h356) h61)) h25
  T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h37 h153) h152) h151) h150) h48) (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h51 (C (T (T (T (T (C h25 (C h49 h25)) h53) h189) h188) h187) h13)) (C (C h61 (C h64 h61)) h13)) (S h68)) h69) (C (T (C h25 (C h65 h25)) (C h25 (C h70 h25))) h13)) (S h71)) (C h13 (C (T (T (T (T h72 h396) h394) h393) h196) h13))) h391) (C (T (C h25 (T (C (S h392) h25) h88)) h87) h13)) h84) h82) h79) h72) h396) h394) h393) h196) h13)) (h v390 v3 v2)) (C (T (T (C h13 (C (C (T (T (T (T (T (T (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h195 h389) h388) h387) h73) h230) h229) h83) (C (T h228 (C h25 (T h86 (C h392 h25)))) h13)) (S h391)) (C h13 (C (T (T (T (T h195 h389) h388) h387) h73) h13))) h71) (C (T (C h25 (C (S h70) h25)) (C h25 (C h64 h25))) h13)) (S h69)) h68) (C (C h61 (C h65 h61)) h13)) (C (T (T (T (T h63 h62) h59) h54) (C h25 (C h48 h25))) h13)) (S h51)) h13) h49) h47) h46) h44) h41) h38) h24) h13)) (h (M v3 (M (M x v2) v3)) z v2)) (C (C h36 (C (S (h x v3 v2)) h36)) h24)) h24)) (C (C h15 (T h35 (C h29 h18))) h24)) (S (h v32 v1 v2))) (h v32 x v2)) h31) h23) h21) h7

