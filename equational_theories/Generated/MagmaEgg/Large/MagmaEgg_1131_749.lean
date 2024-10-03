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
theorem Equation1131_implies_Equation749 (G: Type _) [Magma G] (h: Equation1131 G) : Equation749 G := fun x y z =>
  let v0 := M x z
  let v1 := M v0 y
  let v2 := M z v1
  let v3 := M y v2
  have h4 := h v3 y v2
  have h5 := S h4
  have h6 := h (M (M y (M v2 v3)) v2) x y
  have h7 := R y
  have h8 := R x
  have h9 := h (M (M x v3) y) x x
  have h10 := h v2 x y
  have h11 := h v2 x v3
  have h12 := S h11
  have h13 := C h8 h12
  let v14 := M (M x (M v3 v2)) v3
  have h15 := h v14 x x
  have h16 := h v14 y x
  have h17 := S h16
  have h18 := h v2 z y
  have h19 := S h18
  have h20 := R v2
  have h21 := h y z v0
  have h22 := S h21
  have h23 := R z
  have h24 := C h23 (C h22 h20)
  have h25 := h v0 z v2
  have h26 := T h25 h24
  have h27 := C h26 h7
  have h28 := h z y v3
  have h29 := R v3
  have h30 := h v1 y z
  have h31 := C (T (C h7 (C h30 h29)) (S h28)) h27
  have h32 := h v3 y v1
  have h33 := C h7 (C (T h32 (C h7 (T (T h31 h19) h11))) h8)
  have h34 := S h32
  have h35 := S h25
  have h36 := C h23 (C h21 h20)
  have h37 := T h36 h35
  have h38 := C h37 h7
  have h39 := C (T h28 (C h7 (C (S h30) h29))) h38
  have h40 := C h7 (C (T (C h7 (T (T h12 h18) h39)) h34) h8)
  have h41 := S h15
  have h42 := C h8 h11
  have h43 := h v2 x v0
  let v44 := M v0 v2
  let v45 := M x v44
  have h46 := h (M v45 v0) x x
  have h47 := R v0
  have h48 := h v45 v3 v2
  have h49 := S h48
  have h50 := h z v2 v2
  have h51 := C h8 (C (C h8 (S h50)) h20)
  have h52 := h (M (M v2 (M v2 z)) v2) x v2
  have h53 := h z x x
  have h54 := S h53
  have h55 := h v0 x v1
  have h56 := C h8 (C (C h8 (S h55)) h8)
  let v57 := M v1 v0
  let v58 := M x v57
  have h59 := h (M v58 v1) x x
  have h60 := R v1
  have h61 := h x v3 y
  have h62 := S h61
  have h63 := h (M (M v3 (M y x)) y) x v3
  have h64 := S h63
  have h65 := h x v3 x
  have h66 := C h8 (S h65)
  have h67 := C h8 (C (T h66 (C h8 h61)) h29)
  have h68 := C h8 h65
  let v69 := M x x
  have h70 := h v69 x v2
  let v71 := M (M z (M v3 y)) v3
  have h72 := h x v2 v71
  have h73 := R v71
  have h74 := h v71 x z
  have h75 := S h74
  have h76 := h y z v3
  have h77 := C h8 (C (T (C h8 h22) (C h8 h76)) h23)
  let v78 := M v2 v0
  have h79 := h v78 x z
  have h80 := h z v2 x
  have h81 := h y x v0
  have h82 := S h81
  have h83 := h (M (M x v1) v0) v2 x
  have h84 := h v3 v3 v3
  have h85 := S h84
  have h86 := C h8 (C (T (T (T (C h8 h85) (C h8 (T h32 (C (T h81 (C h8 (T h83 (C h20 (C (T (T (C h20 h82) (C h20 (T h76 (C (T h80 (C h20 (C (T (T h79 h77) h75) h8))) h73)))) (S h72)) h8))))) (T h31 h19))))) (S h70)) h68) h29)
  let v87 := M v3 v3
  let v88 := M (M v3 v87) v3
  have h89 := h v88 x v3
  have h90 := h v88 z v3
  have h91 := S h90
  have h92 := C h23 (C (T (T h25 h24) (C h23 h84)) h29)
  have h93 := C h29 (T (T (T (T (T h92 h91) h89) h86) h67) h64)
  have h94 := T h93 h62
  have h95 := C h94 h23
  have h96 := C h23 (C (T (T (C h23 h85) h36) h35) h29)
  have h97 := S h89
  have h98 := S h76
  have h99 := S h79
  have h100 := C h8 (C (T (C h8 h98) (C h8 h21)) h23)
  have h101 := C h8 (C (T (T (T h66 h70) (C h8 (T (C (T (C h8 (T (C h20 (C (T (T h72 (C h20 (T (C (T (C h20 (C (T (T h74 h100) h99) h8)) (S h80)) h73) h98))) (C h20 h81)) h8)) (S h83))) h82) (T h18 h39)) h34))) (C h8 h84)) h29)
  have h102 := C h8 (C (T (C h8 h62) h68) h29)
  have h103 := C h29 (T (T (T (T (T h63 h102) h101) h97) h90) h96)
  let v104 := M v0 v3
  have h105 := h (M z v104) z v3
  have h106 := S h105
  have h107 := T h61 h103
  have h108 := C h23 h107
  let v109 := M z x
  have h110 := h v109 v3 v3
  have h111 := S h110
  have h112 := h z v3 v3
  have h113 := S h112
  let v114 := M v3 z
  have h115 := h (M (M v3 v114) v3) x v3
  have h116 := h v104 v3 x
  have h117 := h v104 v3 z
  have h118 := S h117
  have h119 := C h107 h23
  have h120 := C h29 h119
  have h121 := h (M (M v3 (M v3 v0)) v3) x v3
  have h122 := S h121
  have h123 := h v0 v3 v3
  have h124 := h v0 v3 v0
  have h125 := C h8 (S h124)
  have h126 := C h8 (C (T h125 (C h8 h123)) h29)
  have h127 := C h8 h124
  have h128 := h v0 v3 z
  have h129 := S h128
  have h130 := h (M (M v3 (M z v0)) z) x v3
  have h131 := C h29 (T (T (T (T h130 (C h8 (C (T (C h8 h129) h127) h29))) h126) h122) (C (C h29 (T (T (T h120 h118) h116) (C h29 (C (T (C h29 (T (C h8 (C (C h8 h112) h29)) (S h115))) h113) h8)))) h29))
  have h132 := C h23 (T (T h120 h118) (C (T (T (T h128 h131) h111) h108) h29))
  have h133 := C h29 (T (T (T (T (T (T (T h132 h106) h92) h91) h89) h86) h67) h64)
  have h134 := T h133 h103
  have h135 := C h134 h23
  have h136 := C h29 h95
  have h137 := C h8 (C (T (C h8 (S h123)) h127) h29)
  have h138 := C h29 (T (T (T (T (C (C h29 (T (T (T (C h29 (C (T h112 (C h29 (T h115 (C h8 (C (C h8 h113) h29))))) h8)) (S h116)) h117) h136)) h29) h121) h137) (C h8 (C (T h125 (C h8 h128)) h29))) (S h130))
  have h139 := C h23 h94
  have h140 := C h29 (T (T (T (T (T (T (T h63 h102) h101) h97) h90) h96) h105) (C h23 (T (T (C (T (T (T h139 h110) h138) h129) h29) h117) h136)))
  have h141 := h x v1 x
  have h142 := S h141
  have h143 := h (M (M v1 v69) x) x v1
  have h144 := S h143
  have h145 := h x v1 v3
  have h146 := S h145
  have h147 := C h8 (C (T (C h8 h146) (C h8 h141)) h60)
  let v148 := M (M v1 (M v3 x)) v3
  have h149 := h v148 x v1
  have h150 := h v148 z v1
  have h151 := S h150
  have h152 := C h23 h145
  have h153 := C (T (T (T h128 h131) h111) h152) h60
  have h154 := C h23 h153
  have h155 := C h60 (T (T (T (T h154 h151) h149) h147) h144)
  have h156 := C (T (T (T h155 h142) h61) h140) h23
  have h157 := C h60 (T (T h156 h135) h95)
  let v158 := M v0 v1
  have h159 := h v158 v1 z
  have h160 := h v158 v1 x
  have h161 := S h160
  have h162 := h z v1 v3
  have h163 := S h162
  have h164 := C h8 (C (C h8 h163) h60)
  let v165 := M (M v1 v114) v3
  have h166 := h v165 x v1
  have h167 := C h60 (C (T h162 (C h60 (T h166 h164))) h8)
  have h168 := T (T (T h167 h161) h159) h157
  have h169 := C h8 h168
  have h170 := C h169 h60
  have h171 := S h166
  have h172 := C h8 (C (C h8 h162) h60)
  have h173 := C h60 (C (T (C h60 (T h172 h171)) h163) h8)
  have h174 := S h159
  have h175 := C h23 h146
  have h176 := C (T (T (T h175 h110) h138) h129) h60
  have h177 := C h23 h176
  have h178 := S h149
  have h179 := C h8 (C (T (C h8 h142) (C h8 h145)) h60)
  have h180 := C h60 (T (T (T (T h143 h179) h178) h150) h177)
  have h181 := C (T (T (T h133 h62) h141) h180) h23
  have h182 := T h93 h140
  have h183 := C h182 h23
  have h184 := C h60 (T (T h119 h183) h181)
  have h185 := T (T (T h184 h174) h160) h173
  have h186 := C h8 h185
  have h187 := h v58 v3 v1
  have h188 := h (M v1 v109) v1 z
  have h189 := C h23 h134
  have h190 := C h23 (T (T h184 h174) h153)
  have h191 := C h60 (T (T (T (T h190 h151) h149) h147) h144)
  have h192 := C h23 (T (T (T h191 h142) h61) h140)
  have h193 := C (T (T (T h192 h189) h139) h152) h60
  have h194 := C h23 (T (T (T h193 h176) h160) h173)
  let v195 := M z v57
  have h196 := h v195 z v1
  have h197 := C h23 (T (T h176 h159) h157)
  have h198 := h v3 v1 v3
  have h199 := S h198
  let v200 := M (M v1 v87) v3
  have h201 := h v200 z v1
  have h202 := h v200 x v1
  have h203 := h v3 v1 z
  have h204 := h (M (M v1 (M z v3)) z) x v1
  have h205 := h x v1 z
  have h206 := C h60 (T (T (T (T h143 h179) h178) h150) h197)
  have h207 := h v1 x v0
  have h208 := S h207
  have h209 := h (M (M x v158) v0) v0 x
  have h210 := h (M v57 x) x v1
  have h211 := h z v1 x
  have h212 := h v165 x v0
  have h213 := h v114 x v0
  have h214 := h v3 v0 v1
  have h215 := S h214
  have h216 := h (M (M v0 (M v1 v3)) v1) z v0
  let v217 := M v0 v0
  have h218 := h v217 v0 z
  have h219 := h (M (M x v217) v0) x x
  have h220 := h v0 x v0
  let v221 := M x v0
  have h222 := h (M v221 x) x x
  have h223 := h z x v0
  have h224 := S h223
  have h225 := h (M (M x (M v0 z)) v0) x x
  have h226 := C h23 (T (T (T h133 h62) h141) h206)
  have h227 := C h23 h182
  have h228 := C (T (T (T h175 h108) h227) h226) h60
  have h229 := C (T (T (C h29 (T (T (T (T h167 h161) h153) h228) (C (T (T (T (T (T (T (T (T h192 h189) h139) h110) h138) h129) (C h8 (T (T (T h223 (C h8 (T (T (T (T h225 (C h8 (C (C h8 h224) h8))) (C h8 (C (C h8 h53) h8))) (S h222)) (C (C h8 h220) h8)))) (S h219)) (C (C h8 (T h218 (C h47 (C (T (C h47 (T (C h23 (C (T (T h25 h24) (C h23 h214)) h47)) (S h216))) h215) h23)))) h47)))) (S h213)) (C h29 (T (T h162 (C h60 (T h212 (C h8 (T (C (T (C h8 (T (C h47 (T (T (T (T h166 h164) (C h8 (C (C h8 h211) h60))) (S h210)) (C (T (T h184 h174) (C h47 h207)) h8))) (S h209))) h208) (T (T (T (T h119 h183) h181) (C (T h155 h206) h23)) (C (T (T (T h191 h142) h205) (C h60 (T (T (T (T (T (T (T (T (T (C (T (T (T (T h167 h161) h159) h157) (C h60 h26)) h23) h204) (C h8 (C (T (C h8 (S h203)) (C h8 h198)) h60))) (S h202)) h201) (C h23 (C (T (T (C h23 h199) h36) h35) h60))) h154) h197) h196) h194))) h23))) (S h188)))))) (C h60 h169)))) h60))) (S h187)) h186) h60
  have h230 := C (C h29 h185) h60
  have h231 := h (M (M v3 v57) v1) x v3
  have h232 := S h231
  have h233 := h v0 v3 v1
  have h234 := C h8 (C (T h125 (C h8 h233)) h29)
  have h235 := h v0 v3 v2
  have h236 := C h8 (C (T (C h8 (S h235)) h127) h29)
  have h237 := h (M (M v3 v78) v2) x v3
  have h238 := T (T (T h237 h236) h234) h232
  have h239 := S h237
  have h240 := C h8 (C (T h125 (C h8 h235)) h29)
  have h241 := T (T (T h121 h137) h240) h239
  have h242 := h v0 v3 x
  have h243 := C h8 (C (T (C h8 (S h242)) h127) h29)
  have h244 := h (M (M v3 v221) x) x v3
  have h245 := T (T (T h244 h243) h126) h122
  have h246 := S h244
  have h247 := C h8 (C (T h125 (C h8 h242)) h29)
  have h248 := h v0 v3 y
  have h249 := S h248
  have h250 := C h8 (C (T (C h8 h249) h127) h29)
  have h251 := h (M (M v3 (M y v0)) y) x v3
  have h252 := T (T (T h251 h250) h247) h246
  have h253 := S h251
  have h254 := C h8 (C (T h125 (C h8 h248)) h29)
  let v255 := M (M v3 v217) v0
  have h256 := h v255 x v3
  have h257 := C (C h20 (T (T (T (T (T (C h20 (T (T h256 h254) h253)) (C h20 h252)) (C h20 h245)) (C h20 h241)) (C h20 h238)) (C h20 (T (T (T (T (T h230 h229) h170) h59) h56) h54)))) h20
  have h258 := C h20 (T (T h257 h52) h51)
  have h259 := h v255 v2 v2
  have h260 := S h256
  have h261 := T (T (T (T h251 h250) h260) h259) h258
  have h262 := C h29 h261
  have h263 := h v109 x v1
  have h264 := S h263
  have h265 := C h8 (T h230 h229)
  have h266 := C h8 h238
  have h267 := C h8 h241
  have h268 := C h8 h245
  have h269 := C h8 h252
  have h270 := S h259
  have h271 := T (T (T h244 h243) h254) h253
  have h272 := T (T (T h121 h137) h247) h246
  have h273 := T (T (T h237 h236) h126) h122
  have h274 := C h8 (C (T (C h8 (S h233)) h127) h29)
  have h275 := T (T (T h231 h274) h240) h239
  have h276 := C (C h29 h168) h60
  have h277 := S h196
  have h278 := C h23 (T (T (T h167 h161) h153) h228)
  have h279 := C (T (T h169 h187) (C h29 (T (T (T (T (C (T (T (T (T (T (T (T (T (C h29 (T (T (C h60 h186) (C h60 (T (C h8 (T h188 (C (T h207 (C h8 (T h209 (C h47 (T (T (T (T (C (T (T (C h47 h208) h159) h157) h8) h210) (C h8 (C (C h8 (S h211)) h60))) h172) h171))))) (T (T (T (T (C (T (T (T (C h60 (T (T (T (T (T (T (T (T (T h278 h277) h190) h177) (C h23 (C (T (T h25 h24) (C h23 h198)) h60))) (S h201)) h202) (C h8 (C (T (C h8 h199) (C h8 h203)) h60))) (S h204)) (C (T (T (T (T (C h60 h37) h184) h174) h160) h173) h23))) (S h205)) h141) h206) h23) (C (T h191 h180) h23)) h156) h135) h95)))) (S h212)))) h163)) h213) (C h8 (T (T (T (C (C h8 (T (C h47 (C (T h214 (C h47 (T h216 (C h23 (C (T (T (C h23 h215) h36) h35) h47))))) h23)) (S h218))) h47) h219) (C h8 (T (T (T (T (C (C h8 (S h220)) h8) h222) (C h8 (C (C h8 h54) h8))) (C h8 (C (C h8 h223) h8))) (S h225)))) h224))) h128) h131) h111) h108) h227) h226) h60) h193) h176) h160) h173))) h60
  have h280 := C h186 h60
  have h281 := S h59
  have h282 := C h8 (C (C h8 h55) h8)
  have h283 := C (C h20 (T (T (T (T (T (C h20 (T (T (T (T (T h53 h282) h281) h280) h279) h276)) (C h20 h275)) (C h20 h273)) (C h20 h272)) (C h20 h271)) (C h20 (T (T h251 h250) h260)))) h20
  have h284 := S h52
  have h285 := C h8 (C (C h8 h50) h20)
  have h286 := C h20 (T (T h285 h284) h283)
  have h287 := T (T (T (T h286 h270) h256) h254) h253
  have h288 := C h8 h287
  have h289 := C (T (T (T (T (T (T (T (T (T (T (T h288 h269) h268) h267) h266) h265) h264) h110) h138) h129) h248) h262) h20
  have h290 := C h8 h261
  have h291 := C h8 h271
  have h292 := C h8 h272
  have h293 := C h8 h273
  have h294 := C h8 h275
  have h295 := C h8 (T h279 h276)
  have h296 := C (T (T (T (T (T (T (T (T (T h128 h131) h111) h263) h295) h294) h293) h292) h291) h290) h20
  have h297 := C h29 (T h296 h289)
  have h298 := h (M v3 v44) x v2
  have h299 := C (T (T (T (T (T (T (T (T (T h288 h269) h268) h267) h266) h265) h264) h110) h138) h129) h20
  have h300 := C h29 h287
  have h301 := C (T (T (T (T (T (T (T (T (T (T (T h300 h249) h128) h131) h111) h263) h295) h294) h293) h292) h291) h290) h20
  have h302 := C h29 (T h301 h299)
  have h303 := C h20 (T (T (T (T h257 h52) h51) h48) h302)
  have h304 := T h286 h303
  have h305 := C h20 (T (T (T (T h297 h49) h285) h284) h283)
  have h306 := T h305 h258
  have h307 := C h29 h306
  have h308 := C h29 h304
  have h309 := h v44 v2 v3
  have h310 := h v3 x z
  have h311 := h v0 z v1
  have h312 := h (M v195 v1) x z
  have h313 := h v109 z v1
  have h314 := h v71 v0 z
  let v315 := M v1 z
  have h316 := h v315 x v0
  T (T (T (T (T h61 h140) (C h29 (T (T (T (T h132 h106) h92) h91) (C (C h29 (C h29 (T h4 (C h7 (T (T (T h6 (C h8 (T (T (T (T (T (C (C h8 h5) h7) h9) (C h8 (C (T (C h8 (S h10)) h42) h8))) h41) h16) h40))) (C h8 (T (T (T (T (T h33 h17) h15) (C h8 (C (T h13 (C h8 h43)) h8))) (S h46)) (C (T (T (T (T h48 h302) h298) (C h8 (T (T (T (T (T (T (T (T (C (T (T (T (T (T (T (T (T (T (T (T (T (T (C h8 h306) h288) h269) h268) h267) h266) h265) h264) h110) h138) h129) h248) h262) h308) h20) (C h307 h20)) h301) h299) h309) (C h20 (T (T (T (T (C (T (T (T (T (T (T (T (T (T (T h305 h270) h256) h234) h232) h230) h229) h170) h59) h56) h54) (T (T (T h310 (C h8 (C (T (C h8 h37) (C h8 h311)) h23))) (S h312)) (C (T h196 h194) h60))) (S h313)) h110) h138) h129))) h79) h77) h75))) (C h8 (T h314 (C h47 (C (T (C h26 h98) h38) h23))))) h47)))) (S h316)))))) h29)))) (S (h (M y v315) v3 v3))) (C h7 (T (T (T h316 (C h8 (T (T (T (T (T (C (T (T (T (T (C h8 (T (C h47 (C (T h27 (C h37 h76)) h23)) (S h314))) (C h8 (T (T (T (T (T (T (T (T h74 h100) h99) (C h20 (T (T (T (T h128 h131) h111) h313) (C (T (T (T (T (T (T (T (T (T (T h53 h282) h281) h280) h279) h276) h231) h274) h260) h259) h303) (T (T (T (C (T h278 h277) h60) h312) (C h8 (C (T (C h8 (S h311)) (C h8 h26)) h23))) (S h310)))))) (S h309)) h296) h289) (C h308 h20)) (C (T (T (T (T (T (T (T (T (T (T (T (T (T h307 h300) h249) h128) h131) h111) h263) h295) h294) h293) h292) h291) h290) (C h8 h304)) h20)))) (S h298)) h297) h49) h47) h46) (C h8 (C (T (C h8 (S h43)) h42) h8))) h41) h16) h40))) (C h8 (T (T (T (T (T h33 h17) h15) (C h8 (C (T h13 (C h8 h10)) h8))) (S h9)) (C (C h8 h4) h7)))) (S h6)))) h5

