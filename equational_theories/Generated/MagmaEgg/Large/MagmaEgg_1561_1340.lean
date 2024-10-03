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
theorem Equation1561_implies_Equation1340 (G: Type _) [Magma G] (h: Equation1561 G) : Equation1340 G := fun x y z =>
  let v0 := M y z
  let v1 := M v0 z
  let v2 := M v1 x
  have h3 := R v2
  have h4 := h y z v0
  have h5 := S h4
  let v6 := M y v1
  have h7 := R v6
  let v8 := M z v0
  have h9 := h v8 v1 v2
  have h10 := S h9
  have h11 := h v2 z v0
  have h12 := h x z v0
  let v13 := M x v1
  have h14 := h v13 v2 v1
  have h15 := S h14
  have h16 := h v1 x v1
  let v17 := M v2 v1
  have h18 := R v17
  have h19 := C h18 h16
  have h20 := T h19 h15
  have h21 := R v8
  have h22 := h v17 z v0
  have h23 := T (T h22 (C h21 h20)) (S h12)
  have h24 := R v1
  let v25 := M v1 v2
  have h26 := R v25
  have h27 := C h26 (T (C h24 h23) h11)
  have h28 := h v1 v1 v2
  have h29 := T (T h28 h27) h10
  have h30 := C h29 h7
  have h31 := h (M v1 v6) v1 v0
  let v32 := M v0 v1
  have h33 := h v32 z v0
  have h34 := S h33
  have h35 := h v1 z y
  let v36 := M v1 v0
  have h37 := R v36
  let v38 := M z y
  have h39 := h v38 v0 z
  have h40 := S h39
  have h41 := h z z y
  have h42 := C h24 h41
  let v43 := M v1 z
  have h44 := h v43 v0 z
  have h45 := S h44
  have h46 := h v8 v1 v0
  have h47 := S h46
  have h48 := h v0 z v0
  have h49 := C h37 h48
  have h50 := T h49 h47
  have h51 := S h41
  have h52 := C h24 h51
  have h53 := T h39 h52
  have h54 := h v36 z y
  have h55 := C h24 (T h54 (C h53 h50))
  let v56 := M v1 v36
  have h57 := h v56 y z
  have h58 := S h57
  have h59 := h v56 v0 v0
  let v60 := M v0 v0
  have h61 := R v60
  have h62 := S h54
  have h63 := C h37 (S h48)
  have h64 := R v38
  have h65 := C h64 (T h46 h63)
  have h66 := T h42 h40
  have h67 := C h24 (T (T (C h66 h21) h65) h62)
  have h68 := T h44 h67
  have h69 := h v0 z y
  have h70 := h v0 x v1
  have h71 := S h70
  let v72 := M v0 v2
  have h73 := h v72 z v1
  let v74 := M y v2
  have h75 := h v43 y v74
  let v76 := M v74 y
  have h77 := h v76 y v2
  have h78 := S h77
  let v79 := M v2 y
  have h80 := h v79 v74 v2
  have h81 := h v2 v2 y
  let v82 := M v74 v2
  have h83 := R v82
  have h84 := h v2 v13 v74
  have h85 := S h84
  have h86 := h v74 v1 x
  have h87 := h y x v1
  have h88 := C h87 h86
  have h89 := T h88 h85
  have h90 := R v76
  have h91 := h v82 v74 y
  have h92 := R v74
  have h93 := C h92 (T h91 (C h90 (T (T (C h83 h89) (C h83 h81)) (S h80))))
  have h94 := h (M v74 v82) v0 z
  have h95 := S h94
  have h96 := C (S h87) (S h86)
  have h97 := T h84 h96
  have h98 := C h92 (T (C h90 (T (T h80 (C h83 (S h81))) (C h83 h97))) (S h91))
  have h99 := T h77 h98
  have h100 := h v25 v74 y
  have h101 := C h24 (T h100 (C h99 (T (T (C h26 h89) (C h26 h11)) h10)))
  let v102 := M v1 v25
  have h103 := h v102 v2 v2
  let v104 := M v2 v2
  have h105 := h v104 y v74
  have h106 := h v102 v1 v17
  have h107 := S h106
  have h108 := C h18 (S h16)
  have h109 := h v13 v2 v2
  have h110 := S h109
  have h111 := h v2 x v1
  have h112 := R v104
  have h113 := C h112 h111
  have h114 := S h100
  have h115 := C h26 (S h11)
  have h116 := T (T h9 h115) (C h26 h97)
  have h117 := T h93 h78
  have h118 := C h24 (T (C h117 h116) h114)
  have h119 := T (T (T h77 h98) h94) h118
  have h120 := C h119 (T (T (T (T (C h112 h89) h113) h110) h14) h108)
  have h121 := h v104 v74 y
  have h122 := R (M v1 v17)
  have h123 := C h122 (T h121 h120)
  have h124 := S h121
  have h125 := C h112 (S h111)
  have h126 := T (T (T h101 h95) h93) h78
  have h127 := C h126 (T (T (T (T h19 h15) h109) h125) (C h112 h97))
  have h128 := C h122 (T h127 h124)
  have h129 := h v76 v1 x
  have h130 := R (M v17 v1)
  let v131 := M y v74
  have h132 := h v131 v2 v2
  have h133 := R v131
  have h134 := h v131 v74 y
  have h135 := R v43
  have h136 := h v13 v2 v0
  let v137 := M v2 v0
  have h138 := R v137
  have h139 := h v137 z y
  have h140 := R v72
  have h141 := h v131 v0 v2
  let v142 := M z v1
  have h143 := R v142
  have h144 := R v13
  have h145 := C h144 (T (C h143 (T (T (T h84 h96) h141) (C h140 (T (C h133 (T (T h139 (C h53 (T (T (T (C h138 h70) (S h136)) h14) h108))) (C h135 (T (T (T (T (T (T (T (T (T h19 h15) h109) h125) (C h112 (T (T (T h84 h96) h134) (C h119 (T (C h133 (T (T h132 (C h112 (T (T (T (T (T (T (T (C h89 (T (T (T h121 h120) (C (T h101 h95) h130)) (C h117 h20))) (S h129)) h77) h98) h94) h118) h106) h128))) (C h112 (T (T (T (T (T h123 h107) h101) h95) h93) h78)))) (S h105)))))) (S h103)) h101) h95) h93) h78)))) (S h75))))) (S h73))
  have h146 := h v142 x v1
  have h147 := C h68 (T (T (T (T (T (C h61 (T (T (T (T (T h146 h145) h71) h69) (C h53 h61)) (C h68 h61))) (S h59)) h55) h45) h42) h40)
  have h148 := h v60 v1 z
  have h149 := R v0
  have h150 := C h149 (T h148 h147)
  let v151 := M v0 v60
  have h152 := h v151 y v2
  have h153 := S h152
  have h154 := R v79
  have h155 := S h148
  have h156 := S h146
  have h157 := T h14 h108
  have h158 := C h144 (T h73 (C h143 (T (T (T (C h140 (T h75 (C h133 (T (T (C h135 (T (T (T (T (T (T (T (T (T h77 h98) h94) h118) h103) (C h112 (T (T (T (C h126 (T h105 (C h133 (T (T (C h112 (T (T (T (T (T h77 h98) h94) h118) h106) h128)) (C h112 (T (T (T (T (T (T (T h123 h107) h101) h95) h93) h78) h129) (C h97 (T (T (T (C h99 h157) (C (T h94 h118) h130)) h127) h124))))) (S h132))))) (S h134)) h88) h85))) h113) h110) h14) h108)) (C h66 (T (T (T h19 h15) h136) (C h138 h71)))) (S h139))))) (S h141)) h88) h85)))
  have h159 := T h55 h45
  have h160 := C h159 (T (T (T (T (T h39 h52) h44) h67) h59) (C h61 (T (T (T (T (T (C h159 h61) (C h66 h61)) (S h69)) h70) h158) h156)))
  have h161 := C h149 (T h160 h155)
  have h162 := T (T (T h44 h67) h57) h161
  have h163 := h v79 v74 v0
  have h164 := h v0 v2 y
  let v165 := M v74 v0
  have h166 := R v165
  have h167 := h v165 z y
  have h168 := C h92 (T (T h167 (C h53 (T (C h166 h164) (S h163)))) (C h162 h154))
  have h169 := T (C (T (T (T (T (T (T (T h168 h153) h150) h58) h55) h45) h42) h40) h37) (S h35)
  have h170 := R v32
  have h171 := C h170 h169
  let v172 := M v74 v165
  have h173 := h v172 v0 v1
  have h174 := C h92 (T (T (C (T (T (T (T (T h150 h58) h55) h45) h42) h40) h154) (C h64 (T h163 (C h166 (S h164))))) (S h167))
  have h175 := T (T (T (T (T (T (T h44 h67) h57) h161) h152) h174) h173) h171
  have h176 := C h29 h175
  have h177 := C h24 h53
  let v178 := M v1 v38
  have h179 := h v178 z z
  have h180 := S h179
  let v181 := M z z
  have h182 := R v181
  have h183 := C h24 h66
  have h184 := S h22
  have h185 := C h21 h157
  have h186 := T (T h12 h185) h184
  have h187 := T (T (T h9 h115) (C h26 (C h24 h186))) (S h28)
  have h188 := C h187 h135
  have h189 := C h21 (T (T (T (T (T (C h170 (T (T h35 (C h53 h37)) (C h162 h37))) (S (h v151 v0 v1))) h150) h58) h55) h45)
  have h190 := T (T h33 h189) h188
  have h191 := T (T h54 (C h64 h50)) h51
  have h192 := R z
  have h193 := C h192 h191
  have h194 := h z v0 v1
  have h195 := h (M z v8) v0 v1
  have h196 := T (T h41 h65) h62
  have h197 := C h192 h29
  have h198 := h v178 v1 v0
  have h199 := S h198
  have h200 := h v32 v0 z
  have h201 := h v32 y v2
  have h202 := S h201
  have h203 := h v79 z v1
  have h204 := S h203
  have h205 := h v43 z v1
  have h206 := S h205
  have h207 := T (T h70 h158) h156
  have h208 := C h207 (T (T h148 h147) (C h159 h53))
  have h209 := h v172 v0 v74
  have h210 := T (T h146 h145) h71
  have h211 := C h210 (T (T (C h68 h66) h160) h155)
  have h212 := T (T (T h205 h211) h152) h174
  have h213 := h v74 v1 z
  let v214 := M v0 v74
  have h215 := R v214
  have h216 := h v214 v2 y
  have h217 := C h143 (T (T h216 (C h154 (T (T (T (T (T (T (T (C h215 (T h213 (C h212 (C h92 h210)))) (S h209)) h168) h153) h208) h206) h42) h40))) (C h154 h53))
  have h218 := C h207 h215
  have h219 := h (M v0 v214) v74 z
  have h220 := R (M z v74)
  have h221 := C h210 h215
  have h222 := C h143 (T (T (C h154 h66) (C h154 (T (T (T (T (T (T (T h39 h52) h205) h211) h152) h174) h209) (C h215 (T (C (T (T (T h168 h153) h208) h206) (C h92 h207)) (S h213)))))) (S h216))
  have h223 := h z v2 y
  have h224 := h z v1 z
  have h225 := S h224
  have h226 := C h192 h207
  have h227 := C h24 h210
  let v228 := M v1 v142
  have h229 := R v228
  have h230 := C h53 (T (T (T (T (T (C h229 h207) (C h227 h143)) (C h37 h210)) h49) h47) h226)
  have h231 := h v228 z y
  have h232 := C h24 h207
  let v233 := M v74 z
  have h234 := R v233
  have h235 := h v233 v0 v1
  have h236 := C h92 (T h235 (C h170 (T (T (T (T (C h234 (T (T (T (T (T h232 h231) h230) h225) h223) (C (T (T h203 h222) h221) h220))) (S h219)) h218) h217) h204)))
  have h237 := T h236 h202
  let v238 := M v74 v233
  have h239 := h v238 y z
  have h240 := S h239
  have h241 := R v238
  have h242 := S h231
  have h243 := C h192 h210
  have h244 := C h66 (T (T (T (T (T h243 h46) h63) (C h37 h207)) (C h232 h143)) (C h229 h210))
  have h245 := C h92 (T (C h170 (T (T (T (T h203 h222) h221) h219) (C h234 (T (T (T (T (T (C (T (T h218 h217) h204) h220) (S h223)) h224) h244) h242) h227)))) (S h235))
  have h246 := T h201 h245
  have h247 := h v1 v0 v1
  have h248 := h v1 v1 z
  have h249 := S h248
  have h250 := h z z v0
  have h251 := C h135 (T (T (T (S h250) h224) h244) h242)
  have h252 := h v8 v1 z
  have h253 := C h210 (T (T (T (T (T h252 h251) h249) h247) (C h246 h159)) (C h241 h66))
  have h254 := C h207 h21
  have h255 := R (M v0 v8)
  have h256 := C h210 h21
  have h257 := S h252
  have h258 := C h135 (T (T (T h231 h230) h225) h250)
  have h259 := C h207 (T (T (T (T (T (C h241 h53) (C h237 h68)) (S h247)) h248) h258) h257)
  let v260 := M z v142
  have h261 := h v260 v0 z
  have h262 := h v260 v1 v1
  let v263 := M v1 v1
  have h264 := R v263
  have h265 := h v8 z v1
  have h266 := S h265
  have h267 := C h143 (T h33 h189)
  have h268 := C h207 h170
  have h269 := C h210 h170
  have h270 := C h143 (T (C h21 h175) h34)
  have h271 := h v1 z v0
  have h272 := h v263 v0 z
  have h273 := T (T (T (T (T (C h24 (T h272 (C (T (T (T h248 h258) h257) h226) (T (T (C h264 (T (T (T (T (T h252 h251) h249) h271) (C (T (T h265 h270) h269) h264)) (C (T (T (T h268 h267) h266) h226) h264))) (S h262)) h243)))) (S h261)) h243) h252) h251) h249
  have h274 := T (T (T (T (T h248 h258) h257) h226) h261) (C h24 (T (C (T (T (T h243 h252) h251) h249) (T (T h226 h262) (C h264 (T (T (T (T (T (C (T (T (T h243 h265) h270) h269) h264) (C (T (T h268 h267) h266) h264)) (S h271)) h248) h258) h257)))) (S h272)))
  have h275 := h (M v1 v43) v0 z
  have h276 := T (T h231 h230) h225
  have h277 := S h173
  have h278 := T h248 (C h212 h227)
  have h279 := T h176 h34
  have h280 := C h24 (T (T (T (T (T (T (T (T (C h279 h187) (C h170 h278)) h277) h168) h153) h208) h206) h42) h40)
  have h281 := C h273 h53
  have h282 := C h274 (T (T (T (T (T (T (T (T (T (T (C h246 h21) (C (T (T h239 h259) h256) h21)) (C h255 h187)) (C (T (T (T (T h254 h253) h240) h236) h202) h278)) h277) h168) h153) h208) h206) h42) h40)
  have h283 := T (T (T (T h200 h282) h281) h275) h280
  have h284 := h v228 v0 v1
  have h285 := h v181 v0 v1
  have h286 := C h196 (T h285 (C h283 (T (T (T (T (T (T (C h182 (T (T h232 h284) (C h283 (T (C h276 h37) h193)))) h180) (C h24 (T (T (T (T (T (T (T (T h39 h52) h205) h211) h152) h174) h173) h171) (C h190 h29)))) (S h275)) (C h274 h66)) (C h273 (T (T (T (T (T (T (T (T (T (T h39 h52) h205) h211) h152) h174) h173) (C (T (T (T (T h201 h245) h239) h259) h256) h169)) (C h255 h29)) (C (T (T h254 h253) h240) h21)) (C h237 h21)))) (S h200))))
  have h287 := h (M z v181) v2 v1
  have h288 := S h287
  have h289 := h v25 x z
  let v290 := M x z
  have h291 := R v290
  have h292 := C h192 h196
  have h293 := T (T h177 h176) h34
  have h294 := h v290 v0 v1
  have h295 := T h294 (C (T (T (T (T (T h33 h189) h188) h183) h198) (C h191 (T (C h293 (T (T (T (T (T (T h200 h282) h281) h275) h280) h179) (C h182 (T (T (C h293 (T h292 (C (T (T h224 h244) h242) h37))) (S h284)) h227)))) (S h285)))) (T (C h291 (T (h v36 v1 v2) (C h26 (T (T (C h232 h18) (C h276 h18)) (C h192 h23))))) (S h289)))
  let v296 := M x v290
  have h297 := S h294
  have h298 := T h289 (C h291 (T (T (T (T (C h26 (C h192 h186)) (S (h z v1 v2))) h41) h65) h62))
  have h299 := h z z z
  have h300 := C h187 h7
  have h301 := T (T (T (T (T (T (T (T h28 h27) h10) h46) h63) (C h37 (C (T h4 h300) (T (T (T (T (T h299 (C h182 (T (T (T (T (T (T (T (T h287 (C h23 (T (C (T (T (T (T h286 h199) h177) h176) h34) h298) h297))) (h v296 v0 z)) (C h24 (T (T (C (R v296) h187) (C (T (T (T (T (T (T (C h186 h295) h288) h286) h199) h177) h176) h34) (C (T (T (T h70 h158) h156) h197) h196))) (S h195)))) (S (h z v0 z))) h194) (C h170 h193)) (C h190 h182)) (C h183 h182)))) h180) h177) h176) h34)))) (S h31)) h30) h5
  T (T (T (T (T (T (T (T h12 h185) h184) (C h3 h301)) (h v79 v74 y)) (C h90 (T (T (T (T (T (S (h y v2 y)) h4) h300) h31) (C h37 (T (C (T h30 h5) (T (T (T (T (T (T h33 h189) h188) h183) h179) (C h182 (T (T (T (T (T (T (T (T (C h177 h182) (C h279 h292)) (S h194)) h250) (C h21 (T (T h197 h195) (C (T (T (T (T (T h33 h189) h188) h183) (h v178 v2 v1)) (C h23 (T (T (C h293 h26) (C h170 h298)) h297))) (C (T (T (T (C h192 h187) h146) h145) h71) h191))))) (S (h v296 z v0))) (C h186 h291)) (C h18 h295)) h288))) (S h299))) h48))) h47))) (C h90 h116)) h114) (C h301 h3)

