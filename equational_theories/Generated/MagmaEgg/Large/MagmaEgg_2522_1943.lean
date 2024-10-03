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
theorem Equation2522_implies_Equation1943 (G: Type _) [Magma G] (h: Equation2522 G) : Equation1943 G := fun x y z =>
  let v0 := M x z
  let v1 := M y z
  let v2 := M y v1
  let v3 := M v2 v0
  have h4 := h v3 v3 v3
  have h5 := S h4
  have h6 := R v3
  have h7 := h v3 v0 y
  have h8 := S h7
  have h9 := R v0
  have h10 := h (M v0 (M (M v3 y) y)) x v0
  have h11 := S h10
  have h12 := R x
  let v13 := M v3 v0
  have h14 := h (M x v13) x x
  have h15 := h v2 x v0
  have h16 := h v2 x v1
  have h17 := S h16
  let v18 := M v2 v1
  let v19 := M v18 v1
  have h20 := h (M x v19) x x
  have h21 := C (T (T (T h20 (C (C h12 (T (C h17 h12) (C h15 h12))) h12)) (S h14)) (C h12 (C h7 h9))) h12
  have h22 := h v2 v3 v0
  have h23 := S h22
  have h24 := h (M v3 v13) x v3
  have h25 := h v2 v3 y
  have h26 := C (S h25) h6
  let v27 := M v2 y
  let v28 := M v27 y
  let v29 := M v3 v28
  have h30 := h v29 x v3
  have h31 := R y
  have h32 := C (T (T (T (C h12 (C h8 h9)) h14) (C (C h12 (T (C (S h15) h12) (C h16 h12))) h12)) (S h20)) h12
  have h33 := T (T h10 h32) h17
  have h34 := C h33 h31
  have h35 := C h34 h31
  have h36 := T (T h16 h21) h11
  have h37 := C h36 h31
  have h38 := h v27 x v2
  have h39 := S h38
  have h40 := R v2
  have h41 := h y v1 x
  have h42 := S h41
  have h43 := R v1
  let v44 := M (M y x) x
  have h45 := h (M v1 v44) x v1
  have h46 := h y v1 v2
  have h47 := C (S h46) h43
  let v48 := M (M y v2) v2
  let v49 := M v1 v48
  have h50 := h v49 x v1
  have h51 := h v49 v2 v1
  have h52 := S h51
  have h53 := C h46 h43
  have h54 := C (C h40 h53) h40
  have h55 := C (T (T (T (T h54 h52) h50) (C (T (C h12 h47) (C h12 (C h41 h43))) h12)) (S h45)) h43
  have h56 := C (C h40 h47) h40
  have h57 := h v49 v1 v1
  have h58 := C (T (T (T (C (C h43 h53) h43) (S h57)) h51) h56) h43
  have h59 := C h36 (T (T h58 h55) h42)
  let v60 := M v1 v2
  have h61 := h v60 v2 v1
  have h62 := h (M x (M v60 v2)) x x
  have h63 := h v1 x v2
  have h64 := h v1 x x
  have h65 := S h64
  let v66 := M (M v1 x) x
  have h67 := h (M x v66) x x
  have h68 := C (T (T (T h67 (C (C h12 (T (C h65 h12) (C h63 h12))) h12)) (S h62)) (C h12 (C (T h61 (C (T h59 h34) h40)) h40))) h12
  have h69 := C (T (T (T h64 h68) h39) h37) h31
  have h70 := h v1 y v1
  have h71 := C (S h70) h31
  have h72 := T (T h71 h69) h35
  have h73 := C (T (T (T (C h6 h72) h30) (C (C h12 (T h26 (C h22 h6))) h12)) (S h24)) h6
  let v74 := M (M v1 v1) v1
  let v75 := M y v74
  have h76 := h v75 v3 y
  have h77 := T (T (T (T (T h76 h73) h23) h16) h21) h11
  have h78 := h v75 v1 y
  have h79 := S h78
  have h80 := C h70 h31
  have h81 := S h61
  have h82 := C (T (T (T h54 h52) h57) (C (C h43 h47) h43)) h43
  have h83 := C (T (T (T (T h45 (C (T (C h12 (C h42 h43)) (C h12 h53)) h12)) (S h50)) h51) h56) h43
  have h84 := C h33 (T (T h41 h83) h82)
  have h85 := C (T (T (T (C h12 (C (T (C (T h37 h84) h40) h81) h40)) h62) (C (C h12 (T (C (S h63) h12) (C h64 h12))) h12)) (S h67)) h12
  have h86 := C (T (T (T h34 h38) h85) h65) h31
  have h87 := C h37 h31
  have h88 := T (T h87 h86) h80
  have h89 := h (M v1 v28) x v1
  have h90 := h v2 v1 y
  have h91 := h (M x v18) x x
  have h92 := h y x v1
  have h93 := h y x v0
  have h94 := S h93
  have h95 := C h94 h12
  let v96 := M (M y v0) v0
  have h97 := h (M x v96) x x
  have h98 := h y z x
  have h99 := S h98
  have h100 := R z
  have h101 := h (M z v44) x z
  have h102 := S h101
  have h103 := h y z v2
  have h104 := C (S h103) h100
  have h105 := C (T (C h12 h104) (C h12 (C h98 h100))) h12
  let v106 := M z v48
  have h107 := h v106 x z
  have h108 := h v106 y z
  have h109 := S h108
  have h110 := C h103 h100
  have h111 := C (C h31 h110) h31
  have h112 := T (T (T (T (T (T (T h64 h68) h39) h111) h109) h107) h105) h102
  have h113 := C h112 h100
  have h114 := C (T (T (T (T (T h113 h99) h93) (C (T (T (T h97 (C (C h12 (T h95 (C h92 h12))) h12)) (S h91)) (C h12 (C h90 h43))) h12)) (S h89)) (C h43 h88)) h43
  have h115 := h v27 z y
  have h116 := S h115
  have h117 := T h69 h35
  let v118 := M v1 y
  have h119 := h (M z (M v118 y)) x z
  have h120 := h v1 z y
  have h121 := h y x z
  have h122 := C (T (T (T (T (T h113 h99) h121) (C (C h12 (C h120 h100)) h12)) (S h119)) (C h100 (C h117 h31))) h100
  let v123 := M v1 z
  let v124 := M v123 z
  have h125 := h v124 y x
  have h126 := S h125
  have h127 := S h121
  have h128 := h v1 z v1
  have h129 := C (C h12 (C (S h128) h100)) h12
  have h130 := h (M z v74) x z
  have h131 := T (T (T (T h122 h116) h38) h85) h65
  have h132 := C (C h131 h43) h43
  have h133 := C h100 h132
  have h134 := h v124 z x
  have h135 := S h134
  have h136 := C (C h31 h104) h31
  have h137 := S h107
  have h138 := C (T (C h12 (C h99 h100)) (C h12 h110)) h12
  have h139 := T (T (T (T (T (T (T h101 h138) h137) h108) h136) h38) h85) h65
  have h140 := C h139 h100
  have h141 := C (T (T (T (T (T (C h100 (C (T h87 h86) h31)) h119) (C (C h12 (C (S h120) h100)) h12)) h127) h98) h140) h100
  have h142 := T (T (T (T (T (T h101 h138) h137) h108) h136) h115) h141
  have h143 := T (C (C h112 h12) h12) (C (C h142 h12) h12)
  have h144 := h (M z v66) x z
  have h145 := h v1 z x
  have h146 := h v123 z x
  have h147 := S h146
  have h148 := S h97
  have h149 := C h93 h12
  have h150 := h (M x v123) x x
  have h151 := h v1 z v3
  have h152 := C (T (T (T (C h12 (C (S h151) h100)) h150) (C (C h12 (T (C h127 h12) h149)) h12)) h148) h12
  let v153 := M (M v1 v3) v3
  have h154 := h (M z v153) x z
  have h155 := S h154
  have h156 := C (T (T (T h97 (C (C h12 (T h95 (C h121 h12))) h12)) (S h150)) (C h12 (C h151 h100))) h12
  have h157 := C (T (T (T (T (T (T (T h122 h116) h111) h109) h107) h105) h102) (C h100 (T (C (C (T (T h93 h156) h155) h12) h12) (C (C (T (T (T (T h154 h152) h94) h98) h140) h12) h12)))) h100
  have h158 := C (T (T (T (T (T (T (T h157 h147) h113) h99) h121) (C (C h12 (C h145 h100)) h12)) (S h144)) (C h100 h143)) h100
  have h159 := T (T (T (T (T (T h158 h135) h122) h116) h38) h85) h65
  have h160 := T (T (T (T h64 h68) h39) h115) h141
  have h161 := C (C h160 h159) h43
  have h162 := h v124 v1 z
  have h163 := T (T (T (T (T (T h64 h68) h39) h115) h141) h162) h161
  have h164 := C h100 h163
  let v165 := M z v1
  have h166 := h v165 v3 z
  have h167 := S h166
  have h168 := S h162
  have h169 := C (T (T (T (T (T (T (T (C h100 (T (C (C (T (T (T (T h113 h99) h93) h156) h155) h12) h12) (C (C (T (T h154 h152) h94) h12) h12))) h101) h138) h137) h108) h136) h115) h141) h100
  have h170 := T (T (T (T (T (T h122 h116) h111) h109) h107) h105) h102
  have h171 := T (C (C h170 h12) h12) (C (C h139 h12) h12)
  have h172 := C (T (T (T (T (T (T (T (C h100 h171) h144) (C (C h12 (C (S h145) h100)) h12)) h127) h98) h140) h146) h169) h100
  have h173 := T (T (T (T (T (T h64 h68) h39) h115) h141) h134) h172
  have h174 := C (C h131 h173) h43
  have h175 := T (T (T (T (T (T h174 h168) h122) h116) h38) h85) h65
  have h176 := C h100 h175
  have h177 := C (C h160 h43) h43
  have h178 := C h100 h177
  have h179 := S h130
  have h180 := C (C h12 (C h128 h100)) h12
  have h181 := C (T (T (T (T (T (T (T (T h157 h147) h113) h99) h121) h180) h179) h178) h176) h100
  have h182 := T h113 h99
  have h183 := C (C h182 h40) h40
  have h184 := C (C (T (T (T (T (T (T h164 h133) h130) h129) h127) h98) h140) h40) h40
  have h185 := C (T (T (T (T (T (T (T (T (C h100 h184) (C h100 h183)) h108) h136) h115) h141) h134) h172) h181) h100
  have h186 := h v165 z v2
  have h187 := C (C h6 (T (T (T (T (T (T (T (T (T h58 h55) h42) h121) h180) h179) h178) h176) h186) h185)) h6
  have h188 := h v60 v3 v1
  have h189 := C (T (T (T h122 h116) h37) h84) h40
  have h190 := h v124 v2 z
  have h191 := C (T (T (T (T h114 h79) h76) h73) h23) h173
  have h192 := C (T (T (T (T (T (C h43 h72) h89) (C (T (T (T (C h12 (C (S h90) h43)) h91) (C (C h12 (T (C (S h92) h12) h149)) h12)) h148) h12)) h94) h98) h140) h43
  have h193 := C (T h78 h192) h43
  have h194 := S h76
  have h195 := S h30
  have h196 := C h25 h6
  have h197 := C (T (T (T h24 (C (C h12 (T (C h23 h6) h196)) h12)) h195) (C h6 h88)) h6
  have h198 := T (T (T (T (T h10 h32) h17) h22) h197) h194
  have h199 := C h198 h43
  have h200 := C h36 h43
  have h201 := C (T (T (T h200 h199) h193) h191) h40
  have h202 := C (T h201 (S h190)) h40
  have h203 := C h33 h43
  have h204 := C h77 h43
  have h205 := C (T h114 h79) h43
  have h206 := C (T (T (T (T h22 h197) h194) h78) h192) h159
  have h207 := C (T (T (T h206 h205) h204) h203) h40
  have h208 := h v18 v3 v2
  have h209 := C (T h190 h207) h40
  have h210 := C (T (T (T h59 h34) h115) h141) h40
  have h211 := S h188
  have h212 := S h186
  have h213 := C (C (T (T (T (T (T (T h113 h99) h121) h180) h179) h178) h176) h40) h40
  have h214 := T h98 h140
  have h215 := C (C h214 h40) h40
  have h216 := C (T (T (T (T (T (T (T (T h164 h133) h130) h129) h127) h98) h140) h146) h169) h100
  have h217 := C (T (T (T (T (T (T (T (T h216 h158) h135) h122) h116) h111) h109) (C h100 h215)) (C h100 h213)) h100
  have h218 := C (C h6 (T (T (T (T (T (T (T (T (T h217 h212) h164) h133) h130) h129) h127) h41) h83) h82)) h6
  have h219 := C (C h6 (T (T (T (T (T (T (T h217 h212) h166) h218) h211) h61) h210) h209)) h6
  have h220 := T (T (T (T (T (T (T (T (T (T (T (C (T (C (T (T (T (T (T (T h166 h219) (S h208)) h200) h199) h193) h191) h40) h207) h40) h202) h189) h81) h188) h187) h167) h164) h133) h130) h129) h127
  have h221 := h (M y v66) x y
  have h222 := h v1 y x
  have h223 := h v75 x y
  have h224 := C (T (T (T (T (T (T h22 h197) h194) h223) (C (C h12 (T h71 (C h222 h31))) h12)) (S h221)) (C h31 h143)) h220
  have h225 := C h40 h213
  have h226 := C h40 h215
  have h227 := h (M v2 v48) x v2
  have h228 := S h227
  have h229 := h y v2 v2
  have h230 := h y v2 x
  have h231 := S h230
  have h232 := C h231 h40
  have h233 := C (C h12 (T h232 (C h229 h40))) h12
  let v234 := M v2 v44
  have h235 := h v234 x v2
  have h236 := h v234 v1 v0
  have h237 := S h236
  have h238 := S h235
  have h239 := C h230 h40
  have h240 := C (C h12 (T (C (S h229) h40) h239)) h12
  have h241 := C h40 h183
  have h242 := C h40 h184
  have h243 := C (C h6 (T (T (T (T (T (T (T h202 h189) h81) h188) h187) h167) h186) h185)) h6
  have h244 := T (T (T (T (T (T (T (T (T (T (T h121 h180) h179) h178) h176) h166) h218) h211) h61) h210) h209) (C (T h201 (C (T (T (T (T (T (T h206 h205) h204) h203) h208) h243) h167) h40)) h40)
  have h245 := C (T (T (T (T (T (T (C h31 h171) h221) (C (C h12 (T (C (S h222) h31) h80)) h12)) (S h223)) h76) h73) h23) h244
  have h246 := h v124 v0 z
  have h247 := S h246
  have h248 := C (C h9 h173) h9
  have h249 := C (C h9 h159) h9
  have h250 := h (M v1 (M (M v1 v0) v0)) x v1
  have h251 := h v1 v1 v0
  have h252 := h v1 v1 v3
  have h253 := C (S h252) h43
  have h254 := C h252 h43
  have h255 := h v1 v1 v1
  have h256 := h (M v1 v74) x v1
  have h257 := h y v2 v1
  have h258 := C (C h12 (T (C (S h257) h40) h239)) h12
  have h259 := h (M v2 v18) x v2
  have h260 := S h259
  have h261 := C (C h12 (T h232 (C h257 h40))) h12
  have h262 := h y v2 v3
  have h263 := C (C h12 (T (C (S h262) h40) h239)) h12
  have h264 := h (M v2 (M (M y v3) v3)) x v2
  have h265 := T (T (T h264 h263) h261) h260
  have h266 := S h264
  have h267 := C (C h12 (T h232 (C h262 h40))) h12
  have h268 := h y v2 z
  have h269 := C (C h12 (T (C (S h268) h40) h239)) h12
  have h270 := h (M v2 v123) x v2
  have h271 := T (T (T h270 h269) h267) h266
  have h272 := S h270
  have h273 := C (C h12 (T h232 (C h268 h40))) h12
  have h274 := h y v2 v0
  have h275 := C (C h12 (T (C (S h274) h40) h239)) h12
  have h276 := h (M v2 v96) x v2
  have h277 := T (T (T h276 h275) h273) h272
  have h278 := S h276
  have h279 := C (C h12 (T h232 (C h274 h40))) h12
  have h280 := h y v2 y
  have h281 := C (C h12 (T (C (S h280) h40) h239)) h12
  have h282 := h (M v2 (M (M y y) y)) x v2
  have h283 := T (T (T h282 h281) h279) h278
  have h284 := S h282
  have h285 := C (C h12 (T h232 (C h280 h40))) h12
  have h286 := T (T (T h227 h240) h285) h284
  have h287 := T (T h235 h233) h228
  have h288 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (C h287 h43) (C h286 h43)) (C h283 h43)) (C h277 h43)) (C h271 h43)) (C h265 h43)) (C (T (T (T (T (T (T (T (T (T (T (T (T h259 h258) h233) h228) h226) h225) h224) h126) h122) h116) h38) h85) h65) h163)) (C h43 h132)) h256) (C (C h12 (T (C (S h255) h43) h254)) h12)) (C (C h12 (T h253 (C h251 h43))) h12)) (S h250)) (C h43 (C (C h160 h9) h9))) (C h43 (C (T (C (T h246 h249) h9) (C (T (T (T (T (T (T (T (T h248 h247) h125) h245) h242) h241) h227) h240) h238) h9)) h9))) h43
  have h289 := C h214 (T (T (T (T (T (T (T (T (T (T (T (T (T h288 h237) h235) h233) h228) h226) h225) h224) h126) h122) h116) h38) h85) h65)
  have h290 := T (T h227 h240) h238
  have h291 := T (T (T h282 h281) h233) h228
  have h292 := T (T (T h276 h275) h285) h284
  have h293 := T (T (T h270 h269) h279) h278
  have h294 := T (T (T h264 h263) h273) h272
  have h295 := T (T (T h259 h258) h267) h266
  have h296 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (C h43 (C (T (C (T (T (T (T (T (T (T (T h235 h233) h228) h226) h225) h224) h126) h246) h249) h9) (C (T h248 h247) h9)) h9)) (C h43 (C (C h131 h9) h9))) h250) (C (C h12 (T (C (S h251) h43) h254)) h12)) (C (C h12 (T h253 (C h255 h43))) h12)) (S h256)) (C h43 h177)) (C (T (T (T (T (T (T (T (T (T (T (T (T h64 h68) h39) h115) h141) h125) h245) h242) h241) h227) h240) h261) h260) h175)) (C h295 h43)) (C h294 h43)) (C h293 h43)) (C h292 h43)) (C h291 h43)) (C h290 h43)) h43
  have h297 := h v234 z v1
  have h298 := S h297
  have h299 := T (T (T (T (T (T (T (T (T (T h174 h168) h125) h245) h242) h241) h227) h240) h238) h236) h296
  have h300 := C (T (T (T (T (T (T (T (T (T (T h259 h258) h233) h228) h226) h225) h224) h126) h134) h172) h181) h100
  have h301 := C h265 h100
  have h302 := C h271 h100
  have h303 := C h277 h100
  have h304 := C h283 h100
  have h305 := C h286 h100
  have h306 := C h287 h100
  have h307 := C (T (T (T (T (T (T (T (T (T (T h306 h305) h304) h303) h302) h301) h300) h217) h212) h164) (C h100 h299)) h100
  have h308 := T (T (T h307 h298) h236) h296
  have h309 := C h31 h308
  have h310 := T (T (T (T (T (T (T (T (T (T h288 h237) h235) h233) h228) h226) h225) h224) h126) h162) h161
  have h311 := C (T (T (T (T (T (T (T (T (T (T (C h100 h310) h176) h186) h185) (C (T (T (T (T (T (T (T (T (T (T h216 h158) h135) h125) h245) h242) h241) h227) h240) h261) h260) h100)) (C h295 h100)) (C h294 h100)) (C h293 h100)) (C h292 h100)) (C h291 h100)) (C h290 h100)) h100
  have h312 := T (T (T (T (T (T (T (T (T (T (T (T (T h64 h68) h39) h115) h141) h125) h245) h242) h241) h227) h240) h238) h297) h311
  have h313 := h v165 v1 v2
  have h314 := S h313
  have h315 := T (T (T (T (T (T (T (T (T (T (T h235 h233) h228) h226) h225) h224) h126) h122) h116) h38) h85) h65
  have h316 := C h315 h244
  have h317 := C h290 h31
  have h318 := C h291 h31
  have h319 := C h292 h31
  have h320 := C h293 h31
  have h321 := C h294 h31
  have h322 := C h295 h31
  have h323 := C (T (T (T (T (T (T (T h125 h245) h242) h241) h227) h240) h261) h260) h31
  have h324 := C h142 h31
  have h325 := C (T (T (T (T (T h34 h111) h109) h107) h105) h102) h31
  have h326 := C (T (T (T (T (T (T (T (T (T (T h69 h325) h324) h323) h322) h321) h320) h319) h318) h317) h316) h43
  have h327 := C (T (T (T (T (T (T h326 h314) h164) h133) h130) h129) h127) h312
  have h328 := C (T (T (T (T (T h101 h138) h137) h108) h136) h37) h31
  have h329 := C h170 h31
  have h330 := C (T (T (T (T (T (T (T h259 h258) h233) h228) h226) h225) h224) h126) h31
  have h331 := C h265 h31
  have h332 := C h271 h31
  have h333 := C h277 h31
  have h334 := C h283 h31
  have h335 := C h286 h31
  have h336 := C h287 h31
  have h337 := T (T (T (T (T (T (T (T (T (T (T h64 h68) h39) h115) h141) h125) h245) h242) h241) h227) h240) h238
  have h338 := C h337 h220
  have h339 := C (T (T (T (T (T (T (T (T (T (T h338 h336) h335) h334) h333) h332) h331) h330) h329) h328) h86) h43
  have h340 := T (T (T (T (T (T (T h327 h309) h289) h114) h79) h76) h73) h23
  have h341 := C (T (T (T (T (T (T (T (T (C h337 h340) h231) h121) h180) h179) h178) h176) h313) h339) h43
  have h342 := h v118 v1 v1
  have h343 := h v118 v0 v1
  have h344 := S h343
  have h345 := T (T (T (T (T (T (T (T (T (T (T (T (T h307 h298) h235) h233) h228) h226) h225) h224) h126) h122) h116) h38) h85) h65
  have h346 := C (T (T (T (T (T (T h121 h180) h179) h178) h176) h313) h339) h345
  have h347 := T (T (T h288 h237) h297) h311
  have h348 := C h31 h347
  have h349 := C h182 (T (T (T (T (T (T (T (T (T (T (T (T (T h64 h68) h39) h115) h141) h125) h245) h242) h241) h227) h240) h238) h236) h296)
  have h350 := T (T (T (T (T (T (T h22 h197) h194) h78) h192) h349) h348) h346
  have h351 := C (C h9 h350) h9
  let v352 := M v0 v2
  have h353 := h v352 v3 v0
  have h354 := h v0 v2 y
  have h355 := C (S h354) h40
  have h356 := C (C h6 (T (T h355 h353) (C (C h6 (T (T (C (T (T (T (T (T (T (T (T h351 h344) h342) h341) h327) h309) h289) h114) h79) h9) (C h77 h9)) h8)) h6))) h6
  have h357 := C h354 h40
  have h358 := S h353
  have h359 := C (C h9 h340) h9
  have h360 := h v118 v3 v1
  have h361 := S h360
  let v362 := M (M v0 y) y
  let v363 := M v2 v362
  have h364 := h v363 v3 v2
  have h365 := h v363 x v2
  have h366 := h v0 v2 v2
  have h367 := S h366
  let v368 := M v352 v2
  have h369 := h (M v2 v368) x v2
  have h370 := T (T (T (T (T h369 (C (C h12 (T (C h367 h40) h357)) h12)) (S h365)) h364) h356) h5
  have h371 := C h370 h350
  have h372 := C (T h366 h371) h6
  have h373 := h v0 v3 y
  have h374 := C (S h373) h6
  have h375 := S h342
  have h376 := C (T (T (T (T (T (T (T (T h326 h314) h164) h133) h130) h129) h127) h230) (C h315 h350)) h43
  have h377 := C (T (T (T (T (T (T (T (T h78 h192) h349) h348) h346) h376) h375) h343) h359) h9
  have h378 := C h198 h9
  have h379 := T (T (T (T (T h4 (C (C h6 (T (T (C (C h6 (T (T h7 h378) h377)) h6) h358) h357)) h6)) (S h364)) h365) (C (C h12 (T h355 (C h366 h40))) h12)) (S h369)
  have h380 := C h379 (T (T (T (T (T (T (T (T (T (T (T (T h374 h372) h361) h342) h341) h327) h309) h289) h114) h79) h76) h73) h23)
  have h381 := C (T h380 h371) h6
  let v382 := M v3 v362
  have h383 := h v382 v3 v3
  have h384 := h v382 x v3
  have h385 := S h384
  have h386 := C h373 h6
  have h387 := h v0 v3 v2
  have h388 := S h387
  have h389 := C (C h12 (T (C h388 h6) h386)) h12
  have h390 := h (M v3 v368) x v3
  have h391 := C h379 h340
  have h392 := h x z v2
  have h393 := S h392
  have h394 := C h393 h100
  let v395 := M z (M (M x v2) v2)
  have h396 := h v395 v2 z
  have h397 := h v395 v0 z
  have h398 := C h392 h100
  have h399 := C (T h391 h367) h6
  have h400 := C h370 (T (T (T (T (T (T (T (T (T (T (T (T h22 h197) h194) h78) h192) h349) h348) h346) h376) h375) h360) h399) h386)
  have h401 := S h390
  have h402 := C (C h12 (T h374 (C h387 h6))) h12
  have h403 := S h383
  have h404 := C (T h391 h400) h6
  have h405 := C h6 (T (T (T (C (T (T (T (C (T (T (T (T (T (T (T (T (T (T (T (T h78 h192) h349) h348) h346) h376) h375) h360) h404) h403) h384) h402) h401) h6) h388) h366) h400) h6) h381) h399) h386)
  have h406 := C h6 (C (C (T (T h22 h197) h194) h6) h6)
  have h407 := h (M v3 (M (M v2 v3) v3)) x v3
  have h408 := S h407
  have h409 := h v2 v3 v3
  have h410 := C (C h12 (T h26 (C h409 h6))) h12
  have h411 := h v2 v3 v2
  have h412 := C (C h12 (T (C (S h411) h6) h196)) h12
  have h413 := h (M v3 (M (M v2 v2) v2)) x v3
  have h414 := T (T (T (T (T (T (T h413 h412) h410) h408) h406) h405) h380) h367
  have h415 := S h413
  have h416 := C (C h12 (T h26 (C h411 h6))) h12
  have h417 := h v2 v3 x
  have h418 := C (C h12 (T (C (S h417) h6) h196)) h12
  have h419 := h (M v3 (M (M v2 x) x)) x v3
  have h420 := T (T (T h419 h418) h416) h415
  have h421 := S h419
  have h422 := C (C h12 (T h26 (C h417 h6))) h12
  have h423 := h v2 v3 v1
  have h424 := C (C h12 (T (C (S h423) h6) h196)) h12
  have h425 := h (M v3 v19) x v3
  have h426 := T (T (T h425 h424) h422) h421
  have h427 := S h425
  have h428 := C (C h12 (T h26 (C h423 h6))) h12
  have h429 := C (C h12 (T (C (S h409) h6) h196)) h12
  have h430 := T (T (T h407 h429) h428) h427
  have h431 := h v2 v3 z
  have h432 := C (C h12 (T (C (S h431) h6) h196)) h12
  have h433 := h (M v3 (M (M v2 z) z)) x v3
  have h434 := T (T (T h433 h432) h410) h408
  have h435 := S h433
  have h436 := C (C h12 (T h26 (C h431 h6))) h12
  have h437 := T (T (T (T (T (T (T (T (T (T (T (T (C (C (T (T h30 h436) h435) h9) h9) (C (C h434 h9) h9)) (C (C h430 h9) h9)) (C (C h426 h9) h9)) (C (C h420 h9) h9)) (C (C h414 h9) h9)) (C (C h9 h398) h9)) (S h397)) h396) (C (C h40 h394) h40)) (C h6 h350)) h391) h367
  have h438 := T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h22 h197) h194) h78) h192) h349) h348) h346) h376) h375) h360) h404) h403) h384) h402) h401
  have h439 := T (T (T h407 h429) h436) h435
  have h440 := T (T (T h425 h424) h410) h408
  have h441 := T (T (T h419 h418) h428) h427
  have h442 := T (T (T h413 h412) h422) h421
  have h443 := C h6 (C (C (T (T h76 h73) h23) h6) h6)
  have h444 := C h6 (T (T (T h374 h372) h404) (C (T (T (T h380 h367) h387) (C (T (T (T (T (T (T (T (T (T (T (T (T h390 h389) h385) h383) h381) h361) h342) h341) h327) h309) h289) h114) h79) h6)) h6))
  have h445 := T (T (T (T (T (T (T h366 h400) h444) h443) h407) h429) h416) h415
  have h446 := T (T (T (T (T (T (T (T (T (T (T (T h366 h371) (C h6 h340)) (C (C h40 h398) h40)) (S h396)) h397) (C (C h9 h394) h9)) (C (C h445 h9) h9)) (C (C h442 h9) h9)) (C (C h441 h9) h9)) (C (C h440 h9) h9)) (C (C h439 h9) h9)) (C (C (T (T h433 h432) h195) h9) h9)
  have h447 := h v1 v2 v3
  have h448 := C (S h447) h40
  let v449 := M v2 v153
  have h450 := h v449 v3 v2
  have h451 := h v449 x v2
  have h452 := C h447 h40
  have h453 := h v1 v2 v1
  have h454 := h (M v2 v74) x v2
  have h455 := h z v0 x
  have h456 := S h455
  have h457 := h (M v0 (M (M z x) x)) v0 v0
  have h458 := h (M z v0) x z
  have h459 := S h458
  have h460 := h v395 z z
  have h461 := C (C h12 (T h392 (C (T h460 (C (C h100 h394) h100)) h100))) h12
  let v462 := M (M x x) x
  have h463 := h v462 v3 z
  have h464 := C (C h12 (T (C (T (C (C h100 h398) h100) (S h460)) h100) h393)) h12
  have h465 := h v29 z v0
  have h466 := C (T (T (T (T h433 h432) h195) h465) (C (T (T (C h100 h437) h458) h464) h100)) h100
  have h467 := C h439 h100
  have h468 := C h440 h100
  have h469 := C h441 h100
  have h470 := C h442 h100
  have h471 := C h445 h100
  let v472 := M v0 z
  have h473 := h (M v3 v472) x v3
  have h474 := h x v3 z
  have h475 := h x v3 v1
  have h476 := C (S h475) h6
  have h477 := C h475 h6
  have h478 := h x v3 x
  have h479 := S h478
  have h480 := h (M v3 v462) x v3
  have h481 := C (T (T (T (T h480 (C (C h12 (T (C h479 h6) h477)) h12)) (C (C h12 (T h476 (C h474 h6))) h12)) (S h473)) (C h6 (T (T (T (T (T h471 h470) h469) h468) h467) h466))) h6
  let v482 := M v0 x
  have h483 := C h414 h100
  have h484 := C h420 h100
  have h485 := C h426 h100
  have h486 := C h430 h100
  have h487 := C h434 h100
  have h488 := S h465
  have h489 := C (T (T h461 h459) (C h100 h446)) h100
  have h490 := C (T (T (T (T h489 h488) h30) h436) h435) h100
  T (T (T (T h478 h481) (C (C h6 (T (T (T (T (T (T (T (T (T h490 h487) h486) h485) h484) h483) (h v472 v3 v0)) (C (C h6 (T (T (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (C (T (T (T (T (T (T h471 h470) h469) h468) h467) h466) (C (T (T (T (T (T (T (T (T h489 h488) h30) h410) h408) h406) h405) h380) h367) (T h455 (C (T h457 (C (T (T (T (T (T (C (T (T (T (T (T (T (T h366 h400) h444) h443) h407) h429) h436) h435) (T (T (T (T (T (C h456 h9) h458) h464) h463) (C (T (T (T (T (C h6 (T (T (T (T (T h490 h487) h486) h485) h484) h483)) h473) (C (C h12 (T (C (S h474) h6) h477)) h12)) (C (C h12 (T h476 (C h478 h6))) h12)) (S h480)) h6)) h479)) (C h434 h12)) (C h430 h12)) (C h426 h12)) (C h420 h12)) (C h414 h12)) h9)) h9)))) h9) (S (h v482 v0 v0))) (h v482 v1 v0)) (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (C h337 (T (C (T (C (T (T (T (T (T (C h445 h12) (C h442 h12)) (C h441 h12)) (C h440 h12)) (C h439 h12)) (C (T (T (T (T (T (T (T h433 h432) h410) h408) h406) h405) h380) h367) (T (T (T (T (T h478 h481) (S h463)) h461) h459) (C h455 h9)))) h9) (S h457)) h9) h456)) h306) h305) h304) h303) h302) h301) h300) h217) h212) h166) h219) (C (C h6 (T (T (T h202 h189) h81) h452)) h6)) (S h450)) h451) (C (C h12 (T h448 (C h453 h40))) h12)) (S h454)) (C h40 h177)) (C h40 h299)) (C h40 h347)) (C h438 h345)) h43)) (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h390 h389) h385) h383) h381) h361) h342) h341) h327) h309) h289) h114) h79) h76) h73) h23) h312) (C h40 h308)) (C h40 h310)) (C h40 h132)) h454) (C (C h12 (T (C (S h453) h40) h452)) h12)) (S h451)) h450) (C (C h6 (T (T (T h448 h61) h210) h209)) h6)) h243) h167) h164) h133) h130) h129) h127) h92) (C (C h12 (C (h v2 v1 v0) h43)) h12)) (S (h (M v1 v13) x v1))) (C h43 (C (T h7 h378) h9))) (C h43 (C (T (T h377 (C (T h351 h344) h9)) (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T h69 h325) h324) h323) h322) h321) h320) h319) h318) h317) h316) (C h43 h184)) (C h43 h183)) h51) h56) h9)) h9))) (C h43 (C (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T h54 h52) (C h43 h215)) (C h43 h213)) h338) h336) h335) h334) h333) h332) h331) h330) h329) h328) h86) h9) h9))) (C h43 (C (C h117 h9) h9))) h43)) (S (h v28 v1 v0))) h87) h86) h342) h341) h327) h309) h289) h114) h79) h76) h73) h23) h446) (C h438 h437)) (C (T (T (T (T (T (T (T h390 h389) h385) h383) h381) h361) h343) h359) h9))) h6)) h358) h357)) h6)) h356) h5

