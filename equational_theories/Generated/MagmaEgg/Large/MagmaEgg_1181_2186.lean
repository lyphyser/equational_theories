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
theorem Equation1181_implies_Equation2186 (G: Type _) [Magma G] (h: Equation1181 G) : Equation2186 G := fun x y z =>
  let v0 := M z x
  let v1 := M y z
  let v2 := M v1 y
  let v3 := M v2 v0
  have h4 := h v3 v3 v3
  have h5 := S h4
  have h6 := R v3
  have h7 := R v0
  have h8 := h y x v1
  have h9 := S h8
  have h10 := R x
  have h11 := h v2 v1 x
  have h12 := R v1
  have h13 := C h10 (C (C h12 (S h11)) h10)
  let v14 := M x (M x v2)
  let v15 := M v14 v1
  have h16 := h v15 x v1
  have h17 := h v15 x y
  have h18 := S h17
  have h19 := S h16
  have h20 := C h10 (C (C h12 h11) h10)
  have h21 := T (T h8 h20) h19
  have h22 := R y
  have h23 := C h22 (C h22 h21)
  have h24 := h y v1 v2
  have h25 := S h24
  let v26 := M v2 y
  let v27 := M (M v2 v26) v1
  have h28 := h v27 v1 v1
  have h29 := S h28
  have h30 := C h12 h24
  have h31 := C h30 h12
  have h32 := T (C h12 (T (C h12 h31) h29)) h25
  have h33 := C h22 (C h32 h22)
  let v34 := M v2 v1
  have h35 := h v34 y v1
  have h36 := h v34 z v1
  have h37 := S h36
  have h38 := R z
  have h39 := C h12 h25
  have h40 := C h39 h12
  have h41 := T h24 (C h12 (T h28 (C h12 h40)))
  have h42 := C h38 (C h41 h38)
  have h43 := h v1 z v3
  have h44 := S h43
  let v45 := M v3 (M v3 v1)
  have h46 := h (M v45 z) x z
  have h47 := S h46
  have h48 := C h38 (C h32 h38)
  have h49 := h v1 v2 v3
  have h50 := R v2
  have h51 := C h50 (S h49)
  have h52 := C h10 (C (T (T (T h51 h36) h48) (C h38 h43)) h10)
  let v53 := M v45 v2
  have h54 := h v53 x v2
  have h55 := T (T h54 h52) h47
  have h56 := C h38 h55
  have h57 := C h38 (T h56 h44)
  have h58 := C h10 (C (T (T (T (T (T h57 h42) h37) h35) h33) h23) h10)
  have h59 := h v53 x z
  have h60 := S h54
  have h61 := C h50 h49
  have h62 := h v34 v2 v1
  have h63 := h z y v0
  have h64 := S h63
  have h65 := C h22 h64
  have h66 := C h22 (C h65 h22)
  let v67 := M v0 z
  let v68 := M (M v0 v67) y
  have h69 := h v68 y y
  have h70 := h v68 v2 y
  have h71 := C h22 h63
  have h72 := C h10 (C (T (T (T (C h50 (T (C h50 (C h71 h50)) (S h70))) (C h50 (T (T h69 h66) (C h41 h50)))) (S h62)) h61) h10)
  let v73 := M v1 v2
  have h74 := h v73 x v2
  have h75 := h v2 y x
  have h76 := S h75
  have h77 := h (M v14 y) x y
  have h78 := h v2 y v2
  have h79 := C h22 (S h78)
  let v80 := M (M v2 (M v2 v2)) y
  have h81 := h v80 x y
  have h82 := h v80 v3 y
  have h83 := C h22 h78
  have h84 := h v68 v1 y
  have h85 := S h59
  have h86 := C h10 (C (T (T (T (C h38 h44) h42) h37) h61) h10)
  have h87 := T (T h46 h86) h60
  have h88 := C h38 h87
  have h89 := C h38 (T h43 h88)
  have h90 := S h35
  have h91 := C h22 (C h41 h22)
  have h92 := T (T h16 h13) h9
  have h93 := C h22 (C h22 h92)
  have h94 := C h10 (C (T (T (T (T (T h93 h91) h90) h36) h48) h89) h10)
  have h95 := T (T (T (T (T h17 h94) h85) h54) h52) h47
  have h96 := C h38 h95
  have h97 := C h38 h21
  let v98 := M z y
  have h99 := h v98 v2 v3
  have h100 := S h99
  have h101 := C h38 h92
  have h102 := T (T (T (T (T h46 h86) h60) h59) h58) h18
  have h103 := C h38 h102
  have h104 := C h50 (T (T (T (T (T (T h8 h20) h19) h17) h94) h85) (C (C h6 (C h6 (T (T h43 h103) h101))) h50))
  have h105 := h v26 v3 v1
  have h106 := C h50 (T (T (T (T (T (T (C (C h6 (C h6 (T (T h97 h96) h44))) h50) h59) h58) h18) h16) h13) h9)
  have h107 := h v53 v1 x
  have h108 := h (M (M x (M x y)) v1) x v1
  have h109 := h y v1 x
  have h110 := C h39 h10
  have h111 := h v27 x v1
  have h112 := C h38 (T h96 h88)
  have h113 := C h38 h97
  have h114 := C h12 (T (T (T (T (T h113 h112) h57) h42) h37) h31)
  have h115 := T (T (T (T (T (T (T (C h12 (T (T (T (T (T h114 h29) h111) (C h10 (T h110 (C (C h12 h109) h10)))) (S h108)) (C (T (C h10 (C h10 (T (T (T (T (T (T (T (T h8 h20) h19) h17) h94) h85) h54) h52) h47))) (C h10 (C h10 h87))) h12))) (S h107)) h59) h58) h18) h16) h13) h9
  have h116 := C h115 (T (T (T (T (T (T (T (T (T (T h43 h103) h101) h99) h106) h105) (C h6 (C (T (T (T (T (T (C h12 (C h12 (T (T (T (T h104 h100) h97) h96) h44))) (C h12 (C h71 h12))) (S h84)) h69) h66) h83) h6))) (S h82)) h81) (C h10 (C (T h79 (C h22 h75)) h10))) (S h77))
  have h117 := C h12 (T h116 h76)
  have h118 := C h38 h101
  have h119 := C h38 (T h56 h103)
  have h120 := C h12 (T (T (T (T (T h40 h36) h48) h89) h119) h118)
  have h121 := S h111
  have h122 := C h30 h10
  have h123 := T (T (T (T (T (T (T h8 h20) h19) h17) h94) h85) h107) (C h12 (T (T (T (T (T (C (T (C h10 (C h10 h55)) (C h10 (C h10 (T (T (T (T (T (T (T (T h46 h86) h60) h59) h58) h18) h16) h13) h9)))) h12) h108) (C h10 (T (C (C h12 (S h109)) h10) h122))) h121) h28) h120))
  have h124 := C h123 h12
  let v125 := M y v1
  have h126 := h v125 x v1
  have h127 := S h126
  have h128 := h v34 v1 v1
  have h129 := h v27 v0 v1
  have h130 := S h129
  have h131 := C h7 (C h30 h7)
  have h132 := h v3 v0 v0
  have h133 := C h7 (S h132)
  have h134 := C h10 (C (T (T (T (T h133 h131) h130) h28) (C h12 (T (T h40 h128) (C h12 (C h32 h12))))) h10)
  have h135 := C h7 h132
  have h136 := h v3 v0 y
  have h137 := C h10 (C (T (C h7 (S h136)) h135) h10)
  have h138 := h (M (M y (M y v3)) v0) x v0
  have h139 := C h12 (T (T (T (T h138 h137) h134) h127) h124)
  have h140 := C h12 (T (T (T (T (T (T (T (T (T (T h139 h117) h74) h72) h60) h59) h58) h18) h16) h13) h9)
  have h141 := S h138
  have h142 := C h10 (C (T h133 (C h7 h136)) h10)
  have h143 := C h7 (C h39 h7)
  have h144 := C h10 (C (T (T (T (T (C h12 (T (T (C h12 (C h41 h12)) (S h128)) h31)) h29) h129) h143) h135) h10)
  have h145 := C h115 h12
  have h146 := C h12 (T (T (T (T h145 h126) h144) h142) h141)
  let v147 := M z v98
  have h148 := h v147 v1 v1
  have h149 := C h12 (T h148 h146)
  have h150 := h v27 v2 v1
  have h151 := S h150
  have h152 := C h50 (C h30 h50)
  let v153 := M (M v0 (M v0 v3)) v0
  have h154 := h v153 x v0
  have h155 := h v153 v3 v1
  have h156 := S h155
  have h157 := S h154
  have h158 := C h12 (C h12 (T (T h138 h137) h157))
  have h159 := S h69
  have h160 := C h22 (C h71 h22)
  have h161 := C h123 (T (T (T (T (T (T (T (T (T (T h77 (C h10 (C (T (C h22 h76) h83) h10))) (S h81)) h82) (C h6 (C (T (T (T (T (T h79 h160) h159) h84) (C h12 (C h65 h12))) (C h12 (C h12 (T (T (T (T h43 h103) h101) h99) h106)))) h6))) (S h105)) h104) h100) h97) h96) h44)
  have h162 := C h12 (T h75 h161)
  have h163 := S h74
  have h164 := C h10 (C (T (T (T h51 h62) (C h50 (T (T (C h32 h50) h160) h159))) (C h50 (T h70 (C h50 (C h65 h50))))) h10)
  have h165 := C h12 (T (T (T (T (T (T (T (T (T (T h8 h20) h19) h17) h94) h85) h54) h164) h163) h162) h146)
  have h166 := C (T h165 h158) h6
  have h167 := h (M v2 v3) x v3
  have h168 := S h167
  have h169 := h v27 v3 v1
  have h170 := h x z v2
  have h171 := S h170
  have h172 := C h38 h171
  let v173 := M (M v2 (M v2 x)) z
  have h174 := h v173 v3 z
  have h175 := h v173 v0 z
  have h176 := S h175
  have h177 := C h38 h170
  have h178 := C h7 (C h177 h7)
  have h179 := C h10 (C (T (T (T (T h178 h176) h174) (C h6 (T (T (C h172 h6) h131) h130))) (C h6 (T h169 (C h6 (C h39 h6))))) h10)
  have h180 := h v0 x v0
  have h181 := C h6 (T (T (T h180 h179) h168) h166)
  have h182 := T (T (T (T (T (T (T h181 h156) h154) h134) h127) h124) h116) h76
  have h183 := C h50 (C h50 h182)
  have h184 := T (T (T (T (T (T h183 h152) h151) h28) h120) h149) h140
  have h185 := C h184 h7
  have h186 := S h180
  have h187 := C h7 (C h172 h7)
  have h188 := C h10 (C (T (T (T (T (C h6 (T (C h6 (C h30 h6)) (S h169))) (C h6 (T (T h129 h143) (C h177 h6)))) (S h174)) h175) h187) h10)
  have h189 := C h12 (C h12 (T (T h154 h142) h141))
  have h190 := C (T h189 h140) h6
  have h191 := C h6 (T (T (T h190 h167) h188) h186)
  have h192 := T (T (T (T (T (T (T h75 h161) h145) h126) h144) h157) h155) h191
  have h193 := C h50 (C h50 h192)
  have h194 := C h50 (C h39 h50)
  have h195 := S h148
  have h196 := C h12 (T h139 h195)
  let v197 := M v3 v0
  have h198 := h v197 v1 v2
  have h199 := S h198
  have h200 := T (T (T (T (T (T h165 h196) h114) h29) h150) h194) h193
  have h201 := h v53 v1 v2
  have h202 := C h22 (C h22 h102)
  have h203 := C h22 (C h22 h55)
  have h204 := C h22 (C h22 h87)
  have h205 := C h22 (C h22 h95)
  have h206 := h (M v147 v1) x v1
  have h207 := h y v1 z
  have h208 := C h12 (T (T (T (T (T (T (T (T (T (T (T (T (C h12 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h181 h156) h154) h134) h127) h124) h116) h76) h165) h196) h114) h29) h111) (C h10 (T h110 (C (C h12 h207) h10)))) (S h206)) (C (T (T (T (T (T (T (T (T (T h113 h112) h57) h42) h37) h35) h33) h23) h205) h204) h12)) (C (T (T (T (T (T (T (T h203 h202) h93) h91) h90) h36) h48) h89) h12)) (C (T (T (T h57 h42) h37) h61) h12))) (S h201)) h54) h164) h163) h162) h195) h113) h112) h57) h42) h37) (C h200 h12))
  have h209 := T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h208 h199) h181) h156) h154) h134) h127) h124) h116) h76) h165) h196) h114) h29) h150) h194) h193
  have h210 := C h209 h7
  have h211 := h v0 v3 v0
  have h212 := S h211
  have h213 := h v173 x z
  have h214 := S h213
  have h215 := h v0 v2 x
  have h216 := S h215
  let v217 := M x v0
  let v218 := M (M x v217) v2
  have h219 := h v218 v2 v2
  have h220 := C h50 h215
  have h221 := C h10 (T (C (T (C h50 (T (C h50 (C h220 h50)) (S h219))) h216) h10) (C h177 h10))
  have h222 := h (M v3 v2) x v2
  have h223 := h v197 v3 y
  have h224 := S h223
  have h225 := C h22 (T (T (T h69 h66) (C h123 h50)) (C h115 h192))
  have h226 := C (T h63 h225) h6
  have h227 := C h6 h226
  have h228 := C h6 (T (T (T (T (T (T (T (T (T h227 h224) h181) h156) h154) h134) h127) h124) h116) h76)
  have h229 := C h6 (C (T (T (T (T (T h228 h222) h221) h214) h175) h187) h6)
  let v230 := M z v3
  have h231 := h v230 v3 v3
  have h232 := T (T h231 h229) h212
  have h233 := C h12 (T (T (T (T (T (T (T (T (T (T (T (T (C h184 h12) h36) h48) h89) h119) h118) h148) h117) h74) h72) h60) h201) (C h12 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (C (T (T (T h51 h36) h48) h89) h12) (C (T (T (T (T (T (T (T h57 h42) h37) h35) h33) h23) h205) h204) h12)) (C (T (T (T (T (T (T (T (T (T h203 h202) h93) h91) h90) h36) h48) h89) h119) h118) h12)) h206) (C h10 (T (C (C h12 (S h207)) h10) h122))) h121) h28) h120) h149) h140) h75) h161) h145) h126) h144) h157) h155) h191)))
  have h234 := T (T (T (T (T (T (T (T (T h75 h161) h145) h126) h144) h157) h155) h191) h198) h233
  have h235 := C h234 h232
  have h236 := h v230 v2 v0
  have h237 := S h236
  have h238 := C h22 (T (T (T (C h123 h182) (C h115 h50)) h160) h159)
  have h239 := C (T h238 h64) h6
  have h240 := h z v0 y
  have h241 := S h240
  let v242 := M v125 v0
  have h243 := h v242 v0 v0
  have h244 := S h243
  have h245 := h v67 x z
  have h246 := S h245
  have h247 := h v173 z z
  have h248 := C h10 (C (T h170 (C h38 (T h247 (C h38 (C h172 h38))))) h10)
  let v249 := M x (M x x)
  have h250 := h v249 v3 z
  have h251 := C h10 (C (T (C h38 (T (C h38 (C h177 h38)) (S h247))) h171) h10)
  have h252 := h v230 v3 v2
  have h253 := S h231
  have h254 := C h6 h239
  have h255 := C h6 (T (T (T (T (T (T (T (T (T h75 h161) h145) h126) h144) h157) h155) h191) h223) h254)
  have h256 := S h222
  have h257 := C h50 h216
  have h258 := C h10 (T (C h172 h10) (C (T h215 (C h50 (T h219 (C h50 (C h257 h50))))) h10))
  have h259 := C h6 (C (T (T (T (T (T h178 h176) h213) h258) h256) h255) h6)
  have h260 := T (T h211 h259) h253
  have h261 := T (T (T (T (T (T (T (T (T h208 h199) h181) h156) h154) h134) h127) h124) h116) h76
  have h262 := C h261 h260
  have h263 := T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h183 h152) h151) h28) h120) h149) h140) h75) h161) h145) h126) h144) h157) h155) h191) h198) h233
  have h264 := C h263 h7
  have h265 := C h200 h7
  have h266 := C h261 (T (T h265 h264) h262)
  have h267 := C h263 h6
  have h268 := C (T (T (T (T (T (T h189 h196) h114) h29) h150) h194) h193) h6
  have h269 := h v197 v0 v1
  have h270 := T (T (T (T (T (T (T (T (T (T (T (C h7 (C h7 h232)) h178) h176) h213) h258) h256) h255) (C h6 (T (T (T h227 h224) h269) (C (T (T (T (T (T (T h180 h179) h168) h166) h268) h267) h266) (T h210 h185))))) (S h252)) h231) h229) h212
  have h271 := h v230 z v0
  have h272 := h (M (M z v0) v3) x v3
  have h273 := h x v3 z
  have h274 := h x v3 v1
  have h275 := C h6 (S h274)
  have h276 := C h6 h274
  have h277 := h x v3 x
  have h278 := S h277
  have h279 := h (M v249 v3) x v3
  have h280 := C h6 (T (T (T (T h279 (C h10 (C (T (C h6 h278) h276) h10))) (C h10 (C (T h275 (C h6 h273)) h10))) (S h272)) (C (C h38 (T (T (T (T h211 h259) h253) h271) (C h38 (T (T (C h270 h38) h245) h251)))) h6))
  have h281 := C (T (T (T (T (T h277 h280) (S h250)) h248) h246) (C h7 h240)) h7
  have h282 := C h7 (T (C h7 h281) h244)
  have h283 := h v217 v3 v0
  have h284 := S h271
  have h285 := C (T (T (T (T (T (T h183 h152) h151) h28) h120) h149) h158) h6
  have h286 := C h209 h6
  have h287 := C h234 (T (T h235 h210) h185)
  have h288 := T (T (T (T (T (T (T (T (T (T (T h211 h259) h253) h252) (C h6 (T (T (T (C (T (T (T (T (T (T h287 h286) h285) h190) h167) h188) h186) (T h265 h264)) (S h269)) h223) h254))) h228) h222) h221) h214) h175) h187) (C h7 (C h7 h260))
  have h289 := C h38 (T (T h248 h246) (C h288 h38))
  have h290 := C (T (T (T (T (T (C h7 h241) h245) h251) h250) (C h6 (T (T (T (T (C (C h38 (T (T (T (T h289 h284) h231) h229) h212)) h6) h272) (C h10 (C (T (C h6 (S h273)) h276) h10))) (C h10 (C (T h275 (C h6 h277)) h10))) (S h279)))) h278) h7
  have h291 := C h288 (T (T (T (T (T (T (T (T (T (T (T (T h290 h283) (C h6 (T (C (T (T (T h282 h241) h63) h225) h6) h239))) h227) h224) h181) h156) h154) h134) h127) h124) h116) h76)
  have h292 := C h50 (T h243 h291)
  have h293 := C h50 (T h292 h237)
  have h294 := C h6 (C (T (T (T h293 h235) h210) h185) h6)
  have h295 := h v242 v3 v2
  have h296 := C (T (T (T h238 h64) h240) (C h7 (T h243 (C h7 h290)))) h6
  have h297 := C h270 (T (T (T (T (T (T (T (T (T (T (T (T h75 h161) h145) h126) h144) h157) h155) h191) h223) h254) (C h6 (T h226 h296))) (S h283)) h281)
  have h298 := C h288 h50
  have h299 := h v2 v0 x
  have h300 := C h7 (S h299)
  have h301 := C h6 (C (T (T (T (T (T h300 h298) h297) h244) h295) h294) h6)
  let v302 := M v14 v0
  have h303 := h v302 v3 v0
  have h304 := h v302 x v0
  have h305 := S h304
  have h306 := C h7 h299
  have h307 := h v2 v0 v1
  have h308 := C h10 (C (T (C h7 (S h307)) h306) h10)
  let v309 := M (M v1 v73) v0
  have h310 := h v309 x v0
  have h311 := h v309 x v2
  have h312 := S h310
  have h313 := C h10 (C (T h300 (C h7 h307)) h10)
  have h314 := S h303
  have h315 := C h270 h50
  have h316 := S h295
  have h317 := C h50 (T h297 h244)
  have h318 := C h50 (T h236 h317)
  have h319 := C h6 (C (T (T (T h265 h264) h262) h318) h6)
  have h320 := C h6 (C (T (T (T (T (T h319 h316) h243) h291) h315) h306) h6)
  have h321 := h v218 x v2
  have h322 := h v218 v3 v2
  T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h277 h280) (C h6 (C (C h38 (T (T (T (T h289 h284) h226) h296) (C (T h282 h241) (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h4 h320) h314) h304) h313) h312) h311) (C h10 (T (C (T (T (T (T (C h50 (T (T (T (T (T (T (T (T (T (T (T (T (C h50 (T (T (T (T (T (T (T (T h310 h308) h305) h303) h301) h5) h265) h264) h262)) h287) h286) h285) h190) h167) h188) h186) h211) h259) h253) h236) h317)) h293) h235) h210) h185) h10) (C h220 h10)))) (S h321)) h322) (C h6 (C h257 h6))) h319) h316) h243) h291) h315)))) h6))) (S (h (M v0 v2) v3 z))) h298) h297) h244) h295) h294) (C h6 (C h220 h6))) (S h322)) h321) (C h10 (T (C h257 h10) (C (T (T (T (T h265 h264) h262) h318) (C h50 (T (T (T (T (T (T (T (T (T (T (T (T h292 h237) h231) h229) h212) h180) h179) h168) h166) h268) h267) h266) (C h50 (T (T (T (T (T (T (T (T h235 h210) h185) h4) h320) h314) h304) h313) h312))))) h10)))) (S h311)) h310) h308) h305) h303) h301) h5

