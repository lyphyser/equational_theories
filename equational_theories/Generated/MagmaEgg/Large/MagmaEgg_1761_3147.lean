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
theorem Equation1761_implies_Equation3147 (G: Type _) [Magma G] (h: Equation1761 G) : Equation3147 G := fun x y z =>
  let v0 := M y y
  let v1 := M v0 x
  let v2 := M v1 z
  let v3 := M v2 z
  have h4 := h v3 v3 z
  have h5 := S h4
  have h6 := h z z v3
  have h7 := S h6
  have h8 := h v1 z z
  have h9 := h v3 v1 z
  have h10 := R (M z v3)
  let v11 := M v3 v1
  have h12 := R v11
  have h13 := h z v3 v1
  have h14 := T h13 (C h12 (T (C h10 h8) h7))
  have h15 := h v2 z v1
  have h16 := S h8
  have h17 := T (C h12 (T h6 (C h10 h16))) (S h13)
  have h18 := C h17 (T (C (S h15) h14) (S h9))
  let v19 := M z v1
  have h20 := h v19 v11 z
  have h21 := T h20 h18
  have h22 := C h21 h8
  let v23 := M v19 v1
  have h24 := h v23 z v3
  have h25 := S h24
  have h26 := R v3
  have h27 := R z
  have h28 := S h20
  have h29 := C h14 (T h9 (C h15 h17))
  have h30 := T h29 h28
  have h31 := C h30 h16
  have h32 := T h6 h31
  have h33 := C h32 h27
  have h34 := R v1
  have h35 := T h22 h7
  have h36 := C h35 h34
  have h37 := C (T (T h36 h20) h18) (T h8 (C h33 h26))
  have h38 := h v1 v1 v3
  have h39 := S h38
  let v40 := M v1 v1
  have h41 := h v40 z v3
  have h42 := S h41
  have h43 := R v40
  have h44 := h v23 v1 v1
  have h45 := C (T h44 (C h43 (T (T (T h37 h25) h22) h7))) h26
  have h46 := C h32 h26
  have h47 := C h21 (T (T (T (T (C h17 h34) h20) h18) h46) h45)
  have h48 := h v11 z v1
  let v49 := M v1 v3
  have h50 := R v49
  have h51 := C h50 (C (T (T h48 h47) h42) h26)
  have h52 := h v3 v1 v3
  have h53 := T (T h52 h51) h39
  have h54 := C h32 h34
  have h55 := C h35 h26
  have h56 := T (T (T h55 h29) h28) h54
  have h57 := C h56 h53
  have h58 := h v23 v1 v3
  have h59 := S h58
  have h60 := S h52
  have h61 := S h48
  have h62 := C h35 h27
  have h63 := C (T (T h29 h28) h54) (T (C h62 h26) h16)
  have h64 := C (T (C h43 (T (T (T h6 h31) h24) h63)) (S h44)) h26
  have h65 := C h30 (T (T (T (T h64 h55) h29) h28) (C h14 h34))
  have h66 := C h50 (C (T (T h41 h65) h61) h26)
  have h67 := T (T h38 h66) h60
  have h68 := T (T (T h36 h20) h18) h46
  have h69 := C h68 h67
  have h70 := C h50 (T (T (T (T (T h6 h31) h24) h63) h69) (C h56 h26))
  have h71 := C (T h70 h59) h53
  let v72 := M v3 v3
  have h73 := R v72
  have h74 := C h73 (T (T (T (T (T (C (T (T (T (T h71 h36) h20) h18) h46) h26) h57) h37) h25) h22) h7)
  have h75 := h (M v49 z) v3 v3
  have h76 := C h50 (T (T (T (T (T (C h68 h26) h57) h37) h25) h22) h7)
  let v77 := M v3 z
  have h78 := R v77
  have h79 := C h78 (T (T (T (T (T h6 h31) h58) h76) h75) h74)
  have h80 := h (M v77 z) v3 v2
  have h81 := S h80
  have h82 := R v2
  have h83 := S h75
  have h84 := C (T h58 h76) h67
  have h85 := C h73 (T (T (T (T (T h6 h31) h24) h63) h69) (C (T (T (T (T h55 h29) h28) h54) h84) h26))
  have h86 := C h78 (T (T (T (T (T h85 h83) h70) h59) h22) h7)
  have h87 := C (T (T (T (T h38 h66) h60) h4) h86) h67
  have h88 := C h10 (T (T (T (T (T h71 h36) h20) h18) h46) h45)
  have h89 := C h10 (C (T h85 h83) h26)
  have h90 := h v72 z v3
  have h91 := h v72 z z
  have h92 := S h91
  have h93 := T (T (T h58 h76) h75) h74
  have h94 := C h93 h27
  let v95 := M z z
  have h96 := h v95 v3 z
  have h97 := S h96
  have h98 := h z v2 v0
  have h99 := h v0 x z
  have h100 := S h99
  have h101 := R (M z v2)
  have h102 := h x z v2
  have h103 := R (M v2 v0)
  have h104 := h v2 v0 x
  have h105 := C h78 (T h104 (C h8 (T (C h103 (T h102 (C h101 h100))) (S h98))))
  have h106 := h v77 z v3
  have h107 := S h106
  have h108 := T (T (T (T h90 h89) h88) h42) h87
  have h109 := C h10 h108
  have h110 := h v2 z v3
  have h111 := h v2 z z
  have h112 := S h111
  have h113 := T (T h110 h109) h107
  have h114 := C h113 h82
  have h115 := T (T h114 h105) h97
  have h116 := C h115 h113
  have h117 := T (T (T (T h116 h112) h110) h109) h107
  have h118 := C h117 h82
  have h119 := C h115 (T (T (T (T h118 h105) h97) h33) h94)
  let v120 := M v2 v2
  have h121 := h v120 v2 v2
  have h122 := S h110
  have h123 := S h90
  have h124 := C h10 (C (T h75 h74) h26)
  have h125 := C h10 (T (T (T (T (T h64 h55) h29) h28) h54) h84)
  have h126 := C (T (T (T (T h79 h5) h52) h51) h39) h53
  have h127 := T (T (T (T h126 h41) h125) h124) h123
  have h128 := C h10 h127
  have h129 := T (T h106 h128) h122
  have h130 := C h129 h82
  have h131 := S h102
  have h132 := C h78 (T (C h16 (T h98 (C h103 (T (C h101 h99) h131)))) (S h104))
  have h133 := T (T h96 h132) h130
  have h134 := C h133 h129
  have h135 := T (T (T (T h106 h128) h122) h111) h134
  have h136 := C h135 h82
  have h137 := C (T (T h96 h132) h136) h129
  let v138 := M v3 v2
  have h139 := R v138
  have h140 := C h139 (T (T h111 h137) (C (T (T (T (T (T (T (T (T (T h118 h130) h121) h119) h92) h90) h89) h88) h42) h87) h82))
  have h141 := h (M v138 v2) v2 v2
  have h142 := S h141
  have h143 := C (T (T h118 h105) h97) h113
  have h144 := S h121
  have h145 := T (T (T h85 h83) h70) h59
  have h146 := C h145 h27
  have h147 := C h133 (T (T (T (T h146 h62) h96) h132) h136)
  have h148 := C (T h140 h81) h26
  have h149 := T (T (T (T (T (T (T (T (T (T h148 h126) h41) h125) h124) h123) h91) h147) h144) h114) h136
  have h150 := h v138 v0 v3
  let v151 := M v138 v0
  have h152 := h v151 v1 v2
  have h153 := R v151
  have h154 := h (M x z) v2 x
  have h155 := h x v1 y
  have h156 := h y y x
  have h157 := S h156
  have h158 := R (M x v1)
  have h159 := h y x v1
  let v160 := M v1 y
  have h161 := R v160
  have h162 := h v1 y y
  have h163 := R (M v2 x)
  have h164 := R x
  have h165 := C (T (T (C (C h129 h164) h53) (C h163 (T h162 (C h99 (T (C h161 (T h159 (C h158 h157))) (S h155)))))) (S h154)) h82
  have h166 := h (M v77 x) v3 v2
  have h167 := C (T (T h154 (C h163 (T (C h100 (T h155 (C h161 (T (C h158 h156) (S h159))))) (S h162)))) (C (C h113 h164) h67)) h82
  let v168 := M v1 v2
  have h169 := R v168
  have h170 := R (M v0 v3)
  have h171 := h v168 v0 v3
  have h172 := C (T (T h171 (C h170 (C (T (C h169 (T (T (T h99 h167) (C (C (T h166 (C h139 (T h165 h100))) h26) h82)) (C (C h153 h53) h82))) (S h152)) h26))) (S h150)) h82
  have h173 := C h172 h26
  let v174 := M v168 v2
  have h175 := R v174
  have h176 := C h175 h67
  have h177 := C h139 (T (T (C (T (T (T (T (T (T (T (T (T h126 h41) h125) h124) h123) h91) h147) h144) h114) h136) h82) h143) h112)
  have h178 := h v174 v1 v2
  have h179 := C (T (T h150 (C h170 (C (T h152 (C h169 (T (T (T (C (C h153 h67) h82) (C (C (T (C h139 (T h99 h167)) (S h166)) h26) h82)) h165) h100))) h26))) (S h171)) h82
  have h180 := C (T (T (T (T (T (T (T (T (T (T h176 h173) h148) h126) h41) h125) h124) h123) h91) h147) h144) (T (T (T (T (T (T (T (T (T h38 h66) h60) h4) h86) h80) h177) h179) h178) (C (C (T (T (T (T (T (T h38 h66) h60) h4) h86) h80) h177) h82) (T (T (T (T (C h176 h82) (C h173 h82)) (C h149 h82)) h143) h112)))
  have h181 := C h175 h53
  have h182 := C h181 h53
  have h183 := R (M v174 v3)
  have h184 := C h183 h67
  have h185 := C h176 h53
  have h186 := C h179 h26
  have h187 := C (T h186 h181) h26
  have h188 := C (T h80 h177) h26
  have h189 := T (T (T (T (T (T (T (T (T (T h118 h130) h121) h119) h92) h90) h89) h88) h42) h87) h188
  have h190 := C h189 h26
  have h191 := C (T h114 h136) h67
  let v192 := M v120 v2
  have h193 := h v192 v2 v3
  have h194 := S h193
  have h195 := C h149 h26
  have h196 := C (T h176 h173) h26
  have h197 := C h181 h67
  have h198 := C h183 h53
  have h199 := C h176 h67
  have h200 := C (T (T (T (T (T (T (T (T (T (T h121 h119) h92) h90) h89) h88) h42) h87) h188) h186) h181) (T (T (T (T (T (T (T (T (T (C (C (T (T (T (T (T (T h140 h81) h79) h5) h52) h51) h39) h82) (T (T (T (T h111 h137) (C h189 h82)) (C h186 h82)) (C h181 h82))) (S h178)) h172) h140) h81) h79) h5) h52) h51) h39)
  let v201 := M v2 v3
  have h202 := R v201
  have h203 := C h202 (T (T (T (T (T (T (T (T (T (T (T (T (T h38 h66) h60) h4) h86) h80) h177) h141) h200) h199) h198) h197) h196) h195)
  let v204 := M v201 v1
  have h205 := h v204 v0 x
  have h206 := R v0
  have h207 := h v204 v2 v1
  have h208 := S h207
  have h209 := R (M v204 v2)
  have h210 := C h202 (T (T (T (T (T (T (T (T (T (T (T (T (T h190 h187) h185) h184) h182) h180) h142) h140) h81) h79) h5) h52) h51) h39)
  have h211 := T h193 h210
  have h212 := h v174 v3 v1
  have h213 := C h129 h53
  have h214 := C h78 h67
  have h215 := C h117 h53
  have h216 := T h203 h194
  have h217 := C h216 h26
  have h218 := R v204
  have h219 := C h218 h67
  have h220 := C (T (T (T (T h219 h217) h215) h214) h213) (T (T (T (T (T (T (T (T (T (T h38 h66) h60) h4) h86) h80) h177) h179) h212) (C (T (T (T (T (T (T (T (T (T (T h48 h47) h125) h124) h123) h91) h147) h144) h114) h136) (C h211 h82)) (T (T (T (T (T (T (T h184 h182) h180) h142) h140) h81) h79) h5))) (C h209 h53))
  have h221 := R (M v204 v1)
  have h222 := C h221 h53
  have h223 := C h218 h53
  have h224 := C h223 h26
  have h225 := C h211 h26
  have h226 := R v192
  have h227 := C h226 h67
  have h228 := C (T h227 h225) h67
  have h229 := R (M v192 v1)
  have h230 := C h229 h53
  have h231 := C h226 h53
  have h232 := C h231 h26
  have h233 := R (M v192 v3)
  have h234 := C h233 h67
  have h235 := C (T (T (T (T h146 h62) h96) h132) h130) h82
  have h236 := C h94 h82
  have h237 := C h33 h82
  have h238 := T (T h237 h236) h235
  have h239 := C h238 h67
  have h240 := C h239 h53
  have h241 := C h62 h82
  have h242 := C h146 h82
  have h243 := C (T (T (T (T h114 h105) h97) h33) h94) h82
  have h244 := T (T h243 h242) h241
  have h245 := C h244 h53
  have h246 := C h135 h67
  have h247 := C (T h246 h245) h67
  have h248 := R (M v77 v1)
  have h249 := C h248 h53
  have h250 := C h78 h53
  have h251 := C h250 h67
  have h252 := R (M v77 v3)
  have h253 := C h252 h53
  have h254 := C h113 h67
  have h255 := C h254 h67
  have h256 := T (T (T (T (T (T (T (T (T (T (T (T (T h255 h253) h251) h249) h247) h240) h234) h232) h230) h228) h224) h222) h220) h208
  have h257 := C h213 h53
  have h258 := C h252 h67
  have h259 := C h214 h53
  have h260 := C h248 h67
  have h261 := C (T h239 h215) h53
  have h262 := C h245 h67
  have h263 := C h233 h53
  have h264 := C h227 h26
  have h265 := C h229 h67
  have h266 := C (T h217 h231) h53
  have h267 := C h219 h26
  have h268 := C h221 h67
  have h269 := C (T (T (T (T h254 h250) h246) h225) h223) (T (T (T (T (T (T (T (T (T (T (C h209 h67) (C (T (T (T (T (T (T (T (T (T (T (C h216 h82) h118) h130) h121) h119) h92) h90) h89) h88) h65) h61) (T (T (T (T (T (T (T h4 h86) h80) h177) h141) h200) h199) h198))) (S h212)) h172) h140) h81) h79) h5) h52) h51) h39)
  have h270 := h (M v95 v2) v2 v3
  have h271 := S h270
  have h272 := C h202 (T (T (T (T (T (T (T (T (T (T (T h4 h86) h80) h177) h141) h200) h199) h198) h197) h196) h195) (C (C h244 h82) h26))
  have h273 := T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h272 h271) h237) h236) h235) h193) h210) h207) h269) h268) h267) h266) h265) h264) h263) h262) h261
  have h274 := C h202 (T (T (T (T (T (T (T (T (T (T (T (C (C h238 h82) h26) h190) h187) h185) h184) h182) h180) h142) h140) h81) h79) h5)
  have h275 := C h35 h82
  have h276 := C h145 h82
  have h277 := h (M v72 z) v2 v0
  have h278 := C (C h93 h82) h206
  have h279 := C (C h32 h82) h100
  have h280 := T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h247 h240) h234) h232) h230) h228) h224) h222) h220) h208) h203) h194) h243) h242) h241) h270) h274
  have h281 := T (T (T (T (T (T (T (T (T (T (T (T (T h207 h269) h268) h267) h266) h265) h264) h263) h262) h261) h260) h259) h258) h257
  have h282 := C (T h118 h130) h53
  have h283 := R y
  have h284 := h v174 v1 z
  have h285 := h z v3 v3
  T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h102 h279) h278) (C (T h276 h275) (T (T (T (T (h v0 v1 y) (C h161 (T (T (T (T (T (C (R (M v0 v1)) (T h156 (C (T (h (M y x) v1 y) (C h161 (C h157 h283))) h34))) (S (h v160 v0 v1))) (C (T (T (T (T (T (T (T (T (T h38 h66) h60) h4) h86) h80) h177) h179) h284) (C (T (T (T (T (T (T h111 h134) h243) h242) h241) h270) h274) (T (T (T (T (C h176 h27) (C h173 h27)) (C h148 h27)) (C h127 (T (T (T (T (T (T h6 h31) h24) h63) h69) (C (T (T h55 h29) h28) h26)) (C h21 h26)))) (S h285)))) h283)) (C (T (T (T (T (C h273 h27) (C h260 h27)) (C h259 h27)) (C h258 h27)) (C h257 h27)) h283)) (C (C h256 h27) h283)) (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (C h281 h27) (C h255 h27)) (C h253 h27)) (C h251 h27)) (C h249 h27)) (C h280 h27)) (C (T (T (T (T (T (T h272 h271) h237) h236) h235) h116) h112) (T (T (T (T h285 (C h108 (T (T (T (T (T (T (C h30 h26) (C (T (T h20 h18) h46) h26)) h57) h37) h25) h22) h7))) (C h188 h27)) (C h186 h27)) (C h181 h27)))) (S h284)) h172) h141) h200) h199) h198) h197) h196) h195) h282) h283)))) (S (h v120 v1 y))) (h v120 v1 z)) (C (T (T (T (T (T h111 h134) h193) h210) h205) (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T h38 h66) h60) h4) h86) h80) h177) h141) h200) h199) h198) h197) h196) h195) h282) (T (T (T (T (T (T (T (T (T (T (C (C h281 h206) h164) (C (T (T (T (T (C h255 h206) (C h253 h206)) (C h251 h206)) (C h249 h206)) (C h280 h206)) h164)) (C (C (T (T (T (T (T (T (T (T (T h272 h271) h237) h236) h235) h116) h112) h110) h109) h107) h206) h164)) (C (C h129 h206) (T (T h102 h279) h278))) (S h277)) h85) h83) h70) h59) h22) h7))) (T (T (T (T (T (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T h191 h190) h187) h185) h184) h182) h180) h142) h140) h81) h79) h5) h52) h51) h39) (T (T (T (T (T (T (T (T (T (T h6 h31) h58) h76) h75) h74) h277) (C (C h113 h206) (T (T (C h276 h206) (C h275 h99)) h131))) (C (C (T (T (T (T (T (T (T (T (T h106 h128) h122) h111) h134) h243) h242) h241) h270) h274) h206) h164)) (C (T (T (T (T (C h273 h206) (C h260 h206)) (C h259 h206)) (C h258 h206)) (C h257 h206)) h164)) (C (C h256 h206) h164))) (S h205)) h203) h194) h116) h112))))) (S (h (M v120 v1) z v2))) h191) h190) h187) h185) h184) h182) h180) h142) h140) h81) h79) h5

