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
theorem Equation1181_implies_Equation3370 (G: Type _) [Magma G] (h: Equation1181 G) : Equation3370 G := fun x y z =>
  let v0 := M z x
  let v1 := M z v0
  let v2 := M y v1
  have h3 := R v2
  have h4 := h v1 y v1
  have h5 := S h4
  have h6 := R y
  have h7 := h x v1 z
  have h8 := C h7 h6
  have h9 := C h6 (T (C h6 h8) h5)
  let v10 := M x y
  have h11 := h v10 v2 y
  have h12 := T h11 (C h3 (C h9 h3))
  let v13 := M (M v1 (M v1 v1)) v10
  have h14 := h v2 v13 v2
  have h15 := S h14
  have h16 := R v13
  have h17 := h v1 v10 v1
  have h18 := R v10
  have h19 := C h7 h18
  have h20 := C h19 (T h17 (C h12 h16))
  have h21 := h (M (M x v10) v1) x v1
  have h22 := S h21
  have h23 := R x
  have h24 := h y v1 x
  have h25 := h v1 x v1
  have h26 := S h25
  have h27 := C h23 (C h7 h23)
  have h28 := T h27 h26
  have h29 := h y v1 v1
  have h30 := S h29
  have h31 := S h7
  have h32 := C h23 (C h31 h23)
  have h33 := T h25 h32
  have h34 := C h23 (C (T (C h33 h30) (C h28 h24)) h23)
  let v35 := M v1 (M v1 y)
  have h36 := h (M v35 v1) x v1
  have h37 := T (T (T (T h36 h34) h22) h20) h15
  have h38 := S h36
  have h39 := C h23 (C (T (C h33 (S h24)) (C h28 h29)) h23)
  have h40 := S h17
  have h41 := C h31 h6
  have h42 := C h6 (T h4 (C h6 h41))
  have h43 := T (C h3 (C h42 h3)) (S h11)
  have h44 := C h31 h18
  have h45 := C h44 (T (C h43 h16) h40)
  have h46 := T (T (T (T h14 h45) h21) h39) h38
  have h47 := C h28 h46
  have h48 := C h33 h3
  have h49 := h (M v1 v2) x v2
  have h50 := S h49
  have h51 := h x v2 z
  let v52 := M v2 x
  have h53 := h v52 x x
  have h54 := S h53
  have h55 := h v10 x y
  have h56 := C h23 (C (T h19 (C h31 (T h55 (C h23 (C h9 h23))))) h23)
  have h57 := h y x x
  have h58 := S h57
  have h59 := C h23 (C (T (C h7 (T (C h23 (C h42 h23)) (S h55))) h44) h23)
  have h60 := h x v2 v2
  have h61 := T (T (T (C h3 (S h60)) h53) h59) h58
  have h62 := C h61 h23
  have h63 := C h23 (T h62 (C (T (T (T h57 h56) h54) (C h3 h51)) h23))
  have h64 := T (T (T h57 h56) h54) (C h3 h60)
  have h65 := C h64 h23
  have h66 := h x v2 v10
  have h67 := C h23 (T (C (T (T (T (C h3 (S h66)) h53) h59) h58) h23) h65)
  let v68 := M (M v10 (M v10 x)) v2
  have h69 := h v68 x v2
  have h70 := h v68 x v1
  have h71 := S h70
  have h72 := S h69
  have h73 := C h23 (T h62 (C (T (T (T h57 h56) h54) (C h3 h66)) h23))
  have h74 := C h23 (T (C (T (T (T (C h3 (S h51)) h53) h59) h58) h23) h65)
  have h75 := C h28 h3
  have h76 := C h33 h37
  have h77 := R v1
  have h78 := C (C h77 (T (C h33 h6) (C h28 (T (T (T (T (T (T h29 h76) h75) h49) h74) h73) h72)))) h23
  have h79 := h (M v35 x) x x
  have h80 := S h79
  have h81 := h y x v1
  have h82 := C h23 (T (C h43 h23) (C (C h23 h81) h23))
  have h83 := h v2 x v2
  have h84 := C h23 (T (T (T (T (T (T (T (T (C h23 (T (T (T (T (T (T (T (T h36 h34) h22) h20) h15) h83) h82) h80) h78)) h71) h69) h67) h63) h50) h48) h47) h30)
  have h85 := C h23 (T (C h7 h3) (C h31 h46))
  have h86 := h (M x (M x v2)) y v2
  have h87 := S h86
  have h88 := C h23 (T (C h7 h37) (C h31 h3))
  have h89 := S h83
  have h90 := C h23 (T (C (C h23 (S h81)) h23) (C h12 h23))
  have h91 := C (C h77 (T (C h33 (T (T (T (T (T (T h69 h67) h63) h50) h48) h47) h30)) (C h28 h6))) h23
  have h92 := C h23 (T (T (T (T (T (T (T (T h29 h76) h75) h49) h74) h73) h72) h70) (C h23 (T (T (T (T (T (T (T (T h91 h79) h90) h89) h14) h45) h21) h39) h38)))
  have h93 := h (M (M v2 (M v2 v10)) y) x y
  have h94 := h v10 y v2
  have h95 := h x x x
  have h96 := C h6 (T (T (T h95 (C h23 (C (T (T (T h27 h26) h4) (C h6 (T h41 h94))) h23))) (S h93)) (C (C h3 (C h3 (T h92 h88))) h6))
  let v97 := M y x
  have h98 := h v97 y v10
  have h99 := S h98
  have h100 := S h95
  have h101 := T h85 h84
  have h102 := C h6 (T (T (T (C (C h3 (C h3 h101)) h6) h93) (C h23 (C (T (T (T (C h6 (T (S h94) h8)) h5) h25) h32) h23))) h100)
  have h103 := h (M v10 v10) x v10
  have h104 := h v2 v10 v2
  have h105 := h v2 v10 v10
  have h106 := S h105
  have h107 := h (M (M v10 (M v10 v2)) v10) x v10
  have h108 := C h18 (T (T (T h107 (C h23 (C (T (C h18 h106) (C h18 (T h104 (C h18 (C h43 h18))))) h23))) (S h103)) (C h18 (T (T (T h92 h88) h86) h102)))
  have h109 := C (T (T h9 h105) h108) h6
  have h110 := h (M (M y (M y v10)) y) x y
  have h111 := S h110
  have h112 := h v10 y y
  have h113 := C h23 (C (T (T (T h27 h26) h4) (C h6 (T h41 h112))) h23)
  let v114 := M (M v2 v52) v2
  have h115 := h v114 x v2
  have h116 := h v114 y v2
  have h117 := S h116
  have h118 := C h6 (C h64 h6)
  have h119 := C h31 (T (T (T (T h92 h88) h86) h102) h65)
  have h120 := h v13 x v10
  have h121 := S h120
  have h122 := C h18 h17
  have h123 := h v1 v10 y
  have h124 := C h23 (C (T (C h18 (S h123)) h122) h23)
  let v125 := M y v2
  let v126 := M v125 v10
  have h127 := h v126 x v10
  have h128 := C h6 (C h6 (T (T (T (T (T (T (T (T h127 h124) h121) h119) h63) h50) h48) h47) h30))
  have h129 := C (T (T (T (T (T (T (T (T h128 h118) h117) h115) h63) h50) h48) h47) h30) (T (T (T h95 h113) h111) h109)
  have h130 := S h127
  have h131 := C h18 h40
  have h132 := C h23 (C (T h131 (C h18 h123)) h23)
  have h133 := C h7 (T (T (T (T h62 h96) h87) h85) h84)
  have h134 := C h6 (C h6 (T (T (T (T (T (T (T (T h29 h76) h75) h49) h74) h133) h120) h132) h130))
  have h135 := C h6 (C h61 h6)
  have h136 := S h115
  have h137 := h v126 x y
  have h138 := S h137
  have h139 := C h23 (C (T (T (T (C h6 (T (S h112) h8)) h5) h25) h32) h23)
  have h140 := C h18 (T (T (T (C h18 (T (T (T h96 h87) h85) h84)) h103) (C h23 (C (T (C h18 (T (C h18 (C h12 h18)) (S h104))) (C h18 h105)) h23))) (S h107))
  have h141 := C (T (T h140 h106) h42) h6
  have h142 := C (T (T (T (T (T (T (T (T h29 h76) h75) h49) h74) h136) h116) h135) h134) (T (T (T h141 h110) h139) h100)
  have h143 := h v97 x v10
  have h144 := S h143
  have h145 := T h105 h108
  have h146 := C h145 h23
  have h147 := C h23 (T (T (T (T (T (T (T (T (T (T (T (T h127 h124) h121) h119) h63) h50) h48) h47) h30) h57) h56) h54) h146)
  have h148 := C h23 (T (T (T h147 h144) h98) h142)
  have h149 := C (T (T (T (T (T (T (T (T (T h148 h138) h127) h124) h121) h119) h136) h116) h135) h134) h23
  have h150 := T h140 h106
  have h151 := C h150 h23
  have h152 := C h23 (T (T (T (T (T (T (T (T (T (T (T (T h151 h53) h59) h58) h29) h76) h75) h49) h74) h133) h120) h132) h130)
  have h153 := C h23 (T (T (T h129 h99) h143) h152)
  have h154 := h v1 v10 v2
  have h155 := C h23 (C (T (C h18 (S h154)) h122) h23)
  let v156 := M (M v2 (M v2 v1)) v10
  have h157 := h v156 x v10
  have h158 := T (T (T h157 h155) h132) h130
  have h159 := C h6 (C h6 h158)
  have h160 := C (T (T (T (T (T (T (T (T (T (T h159 h128) h118) h117) h115) h133) h120) h132) h130) h137) h153) h23
  have h161 := S h157
  have h162 := C h23 (C (T h131 (C h18 h154)) h23)
  have h163 := T (T (T h127 h124) h162) h161
  have h164 := C h6 (C h6 h163)
  have h165 := h v156 x y
  have h166 := S h165
  have h167 := C (T (T (T (T (T (T (T (T (T (T h148 h138) h127) h124) h121) h119) h136) h116) h135) h134) h164) h23
  have h168 := C (T (T (T (T (T (T (T (T (T h128 h118) h117) h115) h133) h120) h132) h130) h137) h153) h23
  have h169 := C h23 h158
  have h170 := C h23 (T (T (T (T (T (T h169 h147) h144) h98) h142) h168) h167)
  have h171 := C (T (T (T (T (T (T (T (T (T (T h170 h166) h157) h155) h121) h119) h136) h116) h135) h134) h164) h23
  have h172 := C h23 h163
  have h173 := C h23 (T (T (T (T (T (T h160 h149) h129) h99) h143) h152) h172)
  have h174 := h v1 v10 v0
  have h175 := C h23 (C (T (C h18 (S h174)) h122) h23)
  let v176 := M (M v0 (M v0 v1)) v10
  have h177 := h v176 x v10
  have h178 := T (T (T h177 h175) h162) h161
  have h179 := C h6 (C h6 h178)
  have h180 := C (T (T (T (T (T (T (T (T (T (T (T h179 h159) h128) h118) h117) h115) h133) h120) h162) h161) h165) h173) h23
  have h181 := S h177
  have h182 := C h23 (C (T h131 (C h18 h174)) h23)
  have h183 := T (T (T h157 h155) h182) h181
  have h184 := C h6 (C h6 h183)
  have h185 := h v176 x y
  have h186 := S h185
  have h187 := C (T (T (T (T (T (T (T (T (T (T (T h170 h166) h157) h155) h121) h119) h136) h116) h135) h134) h164) h184) h23
  have h188 := C (T (T (T (T (T (T (T (T (T (T h159 h128) h118) h117) h115) h133) h120) h162) h161) h165) h173) h23
  have h189 := C h23 h178
  have h190 := C h23 (T (T (T (T (T (T (T (T (T h189 h169) h147) h144) h98) h142) h168) h167) h188) h187)
  have h191 := C (T (T (T (T (T (T (T (T (T (T (T h190 h186) h177) h175) h121) h119) h136) h116) h135) h134) h164) h184) h23
  have h192 := C h23 h183
  have h193 := C h23 (T (T (T (T (T (T (T (T (T h180 h171) h160) h149) h129) h99) h143) h152) h172) h192)
  have h194 := h v1 v10 v10
  have h195 := C h23 (C (T (C h18 (S h194)) h122) h23)
  let v196 := M (M v10 (M v10 v1)) v10
  have h197 := h v196 x v10
  have h198 := T (T (T h197 h195) h182) h181
  have h199 := C h6 (C h6 h198)
  have h200 := C (T (T (T (T (T (T (T (T (T (T (T (T h199 h179) h159) h128) h118) h117) h115) h133) h120) h182) h181) h185) h193) h23
  have h201 := S h197
  have h202 := C h23 (C (T h131 (C h18 h194)) h23)
  have h203 := T (T (T h177 h175) h202) h201
  have h204 := C h6 (C h6 h203)
  have h205 := h v196 x y
  have h206 := S h205
  have h207 := C (T (T (T (T (T (T (T (T (T (T (T (T h190 h186) h177) h175) h121) h119) h136) h116) h135) h134) h164) h184) h204) h23
  have h208 := C (T (T (T (T (T (T (T (T (T (T (T h179 h159) h128) h118) h117) h115) h133) h120) h182) h181) h185) h193) h23
  have h209 := C h23 h198
  have h210 := C h23 (T (T (T (T (T (T (T (T (T (T (T (T h209 h189) h169) h147) h144) h98) h142) h168) h167) h188) h187) h208) h207)
  have h211 := C (T (T (T (T (T (T (T (T (T (T (T (T h210 h206) h197) h195) h121) h119) h136) h116) h135) h134) h164) h184) h204) h23
  have h212 := C h23 h203
  have h213 := C h23 (T (T (T (T (T (T (T (T (T (T (T (T h200 h191) h180) h171) h160) h149) h129) h99) h143) h152) h172) h192) h212)
  have h214 := h v1 v10 x
  have h215 := C h23 (C (T (C h18 (S h214)) h122) h23)
  let v216 := M (M x (M x v1)) v10
  have h217 := h v216 x v10
  have h218 := T (T (T h217 h215) h202) h201
  have h219 := C h6 (C h6 h218)
  have h220 := C (T (T (T (T (T (T (T (T (T (T (T (T (T h219 h199) h179) h159) h128) h118) h117) h115) h133) h120) h202) h201) h205) h213) h23
  have h221 := S h217
  have h222 := C h23 (C (T h131 (C h18 h214)) h23)
  have h223 := T (T (T h197 h195) h222) h221
  have h224 := C h6 (C h6 h223)
  have h225 := h v216 x y
  have h226 := S h225
  have h227 := C (T (T (T (T (T (T (T (T (T (T (T (T (T h210 h206) h197) h195) h121) h119) h136) h116) h135) h134) h164) h184) h204) h224) h23
  have h228 := C (T (T (T (T (T (T (T (T (T (T (T (T h199 h179) h159) h128) h118) h117) h115) h133) h120) h202) h201) h205) h213) h23
  have h229 := C h23 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (C h23 h218) h209) h189) h169) h147) h144) h98) h142) h168) h167) h188) h187) h208) h207) h228) h227)
  have h230 := C (T (T (T (T (T (T (T (T (T (T (T (T (T h229 h226) h217) h215) h121) h119) h136) h116) h135) h134) h164) h184) h204) h224) h23
  have h231 := T (T (T (T (T h119 h63) h50) h48) h47) h30
  have h232 := C h145 h231
  have h233 := h v13 v2 v2
  have h234 := S h233
  have h235 := C h150 (T (T (T (T (T h29 h76) h75) h49) h74) h133)
  have h236 := C h6 h46
  have h237 := C h3 (T h236 (C (T (T (T (T h57 h56) h54) h146) (C h150 (T (T (T (T h95 h113) h111) h109) h235))) h37))
  have h238 := C h3 (T h237 h234)
  have h239 := C h6 h37
  have h240 := C (T (T (T (T (C h145 (T (T (T (T h232 h141) h110) h139) h100)) h151) h53) h59) h58) h46
  have h241 := C h3 (T h240 h239)
  have h242 := C h3 (T (T (T (T (T (T (C (T (T (T (T (T h238 h232) h141) h110) h139) h100) (T (T (T h83 h82) h80) h78)) h71) h69) h67) h133) h233) h241)
  have h243 := h v125 v2 v2
  have h244 := C h23 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h220 h211) h200) h191) h180) h171) h160) h149) h129) h99) h143) h152) h172) h192) h212) (C h23 h223))
  have h245 := C (T (T (T (T (T (T (T (T (T (T h29 h76) h75) h49) h74) h133) h120) h222) h221) h225) h244) (T (T (T (T (T (T (T (T h239 h243) h242) h238) h232) h141) h110) h139) h100)
  have h246 := C h6 h236
  let v247 := M y v125
  have h248 := C h6 h239
  have h249 := C h3 (T h233 h241)
  have h250 := C (T (T (T (T (T (T (T (T (T (T h229 h226) h217) h215) h121) h119) h63) h50) h48) h47) h30) (T (T (T (T (T (T (T (T h95 h113) h111) h109) h235) h249) (C h3 (T (T (T (T (T (T h237 h234) h119) h73) h72) h70) (C (T (T (T (T (T h95 h113) h111) h109) h235) h249) (T (T (T h91 h79) h90) h89))))) (S h243)) h236)
  have h251 := C (T (T (T (T (T (T (T (T (T (T (T (T (T h219 h199) h179) h159) h128) h118) h117) h115) h133) h120) h222) h221) h225) h244) h23
  T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h92 h88) h86) h102) h98) h142) h168) h167) h188) h187) h208) h207) h228) h227) h251) h250) h248) (h v247 v2 x)) (C h3 (T (T (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (C h23 (T (T (T (T (T (T (T (C h23 (T h246 h245)) (S (h v216 x x))) h217) h215) h121) h233) (C (T (T h105 h108) (C h18 (C h18 (T (T (T (T (T (T (T (T (T (T (T (T h98 h142) h168) h167) h188) h187) h208) h207) h228) h227) h251) h250) h248)))) (T (T (T (T (T (T (T (T (T h240 h239) h243) h242) h238) h232) h141) h110) h139) h100))) (C (T (T (T (T (C h18 (C h18 (T (T (T (T (T (T (T (T (T (T (T (T h246 h245) h230) h220) h211) h200) h191) h180) h171) h160) h149) h129) h99))) h140) h106) (h v2 v13 x)) (C h231 (T (T (T (C h101 h16) h40) h4) (C h6 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h41 h92) h88) h86) h102) h98) h142) h168) h167) h188) h187) h208) h207) h228) h227) h251) h250) h248))))) h23))) (S (h v247 x y))) h246) h245) h230) h220) h211) h200) h191) h180) h171) h160) h149) h129) h99) h96) h87) h85) h84) h46) (C h18 h37)) (C h12 h3)))) (S (h v2 v2 v2))

