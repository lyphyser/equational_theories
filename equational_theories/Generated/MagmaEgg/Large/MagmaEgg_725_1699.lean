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
theorem Equation725_implies_Equation1699 (G: Type _) [Magma G] (h: Equation725 G) : Equation1699 G := fun x y z =>
  let v0 := M y x
  let v1 := M y z
  let v2 := M v1 z
  let v3 := M v0 v2
  have h4 := h v3 x v0
  have h5 := S h4
  let v6 := M (M v0 v3) v0
  have h7 := h (M x v6) x x
  have h8 := S h7
  have h9 := R x
  have h10 := h v3 x v1
  have h11 := C (S h10) h9
  have h12 := C h9 (C h9 (T h11 (C h4 h9)))
  let v13 := M (M v1 v3) v1
  let v14 := M x v13
  have h15 := h v14 x x
  have h16 := h v14 v3 x
  have h17 := S h16
  have h18 := C h10 h9
  have h19 := h x v0 x
  have h20 := S h19
  let v21 := M (M x x) x
  have h22 := h (M v0 v21) x v0
  have h23 := R v0
  have h24 := h (M x v0) x x
  have h25 := h y x x
  have h26 := S h25
  let v27 := M (M x y) x
  have h28 := h (M x v27) x x
  have h29 := h v27 x x
  have h30 := C h23 (T (T h25 (C h9 (C h9 (T (T (T h29 (C h9 (C h9 (C (T h28 (C h9 (C h9 (C h26 h9)))) h9)))) (S h24)) (C h19 h23))))) (S h22))
  have h31 := R v3
  have h32 := C h31 (T h30 h20)
  let v33 := M v0 y
  have h34 := h (M v3 v33) x v3
  have h35 := S h34
  have h36 := h x v3 y
  have h37 := h x v3 z
  have h38 := C (S h37) h31
  have h39 := C h37 h31
  have h40 := R v2
  have h41 := h v0 v2 v3
  have h42 := C (S h41) h40
  have h43 := C h9 (T (C h9 h42) h39)
  let v44 := M v2 (M (M v3 v0) v3)
  have h45 := h v44 x v2
  have h46 := C h9 (T (T h45 h43) (C h9 (T h38 (C h36 h31))))
  have h47 := S h45
  have h48 := C h41 h40
  have h49 := C h9 (T h38 (C h9 h48))
  have h50 := h x v3 v1
  have h51 := T (C (S h50) h31) h39
  have h52 := C h9 (T (T (C h9 h51) h49) h47)
  let v53 := M v3 (M (M v1 x) v1)
  have h54 := h v53 x v3
  have h55 := h v53 y v3
  have h56 := S h55
  have h57 := T h38 (C h50 h31)
  have h58 := R y
  have h59 := C h58 (C h58 h57)
  let v60 := M v3 (M (M z x) z)
  have h61 := h v60 y v3
  have h62 := h v60 x v3
  have h63 := S h62
  have h64 := h x v3 x
  have h65 := S h64
  have h66 := C h9 (C h9 (T (C h65 h31) h39))
  let v67 := M v3 v21
  have h68 := h v67 x v3
  have h69 := C h31 (T (T (T (T (T (T (T (T (T (T (T h68 h66) h63) h61) h59) h56) h54) h52) h46) h35) h32) h18)
  have h70 := C h31 (T (T (T h30 h20) h64) h69)
  have h71 := C (T (C h9 (T (T (T (T (T (T (T (T (T (T (T (T (T (T h68 h66) h63) h61) h59) h56) h54) h52) h46) h35) h70) h17) h15) h12) h8)) h5) (T h64 h69)
  have h72 := C h9 (T (T (T (T h71 h17) h15) h12) h8)
  have h73 := S h68
  have h74 := C h9 (C h9 (T h38 (C h64 h31)))
  have h75 := S h61
  have h76 := C h58 (C h58 h51)
  have h77 := S h54
  have h78 := C h9 (T (T h45 h43) (C h9 h57))
  have h79 := C h9 (T (T (C h9 (T (C (S h36) h31) h39)) h49) h47)
  have h80 := C h9 (C h9 (T (T (T (C h20 h23) h24) (C h9 (C h9 (C (T (C h9 (C h9 (C h25 h9))) (S h28)) h9)))) (S h29)))
  have h81 := C h23 (T (T h22 h80) h26)
  have h82 := C h31 (T h19 h81)
  have h83 := C h31 (T (T (T (T (T (T (T (T (T (T (T h11 h82) h34) h79) h78) h77) h55) h76) h75) h62) h74) h73)
  have h84 := C h31 (T (T (T h83 h65) h19) h81)
  have h85 := S h15
  have h86 := C h9 (C h9 (T (C h5 h9) h18))
  have h87 := C (T h4 (C h9 (T (T (T (T (T (T (T (T (T (T (T (T (T (T h7 h86) h85) h16) h84) h34) h79) h78) h77) h55) h76) h75) h62) h74) h73))) (T h83 h65)
  have h88 := h v67 x x
  have h89 := S h88
  have h90 := C h9 (T (T (T (T h7 h86) h85) h16) h87)
  have h91 := T h4 h90
  have h92 := T (T (C h31 h18) h83) h65
  have h93 := C h92 h91
  have h94 := T (T h64 h69) (C h31 h11)
  have h95 := T h38 (C h94 h31)
  have h96 := C (T (T (T (T (T (C h31 h39) (C h31 h95)) (C h31 (T (T (T (T (T (T (T (T (T (T (T (T (T h93 h89) h68) h66) h63) h61) h59) h56) h54) h52) h46) h35) h70) h87))) (C h31 (T (T (T h71 h84) h32) h18))) h83) h65) h91
  have h97 := C h9 (T (T (T (T (T (T (T (T (T (T (T (T (T h96 h89) h68) h66) h63) h61) h59) h56) h54) h52) h46) h35) h70) h87)
  have h98 := T h72 h5
  have h99 := T (C h92 h31) h39
  have h100 := C h94 h98
  have h101 := C (T (T (T (T (T h64 h69) (C h31 (T (T (T h11 h82) h70) h87))) (C h31 (T (T (T (T (T (T (T (T (T (T (T (T (T h71 h84) h34) h79) h78) h77) h55) h76) h75) h62) h74) h73) h88) h100))) (C h31 h99)) (C h31 h38)) h98
  have h102 := C h9 (T h93 h101)
  have h103 := C h9 h95
  have h104 := h v44 v3 v2
  have h105 := h v3 v3 v2
  have h106 := C (S h105) h31
  have h107 := C h105 h31
  have h108 := h v3 v3 v0
  have h109 := T (C (S h108) h31) h107
  let v110 := M v3 v6
  have h111 := h v110 v3 v3
  have h112 := h v110 x v3
  have h113 := T h106 (C h108 h31)
  let v114 := M (M v2 v3) v2
  have h115 := h (M v3 v114) x v3
  have h116 := h v114 x x
  have h117 := h (M x v114) x x
  have h118 := h v3 x v2
  have h119 := h v3 x v3
  let v120 := M (M v3 v3) v3
  have h121 := h (M x v120) x x
  have h122 := C h9 (C h9 (C (T (T h121 (C h9 (C h9 (T (C (S h119) h9) h18)))) h85) h9))
  have h123 := h v120 x x
  have h124 := h v120 x y
  have h125 := S h124
  have h126 := h (M y v120) x y
  have h127 := h v3 y v3
  have h128 := h v3 y v0
  have h129 := h (M y v6) x y
  have h130 := C h9 (C h9 (C (T (T h129 (C h9 (C h9 (T (C (S h128) h58) (C h127 h58))))) (S h126)) h58))
  have h131 := h v6 x y
  have h132 := h v6 x x
  have h133 := S h132
  have h134 := h (M v3 x) x v3
  have h135 := h v0 v2 v0
  have h136 := C h9 (T (C h9 (C (S h135) h40)) h39)
  let v137 := M v2 (M (M v0 v0) v0)
  have h138 := h v137 x v2
  have h139 := C h9 (C h9 (C (T (T (T (T (T (T (T (C h9 (T (T h138 h136) h103)) (S h134)) h82) h70) h17) h15) h12) h8) h9))
  have h140 := h v137 x x
  have h141 := S h138
  have h142 := C h9 (T h38 (C h9 (C h135 h40)))
  have h143 := C h9 h99
  have h144 := C h9 (T h96 h100)
  have h145 := C h9 (T (T (T (T (T (T (T (T (T (T (T (T (T h71 h84) h34) h79) h78) h77) h55) h76) h75) h62) h74) h73) h88) h101)
  have h146 := C (T (T (T (T (T (C h31 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h4 h90) h145) h144) h143) h142) h141) h140) h139) h133) h131) h130) h125) h123) h122) (C h9 (C h9 (C (T (T h15 (C h9 (C h9 (T h11 (C h118 h9))))) (S h117)) h9)))) (S h116))) h115) (C h9 (C h9 h113))) (S h112)) h111) (C h31 (T (T (C h31 h109) (C h31 (T h106 (C h31 h48)))) (S h104)))) h31
  have h147 := S h123
  have h148 := C h9 (C h9 (C (T (T h15 (C h9 (C h9 (T h11 (C h119 h9))))) (S h121)) h9))
  have h149 := h v13 x x
  have h150 := h v13 v3 v2
  have h151 := S h150
  have h152 := h (M v2 v13) x v2
  have h153 := h v3 v2 v1
  have h154 := h v3 v2 v2
  have h155 := C h9 (C (S h154) h40)
  have h156 := C h9 (C h154 h40)
  have h157 := h v3 v2 x
  let v158 := M (M x v3) x
  have h159 := h (M v2 v158) x v2
  have h160 := C h31 (C h31 (C (T (T (T h159 (C h9 (T (C h9 (C (S h157) h40)) h156))) (C h9 (T h155 (C h9 (C h153 h40))))) (S h152)) h40))
  have h161 := h v158 v3 v2
  have h162 := T (T (T (T (T (T h161 h160) h151) h149) h148) h147) h146
  have h163 := C h23 h162
  have h164 := h (M v0 v158) x v0
  have h165 := S h164
  have h166 := h v3 v0 x
  have h167 := C h9 (C h9 (C h166 h23))
  have h168 := h v2 x v0
  have h169 := h v2 z v2
  let v170 := M z (M (M v2 v2) v2)
  have h171 := S h161
  have h172 := C h31 (C h31 (C (T (T (T h152 (C h9 (T (C h9 (C (S h153) h40)) h156))) (C h9 (T h155 (C h9 (C h157 h40))))) (S h159)) h40))
  have h173 := S h149
  have h174 := S h140
  have h175 := C h9 (C h9 (C (T (T (T (T (T (T (T h7 h86) h85) h16) h84) h32) h134) (C h9 (T (T h143 h142) h141))) h9))
  have h176 := S h131
  have h177 := C h9 (C h9 (C (T (T h126 (C h9 (C h9 (T (C (S h127) h58) (C h128 h58))))) (S h129)) h58))
  have h178 := C (T (T (T (T (T (C h31 (T (T h104 (C h31 (T (C h31 h42) h107))) (C h31 h113))) (S h111)) h112) (C h9 (C h9 h109))) (S h115)) (C h31 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h116 (C h9 (C h9 (C (T (T h117 (C h9 (C h9 (T (C (S h118) h9) h18)))) h85) h9)))) h148) h147) h124) h177) h176) h132) h175) h174) h138) h136) h103) h102) h97) h72) h5))) h31
  have h179 := T (T (T (T (T (T h178 h123) h122) h173) h150) h172) h171
  have h180 := T (T (T (T (T (T h140 h139) h133) h131) h130) h125) h146
  have h181 := T (T (T (T (T (T h4 h90) h145) h144) h143) h142) h141
  have h182 := R z
  have h183 := h v1 z v2
  have h184 := C (S h183) h182
  let v185 := M (M v2 v1) v2
  let v186 := M z v185
  have h187 := h v186 v0 z
  have h188 := h v186 x z
  have h189 := C h183 h182
  have h190 := h v1 z y
  have h191 := S h190
  let v192 := M y v1
  have h193 := h (M z (M v192 y)) x z
  have h194 := T (T (T (T (T (T (T (T (T (T h193 (C h9 (T (C h9 (C h191 h182)) (C h9 h189)))) (S h188)) h187) (C h23 (C h23 h184))) (C h23 h181)) (C h23 h180)) (C h23 h179)) h164) (C h9 (C h9 (C (S h166) h23)))) (S h168)
  have h195 := h z y v3
  have h196 := S h195
  let v197 := M (M v3 z) v3
  have h198 := h (M y v197) x y
  have h199 := h z x y
  have h200 := h v1 y v2
  have h201 := h (M y v185) x y
  have h202 := h v185 x y
  have h203 := h v185 x z
  have h204 := h v186 z z
  have h205 := h (M z v2) x z
  have h206 := C h58 (T (T (T (T (T (T (T h190 (C h182 h194)) h205) (C h9 (C h9 (C (T (C h182 (C h182 h189)) (S h204)) h182)))) (S h203)) h202) (C h9 (C h9 (T (C (T (T h201 (C h9 (C h9 (C (S h200) h58)))) (S h199)) h58) (C h195 h58))))) (S h198))
  have h207 := h v192 v3 v3
  have h208 := S h207
  have h209 := T (T (T (T (T (T h138 h136) h103) h102) h97) h72) h5
  have h210 := T (T (T (T (T (T h178 h124) h177) h176) h132) h175) h174
  have h211 := C h58 (T (T (T (T (T (T (T h198 (C h9 (C h9 (T (C h196 h58) (C (T (T h199 (C h9 (C h9 (C h200 h58)))) (S h201)) h58))))) (S h202)) h203) (C h9 (C h9 (C (T h204 (C h182 (C h182 h184))) h182)))) (S h205)) (C h182 (T (T (T (T (T (T (T (T (T (T h168 h167) h165) h163) (C h23 h210)) (C h23 h209)) (C h23 (C h23 h189))) (S h187)) h188) (C h9 (T (C h9 h184) (C h9 (C h190 h182))))) (S h193)))) h191)
  have h212 := C h31 (T h195 h211)
  have h213 := h v197 x v1
  have h214 := R v1
  have h215 := h (M v1 v197) z v1
  have h216 := h z v1 v3
  have h217 := h y z v3
  have h218 := S h217
  have h219 := C h218 h182
  let v220 := M (M v3 y) v3
  let v221 := M z v220
  have h222 := h v221 z z
  have h223 := h y v1 v3
  have h224 := C (S h223) h214
  let v225 := M v1 v220
  have h226 := h v225 x v1
  have h227 := h v225 v3 v1
  have h228 := C h223 h214
  have h229 := h v3 z v2
  have h230 := C (S h229) h182
  have h231 := C h31 (T (T (T (T (T (C h31 (T (T h230 h212) (C h31 h228))) (S h227)) h226) (C h9 (T (C h9 h224) (C h9 (C (T (T h217 (C h182 (T h222 (C h182 (T (C h182 h219) (C h216 h214)))))) (S h215)) h214))))) (S h213)) (C h212 h31))
  let v232 := M z v114
  have h233 := h v232 v3 z
  have h234 := h v232 x z
  have h235 := S h234
  have h236 := C h229 h182
  have h237 := h v3 z x
  have h238 := C h9 (C h9 (T (C (S h237) h182) h236))
  have h239 := h (M z v158) x z
  have h240 := C h182 h179
  have h241 := C h182 h180
  have h242 := C h182 h181
  have h243 := h z v3 v3
  have h244 := C (S h243) h31
  have h245 := C h243 h31
  have h246 := C h182 h209
  have h247 := C h182 h210
  have h248 := C h182 h162
  have h249 := S h239
  have h250 := C h9 (C h9 (T h230 (C h237 h182)))
  have h251 := C h31 (T (T (T (T (T (C (T (T (T (T (C h31 (T (T (T (T (T (T h234 h250) h249) h248) h247) h246) h245)) (C h31 (T (T (T (T (T (T (T (T h244 h242) h241) h240) h239) h238) h235) h233) h231))) h208) h206) h196) (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h4 h90) h145) h144) h143) h142) h141) h140) h139) h133) h131) h130) h125) h123) h122) h173) h150) h172) h171)) h239) h238) h235) h233) h231)
  have h252 := S h233
  have h253 := C h31 (T h206 h196)
  have h254 := C h31 h224
  have h255 := S h226
  have h256 := C h217 h182
  have h257 := C h9 (T (C h9 (C (T (T h215 (C h182 (T (C h182 (T (C (S h216) h214) (C h182 h256))) (S h222)))) h218) h214)) (C h9 h228))
  have h258 := C h253 h31
  have h259 := C h31 (T (T (T (T (T h258 h213) h257) h255) h227) (C h31 (T (T h254 h253) h236)))
  have h260 := C (T (T (T (T h195 h211) h207) (C h31 (T (T (T (T (T (T (T (T h259 h252) h234) h250) h249) h248) h247) h246) h245))) (C h31 (T (T (T (T (T (T h244 h242) h241) h240) h239) h238) h235))) (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h161 h160) h151) h149) h148) h147) h124) h177) h176) h132) h175) h174) h138) h136) h103) h102) h97) h72) h5)
  have h261 := C h31 (T (T (T (T (T (T h254 (C h31 (T h207 (C h31 (T (T (T (T (T h259 h252) h234) h250) h249) h260))))) (S (h v232 v3 v3))) h234) h250) h249) h260)
  have h262 := h v192 v2 v3
  have h263 := h y z v0
  T (T (T (T (T (T (T (T (T h19 (C h23 (T (T (T (T (T (T (T (T (T h22 h80) h26) h263) (C h182 (T (T (T (T (T (h (M z (M v33 v0)) x z) (C h9 (T (C h9 (C (S h263) h182)) (C h9 h256)))) (S (h v221 x z))) (h v221 v3 z)) (C h31 (T (C h31 h219) (C h31 (T h190 (C (T (T (T h195 h211) h262) (C h40 (T (C h40 (T (T (T (T (T (T (T (T (T (T h258 h213) h257) h255) h227) h261) h251) h208) h262) (C h40 (C h40 (T (T (T (T (T (T (T (T (T h258 h213) h257) h255) h227) h261) h251) h208) h206) h196)))) (C h40 (C h169 h182)))) (S (h v170 v2 z))))) h194)))))) (S (h v170 v3 v2))))) (S h169)) h168) h167) h165) h163))) (S (h v44 v0 v3))) h45) h43) h103) h102) h97) h72) h5

