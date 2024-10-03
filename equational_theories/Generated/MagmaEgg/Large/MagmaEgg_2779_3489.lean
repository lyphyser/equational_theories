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
theorem Equation2779_implies_Equation3489 (G: Type _) [Magma G] (h: Equation2779 G) : Equation3489 G := fun x y z =>
  let v0 := M y z
  let v1 := M v0 z
  let v2 := M y v1
  have h3 := h v2 v2 v2
  have h4 := S h3
  have h5 := R v2
  let v6 := M v2 v2
  have h7 := h (M v6 v6) x v2
  have h8 := S h7
  have h9 := R x
  let v10 := M x x
  have h11 := h v2 v2 v10
  have h12 := S h11
  let v13 := M x v2
  have h14 := R v13
  have h15 := C (C h14 (T h12 h3)) h9
  let v16 := M v2 v10
  let v17 := M v16 v16
  have h18 := h v17 x v2
  have h19 := h v17 y v2
  have h20 := S h19
  let v21 := M v2 z
  have h22 := h y v21 v1
  have h23 := S h22
  have h24 := R v21
  have h25 := h v0 v2 z
  have h26 := C h25 h24
  have h27 := h (M v0 v21) x y
  have h28 := S h27
  have h29 := h v2 y z
  have h30 := h v2 y v1
  have h31 := S h30
  let v32 := M x y
  have h33 := R v32
  have h34 := C (C h33 (T h31 h29)) h9
  let v35 := M v2 v1
  let v36 := M v2 v35
  have h37 := h v36 x y
  have h38 := h v36 y y
  have h39 := S h38
  have h40 := h y y x
  have h41 := S h40
  have h42 := h v2 v0 z
  have h43 := S h42
  have h44 := R y
  let v45 := M v0 v0
  have h46 := h v36 v45 y
  have h47 := h v45 v2 y
  have h48 := S h47
  have h49 := h y y z
  let v50 := M v2 y
  have h51 := R v50
  have h52 := h y v1 z
  have h53 := S h52
  have h54 := C (C h5 h53) h40
  let v55 := M v1 z
  let v56 := M v55 v0
  have h57 := h v56 y v1
  have h58 := h v56 v0 v1
  have h59 := S h58
  have h60 := R v0
  let v61 := M v0 v1
  have h62 := R v61
  have h63 := h v0 y z
  have h64 := C (T h63 (C h62 h52)) h60
  have h65 := C (T (T (T (T h64 h59) h57) h54) (C h51 (T h41 h49))) h43
  have h66 := R v45
  have h67 := C (T (T (T (T (T (T (C (C h49 h30) (T (T (C h66 h42) h65) h48)) (S h46)) h37) h34) h28) h26) h23) h44
  have h68 := h v45 y v2
  have h69 := T h68 h67
  have h70 := S h63
  have h71 := C (T (C h62 h53) h70) h60
  have h72 := S h57
  have h73 := C (C h5 h52) h41
  have h74 := S h49
  have h75 := C (T (T (T (T (C h51 (T h74 h40)) h73) h72) h58) h71) h42
  have h76 := S h68
  have h77 := S h37
  have h78 := C (C h33 (T (S h29) h30)) h9
  have h79 := C (S h25) h24
  have h80 := C (T (T (T (T (T (T h22 h79) h27) h78) h77) h46) (C (C h74 h31) (T (T h47 h75) (C h66 h43)))) h44
  have h81 := C (T (T (T (T h80 h76) h47) h75) (C h69 (T h43 h30))) h41
  let v82 := M y y
  have h83 := R v82
  have h84 := C h83 h40
  have h85 := h y y v1
  have h86 := h y v2 v10
  have h87 := S h86
  have h88 := R v6
  have h89 := C (T (C h88 h87) (S h85)) h5
  let v90 := M y v10
  let v91 := M v16 v90
  have h92 := h v91 v2 v2
  have h93 := h v91 x v2
  have h94 := S h93
  have h95 := h y v2 y
  have h96 := h (M v50 v82) x v2
  have h97 := C h51 h40
  have h98 := C (T (T (T (T (T (C h51 (T (T (T (T (T (T h97 h73) h72) h58) h71) h68) h67)) h96) (C (C h14 (T (S h95) h86)) h9)) h94) h92) h89) h11
  have h99 := h v50 v2 y
  have h100 := C (T h99 h98) (T (T (T (T (T (T (T h84 h81) h39) h37) h34) h28) h26) h23)
  have h101 := C (T (T (T (T h100 h20) h18) h15) h8) h5
  have h102 := h v82 v2 y
  have h103 := C h51 (T (T (T (T (T (T (T (T h84 h81) h39) h37) h34) h28) h26) h23) h40)
  have h104 := C h83 h41
  have h105 := T h80 h76
  have h106 := C (T (T (T (T (C h105 (T h31 h42)) h65) h48) h68) h67) h40
  have h107 := C h51 h41
  have h108 := S h92
  have h109 := C (T h85 (C h88 h86)) h5
  have h110 := C (T (C (T (T (T (T (T h109 h108) h93) (C (C h14 (T h87 h95)) h9)) (S h96)) (C h51 (T (T (T (T (T (T h80 h76) h64) h59) h57) h54) h107))) h12) (S h99)) (T (T (T (T (T (T (T h22 h79) h27) h78) h77) h38) h106) h104)
  have h111 := h v50 z v1
  have h112 := S h111
  have h113 := R z
  have h114 := h v1 y v2
  have h115 := S h114
  have h116 := h v50 y y
  have h117 := h y x y
  have h118 := S h117
  have h119 := h (M v32 v82) x x
  have h120 := R v10
  have h121 := h y x v2
  let v122 := M y v2
  have h123 := h (M v13 v122) x x
  have h124 := h y v2 v1
  have h125 := h (M v35 v2) x v2
  have h126 := C (T (T (T (C h14 (T (T (T (T h125 (C (C h14 (T (S h124) h86)) h9)) h94) h92) h89)) h123) (C (T (C h120 (S h121)) (C h120 h117)) h9)) (S h119)) h9
  have h127 := h v35 x v2
  have h128 := R v1
  have h129 := S h18
  have h130 := C (C h14 (T h4 h11)) h9
  have h131 := C h51 (T (T (T (T (T (T (T (T h41 h22) h79) h27) h78) h77) h38) h106) h104)
  have h132 := h (M v45 v45) x v0
  have h133 := h v0 v0 v0
  have h134 := h v0 v0 v10
  have h135 := S h134
  have h136 := R (M x v0)
  have h137 := h v0 v0 z
  have h138 := S h137
  let v139 := M v1 v1
  have h140 := h v139 x v0
  have h141 := h v82 v1 v1
  have h142 := S h102
  have h143 := C (T (T (T (T h7 h130) h129) h19) h110) h5
  have h144 := T (T (T (T (T h3 h143) h142) h141) (C (T (C (T (T (T (T h140 (C (C h136 (T h138 h134)) h9)) (C (C h136 (T h135 h133)) h9)) (S h132)) (C h69 (T (T (T (T h64 h59) h57) h54) h107))) (T (T (T (T (T (C h83 h114) (C (T (T (T (T (T (T (T (T (T (T (T h80 h76) h64) h59) h57) h54) h131) h100) h20) h18) h15) h8) h115)) (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T h7 h130) h129) h19) h110) h103) h73) h72) h58) h71) h68) h67) h102) h101) h4) h128)) h127) h126) h118)) (S h116)) h114)) (C h51 h115)
  let v145 := M z v1
  have h146 := R v145
  have h147 := C h146 h144
  have h148 := h (M v145 v2) x z
  have h149 := S h148
  have h150 := h y z v1
  have h151 := h y z v2
  have h152 := S h151
  let v153 := M x z
  have h154 := R v153
  have h155 := C (C h154 (T h152 h150)) h9
  let v156 := M (M z v2) v122
  have h157 := h v156 x z
  have h158 := h v156 v2 v1
  have h159 := S h158
  have h160 := h v156 v0 z
  have h161 := h v61 v1 y
  have h162 := h v0 v1 z
  have h163 := S h162
  have h164 := R v139
  let v165 := M v55 v1
  have h166 := h v165 v1 v1
  have h167 := h v165 y v1
  have h168 := S h127
  have h169 := C (T (T (T h119 (C (T (C h120 h118) (C h120 h121)) h9)) (S h123)) (C h14 (T (T (T (T h109 h108) h93) (C (C h14 (T h87 h124)) h9)) (S h125)))) h9
  have h170 := S h157
  have h171 := C (C h154 (T (S h150) h151)) h9
  have h172 := T (T (T (T (T (C h51 h114) (C (T h116 (C (T (T (T (T (C h105 (T (T (T (T h97 h73) h72) h58) h71)) h132) (C (C h136 (T (S h133) h134)) h9)) (C (C h136 (T h135 h137)) h9)) (S h140)) (T (T (T (T (T h117 h169) h168) (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T h3 h143) h142) h80) h76) h64) h59) h57) h54) h131) h100) h20) h18) h15) h8) h128)) (C (T (T (T (T (T (T (T (T (T (T (T h7 h130) h129) h19) h110) h103) h73) h72) h58) h71) h68) h67) h114)) (C h83 h115)))) h115)) (S h141)) h102) h101) h4
  have h173 := C h146 h172
  have h174 := C (T (T (T h173 h148) h171) h170) h113
  have h175 := C (C (T (T (T (T (T h111 h174) h152) h117) h169) h168) (T (T (T (T (T (C (C h5 h162) h44) (S h167)) h166) (C (T (C h164 h163) h138) h128)) h161) (C (T (C (C h128 h151) h70) (S h160)) h128))) h5
  let v176 := M v2 v0
  have h177 := h v176 v2 y
  have h178 := h v176 v2 v0
  have h179 := h v176 v1 z
  have h180 := h z v0 v0
  have h181 := S h180
  have h182 := R v176
  have h183 := C h5 h163
  have h184 := S h166
  have h185 := C (T h137 (C h164 h162)) h128
  have h186 := C (T (T (T h157 h155) h149) h147) h113
  have h187 := h v55 x v0
  have h188 := h v0 x v0
  let v189 := M v122 (M v1 v2)
  have h190 := h v189 v0 y
  have h191 := h v189 v61 y
  have h192 := h (M v61 v61) x v0
  have h193 := h v0 v0 v1
  let v194 := M v0 v10
  let v195 := M v194 v194
  have h196 := h v195 x v0
  have h197 := h v195 v1 v0
  have h198 := R (M v1 v0)
  have h199 := h y v0 z
  let v200 := M v1 v21
  have h201 := h v200 v2 v0
  have h202 := h v200 x v0
  have h203 := S h202
  have h204 := h v2 v0 v10
  have h205 := C (C h136 (T (S h204) h42)) h9
  have h206 := h (M v194 v16) x v0
  have h207 := C (T (T (T (T (T (T (T (T (T (T (T (T h206 h205) h203) h201) (C (C h182 (T (T (T (T (T (T (T (T (T h43 (C (T h199 (C h198 h134)) h128)) (S h197)) h196) (C (C h136 (T h135 h193)) h9)) (S h192)) (C (C h63 h114) h62)) (S h191)) h190) (C (T (C (T (C h63 (T (T h151 h186) h112)) (C (T (T (T h70 h188) (C (C h136 (T h64 h59)) h9)) (S h187)) (T (T h111 (C (T (T (T (T (T (T h173 h148) h171) h170) h158) (C (C (T (T (T (T (T h127 h126) h118) h151) h186) h112) (T (T (T (T (T (C (T h160 (C (C h128 h152) h63)) h128) (S h161)) h185) h184) h167) (C h183 h44))) h5)) (S h177)) h180)) (C h182 h181)))) h115) (S h179)) h60))) h5)) (S h178)) h177) h175) h159) h157) h155) h149) h147) h113
  have h208 := S h206
  have h209 := C (C h136 (T h43 h204)) h9
  have h210 := h v2 v0 v1
  have h211 := h (M v61 v35) x v0
  have h212 := h v2 v0 x
  have h213 := h (M (M v0 x) (M v2 x)) x v0
  have h214 := h v2 v0 y
  have h215 := h (M (M v0 y) v50) x v0
  have h216 := h v2 v0 v0
  have h217 := h (M v45 v176) x v0
  have h218 := h v2 v0 v2
  have h219 := h (M (M v0 v2) v6) x v0
  have h220 := h v50 v0 v1
  have h221 := h (M v61 v2) x v0
  have h222 := h y v0 v1
  have h223 := h y v0 v10
  have h224 := S h223
  let v225 := M v194 v90
  have h226 := h v225 x v0
  have h227 := h v225 v0 v0
  have h228 := R (M y v0)
  have h229 := h v0 y v10
  let v230 := M v90 v194
  have h231 := C (T (T (T (T (T h63 (C (T (T (T (T (T (T (h v61 v10 y) (C (C (R (M v10 y)) (T h70 h229)) h120)) (S (h v230 v10 y))) (h v230 x y)) (C (C h33 (T (S h229) (h v0 y v1))) h9)) (S (h (M v2 v61) x y))) (C (T (T h3 h143) h142) (T (T (T (T (T (T (T (T (T (T h185 h184) h167) (C h183 (T (T (T (T (T h151 h186) h112) h220) (C (T (T (T (T (T (C h62 h172) h221) (C (C h136 (T (S h222) h223)) h9)) (S h226)) h227) (C (T (C h66 h224) h74) h60)) h134)) (C h228 h135)))) (C (T (T (T (T (T h178 (C (C h182 (T (T (T (T (T (T (T (T (T (C (T h179 (C (T (C (T (T (T h187 (C (C h136 (T h58 h71)) h9)) (S h188)) h63) (T (T (C h182 h180) (C (T (T (T (T (T (T h177 h175) h159) h157) h155) h149) h147) h181)) h112)) (C h70 (T (T h111 h174) h152))) h114)) h60) (S h190)) h191) (C (C h70 h115) h62)) h192) (C (C h136 (T (S h193) h134)) h9)) (S h196)) h197) (C (T (C h198 h135) (S h199)) h128)) h42)) h5)) (S h201)) h202) h209) h208) (T (T (T (T (T (C h228 h134) (C (T (T (T (T (T (C (T h49 (C h66 h223)) h60) (S h227)) h226) (C (C h136 (T h224 h222)) h9)) (S h221)) (C h62 h144)) h135)) (S h220)) h111) h174) h152))) (C (T (T (T h206 h205) (C (C h136 (T h43 h218)) h9)) (S h219)) h44)) (C (T (T (T h219 (C (C h136 (T (S h218) h42)) h9)) (C (C h136 (T h43 h216)) h9)) (S h217)) h44)) (C (T (T (T h217 (C (C h136 (T (S h216) h42)) h9)) (C (C h136 (T h43 h214)) h9)) (S h215)) h44)) (C (T (T (T h215 (C (C h136 (T (S h214) h42)) h9)) (C (C h136 (T h43 h212)) h9)) (S h213)) h44)) (C (T (T (T h213 (C (C h136 (T (S h212) h42)) h9)) (C (C h136 (T h43 h210)) h9)) (S h211)) h44)) (C (T (T h211 (C (C h136 (T (S h210) h42)) h9)) h203) h44)))) h44)) (S (h v200 y y))) h202) h209) h208) h113
  have h232 := h v1 x z
  have h233 := h v10 v1 y
  let v234 := M v10 x
  have h235 := h x x x
  have h236 := S h235
  let v237 := M v10 v10
  have h238 := h v237 x x
  have h239 := h v10 v10 v2
  have h240 := R v237
  have h241 := h v10 v1 x
  let v242 := M (M v1 x) v234
  T (T (T (T (T (T (T (T (T (T (T (T (T h241 (C (R v242) (T (T (T h231 h207) h174) h152))) (C (T (T (T (T (T (T (T (h v242 x v1) (C (T (T (C (R (M x v1)) (T (S h241) h233)) (C (C (T (T (h x v10 x) (C (C (R v234) (T (T (T (T (h v10 v10 v10) (C (C h240 (T (T (h v237 v10 x) (C (T (C (C h120 h235) h236) (S h238)) h239)) (C h240 (S h239)))) h120)) (S (h v237 v10 v10))) h238) (C (C h120 h236) h9))) h120)) (S (h v234 v10 x))) h232) (S h233))) (S (h (M v153 v55) v10 x))) h9)) (S h232)) h231) h207) h112) h99) h98) h44)) h110) h103) h73) h72) h58) h71) h68) h67) h102) h101) h4

