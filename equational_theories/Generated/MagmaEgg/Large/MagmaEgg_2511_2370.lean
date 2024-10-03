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
theorem Equation2511_implies_Equation2370 (G: Type _) [Magma G] (h: Equation2511 G) : Equation2370 G := fun x y z =>
  let v0 := M x y
  let v1 := M z v0
  let v2 := M y v1
  let v3 := M v2 z
  have h4 := h v3 v1 z
  have h5 := S h4
  have h6 := R z
  have h7 := h (M v1 (M (M v3 v1) z)) z x
  have h8 := R x
  have h9 := h (M z (M v3 x)) x x
  have h10 := h v2 z x
  have h11 := h v2 v3 x
  have h12 := S h11
  have h13 := C h12 h8
  let v14 := M v2 v3
  let v15 := M v3 (M v14 x)
  have h16 := h v15 x x
  have h17 := h v15 x z
  have h18 := S h17
  have h19 := h v1 v3 z
  have h20 := h y v1 z
  have h21 := R v3
  have h22 := T (C (C h21 h20) h6) (S h19)
  have h23 := R y
  have h24 := C h23 h22
  have h25 := h v3 y z
  have h26 := C (C h8 (T h25 (C (T h24 h11) h6))) h6
  have h27 := C (T (C (T (T (T (T (T h26 h18) h16) (C (C h8 (T h13 (C h10 h8))) h8)) (S h9)) (C h6 (C h4 h8))) h8) (S h7)) h6
  let v28 := M x v3
  let v29 := M v28 z
  have h30 := h (M v29 x) v0 x
  have h31 := R v0
  have h32 := S h25
  have h33 := S h20
  have h34 := T h19 (C (C h21 h33) h6)
  have h35 := C h23 h34
  have h36 := C (C h8 (T (C (T h12 h35) h6) h32)) h6
  have h37 := S h16
  have h38 := C h11 h8
  have h39 := h v2 y x
  have h40 := h (M y (M (M v2 y) x)) x x
  have h41 := h v2 v0 v3
  have h42 := S h41
  let v43 := M v2 v0
  let v44 := M v0 (M v43 v3)
  have h45 := h v44 v3 x
  have h46 := h v2 v2 v3
  let v47 := M v2 v2
  have h48 := h (M v2 (M v47 v3)) v3 x
  have h49 := h v47 v1 v2
  have h50 := R v2
  have h51 := R v1
  have h52 := h y z v2
  have h53 := S h52
  let v54 := M z (M (M y z) v2)
  have h55 := h v54 v2 v1
  have h56 := h v54 v2 x
  have h57 := h y v2 v2
  have h58 := h (M v2 (M (M y v2) v2)) v2 x
  have h59 := h y y x
  have h60 := S h59
  have h61 := h (M y (M (M y y) x)) x x
  have h62 := C h59 h8
  have h63 := h (M y x) v0 v3
  have h64 := S h63
  have h65 := h x z v3
  have h66 := S h65
  have h67 := h (M z (M (M x z) v3)) v3 x
  have h68 := h x y v3
  let v69 := M v0 v3
  have h70 := h (M y v69) v3 x
  let v71 := M v1 v3
  have h72 := h v0 v71 v3
  have h73 := S h72
  have h74 := h z v0 v3
  have h75 := R v71
  have h76 := C (T h20 (C h75 h74)) h21
  have h77 := h (M y v3) z y
  have h78 := S h77
  have h79 := h v2 v3 y
  have h80 := S h79
  have h81 := h (M v3 (M v14 y)) y z
  have h82 := h (M z v2) v3 x
  have h83 := S h82
  have h84 := h v44 v3 z
  have h85 := h (M v3 v3) z v3
  have h86 := C (C h21 (C (T h85 (C (C h6 (T (C (T (C (C h21 (T h25 (C (T h24 h41) h6))) h6) (S h84)) h21) h42)) h21)) h8)) h8
  have h87 := h v3 v3 x
  have h88 := C (T (T (T h87 h86) h83) (C h6 (T h79 (C (T h81 (C (C h23 (T (C (T h80 h35) h6) h32)) h6)) h23)))) h23
  have h89 := h (M v3 y) z z
  have h90 := S h89
  have h91 := h v1 v2 z
  have h92 := S h91
  have h93 := C (C h6 (T (C h92 h6) (C h34 h6))) h6
  let v94 := M v2 (M (M v1 v2) z)
  have h95 := h v94 z z
  have h96 := h v94 z x
  have h97 := S h96
  have h98 := h v1 v0 z
  have h99 := C (C h6 (T (C (S h98) h8) (C h91 h8))) h8
  let v100 := M v0 (M (M v1 v0) z)
  have h101 := h v100 z x
  have h102 := h v100 y y
  have h103 := S h101
  have h104 := C (C h6 (T (C h92 h8) (C h98 h8))) h8
  have h105 := S h95
  have h106 := C (C h6 (T (C h22 h6) (C h91 h6))) h6
  have h107 := S h87
  have h108 := C (C h21 (C (T (C (C h6 (T h41 (C (T h84 (C (C h21 (T (C (T h42 h35) h6) h32)) h6)) h21))) h21) (S h85)) h8)) h8
  have h109 := C (T (T (T (C h6 (T (C (T (C (C h23 (T h25 (C (T h24 h79) h6))) h6) (S h81)) h23) h80)) h82) h108) h107) h23
  have h110 := C (T (C h75 (S h74)) h33) h21
  have h111 := C (T (T (T (T (T (T (T (T (T h72 h110) h77) h109) h89) h106) h105) h96) h104) h103) h23
  have h112 := C h23 (C h111 h23)
  let v113 := M v0 y
  have h114 := h (M y (M v113 y)) y x
  have h115 := S h114
  have h116 := h v0 y y
  let v117 := M v0 x
  have h118 := h (M y v117) x x
  have h119 := S h118
  have h120 := h x y x
  have h121 := h x v2 x
  have h122 := S h121
  have h123 := C (C h8 (T (C h122 h8) (C h120 h8))) h8
  let v124 := M x v2
  let v125 := M v2 (M v124 x)
  have h126 := h v125 x x
  have h127 := h v125 x y
  have h128 := S h127
  have h129 := C (C h8 (C h121 h23)) h23
  have h130 := C (T (T (T (T (T h129 h128) h126) h123) h119) (C h23 (C h116 h8))) h8
  have h131 := C (T (T h130 h115) h112) h23
  have h132 := T (T (T (T (T (T (T (T (T (T (T h131 (S h102)) h101) h99) h97) h95) h93) h90) h88) h78) h76) h73
  have h133 := C (T (T (T (C h23 (C h132 h21)) h70) (C (C h21 (T (C (S h68) h8) (C h65 h8))) h8)) (S h67)) h21
  let v134 := M x v0
  have h135 := h (M (M v134 y) x) y v3
  have h136 := C (C h8 (C h122 h23)) h23
  have h137 := S h126
  have h138 := C (C h8 (T (C (S h120) h8) (C h121 h8))) h8
  have h139 := h v0 v2 y
  have h140 := C (T (T (T (T (T (C h23 (C (S h139) h8)) h118) h138) h137) h127) h136) h8
  let v141 := M v0 v2
  let v142 := M v2 (M v141 y)
  have h143 := h v142 y x
  have h144 := h v142 x v0
  have h145 := S h143
  have h146 := C (T (T (T (T (T h129 h128) h126) h123) h119) (C h23 (C h139 h8))) h8
  have h147 := S h135
  have h148 := C (T (T (T (T (T (C h23 (C (S h116) h8)) h118) h138) h137) h127) h136) h8
  have h149 := C (T (T (T (T (T (T (T (T (T h101 h99) h97) h95) h93) h90) h88) h78) h76) h73) h23
  have h150 := C h23 (C h149 h23)
  have h151 := C (T (T h150 h114) h148) h23
  have h152 := T (T (T (T (T (T (T (T (T (T (T h72 h110) h77) h109) h89) h106) h105) h96) h104) h103) h102) h151
  have h153 := C (T (T (T h67 (C (C h21 (T (C h66 h8) (C h68 h8))) h8)) (S h70)) (C h23 (C h152 h21))) h21
  have h154 := h (M x (M (M x x) v0)) v0 x
  have h155 := h x x v0
  have h156 := h x y v0
  have h157 := S h156
  let v158 := M v0 v0
  let v159 := M y v158
  have h160 := h v159 v0 x
  have h161 := h v159 v0 y
  have h162 := h v158 y v0
  have h163 := C h31 (C (T h162 (C (C h23 (T (T (T (T (T (T (C (T (T (T (T (T (C (C h31 (C h156 h23)) h23) (S h161)) h160) (C (C h31 (T (C h157 h8) (C h155 h8))) h8)) (S h154)) (C h8 (C (C (T (T (T (T h65 h153) h147) h146) h145) h8) h31))) h31) (S h144)) h143) h140) h135) h133) h66)) h31)) h21)
  have h164 := h (M v0 (M v158 v3)) v3 x
  have h165 := S h164
  have h166 := h v0 v0 v3
  have h167 := h v0 v1 v3
  have h168 := C (S h167) h8
  have h169 := C (C h21 (T h168 (C h166 h8))) h8
  have h170 := C h167 h8
  have h171 := h v0 y v3
  have h172 := h (M y (M v113 v3)) v3 x
  have h173 := C (T (T (T (T (T (C h23 (C h149 h21)) h172) (C (C h21 (T (C (S h171) h8) h170)) h8)) h169) h165) h163) h21
  have h174 := h v100 y v3
  have h175 := C h8 (T (T (T (T (T (T (T (T (T (T (T (T (T h72 h110) h77) h109) h89) h106) h105) h96) h104) h103) h174) h173) h64) h62)
  have h176 := C h175 h8
  have h177 := C (T h176 (S h61)) h8
  have h178 := S h174
  have h179 := C (C h21 (T (C (S h166) h8) h170)) h8
  have h180 := C h31 (C (T (C (C h23 (T (T (T (T (T (T h65 h153) h147) h146) h145) h144) (C (T (T (T (T (T (C h8 (C (C (T (T (T (T h143 h140) h135) h133) h66) h8) h31)) h154) (C (C h31 (T (C (S h155) h8) (C h156 h8))) h8)) (S h160)) h161) (C (C h31 (C h157 h23)) h23)) h31))) h31) (S h162)) h21)
  have h181 := C (T (T (T (T (T h180 h164) h179) (C (C h21 (T h168 (C h171 h8))) h8)) (S h172)) (C h23 (C h111 h21))) h21
  have h182 := C h60 h8
  have h183 := C h8 (T (T (T (T (T (T (T (T (T (T (T (T (T h182 h63) h181) h178) h101) h99) h97) h95) h93) h90) h88) h78) h76) h73)
  have h184 := C h183 h8
  have h185 := h v134 x x
  have h186 := S h185
  have h187 := C (T h61 h184) h8
  have h188 := C (T h131 (C (T (T (T (T (T h150 h114) h148) h135) h133) h66) (T h59 h187))) h8
  have h189 := C h152 h8
  have h190 := C (T (C (T (T (T h189 h188) h186) h175) h8) h184) h8
  let v191 := M v117 x
  have h192 := h v191 x v3
  have h193 := C h132 h8
  have h194 := C (T (C (T (T (T (T (T h65 h153) h147) h130) h115) h112) (T h177 h60)) h151) h8
  have h195 := C (T h176 (C (T (T (T h183 h185) h194) h193) h8)) h8
  have h196 := T (C (T (T (T (T h189 h188) h186) h175) (C h8 (T (T (T (T (T (T (T (T (T (T (T (T h182 h63) h181) h178) h101) h99) h97) h95) h93) h90) h88) h78) (C (T (T h59 h187) h195) h21)))) h21) (S h192)
  have h197 := C h196 h8
  have h198 := T h192 (C (T (T (T (T (C h8 (T (T (T (T (T (T (T (T (T (T (T (T (C (T (T h190 h177) h60) h21) h77) h109) h89) h106) h105) h96) h104) h103) h174) h173) h64) h62)) h183) h185) h194) h193) h21)
  have h199 := C h198 h8
  have h200 := h v0 v3 v3
  have h201 := C (C h21 (T (C (S h200) h8) h170)) h8
  let v202 := M v3 (M v69 v3)
  have h203 := h v202 v3 x
  have h204 := h v202 x z
  have h205 := S h203
  have h206 := C (C h21 (T h168 (C h200 h8))) h8
  have h207 := h v0 x v3
  have h208 := h (M x (M v117 v3)) v3 x
  have h209 := h (M x v191) x x
  have h210 := h v0 x x
  have h211 := h v0 v2 x
  have h212 := S h211
  have h213 := h (M v2 (M v141 x)) x x
  have h214 := h (M v0 z) v1 x
  have h215 := h z v0 v1
  have h216 := S h215
  let v217 := M v1 v1
  have h218 := h (M v0 v217) v1 v0
  have h219 := h v217 v0 v1
  have h220 := h v1 v1 x
  have h221 := C h8 (T (T (T h220 (C (C h51 (C (T h219 (C (C h31 (T (C (T (C (C h51 (C h215 h31)) h31) (S h218)) h51) h216)) h51)) h8)) h8)) (S h214)) (C (T h211 (C (T (T (T (T (T (T (T h213 (C (C h8 (T (C h212 h8) (C h210 h8))) h8)) (S h209)) (C h8 h198)) h208) (C (C h21 (T (C (S h207) h8) h170)) h8)) h206) h205) h8)) h6))
  have h222 := C h221 h6
  let v223 := M x v1
  have h224 := h v223 z v3
  have h225 := C h8 (T (T (T (C (T (C (T (T (T (T (T (T (T h203 h201) (C (C h21 (T h168 (C h207 h8))) h8)) (S h208)) (C h8 h196)) h209) (C (C h8 (T (C (S h210) h8) (C h211 h8))) h8)) (S h213)) h8) h212) h6) h214) (C (C h51 (C (T (C (C h31 (T h215 (C (T h218 (C (C h51 (C h216 h31)) h31)) h51))) h51) (S h219)) h8)) h8)) (S h220))
  have h226 := C (T (T h225 h224) (C (C h6 (T (T (T (T (T (T (T (T (T (T (T (T (C (T (T (T (T (T (T h222 (S h204)) h203) h201) h169) h165) h163) h21) h181) h178) h101) h99) h97) h95) h93) h90) h88) h78) h76) h73)) h21)) h6
  let v227 := M v223 z
  have h228 := h v227 v2 v2
  have h229 := C h225 h6
  have h230 := C (T (T (C (C h6 (T (T (T (T (T (T (T (T (T (T (T (T h72 h110) h77) h109) h89) h106) h105) h96) h104) h103) h174) h173) (C (T (T (T (T (T (T h180 h164) h179) h206) h205) h204) h229) h21))) h21) (S h224)) h221) h6
  have h231 := C (T (T (T (C h50 (C (T (C (C h51 (T (T (T (T h20 h230) h229) h228) (C (T (T (T (T (T (C h50 (C (T (T (C (T (T (T (T (T h222 h226) h33) h59) h187) h195) h50) (C h199 h50)) (C (T (T (T h197 h190) h177) h60) h50)) h50)) h58) (C (C h50 (T (C (S h57) h8) (C h52 h8))) h8)) (S h56)) h55) (C (C h50 (T (C h53 h34) h24)) h51)) h50))) h50) (S h49)) h21)) h48) (C (C h21 (T (C (S h46) h8) (C h41 h8))) h8)) (S h45)) h21
  have h232 := h (M v1 y) v2 v3
  have h233 := h x v2 z
  have h234 := S h233
  have h235 := C (C h6 (C h234 h23)) h23
  let v236 := M v2 (M v124 z)
  have h237 := h v236 z y
  have h238 := h v236 z x
  have h239 := S h238
  have h240 := h x v1 z
  have h241 := C (C h6 (T (C (S h240) h8) (C h233 h8))) h8
  let v242 := M v1 v227
  have h243 := h v242 z x
  have h244 := C (T (T (T (T (T (C h23 (C (C (T (T (T (T (T (T (T h243 h241) h239) h237) h235) h232) h231) h42) h23) h8)) h40) (C (C h8 (T (C (S h39) h8) h38)) h8)) h37) h17) h36) h8
  have h245 := h v242 y x
  have h246 := S h243
  have h247 := C (C h6 (T (C h234 h8) (C h240 h8))) h8
  have h248 := S h237
  have h249 := C (C h6 (C h233 h23)) h23
  have h250 := S h232
  have h251 := C (T (T (T h45 (C (C h21 (T (C h42 h8) (C h46 h8))) h8)) (S h48)) (C h50 (C (T h49 (C (C h51 (T (T (T (T (C (T (T (T (T (T (C (C h50 (T h35 (C h52 h22))) h51) (S h55)) h56) (C (C h50 (T (C h53 h8) (C h57 h8))) h8)) (S h58)) (C h50 (C (T (T (C (T (T (T h59 h187) h195) h199) h50) (C h197 h50)) (C (T (T (T (T (T h190 h177) h60) h20) h230) h229) h50)) h50))) h50) (S h228)) h222) h226) h33)) h50)) h21))) h21
  have h252 := T (T (T (T (T (T (T (T (T h41 h251) h250) h249) h248) h238) h247) h246) h245) h244
  have h253 := h (M v0 (M v43 x)) x x
  have h254 := h v2 v0 x
  have h255 := h v29 x z
  have h256 := C (T h7 (C (T (T (T (T (T (C h6 (C h5 h8)) h9) (C (C h8 (T (C (S h10) h8) h38)) h8)) h37) h17) h36) h8)) h6
  have h257 := T h4 h256
  have h258 := h v28 z x
  have h259 := T h27 h5
  have h260 := T (T (T (T (T (T (T (T (T (C (T (T (T (T (T h26 h18) h16) (C (C h8 (T h13 (C h39 h8))) h8)) (S h40)) (C h23 (C (C (T (T (T (T (T (T (T h41 h251) h250) h249) h248) h238) h247) h246) h23) h8))) h8) (S h245)) h243) h241) h239) h237) h235) h232) h231) h42
  T (T (T (T h240 (C (T (T (T h245 h244) h30) (C (T (T (T (T (T (T (T (C h31 (C (C h260 h31) h8)) h253) (C (C h8 (T (C (S h254) h8) h38)) h8)) h37) h17) h36) h255) (C (T (T (T (C h8 h259) h258) (C (T (T (T (T (T (C h6 h260) h82) h108) h107) h4) h256) h8)) (C h259 h8)) h6)) h8)) h6)) (C (T (C (T (T (T (T (T (T (T (C (T (T (T (C h257 h8) (C (T (T (T (T (T h27 h5) h87) h86) h83) (C h6 h252)) h8)) (S h258)) (C h8 h257)) h6) (S h255)) h26) h18) h16) (C (C h8 (T h13 (C h254 h8))) h8)) (S h253)) (C h31 (C (C h252 h31) h8))) h8) (S h30)) h6)) h27) h5

