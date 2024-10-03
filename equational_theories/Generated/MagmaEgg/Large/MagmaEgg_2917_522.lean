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
theorem Equation2917_implies_Equation522 (G: Type _) [Magma G] (h: Equation2917 G) : Equation522 G := fun x y z =>
  let v0 := M x z
  let v1 := M z v0
  let v2 := M y v1
  have h3 := R v2
  have h4 := h y v1 v2
  have h5 := S h4
  have h6 := h x z v2
  have h7 := C h6 h3
  have h8 := h x y v2
  have h9 := S h8
  have h10 := h (M (M y (M x y)) v2) v2 x
  have h11 := R x
  let v12 := M y v2
  have h13 := h v1 v12 y
  have h14 := R y
  have h15 := C h14 (S h13)
  have h16 := C h15 h11
  let v17 := M (M v12 (M v1 v12)) y
  have h18 := h v17 y x
  have h19 := S h18
  have h20 := C h14 h13
  have h21 := C h20 h11
  have h22 := S h6
  let v23 := M v1 v2
  have h24 := h v23 v2 x
  have h25 := h v2 v12 y
  have h26 := S h25
  let v27 := M v2 v12
  let v28 := M v12 v27
  let v29 := M v28 y
  have h30 := h v29 y y
  have h31 := S h30
  have h32 := C h14 h25
  have h33 := h y v12 v12
  have h34 := R v12
  have h35 := C h34 (S h33)
  have h36 := C (T h35 (C h32 h14)) h14
  have h37 := C h34 h33
  have h38 := h y y v12
  have h39 := T (C h34 (S h38)) h37
  let v40 := M y (M y y)
  let v41 := M v40 v12
  have h42 := h v41 v12 y
  have h43 := h v41 v12 x
  have h44 := T h35 (C h34 h38)
  let v45 := M y v12
  let v46 := M v12 v45
  let v47 := M v46 v12
  have h48 := h v47 v12 x
  have h49 := h v47 v12 v1
  have h50 := R v1
  let v51 := M v12 y
  have h52 := h v51 v2 v12
  have h53 := S h52
  have h54 := h v51 y x
  have h55 := S h54
  have h56 := C h14 h26
  have h57 := C (T (C h56 h14) h37) h14
  have h58 := C (C (C h14 (T (T h30 h57) (C h35 h14))) h11) h11
  have h59 := h v28 y x
  have h60 := h v28 v12 v12
  have h61 := S h60
  have h62 := h (M v28 v12) v12 x
  have h63 := h v2 v12 v12
  have h64 := C h34 h63
  have h65 := h v2 y v12
  let v66 := M y (M v2 y)
  have h67 := h (M v66 v12) v12 x
  have h68 := h v66 x x
  have h69 := S h68
  have h70 := h (M v66 x) x x
  have h71 := h v2 y x
  have h72 := C h22 h3
  have h73 := h x x y
  have h74 := S h73
  have h75 := C h14 h74
  have h76 := C h14 h73
  have h77 := C (C (C h11 (T (T (C h76 h11) (C (T h75 (C (T (T h4 h72) (C h11 h71)) h11)) h11)) (S h70))) h11) h11
  let v78 := M y x
  have h79 := h v78 x x
  have h80 := C (C (C h34 (T (T (T (T (C h76 h34) (C (T (T (T h75 h79) h77) h69) h34)) h67) (C (C (T (C h34 (S h65)) h64) h11) h11)) (S h62))) h34) h34
  have h81 := h v78 v12 v12
  have h82 := S h79
  have h83 := C (C (C h11 (T (T h70 (C (T (C (T (T (C h11 (S h71)) h7) h5) h11) h76) h11)) (C h75 h11))) h11) h11
  have h84 := T (T (T (T (T (T (T (T (T h68 h83) h82) h81) h80) h61) h59) h58) h55) h37
  have h85 := h (M v66 v2) v2 x
  have h86 := S h85
  have h87 := h v2 y v2
  have h88 := h v2 v1 v2
  have h89 := C h3 (S h88)
  have h90 := C (C (T h89 (C h3 h87)) h11) h11
  let v91 := M v1 (M v2 v1)
  let v92 := M v91 v2
  have h93 := h v92 v2 x
  have h94 := h v92 v2 v2
  have h95 := C h3 h88
  have h96 := h v17 y v2
  have h97 := C (C (C h3 (T (T (T (T (T (T (C (T h96 (C (T (C h15 h3) h95) h3)) h3) (S h94)) h93) h90) h86) (C h84 h3)) (C h35 h3))) h34) h34
  have h98 := h v17 v2 v12
  have h99 := h v17 y v1
  have h100 := h v1 v1 v12
  have h101 := S h100
  have h102 := h (M (M v1 (M v1 v1)) v12) v12 x
  have h103 := h v1 y v12
  have h104 := C h34 (S h103)
  have h105 := C h34 h103
  have h106 := h v1 v0 v12
  let v107 := M v0 (M v1 v0)
  have h108 := h (M v107 v12) v12 x
  have h109 := h v107 y v12
  have h110 := h (M v107 y) y x
  have h111 := h v1 v0 y
  have h112 := S h98
  have h113 := S h81
  have h114 := C h34 (S h63)
  have h115 := C (C (C h34 (T (T (T (T h62 (C (C (T h114 (C h34 h65)) h11) h11)) (S h67)) (C (T (T (T h68 h83) h82) h76) h34)) (C h75 h34))) h34) h34
  have h116 := S h59
  have h117 := C (C (C h14 (T (T (C h37 h14) h36) h31)) h11) h11
  have h118 := T (T (T (T (T (T (T (T (T h35 h54) h117) h116) h60) h115) h113) h79) h77) h69
  have h119 := C (C (C h3 (T (T (T (T (T (T (C h37 h3) (C h118 h3)) h85) (C (C (T (C h3 (S h87)) h95) h11) h11)) (S h93)) h94) (C (T (C (T h89 (C h20 h3)) h3) (S h96)) h3))) h34) h34
  let v120 := M y v51
  have h121 := h v120 y x
  have h122 := h (M v120 y) y x
  have h123 := h v12 y y
  have h124 := h v12 v2 y
  have h125 := C h14 (S h124)
  let v126 := M v12 v2
  let v127 := M v2 v126
  have h128 := h (M v127 y) y x
  have h129 := S h128
  have h130 := C h14 h124
  have h131 := h v12 z y
  let v132 := M z (M v12 z)
  have h133 := h (M v132 y) y x
  have h134 := h v132 y x
  have h135 := h (M v132 v12) v12 x
  have h136 := h v12 z v12
  have h137 := C h34 h136
  have h138 := h v12 v2 v12
  have h139 := S h138
  have h140 := h (M v127 v12) v12 x
  have h141 := C h34 (S h136)
  have h142 := C (T (T (T (T (T h141 (C (T (T h138 (C (T (T (T h140 (C (C (T (C h34 h139) h137) h11) h11)) (S h135)) (C (T (T (T (T h134 (C (C (C h14 (T (T h133 (C (C (T (C h14 (S h131)) h130) h11) h11)) h129)) h11) h11)) (C (C (C h14 (T (T h128 (C (C (T h125 (C h14 h123)) h11) h11)) (S h122))) h11) h11)) (S h121)) (C h14 (T (T (T (T (T h52 h119) h112) h18) (C (T h16 (C (C h14 h111) h11)) h11)) (S h110)))) h34)) h34)) (S h109)) h34)) h108) (C (C (T (C h34 (S h106)) h105) h11) h11)) (C (C (T h104 (C h34 h100)) h11) h11)) (S h102)) h34
  have h143 := C (T (C h56 h34) h137) h34
  have h144 := h v29 y v12
  have h145 := h v29 y v2
  have h146 := C h3 (T (T (T (T (T (T (C h64 h3) (C (T h114 (C h32 h3)) h3)) (S h145)) h144) h143) h142) h101)
  have h147 := C (T (T (T (T (T (C (T h146 (C h20 h50)) h50) (S h99)) h98) h97) h53) h37) h50
  have h148 := h v126 v2 v1
  have h149 := h v126 v2 v12
  have h150 := S h149
  have h151 := S h144
  have h152 := C (T h141 (C h32 h34)) h34
  have h153 := C (T (T (T (T (T h102 (C (C (T (C h34 h101) h105) h11) h11)) (C (C (T h104 (C h34 h106)) h11) h11)) (S h108)) (C (T (T h109 (C (T (T (T (C (T (T (T (T (C h14 (T (T (T (T (T h110 (C (T (C (C h14 (S h111)) h11) h21) h11)) h19) h98) h97) h53)) h121) (C (C (C h14 (T (T h122 (C (C (T (C h14 (S h123)) h130) h11) h11)) h129)) h11) h11)) (C (C (C h14 (T (T h128 (C (C (T h125 (C h14 h131)) h11) h11)) (S h133))) h11) h11)) (S h134)) h34) h135) (C (C (T h141 (C h34 h138)) h11) h11)) (S h140)) h34)) h139) h34)) h137) h34
  have h154 := C h3 (T (T (T (T (T (T h100 h153) h152) h151) h145) (C (T (C h56 h3) h64) h3)) (C h114 h3))
  have h155 := h v1 x v2
  have h156 := C h3 (S h155)
  have h157 := C (C (T h156 h154) h34) h34
  let v158 := M (M x (M v1 x)) v2
  have h159 := h v158 v2 v12
  have h160 := C h50 (T (T (T (T (T (T (T (T (C (T (T (T h159 h157) h150) h64) h50) (C (T (T h114 h148) h147) h50)) (S h49)) h48) (C (C h44 h11) h11)) (S h43)) h42) (C (T (T (C h39 h14) h36) h31) h14)) h26)
  have h161 := C (T (C (T (T (T (T h160 h24) (C (T (C (T (C h3 h22) h21) h11) h19) h11)) (C (T h18 (C (T h16 (C h3 h8)) h11)) h11)) (S h10)) h3) h9) h3
  have h162 := h v158 v1 v2
  have h163 := h v158 v1 v12
  have h164 := S h163
  have h165 := S h159
  have h166 := C h3 h155
  have h167 := C (C (T h146 h166) h34) h34
  have h168 := S h148
  have h169 := C (T (T (T (T (T h35 h52) h119) h112) h99) (C (T (C h15 h50) h154) h50)) h50
  have h170 := C h50 (T (T (T (T (T (T (T (T h25 (C (T (T h30 h57) (C h44 h14)) h14)) (S h42)) h43) (C (C h39 h11) h11)) (S h48)) h49) (C (T (T h169 h168) h64) h50)) (C (T (T (T h114 h149) h167) h165) h50))
  have h171 := h v23 x x
  have h172 := h (M v23 x) x x
  have h173 := h y v1 x
  have h174 := h y v0 x
  have h175 := C h11 (S h174)
  have h176 := C h11 h174
  have h177 := h y v2 x
  have h178 := h (M v27 x) x x
  have h179 := h v27 x x
  have h180 := h v51 v1 y
  have h181 := S h180
  have h182 := S h162
  have h183 := C (T (T (T (T h10 (C (T (C (T (C h3 h9) h21) h11) h19) h11)) (C (T h18 (C (T h16 (C h3 h6)) h11)) h11)) (S h24)) h170) h3
  have h184 := C (T h8 h183) h3
  have h185 := h (M v1 y) y x
  have h186 := h x z y
  have h187 := h v2 v1 x
  have h188 := T (T (C h11 (S h187)) h7) h5
  have h189 := C (T (C h188 h11) h76) h11
  let v190 := M v91 x
  have h191 := h v190 x x
  have h192 := h v190 x v1
  have h193 := S h192
  have h194 := T (T h4 h72) (C h11 h187)
  have h195 := C (C h194 h50) h50
  have h196 := C (C h188 h50) h50
  have h197 := S h191
  have h198 := C (T h75 (C h194 h11)) h11
  have h199 := h x v12 y
  have h200 := T (C h14 (S h199)) h76
  let v201 := M (M v12 (M x v12)) y
  have h202 := h v201 y x
  have h203 := h v201 y y
  have h204 := T h75 (C h14 h199)
  have h205 := h (M (M x (M x x)) y) y y
  have h206 := C (T h73 (C (T (T (T (T (T (T (T h205 (C (C h204 h14) h14)) (S h203)) h202) (C (T (T (T (T (T (C h200 h11) h198) h197) h192) h196) h166) h11)) (C (T (T (T (T (T h156 h195) h193) h191) h189) (C (T h75 (C h14 h186)) h11)) h11)) (S h185)) (C h50 (T (T (T (T (T (T (T (T (T h4 h72) h184) h182) h159) h157) h150) h148) h147) (C h35 h50)))) h14)) h14
  have h207 := S h186
  have h208 := h y y v1
  have h209 := C h50 (S h208)
  have h210 := C (T (C h209 h14) h207) h14
  let v211 := M v40 v1
  have h212 := h v211 v1 y
  have h213 := h v211 v1 x
  have h214 := S h213
  have h215 := C h50 h208
  have h216 := h y v12 v1
  have h217 := C (C (T (C h50 (S h216)) h215) h11) h11
  let v218 := M v46 v1
  have h219 := h v218 v1 x
  have h220 := C h14 (T (T (T (T (T (T (C (T (T (T (T (T (T (T h219 h217) h214) h212) h210) h206) h181) h37) h14) h36) h31) h144) h143) h142) h101)
  have h221 := C (T (T (T (T (C h220 h34) h179) (C (C (C h11 (T (T (T h178 (C (C (T (C h11 (S h177)) h176) h11) h11)) (C (C (T h175 (C h11 h173)) h11) h11)) (S h172))) h11) h11)) (S h171)) h170) h34
  have h222 := h v218 y v12
  have h223 := S h219
  have h224 := C (C (T h209 (C h50 h216)) h11) h11
  have h225 := S h212
  have h226 := C (T h186 (C h215 h14)) h14
  have h227 := C (T (C (T (T (T (T (T (T (T (C h50 (T (T (T (T (T (T (T (T (T (C h37 h50) h169) h168) h149) h167) h165) h162) h161) h7) h5)) h185) (C (T (T (T (T (T (C (T (C h14 h207) h76) h11) h198) h197) h192) h196) h166) h11)) (C (T (T (T (T (T h156 h195) h193) h191) h189) (C h204 h11)) h11)) (S h202)) h203) (C (C h200 h14) h14)) (S h205)) h14) h74) h14
  have h228 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h68 h83) h82) h81) h80) h61) h59) h58) h55) h180) h227) h226) h225) h213) h224) h223) h222) h221) h34
  have h229 := C h118 h34
  have h230 := C h37 h34
  have h231 := C h34 (T (T (T (T (T (T (T h230 h229) h228) h164) h162) h161) h7) h5)
  have h232 := C (T (T (T (T (T (T (T (T (T h231 h180) h227) h226) h225) h213) h224) h223) h222) h221) h34
  have h233 := C h35 h34
  have h234 := C h84 h34
  have h235 := S h222
  have h236 := C (C h14 (T (T (T (T (T (T h100 h153) h152) h151) h30) h57) (C (T (T (T (T (T (T (T h35 h180) h227) h226) h225) h213) h224) h223) h14))) h34
  have h237 := S h179
  have h238 := C (C (C h11 (T (T (T h172 (C (C (T (C h11 (S h173)) h176) h11) h11)) (C (C (T h175 (C h11 h177)) h11) h11)) (S h178))) h11) h11
  have h239 := C (T (T (T (T h160 h171) h238) h237) h236) h34
  have h240 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h239 h235) h219) h217) h214) h212) h210) h206) h181) h54) h117) h116) h60) h115) h113) h79) h77) h69) h34
  have h241 := C h34 (T (T (T (T (T (T (T h4 h72) h184) h182) h163) h240) h234) h233)
  have h242 := h v51 v12 v12
  have h243 := S h242
  have h244 := C (T (T (T (T (T (T (T (T (T h239 h235) h219) h217) h214) h212) h210) h206) h181) h241) h34
  have h245 := C (T (T (T (T (T h4 h72) h184) h182) h163) h244) h34
  have h246 := C (T (T (T h125 h245) h243) h241) h34
  have h247 := C (T (T (T (T (T h232 h164) h162) h161) h7) h5) h34
  have h248 := C h34 (T (T (T (T (T h230 h229) h228) h244) (C (T (T (T h231 h242) h247) h130) h34)) (C h125 h34))
  T (T h8 h183) (C (T (T (T (T (T (T (T (T (T (T (T (T (T h160 h171) h238) h237) h236) (C (T (T (T (T (T (T (T h220 h88) (C (T (T (T h93 h90) h86) (C (T (T (T (T (T (T (T (T (T (T h68 h83) h82) h81) h80) h61) h59) h58) h55) h241) h248) h3)) h3)) (S (h v45 v12 v2))) h245) h243) h241) h248) h34)) (C (T (T (T (T (C h34 (T (T (T (T (T (C h130 h34) h246) h232) h240) h234) h233)) h231) h242) h247) h130) h34)) h246) h232) h164) h162) h161) h7) h5) h3)

