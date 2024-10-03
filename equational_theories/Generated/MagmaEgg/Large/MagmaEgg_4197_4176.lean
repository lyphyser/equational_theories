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
theorem Equation4197_implies_Equation4176 (G: Type _) [Magma G] (h: Equation4197 G) : Equation4176 G := fun x y z =>
  let v0 := M y z
  let v1 := M v0 x
  have h2 := R x
  let v3 := M v1 z
  let v4 := M x v1
  have h5 := R v3
  have h6 := R z
  have h7 := h x v1 x
  have h8 := S h7
  have h9 := R v1
  have h10 := h x x v0
  have h11 := C (S h10) h9
  have h12 := h x v0 v1
  have h13 := C (T h12 h11) h2
  have h14 := T h13 h8
  have h15 := S h12
  have h16 := C h10 h9
  have h17 := C (T h16 h15) h2
  have h18 := h x v0 z
  have h19 := S h18
  have h20 := R v0
  have h21 := h z x y
  have h22 := S h21
  have h23 := h x y v0
  have h24 := C (T h23 (C h22 h20)) h6
  have h25 := C (T (T (T h24 h19) h12) h11) h2
  have h26 := h y z x
  have h27 := T (T h26 h25) h17
  have h28 := C h5 h27
  have h29 := h v3 v0 v0
  have h30 := h y z v0
  have h31 := S h30
  have h32 := h v0 y v0
  have h33 := S h32
  have h34 := h z v0 y
  have h35 := C h34 h20
  have h36 := C (T h35 h33) h6
  have h37 := h v0 v0 z
  have h38 := h v0 v0 y
  have h39 := S h38
  have h40 := R y
  have h41 := h y v0 v1
  have h42 := S h41
  have h43 := C h23 h9
  have h44 := C (T h43 h42) h20
  let v45 := M x y
  have h46 := h v45 v1 v0
  have h47 := S h46
  have h48 := R v45
  have h49 := S h26
  have h50 := h z x v45
  have h51 := C (T (T h22 h50) (C h49 h48)) h9
  have h52 := h z x v0
  have h53 := S h52
  have h54 := S h23
  have h55 := C (T (C h21 h20) h54) h6
  have h56 := C (T (T (T h16 h15) h18) h55) h2
  have h57 := T (T h13 h56) h49
  have h58 := h v0 x z
  have h59 := S h58
  have h60 := h (M (M z v0) x) z v3
  have h61 := S h60
  have h62 := h z v0 v1
  have h63 := S h62
  have h64 := h x z v0
  have h65 := C h64 h9
  have h66 := C (T h65 h63) h2
  have h67 := h z v1 x
  have h68 := T h67 h66
  have h69 := C (C (C h5 h68) h6) h5
  let v70 := M z v1
  have h71 := h v70 z v3
  have h72 := T (T (T h71 h69) h61) h59
  have h73 := C h2 h72
  have h74 := C (T (T (T h73 h7) h56) h49) h6
  let v75 := M v70 z
  have h76 := h v75 z x
  have h77 := h v1 z z
  have h78 := C (T (T h77 h76) (C h74 h2)) h57
  have h79 := C (T (T (T (T h64 h28) h78) h53) h21) h9
  have h80 := S h64
  have h81 := C h80 h9
  have h82 := S h34
  have h83 := S h37
  have h84 := C h82 h20
  have h85 := C (T h32 h84) h6
  have h86 := h (M v0 y) z v3
  have h87 := C h5 h57
  have h88 := S h77
  have h89 := S h71
  have h90 := S h67
  have h91 := C (T h62 h81) h2
  have h92 := T h91 h90
  have h93 := C (C (C h5 h92) h6) h5
  have h94 := T (T (T h58 h60) h93) h89
  have h95 := C h2 h94
  have h96 := C (T (T (T h26 h25) h8) h95) h6
  have h97 := C (T (T (C h96 h2) (S h76)) h88) h27
  have h98 := C (T (T (T (T h22 h52) h97) h87) h80) h9
  have h99 := C (T (T (C h26 h48) (S h50)) h21) h9
  have h100 := C (T (T (T h99 h98) h65) h63) h20
  have h101 := h (M v45 v1) z v3
  have h102 := C h48 h72
  have h103 := C h48 h94
  have h104 := C h54 h9
  have h105 := C h40 h57
  have h106 := T h7 h17
  have h107 := C h40 h106
  have h108 := C (T (T (T (T (T (T (C (T (T (T (T h107 h105) h41) h104) h103) h6) (C h102 h6)) h101) (C (C (C h5 (T (T (T h46 h100) h35) h33)) h6) h5)) (S h86)) h85) h83) h40
  have h109 := h v4 z y
  have h110 := C h73 h6
  have h111 := C (T (C (T (T (T (T (T (T (T (T h96 h110) h109) h108) h82) h62) h81) h79) h51) h20) h47) h20
  have h112 := h z v0 v0
  have h113 := C (T (T (T (C (T (T (T (T (T (T (T h96 h110) h109) h108) h82) h112) h111) h44) h40) h39) h37) h36) h20
  have h114 := h z y v0
  have h115 := T (T h114 h113) h31
  have h116 := h z y v1
  have h117 := S h116
  have h118 := C (T (T (T h117 h114) h113) h31) h5
  have h119 := h y v1 v3
  have h120 := h y v1 z
  have h121 := S h120
  have h122 := S h114
  have h123 := C h95 h6
  have h124 := S h109
  have h125 := C h40 h27
  have h126 := C (T (T (T (T h102 h43) h42) h125) (C h40 h14)) h6
  have h127 := C h103 h6
  have h128 := S h101
  have h129 := C (T (T (T h62 h81) h79) h51) h20
  have h130 := C (C (C h5 (T (T (T h32 h84) h129) h47)) h6) h5
  have h131 := C (T (T (T (T (T (T h37 h36) h86) h130) h128) h127) h126) h40
  have h132 := C (T (T (T h85 h83) h38) (C (T (T (T (T (T (T (T (C (T h41 h104) h20) (C (T h46 (C (T (T (T (T (T (T (T (T h99 h98) h65) h63) h34) h131) h124) h123) h74) h20)) h20)) (S h112)) h34) h131) h124) h123) h74) h40)) h20
  have h133 := T (T h30 h132) h122
  have h134 := C h133 h72
  have h135 := C h134 h6
  have h136 := h v75 z v0
  let v137 := M z y
  have h138 := T (T (T (T (T h13 h56) h49) h30) h132) h122
  have h139 := h v0 v0 v0
  have h140 := S h139
  have h141 := C (T h30 (C (T h85 h83) h20)) h57
  have h142 := T (T (T (T (T h114 h113) h31) h26) h25) h17
  have h143 := C h20 h142
  have h144 := h z y y
  have h145 := S h144
  have h146 := C (T (T (T h145 h114) h113) h31) h133
  have h147 := h y y v0
  have h148 := h y y v3
  have h149 := S h148
  have h150 := h v3 y v0
  have h151 := S h150
  have h152 := h y v1 x
  have h153 := S h152
  have h154 := C (T (T h105 h41) h104) h2
  have h155 := C (T (T (T h154 h153) h119) h118) h40
  let v156 := M (M x v0) x
  have h157 := h v156 x y
  have h158 := h v0 x x
  have h159 := T (T h158 h157) h155
  have h160 := C h159 h115
  have h161 := S h158
  have h162 := h v156 x v1
  have h163 := S h162
  have h164 := h v0 x v0
  have h165 := h v0 v0 v1
  have h166 := S h165
  have h167 := h x v0 v0
  have h168 := C (T (T h24 h19) h167) h9
  have h169 := C (T h18 h55) h9
  have h170 := C (T (T h169 h168) h166) h2
  have h171 := h v0 v1 x
  have h172 := C (T (C (T h171 h170) h20) (S h164)) h27
  have h173 := h v1 v0 v0
  have h174 := h v1 v0 v1
  have h175 := h x v1 v0
  have h176 := C (T (T (T (C h175 h9) (S h174)) h173) h172) h2
  have h177 := h v1 v1 x
  have h178 := h v1 v1 v0
  have h179 := S h178
  have h180 := C h115 h94
  have h181 := h z y x
  have h182 := h v1 y v0
  have h183 := S h182
  have h184 := h z v1 y
  have h185 := h z v1 v45
  have h186 := S h185
  have h187 := S h167
  have h188 := C (T (T h187 h18) h55) h9
  have h189 := h y y x
  have h190 := S h189
  have h191 := C (T (T (T (T (T (T (T h190 h147) h146) h143) h141) h140) h165) h188) h48
  have h192 := h y x v45
  have h193 := C (T (T (T h192 h191) h186) h184) h20
  have h194 := S h192
  have h195 := S h147
  have h196 := C (T (T (T h30 h132) h122) h144) h115
  have h197 := C h20 h138
  have h198 := C (T (C (T h37 h36) h20) h31) h27
  have h199 := C (T (T (T (T (T (T (T h168 h166) h139) h198) h197) h196) h195) h189) h48
  have h200 := C (T (T (T (S h184) h185) h199) h194) h20
  have h201 := h v1 y v3
  have h202 := S h201
  have h203 := h v75 z z
  have h204 := S h203
  have h205 := C (T (T (T (T (T (T (C h142 h2) h161) h58) h60) h93) h89) (C (C h6 h94) h6)) h6
  have h206 := h y x z
  have h207 := h x v1 y
  have h208 := C (T (T (T (T (T (T (T (T h117 h114) h113) h31) h26) h25) h8) h207) (C (T (C (T (T (T h206 h205) h204) h88) h94) (C h5 h72)) h40)) h5
  have h209 := C (T (T (T h30 h132) h122) h116) h5
  have h210 := C (T (T (T (T h209 h208) h202) h182) h200) h40
  have h211 := h v1 x x
  have h212 := h x v1 v1
  have h213 := C (T (T (T (T (T (T (T (T h145 h114) h113) h31) h26) h25) h8) h212) (C (T (T (C (T (T h211 (C (T (T (T (T (C h106 h2) h157) h155) h210) (C (T (T (T (T (T (T h193 h183) h22) h52) h97) h87) h80) h40)) h2)) (S h181)) h9) h180) (C h20 h72)) h9)) h20
  have h214 := h v0 v1 v0
  have h215 := S h171
  have h216 := C (T h24 h19) h9
  have h217 := C (T (T (T (T (T (T (C (T (T h147 h146) h143) h2) (C (T (T (T (T h141 h140) h165) h188) h216) h2)) h215) h214) (C (T (T (T (C (T (T (T (T h139 h198) h197) h196) h195) h9) (C (T (T (T (T h147 h213) h179) h177) h176) h9)) h163) h161) h133)) h160) h151) h40
  have h218 := h y x y
  have h219 := S h206
  have h220 := C (T (T (T (T (T (T (C (C h6 h72) h6) h71) h69) h61) h59) h158) (C h138 h2)) h6
  have h221 := C (T (T (T (T (T h77 h203) h220) h219) h218) h217) h5
  have h222 := S h218
  have h223 := S h214
  have h224 := S h157
  have h225 := C (T (T h43 h42) h125) h2
  have h226 := S h119
  have h227 := C (T (T (T h209 h226) h152) h225) h40
  have h228 := C (T (T (T (T h193 h183) h201) (C (T (T (T (T (T (T (T (T (C (T (C h5 h94) (C (T (T (T h77 h203) h220) h219) h72)) h40) (S h207)) h7) h56) h49) h30) h132) h122) h116) h5)) h118) h40
  have h229 := C h20 h94
  have h230 := C (T (T (T (T (T (T (T (T (C (T (T h229 h134) (C (T (T h181 (C (T (T (T (T (C (T (T (T (T (T (T h64 h28) h78) h53) h21) h182) h200) h40) h228) h227) h224) (C h14 h2)) h2)) (S h211)) h9)) h9) (S h212)) h7) h56) h49) h30) h132) h122) h144) h20
  have h231 := S h177
  have h232 := S h173
  have h233 := T (C (T (T h165 h188) h216) h2) h215
  have h234 := C (T h164 (C h233 h20)) h57
  have h235 := C (T (T (T h234 h232) h174) (C (S h175) h9)) h2
  have h236 := C (T (T (T h158 h162) (C (T (T (T (T h235 h231) h178) h230) h195) h9)) (C (T (T (T (T h147 h146) h143) h141) h140) h9)) h115
  have h237 := T (T h227 h224) h161
  have h238 := C h237 h133
  have h239 := C (T (T (T (T (T (T h150 h238) h236) h223) h171) (C (T (T (T (T h169 h168) h166) h139) h198) h2)) (C (T (T h197 h196) h195) h2)) h40
  have h240 := C (T (T (T (T (T h239 h222) h206) h205) h204) h88) h5
  have h241 := h v1 v1 v45
  have h242 := h v0 y v1
  have h243 := T (T (T h150 (C h237 h27)) h234) h232
  have h244 := h z v1 v1
  have h245 := S h244
  have h246 := h v3 v1 v3
  have h247 := S h246
  have h248 := C (T (T h158 h162) (C (T (T (T (T (T (T h235 h231) h178) h230) h195) h148) h240) h9)) h5
  have h249 := C (T h248 h247) h9
  have h250 := h v3 v1 v1
  have h251 := C (T (T (C (T (T (T (T (T (T h221 h149) h147) h213) h179) h177) h176) h9) h163) h161) h5
  have h252 := C (T h246 h251) h9
  have h253 := C (T (T (T (T (T (T (C (T (T (T (T (T (T (T (T (T h77 h203) h220) h219) h192) h191) h186) h244) h252) (C (T (T (T (T (T (T (T (T h248 h247) h250) (C (T (T (T (T (T (T (T h249 h245) h185) h199) h194) h218) h217) (C h243 h40)) h9)) (S h242)) h32) h84) h129) h47) h9)) h48) (S h241)) h178) h230) h195) h148) h240) h40
  have h254 := T (T (T h173 h172) (C h159 h57)) h151
  have h255 := C (T (T (T (T (T (T (T (T (T (C (T (T (T (T (T (T (T (T h46 h100) h35) h33) h242) (C (T (T (T (T (T (T (T (C h254 h40) h239) h222) h192) h191) h186) h244) h252) h9)) (S h250)) h246) h251) h9) h249) h245) h185) h199) h194) h206) h205) h204) h88) h48
  have h256 := h v1 v1 y
  have h257 := h y v0 v45
  have h258 := h v45 y v3
  have h259 := h v3 y v3
  have h260 := T (T h259 (C (C (T (T (T (T (T (T h221 h149) h147) h213) h179) h241) h255) h40) h5)) (S h258)
  have h261 := h x v0 y
  have h262 := h v45 x v1
  have h263 := h x y v45
  have h264 := S h263
  have h265 := S h262
  have h266 := S h259
  have h267 := C h253 h5
  have h268 := C (T (T h105 h257) (C (T (T (T (T (T (T (T (C (T (T h258 h267) h266) h20) (C h243 h20)) h187) h261) h228) h227) h224) h161) h48)) h2
  have h269 := C (T (T (T (T (T h190 h147) h213) h179) h256) (C (T (T (C (T h119 h118) h9) (C (T (T (T (T h209 h226) h152) h225) h268) h9)) h265) h40)) h48
  T (T (h x y x) (C (T (T (T (T (T (T (T (T (C (T (T (T (h x x v3) (C (T (T (T (T (C (T (T (T (T (T (h v3 x v0) (C (T (T (T (T (T (T (T (T (T (T (C (T (T (T (T (T (T (T (T (T h209 h208) h202) h22) h52) h97) h87) h29) (C (T (T (C (T (T (T h209 h226) h120) (C h180 h6)) h20) (S h136)) h88) h133)) (C (T (T (T (T (T (T h77 h203) h220) h219) h192) h269) h264) h142)) h2) (C (C h48 h57) h2)) (S (h y v0 x))) h41) h104) h46) h100) h35) h33) (h v0 y z)) (C (T (T (T (T (C (T (T h112 h111) h44) h40) h39) h139) h198) h197) h6)) h20)) (S (h v137 z v0))) (h v137 z v1)) (C (T (T (T (T (T (T (T (T (T (C (T h160 h151) h6) (h (M v3 y) z v45)) (C (C (T (T (C h48 h260) (C h48 (T (T (T (T (T (T (T (T h258 h267) h266) h150) h238) h236) h223) h171) h170))) (C h48 h233)) h6) h48)) (S (h (M v0 v1) z v45))) (C h229 h6)) h135) h121) h152) h225) h268) h9)) h265) h2) (S (h y x x))) h192) h269) h264) (T (T (T (T (T (T (T (T h77 h203) h220) h219) h192) h191) h186) h67) h66))) (C h48 h92)) (C h48 (T (T h185 h199) h194))) h40) (C (T (T (T (T (T (T (T (T (C h48 (T (T h192 h191) h186)) (C h48 h68)) (C (T (T (T (T h263 (C (T (T (T (T (T (C (T (T h262 (C (T (T (T (T (C (T (T (C (T (T (T (T (T (T (T h158 h157) h155) h210) (S h261)) h167) (C h254 h20)) (C h260 h20)) h48) (S h257)) h125) h2) h154) h153) h119) h118) h9)) (C (T h209 h226) h9)) h40) (S h256)) h178) h230) h195) h189) h48)) h194) h218) h217) (T (T (T (T (T (T (T (T h91 h90) h185) h199) h194) h206) h205) h204) h88))) h149) h147) h213) h179) h241) h255) h40)) h253) (C (T h221 h149) h40)) (C (T (T (T (T (T (T (T (T (T (T (T (T h147 h146) h143) h141) h140) h37) h36) h86) h130) h128) h127) h126) (C (T h107 (C h40 h138)) h6)) h40)) (S (h v137 z y))) (h v137 z v3)) (C (C (T (T (T (C (T (T h77 h136) (C (T (T (T h135 h121) h119) h118) h20)) h115) (S h29)) h28) (C h5 h14)) h6) h5)) (S (h v4 z v3))) h2)) (S (h v1 z x))

