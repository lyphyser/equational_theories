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
theorem Equation895_implies_Equation1543 (G: Type _) [Magma G] (h: Equation895 G) : Equation1543 G := fun x y z =>
  let v0 := M y y
  let v1 := M z x
  let v2 := M z v1
  let v3 := M v0 v2
  have h4 := h v3 x v0
  have h5 := S h4
  have h6 := h y x x
  have h7 := S h6
  have h8 := R x
  have h9 := C h8 (C h7 h7)
  let v10 := M y x
  have h11 := h x x (M v10 (M x x))
  have h12 := T h11 h9
  have h13 := h y v3 x
  have h14 := S h13
  have h15 := R v3
  have h16 := C h15 (C h14 h14)
  let v17 := M v3 x
  have h18 := h v3 v3 (M v10 v17)
  have h19 := T h18 h16
  have h20 := S h11
  have h21 := C h8 (C h6 h6)
  have h22 := h (M x v0) v0 v0
  have h23 := S h22
  have h24 := h y v0 x
  have h25 := S h24
  have h26 := R v0
  have h27 := C h26 (C h25 h25)
  let v28 := M v0 x
  have h29 := h v0 v0 (M v10 v28)
  have h30 := T h29 h27
  have h31 := C h12 h26
  have h32 := C h31 h30
  have h33 := C h26 (T (T (T h11 h9) h31) h32)
  have h34 := T (T (T h33 h23) h21) h20
  have h35 := C h34 (C h19 h12)
  let v36 := M v28 v17
  have h37 := h v36 v0 v0
  have h38 := S h37
  have h39 := T h21 h20
  have h40 := S h18
  have h41 := C h15 (C h13 h13)
  have h42 := T h41 h40
  have h43 := C h39 h26
  have h44 := S h29
  have h45 := C h26 (C h24 h24)
  have h46 := T h45 h44
  have h47 := C h43 h46
  have h48 := C h26 (T (T (T h47 h43) h21) h20)
  have h49 := T (T (T h11 h9) h22) h48
  have h50 := C h49 (C h42 h39)
  have h51 := T h4 h50
  have h52 := C h51 h26
  have h53 := T (T (T (T h35 h5) h18) h16) h52
  have h54 := C h53 h30
  have h55 := C h26 (T (T (T h18 h16) h52) h54)
  let v56 := M v0 v3
  have h57 := h v56 v3 v0
  have h58 := S h57
  have h59 := T h35 h5
  have h60 := C h59 h26
  have h61 := T (T (T (T h60 h41) h40) h4) h50
  have h62 := C h61 h46
  have h63 := C h26 (T (T (T h62 h60) h41) h40)
  have h64 := T (T (T (T (T (T h60 h41) h40) h4) h50) h37) h63
  have h65 := C h64 h46
  have h66 := T (T (T (T (T (T (T (T h55 h38) h35) h5) h18) h16) h52) h54) h65
  have h67 := C h66 h19
  have h68 := C h64 h42
  have h69 := C h53 h19
  have h70 := C h51 h15
  have h71 := T (T (T h55 h38) h35) h5
  have h72 := C h71 (T (T (T h70 h69) h68) h67)
  let v73 := M v3 v3
  let v74 := M v56 v73
  have h75 := h v74 v2 v3
  have h76 := S h75
  have h77 := R (M v2 v3)
  have h78 := C h59 h15
  have h79 := C h61 h42
  have h80 := T (T (T (T (T (T h55 h38) h35) h5) h18) h16) h52
  have h81 := C h80 h19
  have h82 := C h80 h30
  have h83 := T (T (T (T (T (T (T (T h82 h62) h60) h41) h40) h4) h50) h37) h63
  have h84 := C h83 h42
  have h85 := T (T (T h4 h50) h37) h63
  have h86 := C h85 (T (T (T h84 h81) h79) h78)
  have h87 := T (T (T (T (T (T (T (T (T (T h82 h62) h60) h41) h40) h4) h50) h37) h63) h57) h86
  have h88 := C h87 h42
  have h89 := T h67 h88
  let v90 := M v2 x
  have h91 := h v3 v3 (M v90 v17)
  have h92 := h v2 v3 x
  have h93 := R (M v2 v2)
  have h94 := R v2
  have h95 := h v0 v3 v3
  have h96 := S h95
  have h97 := C h83 h46
  have h98 := T (T (T (T (T (T (T (T (T (T h72 h58) h55) h38) h35) h5) h18) h16) h52) h54) h65
  have h99 := C h98 h30
  have h100 := C (T (T (T (T (T (T h99 h97) h82) h62) h60) h41) h40) (T (T (T (T (T (T (T h41 h40) h4) h50) h37) h63) h57) h86)
  have h101 := C h87 h46
  have h102 := C h66 h30
  have h103 := T (T (T (T (T (T (T (T (T (T (T (T h72 h58) h55) h38) h35) h5) h18) h16) h52) h54) h65) h102) h101
  have h104 := C h103 h19
  have h105 := C (T (T h104 h100) h96) (T (T (T (T (T (T (T h70 h69) h68) h67) h88) h104) h100) h96)
  have h106 := R v73
  have h107 := C h89 h106
  have h108 := C (T h69 h68) h106
  have h109 := C h70 h106
  have h110 := h (M v73 v73) x v3
  have h111 := S h110
  have h112 := T (T h33 h23) h31
  have h113 := C h112 h30
  have h114 := T (T (T (T h113 h47) h43) h22) h48
  have h115 := T (T (T (T (T (T (T (T (T (T (T (T h99 h97) h82) h62) h60) h41) h40) h4) h50) h37) h63) h57) h86
  have h116 := C h78 h106
  have h117 := C (T h81 h79) h106
  have h118 := C h98 h19
  have h119 := T h118 h84
  have h120 := C h119 h106
  have h121 := C h115 h42
  have h122 := C (T (T (T (T (T (T h18 h16) h52) h54) h65) h102) h101) (T (T (T (T (T (T (T h72 h58) h55) h38) h35) h5) h18) h16)
  have h123 := C (T (T h95 h122) h121) (T (T (T (T (T (T (T h95 h122) h121) h118) h84) h81) h79) h78)
  have h124 := C (T (T (T (T (T h29 h27) h123) h120) h117) h116) (T (T (T (T (T (T (T (C h115 h46) h99) h97) h82) h62) h60) h41) h40)
  have h125 := h v74 v0 v0
  have h126 := T (T (T (T (T (T (T h4 h50) h37) h63) h57) h86) h125) h124
  have h127 := C h126 (T (T (T (C h114 h42) (C h112 h19)) (C h43 h42)) (C h39 h15))
  have h128 := h v28 v3 v0
  have h129 := C h114 h46
  have h130 := T (T h43 h22) h48
  have h131 := C h130 h46
  have h132 := h v28 v1 x
  have h133 := S h132
  let v134 := M v1 x
  have h135 := h v1 v1 (M v10 v134)
  have h136 := h y v1 x
  have h137 := R v1
  have h138 := T (C h137 (C h136 h136)) (S h135)
  have h139 := S h136
  have h140 := T h135 (C h137 (C h139 h139))
  have h141 := T (C h140 (T h33 h23)) (C h138 h39)
  have h142 := S h128
  have h143 := T (T (T (T h33 h23) h31) h32) h131
  have h144 := S h125
  have h145 := C (T (T (T (T (T h109 h108) h107) h105) h45) h44) (T (T (T (T (T (T (T h18 h16) h52) h54) h65) h102) h101) (C h103 h30))
  have h146 := T (T (T (T (T (T (T h145 h144) h72) h58) h55) h38) h35) h5
  have h147 := C h146 (T (T (T (C h12 h15) (C h31 h19)) (C h130 h42)) (C h143 h19))
  have h148 := C h49 (T (T (T (T (T h147 h142) h33) h23) h21) h20)
  have h149 := h z v0 x
  have h150 := C h137 (T h149 (C (T (T (T (T (T (T (T h29 h27) h123) h120) h117) h116) h110) h148) h141))
  have h151 := C (T (T (T (T (T (T h150 h133) h33) h23) h31) h32) h131) h30
  have h152 := C (T (T (T (T (T (T h151 h129) h113) h47) h43) h21) h20) (T (T (T h22 h48) h128) h127)
  have h153 := S h149
  have h154 := T (C h140 h12) (C h138 (T h22 h48))
  have h155 := C (T (T (T (T (T (T (T (C h34 (T (T (T (T (T h11 h9) h22) h48) h128) h127)) h111) h109) h108) h107) h105) h45) h44) h154
  have h156 := C h137 (T h155 h153)
  have h157 := C (T (T (T (T (T (T h113 h47) h43) h22) h48) h132) h156) h46
  have h158 := C h143 h30
  have h159 := T (T (T (T (T (T (T (T h150 h133) h33) h23) h31) h32) h131) h158) h157
  have h160 := C h159 h12
  let v161 := M v1 z
  have h162 := R v161
  have h163 := C h162 (T (T (T (T (T h150 h133) h33) h23) h21) h20)
  have h164 := C h94 (T (T (C (C (T (T (T (T (T (T (T (T (T h163 h160) h152) h111) h109) h108) h107) h105) h45) h44) h94) h93) (C h15 (C h92 h92))) (S h91))
  let v165 := M v161 v161
  have h166 := h v165 v2 v2
  have h167 := h v165 v3 v3
  have h168 := S h167
  have h169 := C h162 (T (T (T (T (T h11 h9) h22) h48) h132) h156)
  have h170 := T (T (T (T (T (T (T (T h151 h129) h113) h47) h43) h22) h48) h132) h156
  have h171 := C h170 h39
  have h172 := C (T (T (T (T (T (T h11 h9) h31) h32) h131) h158) h157) (T (T (T h147 h142) h33) h23)
  have h173 := C (T (T (T h110 h172) h171) h169) h15
  have h174 := h v36 v3 v3
  have h175 := C (T (T (T h163 h160) h152) h111) h15
  have h176 := T (T (T (T (T (T (T (T h175 h145) h144) h72) h58) h55) h38) h35) h5
  have h177 := C h176 (T (T (T (T h55 h38) h174) (C h126 (T (T (T (T (T (T (T (T (T (T (T (T h108 h107) h105) h45) h44) h95) h122) h121) h118) h84) h81) h79) h78))) (C h173 h106))
  have h178 := C (T (T (T (T h95 h122) h121) h118) h84) (T (T (T h177 h168) h166) h164)
  have h179 := h v165 v0 v3
  have h180 := C h94 (T (T (T (T (T (T (T (T (T (T (T (T h29 h27) h123) h120) h117) h116) h110) h172) h171) h169) h179) h178) (C h89 h77))
  have h181 := h y v2 x
  have h182 := S h181
  have h183 := C h94 (C h182 h182)
  have h184 := h v2 v2 (M v10 v90)
  have h185 := h v2 v2 (M v134 v90)
  have h186 := S h185
  have h187 := h v1 v2 x
  have h188 := C h94 (C h187 h187)
  let v189 := M v2 (M v1 v1)
  have h190 := h v189 z v3
  have h191 := S h190
  have h192 := h z v1 v1
  have h193 := S h192
  have h194 := S h187
  have h195 := C h94 (C h194 h194)
  have h196 := S h184
  have h197 := C h94 (C h181 h181)
  have h198 := S h179
  have h199 := T (T (T (T (T (T (T (T h4 h50) h37) h63) h57) h86) h125) h124) h173
  have h200 := C h199 (T (T (T (T (C h175 h106) (C h146 (T (T (T (T (T (T (T (T (T (T (T (T h70 h69) h68) h67) h88) h104) h100) h96) h29) h27) h123) h120) h117))) (S h174)) h37) h63)
  have h201 := S h166
  have h202 := S h92
  have h203 := C h94 (T (T h91 (C h15 (C h202 h202))) (C (C (T (T (T (T (T (T (T (T (T h29 h27) h123) h120) h117) h116) h110) h172) h171) h169) h94) h93))
  have h204 := C (T (T (T (T h67 h88) h104) h100) h96) (T (T (T h203 h201) h167) h200)
  have h205 := C h94 (T (T (T (T (T (T (T (T (T (T (T (T (C h119 h77) h204) h198) h163) h160) h152) h111) h109) h108) h107) h105) h45) h44)
  have h206 := T (T (T (T (T (T (T (T (T (T (T h4 h50) h37) h63) h57) h86) h75) h205) h197) h196) h185) h195
  have h207 := C h137 h206
  have h208 := T h207 h193
  have h209 := C h208 h15
  let v210 := M v1 v3
  have h211 := R v210
  have h212 := C (T (T (T (T (T (T (T (T h175 h145) h144) h75) h205) h197) h196) h185) h195) h71
  have h213 := h v1 v0 v3
  have h214 := C h208 (T h213 (C (T (T (T (T (T (T (T (T (T (T (T (T h29 h27) h123) h120) h117) h116) h110) h172) h171) h169) h167) h200) h212) (T (C h211 h71) h209)))
  have h215 := h v210 v1 z
  have h216 := S h215
  have h217 := h v161 v0 v0
  have h218 := h v210 v3 v0
  have h219 := T (T (T (T (T (T (T (T (T (T (T h184 h183) h180) h76) h72) h58) h55) h38) h35) h5) h18) h16
  have h220 := C (T (T (T (T (T (T (T (T h188 h186) h184) h183) h180) h76) h125) h124) h173) h85
  have h221 := T (T (T (T (T (T (T (T (T h184 h183) h180) h76) h72) h58) h55) h38) h35) h5
  have h222 := R v189
  have h223 := T (T (T (T (T (T (T (T (T (T (T h41 h40) h4) h50) h37) h63) h57) h86) h75) h205) h197) h196
  have h224 := h v189 v2 v3
  have h225 := S h224
  have h226 := T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h70 h69) h68) h67) h88) h104) h100) h96) h29) h27) h123) h120) h117) h116) h110) h172) h171) h169) h166) h164
  have h227 := R (M v189 v3)
  have h228 := T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h203 h201) h163) h160) h152) h111) h109) h108) h107) h105) h45) h44) h95) h122) h121) h118) h84) h81) h79) h78
  have h229 := C (T h188 h186) (T (T (T (T (T (T (T (T (T (T (T (T (T h29 h27) h123) h120) h117) h116) h110) h172) h171) h169) h179) h178) (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h67 h88) h104) h100) h96) h29) h27) h123) h120) h117) h116) h110) h172) h171) h169) h167) h200) h212) h228)) (C h227 h226))
  have h230 := R (M v189 v0)
  have h231 := C (T h185 h195) (T (T (T (T (T (T (T (T (T (T (T (T (T (C h227 h228) (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h220 h177) h168) h163) h160) h152) h111) h109) h108) h107) h105) h45) h44) h95) h122) h121) h118) h84) h226)) h204) h198) h163) h160) h152) h111) h109) h108) h107) h105) h45) h44)
  have h232 := C h137 (T (T (T (T (T (T (T (T (T (T (T h188 h186) h184) h183) h180) h76) h72) h58) h55) h38) h35) h5)
  have h233 := T h192 h232
  have h234 := h v210 z v1
  have h235 := T (T (T (T (T (T (T (T (T h4 h50) h37) h63) h57) h86) h75) h205) h197) h196
  have h236 := C h233 h15
  have h237 := h v165 z v3
  have h238 := h v161 v0 x
  have h239 := C h137 (T (T (T h132 h156) h238) (C (T (T (T (T (T (T (T (T (T (T (T h29 h27) h123) h120) h117) h116) h110) h172) h171) h169) h237) (C h233 (T (T (T (C h176 (T (T h236 (C h211 h235)) (C (T h234 (C h233 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (C (T (T (T h214 h191) h224) h231) (T h184 h183)) (C h230 (T (T (T (T (T (T (T (T (T h180 h76) h72) h58) h55) h38) h35) h5) h18) h16))) (C (T h229 h225) h223)) (C h222 h221)) h220) h177) h168) h163) h160) h152) h111) h109) h108) h107) h105) h45) h44))) h219))) (S h218)) h207) h193))) (T (C (T (T (T (T (T (T (T (T h160 h152) h111) h109) h108) h107) h105) h45) h44) (T (T (T (T (T (T (T h33 h23) h31) h32) h131) h158) h157) (C h159 h30))) (S h217))))
  have h240 := C h141 h137
  have h241 := C h233 (T (C (T (T (T (T (T (T (T (T (T (T (T (T h220 h177) h168) h163) h160) h152) h111) h109) h108) h107) h105) h45) h44) (T h236 (C h211 h85))) (S h213))
  have h242 := C (T (T (T h229 h225) h190) h241) (T h197 h196)
  have h243 := C h230 (T (T (T (T (T (T (T (T (T h41 h40) h4) h50) h37) h63) h57) h86) h75) h205)
  have h244 := C (T h224 h231) h219
  have h245 := C h222 h235
  have h246 := C h137 (T (T (T (C (T (T (T (T (T (T (T (T (T (T (T (C h208 (T (T (T h192 h232) h218) (C h199 (T (T (C (T (C h208 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h29 h27) h123) h120) h117) h116) h110) h172) h171) h169) h167) h200) h212) h245) h244) h243) h242)) (S h234)) h223) (C h211 h221)) h209)))) (S h237)) h163) h160) h152) h111) h109) h108) h107) h105) h45) h44) (T h217 (C (T (T (T (T (T (T (T (T h29 h27) h123) h120) h117) h116) h110) h172) h171) (T (T (T (T (T (T (T (C h170 h46) h151) h129) h113) h47) h43) h22) h48)))) (S h238)) h150) h133)
  have h247 := C (T h215 h246) h137
  T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h11 h9) h22) h48) h132) h156) (h v161 v1 x)) (C h137 (T (T (T (T (T (T (T (T (C (T (T h160 h152) h148) (R v134)) h155) h153) h192) h232) h215) h246) (h (M v1 v28) v0 v2)) (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h29 h27) h123) h120) h117) h116) h110) h172) h171) h169) h167) h200) h212) h245) h244) h243) h242) (C h247 h94)) (C h240 h221)) (T (C (T (C (T (T (T h239 h216) h207) h193) (T (T (T (T (T h185 h195) h190) h241) h247) h240)) (S (h v1 z x))) h206) h232))))) (S (h (M v134 v1) v1 v3))) (C h154 h137)) (C (T h239 h216) h137)) h214) h191) h188) h186) h184) h183) h180) h76) h72) h58) h55) h38) h35) h5

