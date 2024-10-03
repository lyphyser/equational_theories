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
theorem Equation637_implies_Equation4 (G: Type _) [Magma G] (h: Equation637 G) : Equation4 G := fun x y =>
  let v0 := M y x
  let v1 := M v0 x
  let v2 := M x v1
  have h3 := h y x v2
  have h4 := S h3
  have h5 := R v2
  have h6 := h y x x
  have h7 := T h6 (C h6 h5)
  have h8 := R x
  have h9 := R y
  have h10 := C h9 (C h8 h7)
  let v11 := M x y
  let v12 := M v11 y
  let v13 := M x (M v12 y)
  let v14 := M x v11
  have h15 := h v11 v14 v13
  have h16 := S h15
  have h17 := R v13
  have h18 := h v11 x y
  have h19 := T h18 (C h18 h17)
  have h20 := R v14
  have h21 := R v11
  have h22 := C h21 (C h20 h19)
  let v23 := M v11 (M v14 v11)
  have h24 := h v23 v11 v11
  have h25 := S h24
  have h26 := S h18
  have h27 := T (C h26 h17) h26
  have h28 := C h21 (C h20 h27)
  have h29 := C (T h15 h28) h21
  have h30 := C h29 h21
  have h31 := C h21 h30
  let v32 := M v11 v11
  have h33 := R v32
  have h34 := C h21 (C h33 h27)
  have h35 := h v11 v32 v13
  have h36 := T (T h35 h34) h31
  have h37 := R v23
  have h38 := C h37 h36
  have h39 := C (T h38 h25) h36
  have h40 := C h9 (T (T (T h39 h25) h22) h16)
  have h41 := S h35
  have h42 := C h21 (C h33 h19)
  have h43 := C (T h22 h16) h21
  have h44 := C h43 h21
  have h45 := C h21 h44
  have h46 := T (T h45 h42) h41
  have h47 := C h37 h46
  have h48 := C (T h24 h47) h46
  have h49 := h v11 v32 v11
  have h50 := S h49
  have h51 := T (T (T (T h30 h39) h25) h22) h16
  have h52 := C h51 (T (T (T h35 h34) h31) (C (T (T (T (T h15 h28) h24) h47) h43) h44))
  have h53 := C h9 (T (T (T (T (T h52 h50) h15) h28) h24) h48)
  have h54 := T (T (T (T h15 h28) h24) h48) h44
  have h55 := C h54 (T (T (T (C (T (T (T (T h29 h38) h25) h22) h16) h30) h45) h42) h41)
  have h56 := h v32 v11 v11
  have h57 := S h56
  have h58 := T h49 h55
  have h59 := C (T (T (T (T (T (T h52 h50) h15) h28) h24) h47) h43) (T (T h49 h55) (C h51 h58))
  have h60 := C h9 (T (T (T (T (T (T (T (T h59 h57) h29) h38) h25) h22) h16) h49) h55)
  have h61 := T h52 h50
  have h62 := C (T (T (T (T (T (T h29 h38) h25) h22) h16) h49) h55) (T (T (C h54 h61) h52) h50)
  let v63 := M v32 v11
  have h64 := h v63 y v11
  have h65 := S h64
  have h66 := C h9 (T (T (T (T (T (T (T (T h52 h50) h15) h28) h24) h47) h43) h56) h62)
  have h67 := C h9 (T (T (T (T (T h39 h25) h22) h16) h49) h55)
  have h68 := C h9 (T (T (T h15 h28) h24) h48)
  have h69 := S h6
  have h70 := T (C h69 h5) h69
  have h71 := C h9 (C h8 h70)
  have h72 := R v63
  have h73 := C h72 (T (T (T (T h3 h71) h68) h67) h66)
  have h74 := C (T h73 h65) h9
  have h75 := C h9 (T (T (T (T (T (T (T (T h74 h73) h65) h30) h39) h47) h43) h56) h62)
  have h76 := C h72 (T (T (T (T h60 h53) h40) h10) h4)
  have h77 := C (T h64 h76) h9
  have h78 := h v63 v11 x
  have h79 := S h78
  let v80 := M x (M (M x x) x)
  let v81 := M v11 x
  have h82 := h x v81 v80
  have h83 := R v80
  have h84 := h x x x
  have h85 := T h84 (C h84 h83)
  have h86 := R v81
  have h87 := C (C h51 h8) h8
  have h88 := T (T (C h8 h87) (C h8 (C h86 h85))) (S h82)
  have h89 := C h72 h88
  have h90 := h v63 x x
  have h91 := C (T h90 h89) h88
  have h92 := h v63 v11 v11
  have h93 := C h51 (T (T (T (C h54 (T (T (T (T (T (T (T (T (T h74 h73) h65) h30) h39) h47) h43) h56) h62) (C h61 (T (T (T (T (T (T h15 h28) h24) h47) h43) h56) h62)))) (S h92)) h90) h91)
  have h94 := h v63 v11 y
  have h95 := S h94
  have h96 := S h90
  have h97 := C (C h54 h8) h8
  have h98 := S h84
  have h99 := T (C h98 h83) h98
  have h100 := T (T h82 (C h8 (C h86 h99))) (C h8 h97)
  have h101 := C h72 h100
  have h102 := C (T h101 h96) h100
  have h103 := C h54 (T (T (T h102 h96) h92) (C h51 (T (T (T (T (T (T (T (T (T (C h58 (T (T (T (T (T (T h59 h57) h29) h38) h25) h22) h16)) h59) h57) h29) h38) h48) h44) h64) h76) h77)))
  have h104 := C h21 h97
  have h105 := C (T (T h104 h103) h95) (T (T (T (T (T (T h15 h28) h24) h48) h44) h94) h93)
  have h106 := C h21 h87
  have h107 := C (T (T (T (T h105 h79) h94) h93) h106) h21
  have h108 := C h9 (T (T (T (T (T h107 h105) h79) h64) h76) h77)
  have h109 := C (T (T h94 h93) h106) (T (T (T (T (T (T h103 h95) h30) h39) h25) h22) h16)
  have h110 := C (T (T (T (T h104 h103) h95) h78) h109) h21
  let v111 := M v81 x
  let v112 := M v11 v111
  have h113 := h v112 y v11
  have h114 := S h113
  have h115 := C h9 (T (T (T (T (T h74 h73) h65) h78) h109) h110)
  have h116 := C h9 (T (T (T (T (T (T (T (T h59 h57) h29) h38) h48) h44) h64) h76) h77)
  have h117 := R v112
  have h118 := C h117 (T (T (T (T (T (T h3 h71) h68) h67) h66) h116) h115)
  have h119 := C (T h118 h114) h9
  have h120 := C h9 (T (T (T (T (T (T (T (T h119 h118) h114) h104) h103) h95) h78) h109) h110)
  have h121 := C h117 (T (T (T (T (T (T h108 h75) h60) h53) h40) h10) h4)
  have h122 := C (T h113 h121) h9
  have h123 := C (T (T (T (T h104 h103) h95) h90) h89) h8
  have h124 := C (T (T (T (T (T h123 h102) h96) h94) h93) h106) h8
  have h125 := C h9 (T (T (T (T (T (T (T (T (T h124 h123) h102) h96) h94) h93) h106) h113) h121) h122)
  have h126 := C (T (T (T (T h101 h96) h94) h93) h106) h8
  have h127 := C (T (T (T (T (T h104 h103) h95) h90) h91) h126) h8
  have h128 := C h9 (T h126 h127)
  have h129 := C h9 h97
  have h130 := T (T (T (T (T (T (T (T (T (T h129 h128) h125) h120) h108) h75) h60) h53) h40) h10) h4
  have h131 := C h130 (T (T (T (T (T (T h15 h28) h24) h48) h44) h90) h91)
  have h132 := C h9 h87
  have h133 := C (T h131 h132) h21
  have h134 := T (T (T (T (T (T (T (T (T (T (T h133 h131) h128) h125) h120) h108) h75) h60) h53) h40) h10) h4
  have h135 := C h9 (T h124 h123)
  have h136 := C h9 (T (T (T (T (T (T (T (T (T h119 h118) h114) h104) h103) h95) h90) h91) h126) h127)
  have h137 := C h9 (T (T (T (T (T (T (T (T h107 h105) h79) h94) h93) h106) h113) h121) h122)
  have h138 := T (T (T (T (T (T (T (T (T (T h3 h71) h68) h67) h66) h116) h115) h137) h136) h135) h132
  have h139 := C h138 (T (T (T (T (T (T h102 h96) h30) h39) h25) h22) h16)
  have h140 := C (T h129 h139) h21
  let v141 := M y v111
  have h142 := h v141 y y
  have h143 := S h142
  have h144 := C h138 h134
  have h145 := T (T (T (T (T (T (T (T (T (T (T h3 h71) h68) h67) h66) h116) h115) h137) h136) h135) h139) h140
  have h146 := C h9 h145
  have h147 := C (T h146 h144) h9
  have h148 := C h9 h147
  let v149 := M y y
  have h150 := R v149
  have h151 := C h9 (C h150 h70)
  have h152 := h y v149 v2
  have h153 := T (T h152 h151) h148
  have h154 := R v141
  have h155 := C h154 h153
  have h156 := C (T h155 h143) h153
  have h157 := T (T (T (T h156 h143) h129) h139) h140
  have h158 := S h152
  have h159 := C h9 (C h150 h7)
  have h160 := C h9 h134
  have h161 := C h130 h145
  have h162 := C (T h161 h160) h9
  have h163 := C h9 h162
  have h164 := T (T h163 h159) h158
  have h165 := C h154 h164
  have h166 := C (T h142 h165) h164
  have h167 := h y v12 y
  have h168 := S h167
  have h169 := h v141 v11 y
  have h170 := S h169
  have h171 := C h21 (T (T (T (T h133 h131) h132) h142) h166)
  have h172 := C h51 (T h139 h140)
  have h173 := h v63 y x
  have h174 := h v11 v11 x
  have h175 := S h174
  have h176 := S h173
  have h177 := C h54 (T h133 h131)
  have h178 := C h21 h157
  have h179 := C h21 h147
  have h180 := C (T (T (T (T (T (T (T (T h179 h178) h177) h176) h30) h39) h25) h22) h16) (T (T (T (T (T (T (T h15 h28) h24) h48) h44) h94) h93) h106)
  have h181 := C h21 h162
  have h182 := C (T (T (T (T (T (T (T (T (T (T h180 h175) h15) h28) h24) h48) h44) h173) h172) h171) h181) h21
  have h183 := C h138 (T (T (T (T (T (T (T (T (T (T h182 h180) h175) h15) h28) h24) h48) h44) h173) h172) h171)
  have h184 := C (T (T (T (T (T (T (T (T h15 h28) h24) h48) h44) h173) h172) h171) h181) (T (T (T (T (T (T (T h104 h103) h95) h30) h39) h25) h22) h16)
  have h185 := C (T (T (T (T (T (T (T (T (T (T h179 h178) h177) h176) h30) h39) h25) h22) h16) h174) h184) h21
  let v186 := M v149 y
  let v187 := M v11 v186
  have h188 := h v187 y v11
  have h189 := S h188
  have h190 := C h130 (T (T (T (T (T (T (T (T (T (T h178 h177) h176) h30) h39) h25) h22) h16) h174) h184) h185)
  have h191 := R v187
  have h192 := C h191 (T (T (T (T (T (T (T (T (T (T (T (T h3 h71) h68) h67) h66) h116) h115) h137) h136) h135) h132) h169) h190)
  have h193 := C (T h192 h189) h9
  have h194 := C h191 (T (T (T (T (T (T (T (T (T (T (T (T h183 h170) h129) h128) h125) h120) h108) h75) h60) h53) h40) h10) h4)
  have h195 := C (T h188 h194) h9
  have h196 := C (T (T (T (T (T (T h179 h178) h177) h176) h90) h91) h126) h8
  have h197 := C h21 (T (T (C h9 h27) h10) h4)
  have h198 := h v11 y v13
  have h199 := C (T (T (T (T (T (T (T (T (T (T h179 h178) h177) h176) h30) h39) h25) h22) h16) h198) h197) (T (T (T (T (T (T (C h9 (T (T (T (T (T (T (T (T (T (T (T (T (C (T (T (T (T (T (T (T (T h196 h124) h123) h102) h96) h173) h172) h171) h181) h8) h196) h124) h123) h102) h96) h173) h172) h171) h181) h188) h194) h195)) (C h9 (T (T (T (T (T (T (T (T (T (T (T (T (T (T h193 h192) h189) h179) h178) h177) h176) h30) h39) h25) h22) h16) h174) h184) h185))) h183) h170) h142) h166) h162)
  have h200 := h v187 y x
  have h201 := T (T (T (T (T (T (T (T (T (T (T (T (T h147 h156) h143) h129) h128) h125) h120) h108) h75) h60) h53) h40) h10) h4
  have h202 := C h201 (T (T (T (T (T (T (T (T (T (T h15 h28) h24) h48) h44) h173) h172) h171) h181) h200) h199)
  have h203 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h202 h168) h3) h71) h68) h67) h66) h116) h115) h137) h136) h135) h132) h142) h166) h162) h21
  have h204 := S h200
  have h205 := C (T (T (T (T (T (T h123 h102) h96) h173) h172) h171) h181) h8
  have h206 := S h198
  have h207 := C h21 (T (T h3 h71) (C h9 h19))
  have h208 := C (T (T (T (T (T (T (T (T (T (T h207 h206) h15) h28) h24) h48) h44) h173) h172) h171) h181) (T (T (T (T (T (T h147 h156) h143) h169) h190) (C h9 (T (T (T (T (T (T (T (T (T (T (T (T (T (T h182 h180) h175) h15) h28) h24) h48) h44) h173) h172) h171) h181) h188) h194) h195))) (C h9 (T (T (T (T (T (T (T (T (T (T (T (T h193 h192) h189) h179) h178) h177) h176) h90) h91) h126) h127) h205) (C (T (T (T (T (T (T (T (T h179 h178) h177) h176) h90) h91) h126) h127) h205) h8))))
  have h209 := T (T (T (T (T (T (T (T (T (T (T (T (T h3 h71) h68) h67) h66) h116) h115) h137) h136) h135) h132) h142) h166) h162
  have h210 := C h209 (T (T (T (T (T (T (T (T (T (T h208 h204) h179) h178) h177) h176) h30) h39) h25) h22) h16)
  have h211 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h147 h156) h143) h129) h128) h125) h120) h108) h75) h60) h53) h40) h10) h4) h167) h210) h21
  have h212 := h v186 y v11
  have h213 := S h212
  have h214 := h y v149 y
  have h215 := R v186
  have h216 := C h215 (T h214 (C h9 (T (T (T (T (T (T (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T h146 h144) h155) h143) h129) h128) h125) h120) h108) h75) h60) h53) h40) h10) h4) h147) h163) h159) h158) h167) h210) h211)))
  have h217 := T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h216 h213) h147) h156) h143) h129) h128) h125) h120) h108) h75) h60) h53) h40) h10) h4) h167) h210) h211
  have h218 := C h215 (T (C h9 (T (T (T (T (T (T h203 h202) h168) h152) h151) h148) (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T h3 h71) h68) h67) h66) h116) h115) h137) h136) h135) h132) h142) h165) h161) h160) h162))) (S h214))
  have h219 := h v149 y y
  have h220 := S h219
  have h221 := T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h3 h71) h68) h67) h66) h116) h115) h137) h136) h135) h132) h142) h166) h162) h212) h218
  have h222 := C (T (T (T (T (T (T h216 h213) h147) h156) h165) h161) h160) (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h3 h71) h68) h67) h66) h116) h115) h137) h136) h135) h132) h142) h166) h162) h212) h218) (C h201 h221))
  have h223 := T (T (T (T (T (T (T (T h222 h220) h146) h144) h155) h166) h162) h212) h218
  have h224 := T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h216 h213) h147) h156) h143) h129) h128) h125) h120) h108) h75) h60) h53) h40) h10) h4
  have h225 := C (T (T (T (T (T (T h146 h144) h155) h166) h162) h212) h218) (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (C h209 h224) h216) h213) h147) h156) h143) h129) h128) h125) h120) h108) h75) h60) h53) h40) h10) h4)
  have h226 := h y v11 x
  have h227 := S h226
  have h228 := C (C h201 h8) h8
  have h229 := h x v0 v80
  have h230 := R v0
  have h231 := T (T (C h8 h228) (C h8 (C h230 h85))) (S h229)
  have h232 := C h215 h231
  have h233 := h v186 x x
  have h234 := C (T h233 h232) h231
  have h235 := h v186 y y
  have h236 := S h235
  have h237 := S h233
  have h238 := C (C h209 h8) h8
  have h239 := C h8 h238
  have h240 := C h8 (C h230 h99)
  have h241 := T (T h229 h240) h239
  have h242 := C h215 h241
  have h243 := C (T h242 h237) h241
  have h244 := C h209 (T (T (T (T (T (T (T (T (T h243 h237) h147) h156) h165) h161) h160) h219) h225) (C h224 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h3 h71) h68) h67) h66) h116) h115) h137) h136) h135) h132) h142) h165) h161) h160) h219) h225)))
  have h245 := C h9 h238
  have h246 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h245 h244) h236) h147) h156) h143) h129) h128) h125) h120) h108) h75) h60) h53) h40) h10) h4) (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h15 h28) h24) h48) h44) h173) h172) h171) h181) h200) h199) (C (T h207 h206) (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h147 h156) h143) h129) h128) h125) h120) h108) h75) h60) h53) h40) h10) h4) h167) h210) h211))) (C h21 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h203 h202) h168) h3) h71) h68) h67) h66) h116) h115) h137) h136) h135) h132) h142) h166) h162) h212) h218))) (C h21 (T (T (T (T (T (T (T (T h216 h213) h147) h156) h165) h161) h160) h219) h225))) (C h21 (T (T (T (T (T (T (T (T h222 h220) h146) h144) h155) h166) h162) h233) h234))) (C h21 h228))
  have h247 := C h9 h228
  have h248 := C h201 (T (T (T (T (T (T (T (T (T (C h221 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h222 h220) h146) h144) h155) h143) h129) h128) h125) h120) h108) h75) h60) h53) h40) h10) h4)) h222) h220) h146) h144) h155) h166) h162) h233) h234)
  have h249 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h246 h227) h3) h71) h68) h67) h66) h116) h115) h137) h136) h135) h132) h142) h166) h162) h235) h248) h247) h21
  have h250 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h3 h71) h68) h67) h66) h116) h115) h137) h136) h135) h132) h142) h166) h162) h235) h248) h247) (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (C h21 h238) (C h21 (T (T (T (T (T (T (T (T h243 h237) h147) h156) h165) h161) h160) h219) h225))) (C h21 h223)) (C h21 h217)) (C (T h198 h197) (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h203 h202) h168) h3) h71) h68) h67) h66) h116) h115) h137) h136) h135) h132) h142) h166) h162))) h208) h204) h179) h178) h177) h176) h30) h39) h25) h22) h16)
  have h251 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h245 h244) h236) h147) h156) h143) h129) h128) h125) h120) h108) h75) h60) h53) h40) h10) h4) h226) h250) h21
  let v252 := M y v1
  have h253 := h v252 y v11
  have h254 := S h253
  have h255 := h v186 y x
  have h256 := R v252
  have h257 := C h256 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h3 h71) h68) h67) h66) h116) h115) h137) h136) h135) h132) h142) h166) h162) h255) (C h201 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h244 h236) h147) h156) h143) h129) h128) h125) h120) h108) h75) h60) h53) h40) h10) h4) h226) h250) h251)))
  have h258 := C h256 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (C h209 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h249 h246) h227) h3) h71) h68) h67) h66) h116) h115) h137) h136) h135) h132) h142) h166) h162) h235) h248)) (S h255)) h147) h156) h143) h129) h128) h125) h120) h108) h75) h60) h53) h40) h10) h4)
  have h259 := C (T (T (T (T h245 h244) h236) h233) h232) h8
  have h260 := C (T (T (T (T h242 h237) h235) h248) h247) h8
  T (T (T (T (T (T (T (T (T (T (T h229 h240) h239) (C h8 (T h260 (C (T (T (T (T (T h245 h244) h236) h233) h234) h260) h8)))) (C h8 (T (T (T (T (T (T (T (T (T (C (T (T (T (T (T h259 h243) h237) h235) h248) h247) h8) h259) h243) h237) h235) h248) h247) h253) h258) (C (T h253 h258) h9)))) (C h8 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (C (T h257 h254) h9) h257) h254) h245) h244) h236) h147) h156) h143) h129) h128) h125) h120) h108) h75) h60) h53) h40) h10) h4) h226) h250) h251))) (C h8 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h249 h246) h227) h3) h71) h68) h67) h66) h116) h115) h137) h136) h135) h132) h142) h165) h161) h160) h219) h225))) (C h8 h223)) (C h8 h217)) (C h8 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h203 h202) h168) h3) h71) h68) h67) h66) h116) h115) h137) h136) h135) h132) h142) h166))) (C h8 h157)) (C h8 h134)

