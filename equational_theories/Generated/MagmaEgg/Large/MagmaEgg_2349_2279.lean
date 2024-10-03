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
theorem Equation2349_implies_Equation2279 (G: Type _) [Magma G] (h: Equation2349 G) : Equation2279 G := fun x y z =>
  let v0 := M z y
  let v1 := M y v0
  let v2 := M x v1
  let v3 := M v2 z
  have h4 := h v3 z z
  have h5 := S h4
  let v6 := M y v1
  let v7 := M x (M x (M y y))
  have h8 := h z v7 v6
  have h9 := S h8
  have h10 := R v6
  have h11 := h y y z
  have h12 := R v7
  have h13 := h y x y
  have h14 := C (T h13 (C h12 (T h13 (C h12 h11)))) h10
  let v15 := M z v3
  let v16 := M z v15
  have h17 := R v16
  have h18 := h z x z
  have h19 := S h18
  have h20 := h z z v2
  let v21 := M x (M x (M z z))
  have h22 := R v21
  have h23 := C (T (C h22 (T (C h22 (S h20)) h19)) h19) h17
  have h24 := h v2 v21 v16
  have h25 := T h24 h23
  have h26 := C h25 (T h14 h9)
  let v27 := M y v6
  have h28 := h v27 v3 v0
  have h29 := S h28
  have h30 := R v0
  have h31 := S h13
  have h32 := C (T (C h12 (T (C h12 (S h11)) h31)) h31) h10
  let v33 := M x (M x (M v3 v3))
  have h34 := h z v33 v2
  have h35 := S h34
  have h36 := R v2
  have h37 := h v3 x v3
  have h38 := R v33
  have h39 := C (T h37 (C h38 h37)) h36
  have h40 := S h24
  have h41 := C (T h18 (C h22 (T h18 (C h22 h20)))) h17
  have h42 := T h41 h40
  have h43 := R v3
  have h44 := C h43 h42
  have h45 := C h30 (T (T (T (T h44 h39) h35) h8) h32)
  have h46 := C h43 h25
  have h47 := S h37
  have h48 := C (T (C h38 h47) h47) h36
  have h49 := T (T h34 h48) h46
  have h50 := C h30 h49
  have h51 := R z
  have h52 := h v0 x v0
  have h53 := S h52
  let v54 := M x (M x (M v0 v0))
  have h55 := R v54
  have h56 := C (T (C h55 h53) h53) h51
  have h57 := h y v54 z
  let v58 := M v0 (M v0 v1)
  have h59 := h y v54 v58
  have h60 := S h59
  have h61 := R v58
  have h62 := h v0 v0 y
  have h63 := C (T h52 (C h55 (T h52 (C h55 h62)))) h61
  have h64 := C (C h43 (C h43 (T (T (T (T (T h63 h60) h57) h56) h50) h45))) h30
  have h65 := h v58 v3 v0
  have h66 := C h36 (T (T h65 h64) h29)
  have h67 := S h65
  have h68 := S h62
  have h69 := C (T (C h55 (T (C h55 h68) h53)) h53) h61
  have h70 := S h57
  have h71 := C (T h52 (C h55 h52)) h51
  have h72 := T (T h44 h39) h35
  have h73 := C h30 h72
  have h74 := C h30 (T (T (T (T h14 h9) h34) h48) h46)
  have h75 := C (C h43 (C h43 (T (T (T (T (T h74 h73) h71) h70) h59) h69))) h30
  let v76 := M x (M x (M v1 v1))
  have h77 := h v0 v76 y
  have h78 := S h77
  have h79 := R y
  have h80 := h v1 x v1
  have h81 := R v76
  have h82 := C (T h80 (C h81 h80)) h79
  have h83 := T h63 h60
  have h84 := R v1
  have h85 := C h84 h83
  have h86 := T (T h85 h82) h78
  have h87 := C h79 h86
  have h88 := T h59 h69
  have h89 := C h84 h88
  have h90 := S h80
  have h91 := C (T (C h81 h90) h90) h79
  have h92 := C h51 h83
  have h93 := T (T (T h92 h77) h91) h89
  have h94 := C h79 h93
  have h95 := C h51 h88
  have h96 := T (T (T h85 h82) h78) h95
  have h97 := C h79 h96
  have h98 := T (T h77 h91) h89
  have h99 := C h79 h98
  have h100 := h v1 v0 v0
  have h101 := S h100
  have h102 := C h88 (T h82 h78)
  have h103 := C h79 (T (T (C h79 (T (T (T h102 h101) h99) h97)) (C h79 h94)) (C h79 h87))
  have h104 := C h36 (T (T (T h103 h28) h75) h67)
  have h105 := C h83 (T h77 h91)
  have h106 := C h79 (T (T (C h79 h99) (C h79 h97)) (C h79 (T (T (T h94 h87) h100) h105)))
  have h107 := T h102 h101
  have h108 := C h30 (C h30 h107)
  let v109 := M x (M x (M v2 v2))
  have h110 := h v1 v109 x
  have h111 := S h110
  have h112 := R x
  have h113 := h v2 x v2
  have h114 := R v109
  have h115 := C (T h113 (C h114 h113)) h112
  have h116 := C h30 (C h30 (T (T (T h115 h111) h100) h105))
  have h117 := T (T (T (T (T h116 h108) h65) h64) h29) h106
  have h118 := C h36 h117
  let v119 := M v0 (M v2 x)
  have h120 := h (M v0 v119) z x
  have h121 := S h120
  have h122 := h x v0 v2
  have h123 := S h122
  let v124 := M z v16
  have h125 := h v124 v1 v1
  have h126 := S h125
  let v127 := M v1 (M v1 v2)
  have h128 := R v127
  have h129 := h v1 v1 x
  have h130 := h x v76 v127
  have h131 := C (T (T h130 (C (T (C h81 (T (C h81 (S h129)) h90)) h90) h128)) (C h84 (C h84 (C h84 h25)))) h107
  have h132 := S h113
  have h133 := C (T (C h114 h132) h132) h112
  have h134 := C h30 (C h30 (T (T (T h102 h101) h110) h133))
  have h135 := T h100 h105
  have h136 := C h30 (C h30 h135)
  have h137 := T (T (T (T (T (T h8 h32) h28) h75) h67) h136) h134
  have h138 := C h137 (T (T (T h131 h126) h41) h40)
  have h139 := C (T (T (C h84 (C h84 (C h84 h42))) (C (T h80 (C h81 (T h80 (C h81 h129)))) h128)) (S h130)) h135
  have h140 := T h125 h139
  have h141 := C h51 h140
  have h142 := T (T h141 h138) h123
  have h143 := h v15 z z
  have h144 := C h51 (T h26 h5)
  have h145 := C h51 h66
  have h146 := C h51 (T h118 h104)
  have h147 := T (T (T (T (T h103 h28) h75) h67) h136) h134
  have h148 := C h36 h147
  have h149 := C h36 (T (T (T h65 h64) h29) h106)
  have h150 := C h51 (T h149 h148)
  have h151 := C h36 (T (T h28 h75) h67)
  have h152 := C h51 h151
  have h153 := C h42 (T h8 h32)
  have h154 := C h51 (T h4 h153)
  have h155 := C (T (T h24 h23) (C h51 (T (T (T (C h51 h154) (C h51 h152)) (C h51 h150)) (C h51 (T (T (T (T h146 h145) h144) h143) (C h142 h137)))))) h142
  have h156 := C h36 (T h155 h121)
  have h157 := T h131 h126
  have h158 := C h51 h157
  have h159 := T (T (T (T (T (T h116 h108) h65) h64) h29) h14) h9
  have h160 := C h159 (T (T (T h24 h23) h125) h139)
  have h161 := T (T h122 h160) h158
  have h162 := C (T (T (C h51 (T (T (T (C h51 (T (T (T (T (C h161 h159) (S h143)) h154) h152) h150)) (C h51 h146)) (C h51 h145)) (C h51 h144))) h41) h40) h161
  have h163 := C h51 h25
  have h164 := C h36 (T (T (T h163 h141) h138) h123)
  have h165 := C h30 h164
  have h166 := C h30 h165
  have h167 := C h51 h42
  have h168 := C h36 (T (T (T h122 h160) h158) h167)
  have h169 := C h30 h168
  have h170 := h v119 v3 v0
  have h171 := h (M v1 y) y y
  have h172 := S h171
  have h173 := C (T (T h8 h32) h106) (T (T (T (T (C h30 h117) (C h30 (T (T (T (T h103 h28) h75) h67) h136))) (C h30 h108)) h63) h60)
  have h174 := C h43 h157
  have h175 := T (T (T (T h164 h115) h111) h100) h105
  have h176 := C h112 h175
  have h177 := C h43 h176
  have h178 := C h43 (T (T (T (T (T (T (T (T (T (T (T h177 h174) h44) h39) h35) h8) h32) h28) h75) h67) h136) h134)
  have h179 := C h112 (T (T (T (T h102 h101) h110) h133) h168)
  have h180 := C h43 h179
  have h181 := C h43 h140
  have h182 := T (T (T (T (T h156 h118) h104) h66) h26) h5
  have h183 := C h182 (T (T (T (T h34 h48) h46) h181) h180)
  have h184 := h v124 v2 z
  have h185 := C h43 (T (T (T (T (T h176 h131) h126) h184) h183) h178)
  have h186 := C (T (T h103 h14) h9) (T (T (T (T h59 h69) (C h30 h136)) (C h30 (T (T (T (T h108 h65) h64) h29) h106))) (C h30 h147))
  have h187 := C h30 (T (T (T (C h51 (T h171 h186)) (C (T (T (T (T (T h34 h48) h46) h181) h180) h185) (T (T (T h173 h172) h82) h78))) (S h170)) h169)
  have h188 := C (T (T (T (T h8 h32) h28) h75) h67) (T (T (T h74 h73) h71) h70)
  have h189 := C (T (T (T (T h65 h64) h29) h14) h9) (T (T (T h57 h56) h50) h45)
  have h190 := C h30 (T (T (T (C h51 h98) (C h51 h96)) (C h51 (T (T h92 h62) h189))) (C h51 (T (T (T h188 h68) h77) h91)))
  have h191 := h (M v0 (M z v0)) v3 v3
  have h192 := S h191
  have h193 := C h30 (T (T (T (C h51 (T (T (T h82 h78) h62) h189)) (C h51 (T (T h188 h68) h95))) (C h51 h93)) (C h51 h86))
  have h194 := C h43 (C h43 h193)
  have h195 := S h184
  have h196 := C h36 (T h120 h162)
  have h197 := T (T (T (T (T h4 h153) h151) h149) h148) h196
  have h198 := C h197 (T (T (T (T h177 h174) h44) h39) h35)
  have h199 := C h43 (T (T (T (T (T (T (T (T (T (T (T h116 h108) h65) h64) h29) h14) h9) h34) h48) h46) h181) h180)
  have h200 := C h43 (T (T (T (T (T h199 h198) h195) h125) h139) h179)
  have h201 := C h30 (T (T (T h165 h170) (C (T (T (T (T (T h200 h177) h174) h44) h39) h35) (T (T (T h77 h91) h171) h186))) (C h51 (T h173 h172)))
  have h202 := C h30 h169
  have h203 := C h182 (T (T (T (T (T (T (T (T h8 h32) h28) h75) h67) h136) h134) h202) h201)
  have h204 := C h43 (T (T h199 h198) h203)
  have h205 := C h43 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h187 h166) h116) h108) h65) h64) h29) h14) h9) h34) h48) h46) h181) h180) h185) h204) h194)
  have h206 := T (T (T (T h24 h23) h184) h203) h205
  have h207 := C h36 (T (T (T (T (T (T (C h206 (T (T (T (T h118 h104) h66) h26) h5)) h192) h190) h187) h166) h120) h162)
  have h208 := C h36 (T (C h36 h149) (C h36 h148))
  have h209 := C h36 (C h36 h151)
  have h210 := C h36 h72
  have h211 := C h36 h49
  have h212 := C h36 (T (C h36 h211) (C h36 (T (T h210 h4) h153)))
  let v213 := M v2 (M v2 v3)
  have h214 := C h197 (T (T (T (T (T (T (T (T h187 h166) h116) h108) h65) h64) h29) h14) h9)
  have h215 := C h43 (T (T h214 h183) h178)
  have h216 := C h43 (C h43 h190)
  have h217 := C h43 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h216 h215) h200) h177) h174) h44) h39) h35) h8) h32) h28) h75) h67) h136) h134) h202) h201)
  have h218 := T (T (T (T h217 h214) h195) h41) h40
  have h219 := C h43 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h216 h215) h200) h177) h174) h44) h39) h35) h8) h32) h28) h75) h67) h136) h134) h202) h201) h193) h191) (C h218 (T (T (T (T (T (T (T (T (T h4 h153) h151) h149) h148) h196) (C h36 (T (T (T (T (T (T h155 h121) h202) h201) h193) h191) (C h218 (T (T (T (T h4 h153) h151) h149) h148))))) (C h36 (T (C h36 h118) (C h36 h104)))) (C h36 (C h36 h66))) (C h36 (T (C h36 (T (T h26 h5) h211)) (C h36 h210))))))
  T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h122 h160) h158) h167) (h (M z v2) y v2)) (C (T (T (T (C h79 (C h79 h175)) h103) h14) h9) (T (T (T (T h24 h23) h125) h139) h179))) (C (T (T (T (T (T (T (T (T (T (T (T (T h8 h32) h28) h75) h67) h136) h134) h120) h162) (C h36 h167)) h164) h115) h111) (T (T (T (T (T (T h176 h131) h126) h184) h203) h205) h219))) (C (T (T (T (T (T (T (T (T (T (T (T (T h110 h133) h168) (C h36 h163)) h155) h121) h116) h108) h65) h64) h29) h14) h9) (R (M v3 (M v2 v213))))) (C (T (T (T h8 h32) (h v27 v2 v2)) (C (T (T (T (T (T (T (T (T h209 h208) h207) h156) h118) h104) h66) h26) h5) (T (T (T (T (T h24 h23) h184) h203) h205) h219))) (T (T (T (T (T (C h43 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (C h206 (T (T (T (T (T (T (T (T (T h212 h209) h208) h207) h156) h118) h104) h66) h26) h5)) h192) h190) h187) h166) h116) h108) h65) h64) h29) h14) h9) h34) h48) h46) h181) h180) h185) h204) h194)) h217) h214) h195) h41) h40))) (S (h v213 v3 v2))) h212) h209) h208) h207) h156) h118) h104) h66) h26) h5

