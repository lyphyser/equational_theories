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
theorem Equation2789_implies_Equation3737 (G: Type _) [Magma G] (h: Equation2789 G) : Equation3737 G := fun x y z =>
  let v0 := M y z
  let v1 := M x z
  let v2 := M v1 v0
  have h3 := h y x x
  have h4 := S h3
  have h5 := R x
  let v6 := M x y
  have h7 := R v6
  have h8 := h x x v6
  have h9 := S h8
  have h10 := C (C h9 h9) h7
  let v11 := M x x
  have h12 := h v6 (M (M x v6) v11) v6
  have h13 := T h12 h10
  have h14 := C h13 h5
  let v15 := M v6 x
  have h16 := h v15 v0 v0
  have h17 := S h16
  have h18 := R v0
  have h19 := S h12
  have h20 := C (C h8 h8) h7
  have h21 := T h20 h19
  have h22 := C h21 h5
  have h23 := T h3 h22
  let v24 := M x v0
  let v25 := M v24 v6
  have h26 := h v0 v25 v0
  have h27 := h y x v0
  have h28 := h z x y
  have h29 := S h28
  have h30 := T h14 h4
  let v31 := M v6 v1
  have h32 := R v31
  have h33 := C h32 h30
  have h34 := T h33 h29
  have h35 := R y
  have h36 := C h35 h34
  have h37 := R (M y y)
  have h38 := T (T (C h37 h36) (C (C h27 h27) h18)) (S h26)
  have h39 := C h38 h23
  let v40 := M v31 v15
  have h41 := h v40 y y
  have h42 := C h32 h23
  have h43 := C (C h18 h36) (T (T (T h28 h42) h41) h39)
  have h44 := h v40 y z
  have h45 := C (T (T (T h28 h42) h44) h43) h18
  let v46 := M z v0
  have h47 := h v46 v0 y
  have h48 := S h47
  have h49 := T (T (T h45 h17) h14) h4
  have h50 := S h44
  have h51 := S h41
  have h52 := T h28 h42
  have h53 := C h35 h52
  have h54 := S h27
  have h55 := T (T h26 (C (C h54 h54) h18)) (C h37 h53)
  have h56 := C h55 h30
  have h57 := C (C h18 h53) (T (T (T h56 h51) h33) h29)
  have h58 := C (T (T (T h57 h50) h33) h29) h18
  have h59 := T (T (T h3 h22) h16) h58
  have h60 := C h38 h59
  have h61 := C h18 h30
  have h62 := T (T (T (T h28 h42) h41) h39) h61
  have h63 := R z
  have h64 := C (T (C h63 h52) (C h62 (T h41 h60))) h49
  let v65 := M (M z z) v46
  have h66 := h v65 v0 v2
  have h67 := R v2
  have h68 := C h55 h49
  have h69 := C h18 h23
  have h70 := C (T (C (T (T (T (T h69 h56) h51) h33) h29) (T h68 h51)) (C h63 h34)) h59
  have h71 := T h47 h70
  have h72 := C h18 h71
  have h73 := R (M v0 v2)
  let v74 := M v0 v0
  have h75 := R v74
  have h76 := C h75 h69
  have h77 := h (M v74 (M v0 y)) x x
  have h78 := S h77
  have h79 := C h75 h61
  have h80 := T (T (T (T h28 h42) h44) h43) h79
  have h81 := C h5 h80
  have h82 := R v11
  have h83 := C h82 h81
  have h84 := R v1
  have h85 := h x x v1
  have h86 := S h85
  have h87 := C (C h86 h86) h84
  have h88 := h v1 (M (M x v1) v11) v1
  have h89 := C (T (T h88 h87) h83) h5
  let v90 := M v1 x
  have h91 := h v90 x z
  have h92 := S h91
  have h93 := T (T (T (T (T (T h89 h78) h76) h57) h50) h33) h29
  have h94 := S h88
  have h95 := C (C h85 h85) h84
  have h96 := T (T (T (T h76 h57) h50) h33) h29
  have h97 := C h5 h96
  have h98 := C h82 h97
  have h99 := C (T (T h98 h95) h94) h5
  have h100 := T h77 h99
  have h101 := C h5 h100
  have h102 := C (T (C h84 h81) (C h84 h101)) h93
  let v103 := M (M v1 v1) v90
  have h104 := h v103 y v6
  have h105 := S h104
  have h106 := C h5 h30
  have h107 := T h45 h17
  have h108 := C h5 h107
  have h109 := T h64 h48
  have h110 := C h5 h109
  have h111 := T (T (T (T (T (T h28 h42) h44) h43) h79) h77) h99
  have h112 := T h89 h78
  have h113 := C h5 h112
  have h114 := C (T (C h84 h113) (C h84 h97)) h111
  have h115 := T h91 h114
  have h116 := C h35 h115
  let v117 := M y v6
  have h118 := R v117
  have h119 := C h35 h100
  have h120 := C (T (T (T (T (T h64 h48) h45) h17) h14) h4) h80
  have h121 := h v0 z z
  have h122 := T h121 h120
  have h123 := C h35 h21
  have h124 := h v65 x z
  have h125 := h v103 x x
  have h126 := h x v1 v1
  have h127 := S h126
  have h128 := C (T (T (T (T (T (T (T (T h28 h42) h44) h43) h79) h77) h99) h91) h114) h84
  have h129 := T h128 h127
  have h130 := C h5 h115
  have h131 := C h5 h71
  have h132 := T h16 h58
  have h133 := C h5 h132
  have h134 := C h5 h23
  have h135 := C (T (T (T (T (T (T (T (C (T (T (T (C h84 h13) (C h84 (T (T h20 h19) h134))) (C h84 h133)) (C h84 h131)) (T (T (T (T (T (T (T (T (T (T (C (T (T (T (T h88 h87) h83) (C h82 h101)) (C h82 h130)) h129) (S h125)) h102) h92) h89) h78) h76) h57) h50) h33) h29)) (S h124)) h64) h48) h45) h17) h14) h4) h13
  let v136 := M z v1
  have h137 := h v136 v1 v6
  have h138 := C (T (T (T (T (T (T (T (T h102 h92) h89) h78) h76) h57) h50) h33) h29) h84
  have h139 := T (T (T (T h126 h138) h137) h135) h123
  have h140 := C (T (T (C h139 h122) (C h118 h119)) (C h118 h116)) (T (T h110 h108) h106)
  have h141 := R v24
  have h142 := C h141 h131
  have h143 := C h141 h133
  have h144 := C h141 h134
  have h145 := h v0 v1 x
  have h146 := h v136 v6 v1
  have h147 := h v1 z v0
  have h148 := S h147
  have h149 := S h121
  have h150 := C (T (T (T (T (T h3 h22) h16) h58) h47) h70) h96
  have h151 := C h35 h112
  have h152 := T h102 h92
  have h153 := C h35 h152
  have h154 := T (T (T (T h144 h143) h142) h140) h105
  have h155 := C h35 h154
  have h156 := R v136
  have h157 := S h137
  have h158 := T h126 h138
  have h159 := C h5 h152
  have h160 := C (T (T (T (T (T (T (T h3 h22) h16) h58) h47) h70) h124) (C (T (T (T (C h84 h110) (C h84 h108)) (C h84 (T (T h106 h12) h10))) (C h84 h21)) (T (T (T (T (T (T (T (T (T (T h28 h42) h44) h43) h79) h77) h99) h91) h114) h125) (C (T (T (T (T (C h82 h159) (C h82 h113)) h98) h95) h94) h158)))) h21
  have h161 := C h35 h13
  have h162 := h v117 v6 x
  have h163 := S h162
  have h164 := h (M v11 v6) y z
  have h165 := C h18 h109
  have h166 := R (M v0 x)
  have h167 := C (T (T (T (T (C h166 h72) (C (T (C h18 h158) (C h18 (T h137 h135))) (T (T (T (T h165 h68) h51) h33) h29))) (S h164)) h20) h19) h139
  have h168 := h v46 v0 x
  have h169 := R v46
  have h170 := C (T (T (T (T (C h35 h23) (C h35 h132)) (C h59 h169)) (C h49 h71)) (C h23 (T (T (T h64 h48) h168) h167))) (T (T (T h160 h157) h128) h127)
  have h171 := C h37 h161
  have h172 := T (T h171 h170) h163
  have h173 := C h37 h123
  have h174 := S h168
  have h175 := T (T (T (T h161 h160) h157) h128) h127
  have h176 := C (T (T (T (T h12 h10) h164) (C (T (C h18 (T h160 h157)) (C h18 h129)) (T (T (T (T h28 h42) h41) h60) h72))) (C h166 h165)) h175
  have h177 := C (T (T (T (T (C h30 (T (T (T h176 h174) h47) h70)) (C h59 h109)) (C h49 h169)) (C h35 h107)) (C h35 h30)) (T (T (T h126 h138) h137) h135)
  have h178 := C (T (T (T (C h35 (T (T (T (T (T (T (T h126 h138) h137) h135) h123) h162) h177) h173)) (C h35 h172)) (C h35 (T (T h161 h160) h157))) (C h59 h156)) (T (T (T (T h155 h153) h151) h150) h149)
  have h179 := C h141 h106
  have h180 := C h141 h108
  have h181 := C h141 h110
  have h182 := T h150 h149
  have h183 := C (T (T (C h118 h153) (C h118 h151)) (C h175 h182)) (T (T h134 h133) h131)
  have h184 := T (T (T (T h104 h183) h181) h180) h179
  have h185 := C h35 h184
  let v186 := M y x
  have h187 := R v186
  have h188 := C h187 h185
  have h189 := C h187 h116
  have h190 := C h187 h119
  have h191 := C h187 h122
  have h192 := T (T h162 h177) h173
  have h193 := h v25 x y
  have h194 := C (T (C (C h111 h67) (T (T (T (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h28 h42) h44) h43) h79) h77) h99) h91) h114) h104) h183) h181) h180) h179) h193) (C (T (T (T (C h7 (C h5 h154)) (C h7 h159)) (C h7 h113)) (C h7 h97)) (T (T (T (T (T h3 h22) h16) h58) h168) h167))) (C h32 (C h7 h192))) (C h32 (C h7 (T (T (T (T (T h171 h170) h163) h161) h160) h157)))) (T (T (T (T (T h191 h190) h189) h188) h178) h148)) (S h146)) h128) h127)) (S h145)) h67
  have h195 := h (M v186 v0) z v2
  have h196 := C h187 h182
  have h197 := C h187 h151
  have h198 := C h187 h153
  have h199 := C h187 h155
  have h200 := T (T (T (T (T (T (T h171 h170) h163) h161) h160) h157) h128) h127
  have h201 := C (T (T (T (C h49 h156) (C h35 (T (T h137 h135) h123))) (C h35 h192)) (C h35 h200)) (T (T (T (T h121 h120) h119) h116) h185)
  have h202 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (C h32 (C h7 (T (T (T (T (T h137 h135) h123) h162) h177) h173))) (C h32 (C h7 h172))) (C (T (T (T (C h7 h81) (C h7 h101)) (C h7 h130)) (C h7 (C h5 h184))) (T (T (T (T (T h176 h174) h45) h17) h14) h4))) (S h193)) h144) h143) h142) h140) h105) h102) h92) h89) h78) h76) h57) h50) h33) h29) (T (T (T (T (T h147 h201) h199) h198) h197) h196)
  T (T (T (h v6 y y) (C h200 (T (T (T (T (T (T (T h3 h22) h16) h58) h47) h70) h66) (C (T (T (T (T (T (T (C h73 h165) (C (T (T (T (T (T (T (T (C (T h145 (C (C h93 h67) (T (T (T h126 h138) h146) h202))) h67) (S h195)) h191) h190) h189) h188) h178) h148) (T (T (T (T (T (T (T (T (T (T (T (T (T h68 h51) h44) h43) h79) h77) h99) h91) h114) h104) h183) h181) h180) h179))) (C h84 h154)) (C h84 h152)) (C h84 h112)) (C h84 (T (T h76 h57) h50))) (C h84 h34)) h67)))) (C (T (T (T (T (T h126 h138) h146) h202) (C h63 (T h195 h194))) (C h62 h73)) (T (T (T (T (T (T (T (C (T (T (T (T (T (T (C h84 h52) (C h84 (T (T h44 h43) h79))) (C h84 h100)) (C h84 h115)) (C h84 h184)) (C (T (T (T (T (T (T (T h147 h201) h199) h198) h197) h196) h195) h194) (T (T (T (T (T (T (T (T (T (T (T (T (T h144 h143) h142) h140) h105) h102) h92) h89) h78) h76) h57) h50) h41) h60))) (C h73 h72)) h67) (S h66)) h64) h48) h45) h17) h14) h4))) (S (h v2 v0 y))

