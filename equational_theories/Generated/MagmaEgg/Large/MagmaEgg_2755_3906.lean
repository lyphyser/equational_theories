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
theorem Equation2755_implies_Equation3906 (G: Type _) [Magma G] (h: Equation2755 G) : Equation3906 G := fun x y z =>
  have h0 := R y
  let v1 := M z z
  let v2 := M y v1
  have h3 := h v2 v2 v2
  have h4 := C (S h3) h0
  have h5 := h v1 (M v2 v2) y
  let v6 := M v2 y
  have h7 := h v2 y v6
  have h8 := S h7
  have h9 := T h5 h4
  have h10 := R v2
  have h11 := h v6 v6 v6
  have h12 := C (S h11) h10
  let v13 := M v6 v6
  have h14 := h y v13 v2
  let v15 := M v1 v2
  let v16 := M v1 v1
  have h17 := h y v16 v15
  have h18 := S h17
  have h19 := R v15
  have h20 := h v1 z y
  have h21 := R (M v16 v16)
  have h22 := h v1 v1 v1
  have h23 := C (T h22 (C h21 h20)) h19
  let v24 := M y y
  have h25 := R v24
  have h26 := C h25 (T (T (T h23 h18) h14) h12)
  have h27 := C h26 h9
  have h28 := h v15 y v1
  have h29 := S h5
  have h30 := C h3 h0
  have h31 := T h30 h29
  have h32 := C h31 (T (T h28 h27) h8)
  have h33 := T (T (T h32 h28) h27) h8
  have h34 := R v13
  have h35 := C h9 h32
  have h36 := S h28
  have h37 := S h20
  have h38 := C (T (C h21 h37) (S h22)) h19
  have h39 := S h14
  have h40 := C h11 h10
  have h41 := C h25 (T (T (T h40 h39) h17) h38)
  have h42 := C h41 h31
  have h43 := C h9 (T (T h7 h42) h36)
  have h44 := h v15 y v6
  have h45 := S h44
  have h46 := R (M v6 v15)
  have h47 := h y z v15
  have h48 := S h47
  have h49 := R v1
  have h50 := C (C h49 h20) h19
  have h51 := h (M v16 v15) z v2
  have h52 := S h51
  have h53 := C (C h49 h37) h19
  have h54 := T h47 h53
  have h55 := C h49 (T (T h5 h4) (C h10 h54))
  have h56 := C h55 h10
  have h57 := T (T (T h56 h52) h50) h48
  have h58 := C h0 h57
  have h59 := T h50 h48
  have h60 := C h49 (T (T (C h10 h59) h30) h29)
  have h61 := C h60 h10
  have h62 := T (T (T h47 h53) h51) h61
  have h63 := C h57 h62
  have h64 := h v1 v1 y
  have h65 := T (T h64 h63) h58
  have h66 := C h31 h43
  have h67 := C (T (T (T (T (T h7 h42) h36) h43) h66) (C h65 h46)) h9
  have h68 := C h31 (T (T h67 h45) h43)
  have h69 := T h68 h35
  have h70 := S h64
  have h71 := C h62 h57
  have h72 := C h0 h62
  have h73 := T (T h72 h71) h70
  have h74 := C (T (T (T (T (T (C h73 h46) h35) h32) h28) h27) h8) h31
  have h75 := T (T (T (T h68 h35) h32) h44) h74
  have h76 := C h9 h75
  have h77 := C h9 (T (T h32 h44) h74)
  let v78 := M v2 v1
  have h79 := h v78 v6 y
  have h80 := S h79
  let v81 := M v16 v2
  have h82 := h v81 z v2
  have h83 := S h82
  have h84 := T h51 h61
  have h85 := C (T h55 (C h49 (C h10 h84))) h33
  have h86 := R v16
  have h87 := C h86 h69
  have h88 := T (T (T (T h67 h45) h43) h66) h77
  have h89 := C h86 h88
  have h90 := T (T (T (T (T (T (T h89 h87) h85) h83) h56) h52) h50) h48
  have h91 := h v1 v1 v2
  have h92 := C (C h34 (T (T (T (C h62 h90) h70) h91) (C h90 (T (T (T (T h7 h42) h36) h44) h74)))) h0
  let v93 := M v16 v78
  have h94 := h v93 v6 y
  have h95 := C h49 (T (T (T (T (T (T (T h94 h92) h80) h67) h45) h43) h66) h77)
  have h96 := T h95 h76
  have h97 := R v93
  have h98 := C h31 h97
  have h99 := C h86 h75
  have h100 := C h86 (T h66 h77)
  have h101 := T h56 h52
  have h102 := C (T (C h49 (C h10 h101)) h60) (T (T (T h7 h42) h36) h43)
  have h103 := T (T (T (T h72 h71) h70) h5) h4
  have h104 := C h103 (T (T (T (T (T (T (T (T (T h23 h18) h47) h53) h51) h61) h82) h102) h100) h99)
  have h105 := C h65 (T (T (T (T (T h56 h52) h50) h48) h14) h12)
  have h106 := T (T h105 h41) h104
  have h107 := R v81
  have h108 := C h31 h107
  have h109 := R v6
  have h110 := C h109 h84
  have h111 := C h9 h54
  have h112 := C h31 h59
  have h113 := C h109 h101
  have h114 := C h9 h107
  have h115 := C h73 (T (T (T (T (T h40 h39) h47) h53) h51) h61)
  have h116 := T (T (T (T h30 h29) h64) h63) h58
  have h117 := C h116 (T (T (T (T (T (T (T (T (T h89 h87) h85) h83) h56) h52) h50) h48) h17) h38)
  have h118 := C h9 h97
  have h119 := S h94
  have h120 := T (T (T (T (T (T (T h47 h53) h51) h61) h82) h102) h100) h99
  have h121 := C (C h34 (T (T (T (C h120 (T (T (T (T h67 h45) h28) h27) h8)) (S h91)) h64) (C h57 h120))) h0
  have h122 := C h49 (T (T (T (T (T (T (T h68 h35) h32) h44) h74) h79) h121) h119)
  have h123 := R (M v6 v78)
  have h124 := C h86 h96
  have h125 := C h86 h98
  have h126 := C h86 h106
  have h127 := C h86 h108
  have h128 := C h86 h110
  have h129 := C h86 h111
  have h130 := C h31 (T (T (T (T (T (T (T (T (T (T (T (T (T (T h129 h128) h127) h126) h125) h124) h99) h94) h92) h80) h67) h45) h43) h66) h77)
  have h131 := C h86 h112
  have h132 := C h86 h113
  have h133 := C h86 h114
  have h134 := T (T h117 h26) h115
  have h135 := C h86 h134
  have h136 := C h86 h118
  have h137 := C h31 h88
  have h138 := C h86 (T h137 h122)
  have h139 := T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h130 h76) h68) h35) h32) h44) h74) h79) h121) h119) h89) h138) h136) h135) h133) h132) h131
  have h140 := C h9 h139
  let v141 := M v1 y
  let v142 := M v16 v141
  have h143 := R (M v6 v142)
  have h144 := C h73 h143
  have h145 := C h9 (T (T (T (T (T (T (T (T (T (T (T (T (T (T h68 h35) h32) h44) h74) h79) h121) h119) h89) h138) h136) h135) h133) h132) h131)
  have h146 := T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h129 h128) h127) h126) h125) h124) h99) h94) h92) h80) h67) h45) h43) h66) h77) h137) h145
  have h147 := C h65 h146
  have h148 := C h49 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h147 h144) h140) h130) h76) h68) h35) h32) h44) h74) h79) h121) h119) h89) h138) h136) h135) h133) h132) h131)
  have h149 := R (M v1 v142)
  have h150 := C h73 h149
  have h151 := C h73 h139
  have h152 := C h65 h143
  have h153 := C h31 h146
  have h154 := C h65 (T (T (T (T h95 h145) h153) h152) h151)
  have h155 := C h73 h98
  have h156 := R (M v6 v93)
  have h157 := C h65 h156
  have h158 := C h49 h106
  have h159 := R (M v1 v81)
  have h160 := C h73 h159
  have h161 := C h25 h108
  have h162 := C h25 h110
  have h163 := C h25 h111
  let v164 := M x x
  let v165 := M v24 v141
  have h166 := h v165 v1 v164
  have h167 := S h166
  have h168 := R v164
  have h169 := C h25 h112
  have h170 := C h25 h113
  have h171 := C h25 h114
  have h172 := C h116 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h163 h162) h161) h160) h158) h157) h155) h154) h150) h148) h147) h144) h140) h130) h122) h118) h117) h26) h115)
  have h173 := T (T (T h172 h171) h170) h169
  have h174 := C h9 h173
  have h175 := R (M v6 v165)
  have h176 := C h73 h175
  have h177 := C h65 h159
  have h178 := C h49 h134
  have h179 := C h73 h156
  have h180 := C h65 h118
  have h181 := C h73 (T (T (T (T h147 h144) h140) h130) h122)
  have h182 := C h65 h149
  have h183 := C h49 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h129 h128) h127) h126) h125) h124) h99) h94) h92) h80) h67) h45) h43) h66) h77) h137) h145) h153) h152) h151)
  have h184 := C h103 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h105 h41) h104) h98) h95) h145) h153) h152) h151) h183) h182) h181) h180) h179) h178) h177) h171) h170) h169)
  have h185 := T (T (T h163 h162) h161) h184
  have h186 := C h65 h185
  have h187 := C h73 h173
  have h188 := C h65 h175
  have h189 := C h31 h185
  let v190 := M v164 v2
  have h191 := R v190
  have h192 := h v1 x y
  have h193 := h y z v190
  have h194 := C (T (T h193 (C (C h49 (S h192)) h191)) (C h86 (T (T (T (T (T (T (T (T (C h168 (T (T (T (T (T h7 h42) h36) h43) h66) h77)) (C h168 (T (T (T (T (T (T (T (T h137 h122) h118) h117) h26) h115) h114) h113) h112))) (C h168 h111)) (C h168 h110)) (C h168 h108)) (C h168 h106)) (C h168 (T (T (T (T (T (T (T (T (T (T (T (T (T h98 h95) h145) h153) h152) h151) h183) h182) h181) h180) h179) h178) h177) h184))) (C h168 (T (T h189 h188) h187))) (C h168 (T (T (T (T (T (T h186 h176) h174) h172) h171) h170) h169))))) h168
  T (T (T (T (h v164 v6 y) (C (T (T (T (T (T (T (T (T (T (C h34 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h194 h167) h163) h162) h161) h160) h158) h157) h155) h154) h150) h148) h147) h144) h140) h130) (C h65 h123)) (C h103 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h137 h145) h153) h152) h151) h183) h182) h181) h180) h179) h178) h177) h171) h170) h169) h166) (C (T (T (C h86 (T (T (T (T (T (T (T (T (C h168 (T (T (T (T (T (T h163 h162) h161) h184) h189) h188) h187)) (C h168 (T (T h186 h176) h174))) (C h168 (T (T (T (T (T (T (T (T (T (T (T (T (T h172 h160) h158) h157) h155) h154) h150) h148) h147) h144) h140) h130) h122) h118))) (C h168 h134)) (C h168 h114)) (C h168 h113)) (C h168 h112)) (C h168 (T (T (T (T (T (T (T (T h111 h110) h108) h105) h41) h104) h98) h95) h76))) (C h168 (T (T (T (T (T h68 h35) h32) h28) h27) h8)))) (C (C h49 h192) h191)) (S h193)) h168))))) (C h34 (T (T (T (T (T (T (T (T (T (C h116 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h194 h167) h163) h162) h161) h160) h158) h157) h155) h154) h150) h148) h147) h144) h140) h130) h76)) (C h73 h123)) h122) h118) h117) h26) h115) h114) h113) h112))) (C h34 h111)) (C h34 h110)) (C h34 h108)) (C h34 h106)) (C h34 h98)) (C h34 h96)) (C h34 h69)) (C h34 h33)) h0)) (S (h v1 v6 y))) h5) h4

