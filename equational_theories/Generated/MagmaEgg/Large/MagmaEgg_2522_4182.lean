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
theorem Equation2522_implies_Equation4182 (G: Type _) [Magma G] (h: Equation2522 G) : Equation4182 G := fun x y z =>
  let v0 := M x y
  let v1 := M y z
  let v2 := M v1 z
  let v3 := M v2 x
  have h4 := h v3 y v0
  have h5 := R y
  have h6 := R x
  have h7 := h y v2 z
  have h8 := S h7
  have h9 := h v3 y v1
  have h10 := C (S h9) h7
  let v11 := M y (M (M v3 v1) v1)
  have h12 := h v11 x y
  have h13 := R v3
  have h14 := R v2
  have h15 := C h9 h8
  have h16 := h v3 y v3
  have h17 := h v2 x v2
  have h18 := S h17
  have h19 := C h6 h7
  have h20 := C (T (C h19 h6) h18) h6
  have h21 := h v0 v3 x
  have h22 := T h21 (C (C h13 h20) h13)
  let v23 := M y v0
  have h24 := h v23 x y
  have h25 := h v0 v2 v2
  have h26 := S h25
  let v27 := M v0 v2
  have h28 := h (M v2 (M v27 v2)) x v2
  have h29 := S h28
  have h30 := h v0 v2 x
  have h31 := C h6 h8
  have h32 := C (T h17 (C h31 h6)) h6
  have h33 := h v3 v0 v3
  have h34 := S h33
  have h35 := R v0
  have h36 := C (C h35 h22) h35
  have h37 := T (T h36 h34) h32
  have h38 := T (C (C h13 h32) h13) (S h21)
  have h39 := C (C h35 h38) h35
  have h40 := T h33 h39
  have h41 := C (C h6 (T (C (T (C (T (C h14 h40) (C h14 h37)) h14) (S h30)) h14) (C h25 h14))) h6
  let v42 := M v2 v3
  have h43 := h v42 x v2
  have h44 := h v2 v3 v2
  let v45 := M v0 y
  have h46 := h v3 v45 v3
  have h47 := R v45
  have h48 := C h35 h8
  have h49 := h v2 v0 v2
  have h50 := h (M v2 v45) x v2
  have h51 := h x v2 y
  have h52 := h x v2 v2
  have h53 := C (S h52) h14
  have h54 := C h52 h14
  have h55 := h x v2 z
  have h56 := S h55
  have h57 := h (M v2 (M (M x z) z)) x v2
  have h58 := T (T (T (T (T h57 (C (C h6 (T (C h56 h14) h54)) h6)) (C (C h6 (T h53 (C h51 h14))) h6)) (S h50)) (C (T h49 (C h48 h22)) h47)) (S h46)
  have h59 := h y x y
  have h60 := S h59
  have h61 := h v2 y v2
  have h62 := T h61 (C (C h5 h8) h5)
  have h63 := h v0 x x
  have h64 := C (T (C h6 (T (C (T (T (C (T (C h6 h40) (C h6 h37)) h6) (S h63)) h19) h6) h18)) (C h6 h62)) h6
  have h65 := h (M x v3) x x
  have h66 := T (C (C h5 h7) h5) (S h61)
  have h67 := S h49
  have h68 := C h35 h7
  have h69 := T (T (T (T (T h46 (C (T (C h68 h38) h67) h47)) h50) (C (C h6 (T (C (S h51) h14) h54)) h6)) (C (C h6 (T h53 (C h55 h14))) h6)) (S h57)
  have h70 := C h69 h66
  have h71 := C h13 h62
  have h72 := h (M v3 v2) x v0
  have h73 := S h72
  have h74 := C h13 h66
  have h75 := C h58 h62
  have h76 := C (T (T h55 h75) h74) h35
  have h77 := h (M x v0) x x
  have h78 := S h77
  have h79 := h v3 x v3
  have h80 := C (C h6 (C (T h79 (C (C h6 h38) h6)) h6)) h6
  have h81 := h v2 x x
  have h82 := C (T (T (T h81 h80) h78) h76) h35
  have h83 := h v2 v0 z
  have h84 := C (S h83) h35
  have h85 := C (C h6 (T h84 h82)) h6
  have h86 := C h83 h35
  have h87 := C (C h6 (T (C (T (C h68 h35) h67) h35) h86)) h6
  have h88 := h v45 x v0
  have h89 := C (T (T (T (T (T (T h88 h87) h85) h73) h71) h70) h56) h13
  have h90 := h v45 v3 v3
  have h91 := S h90
  have h92 := S h88
  have h93 := C (C h6 (T h84 (C (T h49 (C h48 h35)) h35))) h6
  have h94 := S h81
  have h95 := C (C h6 (C (T (C (C h6 h22) h6) (S h79)) h6)) h6
  have h96 := C (T (T h71 h70) h56) h35
  have h97 := C (T (T (T h96 h77) h95) h94) h35
  have h98 := C (C h6 (T h97 h86)) h6
  have h99 := C (T (T (T (T (T (T h55 h75) h74) h72) h98) h93) h92) h13
  have h100 := S h65
  have h101 := T h36 h34
  have h102 := T (T h20 h33) h39
  have h103 := C (T (C h6 h66) (C h6 (T h17 (C (T (T h31 h63) (C (T (C h6 h102) (C h6 h101)) h6)) h6)))) h6
  have h104 := C (T (T (T h59 h103) h100) h99) h20
  have h105 := C h5 h37
  have h106 := C h5 h40
  let v107 := M y v3
  have h108 := h v107 x y
  have h109 := S h108
  have h110 := C h5 h101
  have h111 := C h5 h102
  have h112 := h v0 y x
  have h113 := C (C h6 (C (T h112 (C (T h111 h110) h5)) h5)) h6
  have h114 := h x x y
  have h115 := C h58 (T (T (T (T (T h114 h113) h109) h106) h105) h104)
  have h116 := C h69 h6
  have h117 := C (T h116 h115) h13
  have h118 := C (T h117 h91) h13
  let v119 := M v3 x
  have h120 := h v119 v3 v3
  have h121 := C h58 h6
  have h122 := S h114
  have h123 := C (C h6 (C (T (C (T h106 h105) h5) (S h112)) h5)) h6
  have h124 := C (T (T (T h89 h65) h64) h60) h32
  have h125 := C h69 (T (T (T (T (T h124 h111) h110) h108) h123) h122)
  have h126 := C (T (T (T (T h125 h121) h120) (C (T (C h69 (T (T (T (T h118 h89) h65) h64) h60)) (C h58 h7)) h13)) (S h44)) h13
  have h127 := h (M x v2) x x
  have h128 := h y x z
  have h129 := h y x v1
  have h130 := C (S h129) h6
  have h131 := C h129 h6
  have h132 := h y x v0
  have h133 := S h132
  let v134 := M v23 v0
  have h135 := h (M x v134) x x
  have h136 := C (T (T (T (T (T (T h135 (C (C h6 (T (C h133 h6) h131)) h6)) (C (C h6 (T h130 (C h128 h6))) h6)) (S h127)) (C (T (T (T (T (T (T (T (T (T (T (T h55 h75) h74) h72) h98) h93) h92) h90) h126) h43) h41) h29) h14)) h26) h19) h6
  have h137 := T (T h132 h136) h18
  have h138 := h v3 y y
  have h139 := h v2 v0 y
  have h140 := C (C h6 (T (C (S h139) h35) h86)) h6
  have h141 := h (M v0 (M (M v2 y) y)) x v0
  have h142 := S h141
  have h143 := C (C h6 (T h84 (C h139 h35))) h6
  have h144 := h v2 v0 v3
  have h145 := C (C h6 (T (C (S h144) h35) h86)) h6
  have h146 := h (M v0 (M v42 v3)) x v0
  have h147 := S h146
  have h148 := C (C h6 (T h84 (C h144 h35))) h6
  have h149 := h v2 v0 v1
  have h150 := C (C h6 (T (C (S h149) h35) h86)) h6
  have h151 := h (M v0 (M (M v2 v1) v1)) x v0
  have h152 := S h151
  have h153 := C (C h6 (T h84 (C h149 h35))) h6
  have h154 := h v2 v0 v0
  have h155 := C (C h6 (T (C (S h154) h35) h86)) h6
  have h156 := h (M v0 (M (M v2 v0) v0)) x v0
  have h157 := S h156
  have h158 := C (C h6 (T h84 (C h154 h35))) h6
  have h159 := h v2 v0 x
  have h160 := S h159
  have h161 := C (C h6 (T (C h160 h35) h86)) h6
  have h162 := h (M v0 v119) x v0
  have h163 := S h162
  have h164 := C (C h6 (T h84 (C h159 h35))) h6
  have h165 := C (T h125 h121) h13
  have h166 := C (T h90 h165) h13
  have h167 := C (T (T (T (T h44 (C (T (C h69 h8) (C h58 (T (T (T (T h59 h103) h100) h99) h166))) h13)) (S h120)) h116) h115) h13
  have h168 := S h43
  have h169 := C (C h6 (T (C h26 h14) (C (T h30 (C (T (C h14 h102) (C h14 h101)) h14)) h14))) h6
  have h170 := T (T (T (T (T (T (T (T h28 h169) h168) h167) h91) h88) h87) h164) h163
  let v171 := M v0 (M (M v2 z) z)
  have h172 := h v171 x v0
  have h173 := h v171 v3 v0
  have h174 := S h173
  have h175 := C h170 h35
  have h176 := T (T (T (T (T (T (T (T h162 h161) h93) h92) h90) h126) h43) h41) h29
  have h177 := C h176 h35
  have h178 := h y v0 x
  have h179 := C (S h178) h35
  have h180 := C (C h13 (T (T (T (T h179 (C (T (T (T (T h132 h136) h18) h159) h177) h35)) (C (T (T (T (T (T h175 h160) h81) h80) h78) h76) h35)) h97) h86)) h13
  let v181 := M y x
  let v182 := M v0 (M v181 x)
  have h183 := h v182 v3 v0
  have h184 := h v182 x v0
  have h185 := S h184
  have h186 := C h178 h35
  have h187 := h y v0 v2
  have h188 := C (C h6 (T (C (S h187) h35) h186)) h6
  have h189 := h (M v0 (M (M y v2) v2)) x v0
  have h190 := S h189
  have h191 := C (C h6 (T h179 (C h187 h35))) h6
  have h192 := h y v0 v3
  have h193 := C (C h6 (T (C (S h192) h35) h186)) h6
  have h194 := h (M v0 (M v107 v3)) x v0
  have h195 := S h194
  have h196 := C (C h6 (T h179 (C h192 h35))) h6
  have h197 := h y v0 v0
  have h198 := C (C h6 (T (C (S h197) h35) h186)) h6
  have h199 := h (M v0 v134) x v0
  have h200 := S h199
  have h201 := C (C h6 (T h179 (C h197 h35))) h6
  have h202 := h y v0 z
  have h203 := C (C h6 (T (C (S h202) h35) h186)) h6
  have h204 := h v27 x v0
  have h205 := h v27 v2 v3
  have h206 := S h205
  have h207 := S h204
  have h208 := C (C h6 (T h179 (C h202 h35))) h6
  have h209 := S h183
  have h210 := C (T (T (T (T (T (T h31 h25) (C (T (T (T (T (T (T (T (T (T (T (T h28 h169) h168) h167) h91) h88) h87) h85) h73) h71) h70) h56) h14)) h127) (C (C h6 (T (C (S h128) h6) h131)) h6)) (C (C h6 (T h130 (C h132 h6))) h6)) (S h135)) h6
  have h211 := C (C h13 (T (T (T (T h84 h82) (C (T (T (T (T (T h96 h77) h95) h94) h159) h177) h35)) (C (T (T (T (T h175 h160) h17) h210) h133) h35)) h186)) h13
  have h212 := S h172
  have h213 := C (C h137 (T (T (T (T (T (T h114 h113) h109) h106) h105) h104) (C (T h166 (C (T (T (T (T (T (T (T (T (T (T h117 h91) h88) h87) h212) h173) h211) h209) h184) h208) h207) h13)) h13))) h137
  have h214 := C (T (C (T (T (T (T (T (T (T (T (T (T h204 h203) h185) h183) h180) h174) h172) h93) h92) h90) h165) h13) h118) h13
  have h215 := T (T h17 h210) h133
  have h216 := C h215 (T (T (T (T (T (T h214 h124) h111) h110) h108) h123) h122)
  T (T (T (T (T (T (T (T (T (T (T (T h19 (C (T (T (T (T (T (T h55 h75) h74) h72) h98) h143) h142) h8)) (C (T (T (T h141 h140) h148) h147) h5)) (C (T (T (T h146 h145) h153) h152) h5)) (C (T (T (T h151 h150) h158) h157) h5)) (C (T (T (T h156 h155) h164) h163) h5)) (C h176 h5)) (C (T (T (T (T (T (T (T (T (T (T (T (T (T h28 h169) h168) h167) h91) h88) h87) h212) h173) h211) h209) h184) h191) h190) h5)) (C (T (T (T h189 h188) h196) h195) h5)) (C (T (T (T h194 h193) h201) h200) h5)) (C (T (T (T (T (T h199 h198) h208) h207) h205) (C h216 h215)) h5)) (C (T (T (T (T (T (T (T h213 h206) (h v27 v3 v3)) (C (C h13 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h214 h124) h111) h110) h108) h123) h122) h55) h75) h74) h72) h98) h212) h173) h211) h209) h184) h208) h207) h205) (C (T (T (T (T (T (T h216 (h v181 v3 y)) (C (T (C h69 (T (T (T (T (T (T (T (T (T (T (C (T (T (T (T (T h213 h206) h204) h203) h201) h200) h5) (C (T (T (T h199 h198) h196) h195) h5)) (C (T (T (T h194 h193) h191) h190) h5)) (C (T (T (T (T (T (T (T (T (T (T (T (T (T h189 h188) h185) h183) h180) h174) h172) h93) h92) h90) h126) h43) h41) h29) h5)) (C h170 h5)) (C (T (T (T h162 h161) h158) h157) h5)) (C (T (T (T h156 h155) h153) h152) h5)) (C (T (T (T h151 h150) h148) h147) h5)) (C (T (T (T h146 h145) h143) h142) h5)) (C (T (T (T (T (T (T h141 h140) h85) h73) h71) h70) h56) h7)) h31)) (C h58 h22)) h13)) (S (h v3 v3 v3))) h138) (C (T (T (T (h (M y (M (M v3 y) y)) x y) (C (C h6 (T (C (S h138) h7) h15)) h6)) (C (C h6 (T h10 (C (T h16 (C (C h5 h38) h5)) h8))) h6)) (S h24)) h137)) (C (T (T h24 (C (C h6 (T (C (T (C (C h5 h22) h5) (S h16)) h7) h15)) h6)) (S h12)) h14)) h14))) h13)) (S (h v11 v3 v2))) h12) (C (C h6 (T h10 (C h4 h8))) h6)) (S (h (M y (M (M v3 v0) v0)) x y))) h5)) (S h4)

