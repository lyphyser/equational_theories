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
theorem Equation2349_implies_Equation1320 (G: Type _) [Magma G] (h: Equation2349 G) : Equation1320 G := fun x y z =>
  let v0 := M y x
  let v1 := M v0 z
  let v2 := M x (M x (M v1 v1))
  have h3 := h z v2 v0
  have h4 := S h3
  have h5 := R v0
  have h6 := h v1 x v1
  have h7 := R v2
  have h8 := C (T h6 (C h7 h6)) h5
  let v9 := M x (M x (M v0 v0))
  have h10 := h x v9 y
  have h11 := S h10
  have h12 := R y
  have h13 := h v0 x v0
  have h14 := R v9
  have h15 := C (T h13 (C h14 h13)) h12
  have h16 := T h15 h11
  have h17 := C h12 h16
  have h18 := R v1
  have h19 := C h18 h17
  have h20 := C h18 (T (T h19 h8) h4)
  let v21 := M v0 y
  have h22 := h v21 v1 y
  have h23 := S h22
  have h24 := S h13
  have h25 := C (T (C h14 h24) h24) h12
  have h26 := T h10 h25
  have h27 := C h12 h26
  have h28 := C h18 h27
  have h29 := S h6
  have h30 := C (T (C h7 h29) h29) h5
  have h31 := C h18 (T (T h3 h30) h28)
  have h32 := C h31 h12
  have h33 := T h32 h23
  have h34 := C h12 h33
  have h35 := C h18 h34
  have h36 := C h18 h35
  have h37 := C h20 h12
  have h38 := T h22 h37
  have h39 := C h12 h38
  have h40 := C h18 h39
  let v41 := M v1 z
  let v42 := M x (M x (M v41 v41))
  have h43 := h z v42 v1
  have h44 := S h43
  have h45 := h v41 x v41
  have h46 := R v42
  have h47 := C (T h45 (C h46 h45)) h18
  let v48 := M y v41
  let v49 := M y v48
  let v50 := M x (M x (M z z))
  have h51 := h v1 v50 v49
  have h52 := S h51
  have h53 := R v49
  have h54 := h z y v1
  have h55 := R v50
  have h56 := h z x z
  have h57 := C (T h56 (C h55 (T h56 (C h55 h54)))) h53
  have h58 := T h57 h52
  have h59 := R v41
  have h60 := C h59 h58
  have h61 := C h18 (T (T (T (T (T (T h60 h47) h44) h3) h30) h28) h40)
  have h62 := h (M z v49) z z
  have h63 := S h62
  have h64 := S h56
  have h65 := C (T (C h55 (T (C h55 (S h54)) h64)) h64) h53
  have h66 := T h51 h65
  have h67 := R z
  have h68 := C h67 h66
  let v69 := M z (M z v1)
  have h70 := R v69
  have h71 := h z z v0
  have h72 := C (T (C h55 (T (C h55 (S h71)) h64)) h64) h70
  have h73 := h v0 v50 v69
  have h74 := C (T (T h73 h72) (C h67 (C h67 h68))) (T h8 h4)
  have h75 := T h74 h63
  have h76 := C h59 h75
  have h77 := C h18 h76
  have h78 := S h73
  have h79 := C (T h56 (C h55 (T h56 (C h55 h71)))) h70
  have h80 := C h67 h58
  have h81 := C (T (T (C h67 (C h67 h80)) h79) h78) (T h3 h30)
  have h82 := T h62 h81
  have h83 := C h59 h82
  have h84 := C h59 h66
  have h85 := S h45
  have h86 := C (T (C h46 h85) h85) h18
  have h87 := C h18 (T (T (T (T (T h8 h4) h43) h86) h84) h83)
  have h88 := T (T (T (T h87 h77) h61) h36) h20
  have h89 := C h12 h88
  have h90 := C h18 (T (T (T (T (T h76 h60) h47) h44) h3) h30)
  have h91 := C h18 h83
  have h92 := C h18 (T (T (T (T (T (T h35 h19) h8) h4) h43) h86) h84)
  have h93 := C h18 h40
  let v94 := M x (M x (M v48 v48))
  have h95 := h v41 v94 y
  have h96 := S h95
  have h97 := h v48 x v48
  have h98 := R v94
  have h99 := C (T h97 (C h98 h97)) h12
  let v100 := M v41 v48
  let v101 := M v41 v100
  have h102 := h y v42 v101
  have h103 := S h102
  have h104 := R v101
  have h105 := h v41 v41 y
  have h106 := C (T h45 (C h46 (T h45 (C h46 h105)))) h104
  have h107 := T h106 h103
  have h108 := R v48
  have h109 := C h108 h107
  have h110 := T (T (T (T (T (T (T h109 h99) h96) h31) h93) h92) h91) h90
  have h111 := C h12 h110
  have h112 := C h59 h89
  have h113 := C h59 h112
  have h114 := T (T (T (T h31 h93) h92) h91) h90
  have h115 := C h12 h114
  have h116 := C h59 h115
  have h117 := h v100 v41 v41
  have h118 := T (T h109 h99) h96
  have h119 := C (T (C h46 (T (C h46 (S h105)) h85)) h85) h104
  have h120 := T h102 h119
  have h121 := C h88 h120
  have h122 := h x v1 y
  have h123 := C h108 h120
  have h124 := S h97
  have h125 := C (T (C h98 h124) h124) h12
  have h126 := T (T (T (T (T (T (T h87 h77) h61) h36) h20) h95) h125) h123
  have h127 := R x
  have h128 := C h59 (T (T (T (C h127 h126) (C (T h122 h121) h118)) (S h117)) h116)
  have h129 := C h59 (T h128 h113)
  have h130 := T (T h95 h125) h123
  have h131 := S h122
  have h132 := C h114 h107
  have h133 := C h59 (T (T (T h112 h117) (C (T h132 h131) h130)) (C h127 h110))
  let v134 := M v1 v0
  let v135 := M v1 v134
  have h136 := h v135 v41 x
  have h137 := S h136
  have h138 := C h59 (T (C h59 h116) h133)
  let v139 := M x (M x v0)
  let v140 := M x (M x (M x x))
  have h141 := h y v140 v139
  have h142 := R v139
  have h143 := h x x y
  have h144 := R v140
  have h145 := h x x x
  have h146 := C (T (T (T (T (T (T (C h127 (C h127 (C h127 h39))) (C h127 (C h127 (C h127 (T h34 h17))))) (C (T h145 (C h144 (T h145 (C h144 h143)))) h142)) (S h141)) h102) h119) h138) h127
  have h147 := h (M y v21) x x
  have h148 := C h67 (C h67 (T (C h67 h75) h80))
  let v149 := M v0 v134
  have h150 := h v149 v41 v41
  have h151 := S h150
  have h152 := h v149 z z
  have h153 := T (T (T (T h43 h86) h84) h83) (C h59 (T h152 (C (T (T (T (T (T (T (T (T (T (T (T h148 h79) h78) h27) h147) h146) h137) h87) h77) h61) h36) h20) (T (T (T h43 h86) h84) h83))))
  have h154 := C h153 h118
  let v155 := M z (M z v41)
  have h156 := R v155
  have h157 := h z z v1
  have h158 := h v1 v50 v155
  let v159 := M v41 v101
  have h160 := h v159 z v48
  have h161 := C h59 (T h160 (C (T (T (T (T (T (T (T (T (T (T (T (T (C h67 (T (T (T (T (T (T (T (T (T h154 h151) h74) h63) h57) h52) h158) (C (T (C h55 (T (C h55 (S h157)) h64)) h64) h156)) (C h67 (C h67 (C h67 h114)))) (C h67 (T (C h67 (C h67 h126)) (C h67 (T h154 h151)))))) h148) h79) h78) h27) h147) h146) h137) h87) h77) h61) h36) h20) h115))
  have h162 := C h108 (T (C h59 (T (T (T (T (T (T (T h32 h23) h15) h11) h122) h121) h161) h133)) h129)
  have h163 := C h108 (C h59 h38)
  have h164 := C h108 (C h59 h26)
  have h165 := h (M v48 (M v41 x)) v48 z
  have h166 := S h165
  have h167 := C h108 (C h59 h16)
  have h168 := C h108 (C h59 h33)
  have h169 := C h67 (C h67 (T h68 (C h67 h82)))
  have h170 := S h147
  have h171 := S h145
  have h172 := C (T (T (T (T (T (T h129 h106) h103) h141) (C (T (C h144 (T (C h144 (S h143)) h171)) h171) h142)) (C h127 (C h127 (C h127 (T h27 h39))))) (C h127 (C h127 (C h127 h34)))) h127
  have h173 := T (T (T (T (C h59 (T (C (T (T (T (T (T (T (T (T (T (T (T h31 h93) h92) h91) h90) h136) h172) h170) h17) h73) h72) h169) (T (T (T h76 h60) h47) h44)) (S h152))) h76) h60) h47) h44
  have h174 := C h173 h130
  have h175 := C h108 (T h138 (C h59 (T (T (T (T (T (T (T h128 (C h59 (T (C (T (T (T (T (T (T (T (T (T (T (T (T h31 h93) h92) h91) h90) h136) h172) h170) h17) h73) h72) h169) (C h67 (T (T (T (T (T (T (T (T (T (C h67 (T (C h67 (T h150 h174)) (C h67 (C h67 h110)))) (C h67 (C h67 (C h67 h88)))) (C (T h56 (C h55 (T h56 (C h55 h157)))) h156)) (S h158)) h51) h65) h62) h81) h150) h174))) h89) (S h160)))) h132) h131) h10) h25) h22) h37)))
  have h176 := C (T (C h108 (C h108 h82)) (C h108 (C h108 (T (T (T h150 (C h173 (T (T (T h95 h125) h123) h175))) (C h67 h168)) (C h67 h167))))) h67
  have h177 := h v49 v48 z
  have h178 := C h12 h89
  have h179 := C h12 (T (T (T (T (T (T h178 h177) h176) h166) h164) h163) h162)
  have h180 := C h12 h115
  T (T (T (T (T (T (T (T (T (T h122 h121) h161) h113) (h v101 v48 v41)) (C (C h108 (T (T (T (T (T (T (T (T (T h109 h99) h96) h31) h93) h92) h91) h90) (h v135 y y)) (C (T (T h179 h111) h89) (T (T (T h102 h119) (h v159 y v48)) (C (T (T (T (T (T (T (T (T (T (T (C h12 h111) h178) h177) h176) h166) h164) h163) h162) h109) h99) h96) (T (T (T h115 (C h12 h126)) (C h12 (T (T (T (T (T (T h175 h168) h167) h165) (C (T (C h108 (C h108 (T (T (T (C h67 h164) (C h67 h163)) (C h153 (T (T (T h162 h109) h99) h96))) h151))) (C h108 (C h108 h75))) h67)) (S h177)) h180))) (C h12 h178))))))) h59)) (S (h (M y v49) v48 v41))) (C h12 h180)) h179) h111) h89

