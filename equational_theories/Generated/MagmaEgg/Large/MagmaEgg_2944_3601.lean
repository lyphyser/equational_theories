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
theorem Equation2944_implies_Equation3601 (G: Type _) [Magma G] (h: Equation2944 G) : Equation3601 G := fun x y z =>
  let v0 := M y x
  let v1 := M v0 z
  have h2 := R v1
  let v3 := M (M x (M x z)) z
  have h4 := h z v3 v1
  have h5 := S h4
  have h6 := h z x z
  have h7 := R v3
  have h8 := C (C (T h6 (C h7 h6)) h2) h2
  let v9 := M z v1
  let v10 := M v9 v1
  have h11 := h v10 v0 v1
  have h12 := S h11
  have h13 := T h8 h5
  have h14 := R v0
  have h15 := C h14 h13
  have h16 := S h6
  have h17 := C (C (T (C h7 h16) h16) h2) h2
  have h18 := T h4 h17
  have h19 := C h14 h18
  have h20 := C (C h14 h19) h2
  have h21 := h v0 x v0
  have h22 := S h21
  let v23 := M (M x (M x v0)) v0
  have h24 := R v23
  have h25 := T (C h24 h22) h22
  have h26 := C (C h25 h2) h2
  have h27 := h v0 v23 v1
  have h28 := C (T (T h27 h26) h20) h15
  have h29 := T (T (T h28 h12) h8) h5
  have h30 := C h29 h2
  have h31 := S (h v0 v1 y)
  let v32 := M x y
  let v33 := M (M x v32) y
  have h34 := h y v33 x
  have h35 := S h34
  have h36 := R x
  have h37 := h y x y
  have h38 := R v33
  have h39 := C (C (T h37 (C h38 h37)) h36) h36
  have h40 := S h27
  have h41 := T h21 (C h24 h21)
  have h42 := C (C h41 h2) h2
  have h43 := C (C h14 h15) h2
  have h44 := C (T (T h43 h42) h40) h19
  have h45 := h v10 v0 v9
  have h46 := S h45
  have h47 := T (T (T h27 h26) h20) h30
  have h48 := R v9
  have h49 := T (T (T h4 h17) h11) h44
  have h50 := C (C h49 h48) h47
  have h51 := T h50 h46
  have h52 := C h49 h2
  have h53 := T (T (T h52 h43) h42) h40
  have h54 := C h53 h51
  have h55 := C h52 (T h54 h15)
  have h56 := C (T h55 h44) h2
  have h57 := C (C h29 h48) h53
  have h58 := T h45 h57
  have h59 := C h47 h58
  have h60 := C h30 (T h19 h59)
  let v61 := M (M z v9) v0
  have h62 := h v61 v9 v1
  have h63 := S h62
  have h64 := R v61
  have h65 := C h47 h64
  have h66 := C (T h28 h60) h2
  have h67 := C (T (T (T h27 h26) h20) h66) (T (T h65 h54) h15)
  have h68 := C (T (T (T (T (T h67 h63) h50) h46) h11) h60) h2
  have h69 := C h53 h64
  have h70 := C (T (T (T h56 h43) h42) h40) (T (T h19 h59) h69)
  have h71 := h v61 v0 v0
  have h72 := S h71
  have h73 := h v0 v23 z
  have h74 := S h73
  have h75 := R z
  have h76 := C (C h41 h75) h75
  have h77 := C h2 h13
  have h78 := C h2 h51
  have h79 := h v1 z v0
  have h80 := C (T h79 (C (T h62 h70) h14)) (T (T (T h78 h77) h76) h74)
  have h81 := C (T (T (T h80 h72) h62) h70) h2
  have h82 := C h2 h58
  have h83 := C h2 h82
  have h84 := C h83 h2
  have h85 := C h2 h78
  have h86 := C h2 h18
  have h87 := C (C h25 h75) h75
  have h88 := S h79
  have h89 := C (T (C (T h67 h63) h14) h88) (T (T (T h73 h87) h86) h82)
  have h90 := h v10 v1 v1
  have h91 := S h90
  have h92 := C h2 (T (T h73 h87) h86)
  have h93 := T (T (T h92 h83) h80) h72
  have h94 := C h53 h93
  have h95 := C h85 h2
  have h96 := C (T (T (T h67 h63) h71) h89) h2
  have h97 := C (T (T (T (T (T h55 h12) h45) h57) h62) h70) h2
  have h98 := C (T (T (T (T h52 h66) h97) h96) h95) (T (T (T h94 h65) h54) h15)
  have h99 := T (T (T (T (T (T h98 h91) h45) h57) h71) h89) h85
  have h100 := C h99 h2
  have h101 := C h2 (T (T h77 h76) h74)
  have h102 := T (T (T h71 h89) h85) h101
  have h103 := C h47 h102
  have h104 := C (T (T (T (T h84 h81) h68) h56) h30) (T (T (T h19 h59) h69) h103)
  let v105 := M v1 v0
  have h106 := h v105 v9 v1
  have h107 := S h106
  have h108 := R v105
  have h109 := C h47 h108
  have h110 := T (T (T (T (T (T h83 h80) h72) h50) h46) h90) h104
  have h111 := C h110 h2
  have h112 := C (T (T (T (T (T (T (T h27 h26) h20) h66) h97) h96) h95) h111) (T (T (T (T h109 h94) h65) h54) h15)
  have h113 := T (T (T (T (T (T (T (T (T h112 h107) h92) h83) h80) h72) h50) h46) h90) h104
  have h114 := C h113 h2
  have h115 := C (T h80 h72) h53
  have h116 := C h83 h48
  have h117 := R (M v1 (M v1 v10))
  have h118 := C h117 h47
  have h119 := C h99 h53
  have h120 := R (M v9 (M v9 v105))
  have h121 := C h120 h47
  have h122 := C h113 h53
  have h123 := R (M v0 (M v0 v105))
  have h124 := C h123 h47
  have h125 := C h2 h93
  have h126 := T (T (T (T h125 h78) h77) h76) h74
  have h127 := C h53 h108
  have h128 := C (T (T (T (T (T (T (T h100 h84) h81) h68) h56) h43) h42) h40) (T (T (T (T h19 h59) h69) h103) h127)
  have h129 := T (T (T (T (T (T (T (T (T h4 h17) h45) h57) h71) h89) h85) h101) h106) h128
  have h130 := C h129 (T (T (T (T (T (T (T (T (C h129 h126) h124) h122) h121) h119) h118) h116) h115) h88)
  have h131 := T (T (T (T (T (T (T (T (T h130 h114) h100) h84) h81) h68) h56) h43) h42) h40
  have h132 := C h131 h36
  have h133 := C h2 h102
  have h134 := T (T (T (T h73 h87) h86) h82) h133
  have h135 := T (T (T (T (T (T (T (T (T h112 h107) h92) h83) h80) h72) h50) h46) h8) h5
  have h136 := C h123 h53
  have h137 := T (T (T (T (T (T (T (T (T h98 h91) h45) h57) h71) h89) h85) h101) h106) h128
  have h138 := C h137 h47
  have h139 := C h120 h53
  have h140 := C h110 h47
  have h141 := C h117 h53
  have h142 := C h85 h48
  have h143 := C (T h71 h89) h47
  have h144 := C h135 (T (T (T (T (T (T (T (T h79 h143) h142) h141) h140) h139) h138) h136) (C h135 h134))
  have h145 := C h137 h2
  let v146 := M v1 v105
  have h147 := h v146 z z
  have h148 := S h147
  have h149 := h v105 v0 v0
  have h150 := T (T (T (T (T (T (T (T (T h27 h26) h20) h66) h97) h96) h95) h111) h145) h144
  have h151 := C (T (T (T (T (T h19 h59) h69) h103) h127) (C h150 (T (T (T (T (T (T (T h92 h83) h80) h72) h50) h46) h8) h5))) (T (T (T (T (T (T (T (T (T (C (T (T (T (T (T (T (T h79 h143) h142) h141) h140) h139) h138) h136) h126) (S h149)) h92) h83) h80) h72) h50) h46) h8) h5)
  have h152 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h151 h148) h125) h78) h77) h76) h74) h27) h26) h20) h66) h97) h96) h95) h111) h145) h144) h36
  have h153 := C (T (T (T (T (T (C h131 (T (T (T (T (T (T (T h4 h17) h45) h57) h71) h89) h85) h101)) h109) h94) h65) h54) h15) (T (T (T (T (T (T (T (T (T h4 h17) h45) h57) h71) h89) h85) h101) h149) (C (T (T (T (T (T (T (T h124 h122) h121) h119) h118) h116) h115) h88) h134))
  have h154 := C (T h147 h153) h36
  have h155 := T (T (T (T h154 h152) h132) h39) h35
  have h156 := T (T (T (T (T (T (T (T h52 h43) h42) h40) h73) h87) h86) h82) h133
  let v157 := M v146 x
  let v158 := M (M x (M x x)) x
  have h159 := h x v158 v32
  have h160 := S h159
  have h161 := R v32
  have h162 := h x x x
  have h163 := R v158
  have h164 := C (C (T h162 (C h163 h162)) h161) h161
  have h165 := C h36 h155
  have h166 := C (C h36 h165) h161
  have h167 := C (T h151 h148) h36
  have h168 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h130 h114) h100) h84) h81) h68) h56) h43) h42) h40) h73) h87) h86) h82) h133) h147) h153) h36
  have h169 := C h150 h36
  have h170 := S h37
  have h171 := C (C (T (C h38 h170) h170) h36) h36
  have h172 := C h36 (T (T (T (T h34 h171) h169) h168) h167)
  have h173 := h v157 x v32
  have h174 := C (T (T (C h53 (C h156 (T (T (T (C (T (T (T (T (T (T h34 h171) h169) h168) h167) h173) (C (T (T h166 h164) h160) h172)) h161) h166) h164) h160))) (C h47 (R v157))) (C h156 h155)) (R y)
  have h175 := C (C h36 h172) h161
  have h176 := S h162
  have h177 := C (C (T (C h163 h176) h176) h161) h161
  have h178 := C (T (T (T (T (T (T (C (T (T h159 h177) h175) h165) (S h173)) h154) h152) h132) h39) h35) h161
  T (T (T (T (T (T (T h172 (C (T (T (T (T (T h159 h177) h175) h178) (h (M y v32) v9 y)) (C (T (T (T (T (T h174 h31) h27) h26) h20) h30) (T (T (T (T (T h34 h171) h169) h168) h167) (C (T (T (T (T (T (T (T (T h125 h78) h77) h76) h74) h27) h26) h20) h30) (T (T (T h159 h177) h175) h178))))) h155)) h174) h31) h27) h26) h20) h30

