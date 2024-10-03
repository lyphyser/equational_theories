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
theorem Equation2789_implies_Equation2355 (G: Type _) [Magma G] (h: Equation2789 G) : Equation2355 G := fun x y z =>
  let v0 := M z z
  let v1 := M y v0
  let v2 := M y v1
  let v3 := M v2 x
  have h4 := h v3 v0 v2
  let v5 := M x z
  have h6 := h v1 (M (M x v1) v5) v1
  have h7 := S h6
  have h8 := R v1
  have h9 := h z x v1
  have h10 := C (C h9 h9) h8
  let v11 := M v0 v1
  have h12 := h v11 v1 v2
  have h13 := S h12
  have h14 := R v2
  have h15 := T h10 h7
  have h16 := R v0
  have h17 := C h16 h15
  have h18 := C h15 h17
  have h19 := S h9
  have h20 := C (C h19 h19) h8
  have h21 := T h6 h20
  have h22 := C h16 h21
  have h23 := h v11 v0 v0
  have h24 := S h23
  have h25 := h v0 (M (M x v0) v5) v0
  have h26 := S h25
  have h27 := h z x v0
  have h28 := C (C h27 h27) h16
  have h29 := T h28 h26
  have h30 := S h27
  have h31 := C (C h30 h30) h16
  have h32 := T h25 h31
  have h33 := C (T h22 (C h32 h22)) h29
  have h34 := C (T h33 h24) (T (T h6 h20) h22)
  have h35 := h v0 v0 v1
  let v36 := M v1 v2
  have h37 := R v36
  have h38 := h v1 y v0
  have h39 := C (T h38 (C h37 (T (T h35 h34) h18))) h14
  have h40 := h v36 v1 v1
  have h41 := S h40
  have h42 := T (T (T h39 h13) h10) h7
  have h43 := S h35
  have h44 := C (T (C h29 h17) h17) h32
  have h45 := C (T h23 h44) (T (T h17 h10) h7)
  have h46 := C h21 h22
  have h47 := C (T (C h37 (T (T h46 h45) h43)) (S h38)) h14
  have h48 := T (T (T h6 h20) h12) h47
  have h49 := C (T (T (T h33 h24) h10) h7) h48
  have h50 := C h8 h15
  have h51 := C (T (T (T h35 h34) h18) h50) (T h35 h49)
  have h52 := C (T (T h25 h31) h51) h42
  have h53 := T (T (T (T (T h52 h41) h39) h13) h10) h7
  have h54 := h y (M (M x y) v5) y
  have h55 := S h54
  have h56 := R y
  have h57 := h z x y
  have h58 := C (C h57 h57) h56
  have h59 := T h58 h55
  have h60 := C h59 h53
  have h61 := C (T (T (T h6 h20) h23) h44) h42
  have h62 := C h8 h21
  have h63 := C (T (T (T h62 h46) h45) h43) (T h61 h43)
  have h64 := C (T (T h63 h28) h26) h48
  have h65 := R (M v0 y)
  have h66 := C h65 (T (T (T (T h17 h12) h47) h40) h64)
  have h67 := h v36 v0 y
  have h68 := S h67
  have h69 := T (T (T (T (T h6 h20) h12) h47) h40) h64
  have h70 := S h57
  have h71 := C (C h70 h70) h56
  have h72 := T h54 h71
  have h73 := C h72 h69
  have h74 := C h73 h56
  let v75 := M v2 y
  have h76 := h v75 y v1
  have h77 := S h76
  have h78 := T (T (T (T (T h74 h68) h39) h13) h10) h7
  have h79 := h v75 v1 v1
  have h80 := S h79
  have h81 := C h60 h56
  have h82 := C h15 (T (T (T h52 h41) h67) h81)
  have h83 := C h21 (T h40 h64)
  have h84 := R (M v1 v1)
  have h85 := C h84 (T h83 h82)
  have h86 := C (T (T (T h25 h31) h51) h85) h78
  have h87 := T h86 h80
  have h88 := C h59 h87
  have h89 := T (T (T (T (T h6 h20) h12) h47) h67) h81
  have h90 := C h15 (T h52 h41)
  have h91 := C h21 (T (T (T h74 h68) h40) h64)
  have h92 := C h84 (T h91 h90)
  have h93 := C (T (T (T h92 h63) h28) h26) h89
  have h94 := C h65 (T (T (T (T (T h52 h41) h67) h81) h79) h93)
  have h95 := T (T h73 h94) h88
  have h96 := C h14 h95
  have h97 := C h96 h78
  let v98 := M v2 v2
  let v99 := M v98 v75
  have h100 := h v99 v1 v1
  have h101 := S h100
  have h102 := T (T (T (T (T (T (T h97 h77) h74) h68) h39) h13) h10) h7
  have h103 := C h65 (T (T (T (T (T h86 h80) h74) h68) h40) h64)
  have h104 := T h79 h93
  have h105 := C h72 h104
  have h106 := T (T h105 h103) h60
  have h107 := C h14 h106
  have h108 := C h107 h89
  have h109 := C h15 (T (T (T h86 h80) h76) h108)
  have h110 := C h21 h104
  have h111 := C h84 (T h110 h109)
  have h112 := C (T (T (T (T h25 h31) h51) h85) h111) h102
  have h113 := h y v2 v2
  have h114 := C h59 (T (T (T h112 h101) h97) h77)
  have h115 := T (T (T (T (T (T (T h6 h20) h12) h47) h67) h81) h76) h108
  have h116 := C h15 h87
  have h117 := C h21 (T (T (T h97 h77) h79) h93)
  have h118 := C h84 (T h117 h116)
  have h119 := C (T (T (T (T h118 h92) h63) h28) h26) h115
  have h120 := T h100 h119
  have h121 := C h72 h120
  have h122 := T (T (T (T h121 h114) h105) h103) h60
  have h123 := T h112 h101
  have h124 := C h59 h123
  have h125 := C h72 (T (T (T h76 h108) h100) h119)
  have h126 := T (T (T (T h73 h94) h88) h125) h124
  have h127 := h v75 y v0
  have h128 := h v36 v0 v0
  have h129 := h v36 v0 v1
  have h130 := h v75 v1 v2
  have h131 := C (T (T (T (T (T (T (T (C (T (T (T h67 h81) h130) (C (T (T (T (T (T (C (T h129 (C (T (T (T (T h90 h61) h43) h25) h31) h69)) (T (T (T h91 h90) h61) h43)) (S h128)) h39) h13) h10) h7) h95)) (T (T (T (T (T h117 h116) h91) h90) h61) h43)) (S h127)) h74) h68) h39) h13) h10) h7) h126
  have h132 := h v99 v1 v2
  have h133 := C (T (T (T (T (T (T (T (T (T (T (T h12 h47) h67) h81) h76) h108) h132) h131) (C h115 h122)) (S h113)) h54) h71) (T (T (T (T (T (T (T (T h112 h101) h97) h77) h74) h68) h39) h13) h22)
  have h134 := C h21 h120
  have h135 := C h15 h123
  have h136 := S h132
  have h137 := C (T (T (T (T (T (T (T h6 h20) h12) h47) h67) h81) h127) (C (T (T (T (C (T (T (T (T (T h6 h20) h12) h47) h128) (C (T (C (T (T (T (T h28 h26) h35) h49) h83) h53) (S h129)) (T (T (T h35 h49) h83) h82))) h106) (S h130)) h74) h68) (T (T (T (T (T h35 h49) h83) h82) h110) h109))) h122
  have h138 := C (T (T (T (T (T (T (T (T (T (T (T h58 h55) h113) (C h102 h126)) h137) h136) h97) h77) h74) h68) h39) h13) (T (T (T (T (T (T (T (T h17 h12) h47) h67) h81) h76) h108) h100) h119)
  have h139 := C h65 (T (T (T (T h52 h41) h39) h13) h22)
  have h140 := C (T (T (T (T (T (T (T (T (T (T (T h73 h139) h138) h135) h117) h116) h91) h90) h61) h34) h18) h50) (T (T (T (T (T (T h121 h114) h105) h103) h139) h138) h135)
  have h141 := C h14 (T h125 h124)
  have h142 := R v3
  have h143 := h z x v3
  have h144 := S h143
  let v145 := M x v3
  have h146 := h v3 (M v145 v5) v3
  have h147 := T h146 (C (C h144 h144) h142)
  have h148 := h z x v2
  have h149 := S h148
  let v150 := M x v2
  have h151 := h v2 (M v150 v5) v2
  have h152 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h96 h141) h140) h118) h92) h63) h28) h26) h35) h49) h83) h82) h110) h109) h134) h133) h66) h60) h151) (C (C h149 h149) h14)) h147
  have h153 := h v2 x v3
  have h154 := S h153
  have h155 := C (C h154 h154) h142
  have h156 := h v3 (M v145 v150) v3
  let v157 := M v3 v98
  have h158 := h v98 v1 v3
  have h159 := C h14 (T h121 h114)
  have h160 := C h14 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h96 h141) h140) h118) h92) h63) h28) h26) h35) h49) h83) h82) h110) h109) h134) h133) h66) h94) h88) h125) h124)
  have h161 := C (T (T (T (T (T (T (T (T (T (T (T h62 h46) h45) h49) h83) h82) h110) h109) h134) h133) h66) h60) (T (T (T (T (T (T h134 h133) h66) h94) h88) h125) h124)
  have h162 := C h14 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h121 h114) h105) h103) h139) h138) h135) h117) h116) h91) h90) h61) h43) h25) h31) h51) h85) h111) h161) h159) h107)
  have h163 := h v99 y v0
  have h164 := S h146
  have h165 := C (C h143 h143) h142
  have h166 := T h165 h164
  have h167 := h v3 v0 v1
  have h168 := S h151
  have h169 := C (C h148 h148) h14
  T (T (T (T (h x v2 v3) (C (C (R (M v2 v3)) (T (T (T (T h156 h155) h152) (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h169 h168) h73) h139) h138) h135) h117) h116) h91) h90) h61) h43) h25) h31) h51) h85) h111) h161) h159) h107) h158) (C (T (C (C h21 h147) (T (T (T (T (T (T (T (T (T (T (C h89 (T (T h96 h141) h162)) (C (T (T (T h76 h108) h132) h131) (T (T (T (T (T (T h160 h140) h118) h92) h63) h28) h26))) (S h163)) h97) h77) h74) h68) h39) h13) h10) h7)) (S h167)) h142)) (T (T (T h165 h164) h4) (C (T (T (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h169 h168) h73) h139) h138) h135) h117) h116) h91) h90) h61) h43) h25) h31) h51) h85) h111) h161) h159) h107) h166) (C (C h153 h153) h142)) (S h156)) (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h73 h139) h138) h135) h117) h116) h91) h90) h61) h43) h25) h31) h51) h85) h111) h161) h159) h107))))) (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (C (T h167 (C (C h15 h166) (T (T (T (T (T (T (T (T (T (T h6 h20) h12) h47) h67) h81) h76) h108) h163) (C (T (T (T h137 h136) h97) h77) (T (T (T (T (T (T h25 h31) h51) h85) h111) h161) h162))) (C h78 (T (T h160 h159) h107))))) h142) (S h158)) h96) h141) h140) h118) h92) h63) h28) h26) h35) h49) h83) h82) h110) h109) h134) h133) h66) h60) (R v157)))) h142)) (S (h v157 v2 v3))) (C (T (T h156 h155) h152) (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h96 h141) h140) h118) h92) h63) h28) h26) h35) h49) h83) h82) h110) h109) h134) h133) h66) h60))) (S h4)

