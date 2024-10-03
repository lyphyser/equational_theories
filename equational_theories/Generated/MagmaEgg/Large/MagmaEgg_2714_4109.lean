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
theorem Equation2714_implies_Equation4109 (G: Type _) [Magma G] (h: Equation2714 G) : Equation4109 G := fun x y z =>
  let v0 := M x x
  let v1 := M y z
  let v2 := M v1 z
  let v3 := M v2 y
  have h4 := R y
  have h5 := h x x y
  have h6 := S h5
  have h7 := C (C h6 h6) h4
  have h8 := h y (M v0 (M x y)) y
  have h9 := T h8 h7
  have h10 := R v3
  have h11 := h x x v3
  have h12 := S h11
  have h13 := C (C h12 h12) h10
  have h14 := h v3 (M v0 (M x v3)) v3
  have h15 := T (C (C h5 h5) h4) (S h8)
  have h16 := h v2 (M v0 (M x v2)) v2
  have h17 := S h16
  have h18 := R v2
  have h19 := h x x v2
  have h20 := C (C h19 h19) h18
  have h21 := T h20 h17
  have h22 := C h21 h15
  have h23 := h v2 v0 y
  have h24 := S h23
  have h25 := S h19
  have h26 := C (C h25 h25) h18
  have h27 := T h16 h26
  have h28 := C (C h27 h9) h4
  have h29 := T h28 h24
  have h30 := R v0
  have h31 := C h30 h29
  let v32 := M v3 y
  have h33 := h v32 v0 v3
  have h34 := S h33
  have h35 := T h14 h13
  have h36 := C h22 h4
  have h37 := T h23 h36
  have h38 := C h30 h37
  have h39 := T (T h16 h26) h38
  have h40 := C (C h39 h35) h10
  have h41 := T h40 h34
  have h42 := C h30 h41
  have h43 := T (C (C h11 h11) h10) (S h14)
  have h44 := T (T h31 h20) h17
  have h45 := C (C h44 h43) h10
  have h46 := h v32 v0 v2
  have h47 := S h46
  let v48 := M v0 v2
  have h49 := R v48
  have h50 := C h42 h49
  have h51 := T h33 h45
  have h52 := C h30 h51
  have h53 := T (T (T h16 h26) h38) h52
  have h54 := C h53 (T (T (T (T (T h40 h34) h28) h24) h16) h26)
  have h55 := C h18 h51
  have h56 := C h18 h37
  let v57 := M v2 v2
  have h58 := h v57 v3 y
  have h59 := S h58
  have h60 := R (M v3 v57)
  have h61 := C h60 h37
  have h62 := h y v2 v2
  have h63 := C (T h62 h61) h4
  have h64 := h (M y y) v3 y
  have h65 := S h64
  have h66 := R v32
  have h67 := S h62
  have h68 := C h60 h29
  have h69 := C (T h68 h67) h4
  have h70 := h y v3 v3
  let v71 := M v3 v3
  have h72 := R v71
  have h73 := C (T (T (T (T (C (C h37 h72) h10) (S h70)) h62) h61) (C (C h10 (T h58 h69)) h66)) h4
  have h74 := h v71 v2 y
  have h75 := C (T (T (T (T (T (T (T (T h74 h73) h65) h63) h59) h56) h55) h54) h50) h29
  have h76 := T (T (T h75 h47) h33) h45
  have h77 := C h30 h76
  have h78 := S h74
  have h79 := C (T (T (T (T (C (C h10 (T h63 h59)) h66) h68) h67) h70) (C (C h29 h72) h10)) h4
  have h80 := C h18 h29
  have h81 := C h18 h41
  have h82 := T (T (T h42 h31) h20) h17
  have h83 := C h82 (T (T (T (T (T h20 h17) h23) h36) h33) h45)
  have h84 := C h52 h49
  have h85 := C (T (T (T (T (T (T (T (T h84 h83) h81) h80) h58) h69) h64) h79) h78) h37
  have h86 := T (T (T (T (T h20 h17) h23) h36) h46) h85
  have h87 := C h30 h86
  have h88 := h v0 (M v0 (M x v0)) v0
  have h89 := S h88
  have h90 := h x x v0
  have h91 := C (C h90 h90) h30
  have h92 := T h91 h89
  have h93 := C h92 h49
  have h94 := T (T (T (T h93 h87) h77) h42) h31
  have h95 := C h53 h94
  have h96 := S h90
  have h97 := C (C h96 h96) h30
  have h98 := T h88 h97
  have h99 := C h98 h49
  have h100 := T (T (T (T (T h75 h47) h28) h24) h16) h26
  have h101 := C h30 h100
  have h102 := T (T (T h40 h34) h46) h85
  have h103 := C h30 h102
  have h104 := T (T (T (T h38 h52) h103) h101) h99
  have h105 := C h98 h94
  have h106 := C (T (T (T (T (T (T (T h105 h93) h87) h77) h42) h31) h20) h17) h104
  have h107 := C h92 h104
  have h108 := C h107 h27
  have h109 := h v0 v0 v2
  have h110 := C h4 h104
  have h111 := C h4 h100
  have h112 := C h4 h102
  have h113 := C h4 h51
  have h114 := C h4 h37
  let v115 := M y v2
  have h116 := h v115 v1 z
  have h117 := S h116
  have h118 := R z
  have h119 := h z y v2
  have h120 := C h119 h118
  have h121 := h z (M v0 (M x z)) z
  have h122 := S h121
  have h123 := h x x z
  have h124 := C (C h123 h123) h118
  have h125 := S h109
  have h126 := C h105 h21
  have h127 := C (T (T (T (T (T (T (T h16 h26) h38) h52) h103) h101) h99) h107) h94
  have h128 := C h82 h104
  have h129 := T (T h127 h126) h125
  have h130 := C h129 (T (T (T (T (T (T h56 h55) h54) h128) h127) h126) h125)
  have h131 := T (T (T (T h74 h73) h65) h63) h59
  have h132 := h v3 v0 v2
  have h133 := C h10 (T (T (C (T (T (T (C h10 h37) (C h10 h51)) (C h10 h102)) (C h10 h100)) h66) (C (C h35 h49) h29)) (S h132))
  have h134 := C (T (T (T (T (T (T (T (T (T h133 h74) h73) h65) h63) h59) h56) h55) h54) h128) h131
  have h135 := T (T (T (T h58 h69) h64) h79) h78
  have h136 := C h10 (T (T h132 (C (C h43 h49) h37)) (C (T (T (T (C h10 h86) (C h10 h76)) (C h10 h41)) (C h10 h29)) h66))
  have h137 := C h39 h49
  have h138 := C (T (T (T (T (T (T (T (T (T (T h137 h84) h83) h81) h80) h58) h69) h64) h79) h78) h136) h135
  have h139 := R v57
  have h140 := C h44 h49
  have h141 := C h39 h100
  have h142 := C (T h141 h140) h139
  have h143 := C h44 h86
  have h144 := C (T (T (T (T (T (T (T (T (T h74 h73) h65) h63) h59) h56) h55) h54) h50) h143) h131
  have h145 := T (T h109 h108) h106
  have h146 := C h145 (T (T (T (T (T (T (T (T (T (T (T (T (T h144 h142) h138) h134) h130) h91) h89) h109) h108) h106) h95) h83) h81) h80)
  have h147 := h (M v71 v71) v0 v1
  have h148 := S h147
  have h149 := R v1
  have h150 := h x x v1
  have h151 := S h150
  have h152 := C (C h151 h151) h149
  have h153 := h v1 (M v0 (M x v1)) v1
  have h154 := C (T (T (T (T (T (T (T (T (T h141 h84) h83) h81) h80) h58) h69) h64) h79) h78) h135
  have h155 := C (T h137 h143) h139
  have h156 := C (T (T (T (T (T (T (T (T (T (T h133 h74) h73) h65) h63) h59) h56) h55) h54) h50) h140) h131
  have h157 := C (T (T (T (T (T (T (T (T (T h95 h83) h81) h80) h58) h69) h64) h79) h78) h136) h135
  have h158 := C h145 (T (T (T (T (T (T h109 h108) h106) h95) h83) h81) h80)
  have h159 := C h129 (T (T (T (T (T (T (T (T (T (T (T (T (T h56 h55) h54) h128) h127) h126) h125) h88) h97) h158) h157) h156) h155) h154)
  have h160 := C (T (T h153 h152) (C (T (T (T h88 h97) h158) h159) (T h153 h152))) h149
  have h161 := C h30 (T h160 h148)
  have h162 := C (T (T (C (T (T (T (T h161 h146) h130) h91) h89) (T h124 h122)) h124) h122) h118
  have h163 := h (M v1 v1) v0 z
  have h164 := S h153
  have h165 := C (C h150 h150) h149
  have h166 := C (T (T (C (T (T (T h146 h130) h91) h89) (T h165 h164)) h165) h164) h149
  have h167 := S h163
  have h168 := S h123
  have h169 := C (C h168 h168) h118
  have h170 := C h30 (T h147 h166)
  have h171 := C (T (T h121 h169) (C (T (T (T (T h88 h97) h158) h159) h170) (T h121 h169))) h118
  have h172 := C (S h119) h118
  have h173 := C h4 h29
  have h174 := C h4 h41
  have h175 := C h4 h76
  have h176 := C h4 h86
  have h177 := C h4 h94
  have h178 := T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h177 h176) h175) h174) h173) h116) h172) h171) h167) h160) h148) h144) h142) h138) h134) h130) h91) h89
  have h179 := C h178 (T (T (T h116 h172) h171) h167)
  have h180 := R v115
  have h181 := T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h88 h97) h158) h157) h156) h155) h154) h147) h166) h163) h162) h120) h117) h114) h113) h112) h111) h110
  have h182 := C h181 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (C (T (T h120 h117) h114) (T h120 h117)) (C h113 h180)) (C h112 h180)) (C h111 h180)) (C h110 h180)) h179) h161) h146) h157) h156) h155) h154) h147) h166) h163) h162) h120) h117)
  have h183 := C (T (T h173 h116) h172) (T h116 h172)
  have h184 := C h174 h180
  have h185 := C h175 h180
  have h186 := C h176 h180
  have h187 := C h177 h180
  have h188 := C h181 (T (T (T h163 h162) h120) h117)
  let v189 := M z z
  T (T (T (T (T (T (T (T (T h109 h108) h106) h95) h83) h81) h80) h58) (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h68 h67) h8) h7) (C (T (T (T (T (T (T h88 h97) h158) h159) h170) h188) (C h178 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h116 h172) h171) h167) h160) h148) h144) h142) h138) h134) h159) h170) h188) h187) h186) h185) h184) h183))) h9)) (C (T (T (T (T (T (T (T h182 h187) h186) h185) h184) h183) (h (M v189 v189) v0 v0)) (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (C (T (T (T (T (T (T h182 h179) h161) h146) h130) h91) h89) (T (T (T (T (T (T (T (T h158 h159) h170) h188) h187) h186) h185) h184) h183)) h182) h179) h161) h146) h157) h156) h155) h154) h147) h166) h163) h162) h120) h117) h114) h113) h112) h111) h110) (T (T (T (T (T (T (T (T h109 h108) h106) h95) h83) h81) h80) h58) h69))) h15)) (S (h (M (M v0 v0) v48) y y))) h93) h87) h77) h42) h31) h20) h17) h23) (C (T (T h22 h14) h13) h9)) h4)) (S (h v3 v0 y))

