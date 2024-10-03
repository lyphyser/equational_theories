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
theorem Equation4197_implies_Equation4162 (G: Type _) [Magma G] (h: Equation4197 G) : Equation4162 G := fun x y z =>
  let v0 := M y x
  let v1 := M v0 z
  let v2 := M z v1
  have h3 := R y
  have h4 := R z
  let v5 := M v1 z
  have h6 := R v5
  have h7 := h z v1 v0
  have h8 := S h7
  have h9 := R v0
  have h10 := h v1 v1 v5
  have h11 := S h10
  have h12 := h z v1 v1
  have h13 := h z v1 z
  have h14 := S h13
  have h15 := R v1
  have h16 := h z z v0
  have h17 := S h16
  have h18 := C h17 h15
  have h19 := h z v0 v1
  have h20 := h z v0 x
  have h21 := S h20
  have h22 := R x
  have h23 := h x z y
  have h24 := S h23
  have h25 := h z y v0
  have h26 := C (T h25 (C h24 h9)) h22
  have h27 := C (T (T (T h26 h21) h19) h18) h4
  have h28 := h y x z
  have h29 := C (T (T (T h28 h27) h14) h12) h6
  have h30 := T h29 h11
  have h31 := C h30 h9
  have h32 := S h28
  have h33 := C (T (C h23 h9) (S h25)) h22
  have h34 := S h19
  have h35 := C h16 h15
  have h36 := C (T (T (T h35 h34) h20) h33) h4
  have h37 := S h12
  have h38 := C (T (T (T h37 h13) h36) h32) h6
  have h39 := h v1 v1 v0
  have h40 := S h39
  have h41 := h v0 v1 v5
  have h42 := S h41
  have h43 := h v5 v0 v0
  have h44 := S h43
  have h45 := h (M (M z y) x) z v5
  have h46 := S h45
  have h47 := C (C (C h6 (T h20 h33)) h4) h6
  let v48 := M z v0
  have h49 := h v48 z v5
  have h50 := T (T (T h49 h47) h46) h32
  have h51 := T h10 h38
  have h52 := C h51 h9
  have h53 := C (T (T (T (T h28 h27) h14) h7) h52) h50
  have h54 := S h49
  have h55 := C (C (C h6 (T h26 h21)) h4) h6
  have h56 := T (T (T h28 h45) h55) h54
  have h57 := C h9 h56
  have h58 := C (T (T (T h57 h53) h44) h17) h15
  have h59 := h v0 v0 v5
  have h60 := S h59
  have h61 := h v0 v0 z
  have h62 := S h61
  have h63 := h v0 v1 v0
  have h64 := C (T h63 (C (T (T h58 h35) h34) h9)) h4
  have h65 := h v1 z v0
  have h66 := C (T h65 (C (T (T (T (T h64 h62) h57) h53) h44) h9)) h6
  have h67 := C (T h66 h60) h15
  have h68 := C (T (T h67 h58) h35) h6
  have h69 := h v5 v1 v5
  have h70 := T (T h69 h68) h42
  have h71 := C (T (T (T h31 h8) h12) (C h70 h15)) h9
  have h72 := C (T (T (T (T (T (T (T h64 h62) h57) h53) h71) h40) h10) h38) h9
  have h73 := S h65
  have h74 := C h9 h50
  have h75 := C (T (T (T (T h31 h8) h13) h36) h32) h56
  have h76 := C (T (T (T h16 h43) h75) h74) h15
  have h77 := C (T (C (T (T h19 h18) h76) h9) (S h63)) h4
  have h78 := S h69
  have h79 := C (T (C (T (T (T (T h43 h75) h74) h61) h77) h9) h73) h6
  have h80 := C (T h59 h79) h15
  have h81 := C (T (T h18 h76) h80) h6
  have h82 := T (T h41 h81) h78
  have h83 := C (T (T (T (C h82 h15) h37) h7) h52) h9
  have h84 := C (T (T (T (T (T (T (T h29 h11) h39) h83) h75) h74) h61) h77) h9
  have h85 := T (T (T (T (T (T h28 h27) h14) h7) h52) h84) h73
  have h86 := T (T (T (T (T (T h65 h72) h31) h8) h13) h36) h32
  have h87 := h v0 z z
  have h88 := T (T (T (T (T (T (T (T h65 h72) h31) h8) h13) h36) h45) h55) h54
  have h89 := C h88 h4
  have h90 := T h89 (S h87)
  have h91 := C h90 h85
  have h92 := C h4 h50
  have h93 := C h4 h88
  have h94 := h v0 v1 z
  have h95 := S h94
  have h96 := h z v0 v0
  have h97 := h v0 v0 v1
  have h98 := C (T h97 (C (S h96) h15)) h4
  have h99 := C h74 h4
  have h100 := C h6 h50
  have h101 := C (T (T h100 h43) h75) h4
  let v102 := M v48 z
  have h103 := h y y v5
  have h104 := h v5 y v1
  have h105 := T (T (T (T (T (T (T (T h49 h47) h46) h27) h14) h7) h52) h84) h73
  have h106 := C h105 h4
  have h107 := h v102 z v0
  have h108 := C h57 h4
  have h109 := C (T (C h96 h15) (S h97)) h4
  have h110 := C (T (T (C (T (T h94 h109) h108) h9) (S h107)) h106) h9
  have h111 := h v1 v0 v0
  have h112 := h v0 y v1
  have h113 := C (T (T h112 (C (C (T (T h111 h110) h91) h3) h15)) (S h104)) h3
  have h114 := h x y y
  have h115 := S h111
  have h116 := C (T (T h89 h107) (C (T (T h99 h98) h95) h9)) h9
  have h117 := T h87 h106
  have h118 := C h117 h86
  let v119 := M x y
  have h120 := R v119
  have h121 := h v0 z v5
  have h122 := C h6 h56
  have h123 := C (T (T h93 h92) h19) h85
  have h124 := C h4 h105
  have h125 := C h4 h56
  have h126 := h z v1 x
  have h127 := h v1 y v5
  have h128 := S h127
  have h129 := C h82 h3
  have h130 := h x v1 y
  have h131 := h x v1 z
  have h132 := S h131
  have h133 := h z x x
  have h134 := S h133
  have h135 := h v1 v0 x
  have h136 := C (T (T (T (T h118 h116) h115) h135) (C (T (T (C (T h130 h129) h85) h128) h24) h22)) h22
  have h137 := h v5 x v1
  have h138 := h v5 x v0
  have h139 := S h138
  have h140 := C (C (T (T (T (T (T h57 h53) h71) h40) h10) h38) h22) h9
  have h141 := h v0 x v0
  have h142 := C (T (T (T (T (T (C (T (T h13 h36) h32) h22) h141) h140) h139) h137) (C (T h136 h134) h15)) h4
  have h143 := h v1 x z
  have h144 := C (T (T (T (T (T (C h90 h22) h143) h142) h132) h130) h129) h6
  have h145 := h z x v5
  have h146 := C (T (T (T (T (T h136 h134) h145) h144) h128) h24) h15
  have h147 := h x x v5
  have h148 := h x x v119
  have h149 := h y x x
  have h150 := C (T (T (T (T (T (T (T (T (C (T (T (T (T (T (T (C (T (T (T (T (T (T (T h65 h72) h31) h8) h13) h36) h32) h149) h120) (S h148)) h147) (C (T (T (T (T (T (C (T h137 h146) h22) (S h126)) h7) h52) h84) h73) h86)) h43) h71) h40) h15) (C h51 h15)) (C (T (T (T (T (T (T (T h29 h11) h39) h83) h75) h74) h59) h79) h15)) h67) h58) h35) h34) h125) h124) h86
  have h151 := h v119 v1 v5
  have h152 := C (T (C (T (T (T (T (T (T (T (T h151 h150) h123) h42) h94) h109) h108) (C (T (T h53 h44) h122) h4)) (C h100 h4)) h85) (S h121)) h120
  have h153 := h v1 v0 v119
  have h154 := S h135
  have h155 := S h130
  have h156 := C h70 h3
  have h157 := C (T h156 h155) h86
  have h158 := S h137
  have h159 := C (T (T (T (T (C (T (T h23 h127) h157) h22) h154) h111) h110) h91) h22
  have h160 := S h145
  have h161 := S h143
  have h162 := S h141
  have h163 := C (C (T (T (T (T (T h29 h11) h39) h83) h75) h74) h22) h9
  have h164 := C (T (T (T (T (T (C (T h133 h159) h15) h158) h138) h163) h162) (C (T (T h28 h27) h14) h22)) h4
  have h165 := C (T (T (T (T (T h156 h155) h131) h164) h161) (C h117 h22)) h6
  have h166 := C (T (T (T (T (T h23 h127) h165) h160) h133) h159) h15
  have h167 := C h24 h15
  have h168 := h v1 y x
  have h169 := h v1 x v5
  have h170 := h y v1 x
  have h171 := h v1 v0 y
  have h172 := S h151
  have h173 := C (T (T (T (T (T (T (T (T h93 h92) h19) h18) h76) h80) (C (T (T (T (T (T (T (T h66 h60) h57) h53) h71) h40) h10) h38) h15)) (C h30 h15)) (C (T (T (T (T (T (T h39 h83) h44) (C (T (T (T (T (T h65 h72) h31) h8) h126) (C (T h166 h158) h22)) h85)) (S h147)) h148) (C (T (T (T (T (T (T (T (S h149) h28) h27) h14) h7) h52) h84) h73) h120)) h15)) h85
  have h174 := C (T (T h34 h125) h124) h86
  have h175 := h v119 x v1
  have h176 := h x y v5
  let v177 := M v5 x
  let v178 := M v177 y
  have h179 := h v178 v5 v5
  have h180 := R v178
  have h181 := h v177 y v5
  have h182 := h (M v0 x) y v5
  have h183 := h x x y
  have h184 := h (M x x) v0 v0
  have h185 := h x v0 x
  T (T (T (T h114 h113) (C (T (T (T (C (T (T (T (T h65 h72) h31) (C (T (T (T (T (h v1 v1 x) (C (T (C (T (T (T (T h131 h164) h161) (h v1 x y)) (C (T (T (T (T (C (T (h y v1 v1) (C (T (T (T (T (T (T (T h167 h166) (C (T (T (T (T (T (T h136 h134) h145) h144) h128) h168) (C (T (T (T (C (T (T (T (T h131 h164) h161) h169) (C (T (C (T (T (T (T h69 h68) h174) h173) h172) h22) (S h170)) h86)) h3) (S h171)) h153) h152) h22)) h15)) (S h175)) (C (T (T (T h176 h179) (C (C (T (C h86 h180) (C h9 (T (T (T h181 (C (C (C h6 (T (T h138 h163) h162)) h3) h6)) (S h182)) (S h183)))) h86) h86)) (S h184)) h22)) (S h185)) (C h22 h56)) (C h22 h105)) h15)) h22) (C (T (T (T (T (T (C (T (T (T (T (T (T (T (C h22 h88) (C h22 h50)) h185) (C (T (T (T h184 (C (C (T (C h9 (T (T (T h183 h182) (C (C (C h6 (T (T h141 h140) h139)) h3) h6)) (S h181))) (C h85 h180)) h85) h85)) (S h179)) (S h176)) h22)) h175) (C (T (T (T (T (T (T (C (T (T (T (C (T h121 (C (T (T (T (T (T (T (T (T (C h122 h4) h101) h99) h98) h95) h41) h174) h173) h172) h86)) h120) (S h153)) h171) (C (T (T (T (T (C (T h170 (C (T (T (T (T h151 h150) h123) h81) h78) h22)) h85) (S h169)) h143) h142) h132) h3)) h22) (S h168)) h127) h165) h160) h133) h159) h15)) h146) (C h23 h15)) h15) (C (T (T h167 h166) h158) h15)) (S (h z x v1))) h145) h144) h157) h22)) h154) h153) h152) h3)) h15) (S (h v119 y v1))) h22)) (S (h y y x))) h103) (C (T (C (T (T h104 (C (C (T (T h118 h116) h115) h3) h15)) (S h112)) h3) (S h114)) h6)) h9)) (C (T (C (T h114 h113) h6) (S h103)) h9)) h3) (S (h y v0 y))) (h y v0 z)) (C (T (T (C (h z y v1) h85) (S (h y v1 v5))) (C h3 (T (T (T h87 (h v102 z v5)) (C (T (T (T (T (T (T (T (T h101 h99) h98) h95) h41) h81) h78) (h v5 v1 z)) (C (T (T (T (T (T (T (T (C (T (T (T h93 h92) (h z v0 v5)) (C h91 h86)) h15) (S (h v5 v0 v1))) h43) h71) h40) h10) h38) (C h85 (T (T (T h65 h72) h31) h8))) h4)) h6)) (S (h v2 z v5))))) h4)) h3)) (S (h (M v2 z) z y))) (S (h v1 z z))

