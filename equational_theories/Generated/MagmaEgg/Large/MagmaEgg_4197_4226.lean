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
theorem Equation4197_implies_Equation4226 (G: Type _) [Magma G] (h: Equation4197 G) : Equation4226 G := fun x y z =>
  have h0 := R y
  let v1 := M z z
  have h2 := h v1 x v1
  have h3 := S h2
  have h4 := R v1
  have h5 := R x
  have h6 := h z z z
  have h7 := C (S h6) h4
  have h8 := h z z v1
  have h9 := T h8 h7
  have h10 := C h9 h5
  have h11 := C h10 h4
  let v12 := M v1 x
  let v13 := M v12 y
  have h14 := R v13
  have h15 := R v12
  have h16 := T h11 h3
  have h17 := C (C h16 h0) h15
  have h18 := h v1 y v12
  have h19 := h v1 y x
  have h20 := S h19
  have h21 := h x v1 v1
  have h22 := S h21
  have h23 := S h8
  have h24 := C h6 h4
  have h25 := T h24 h23
  have h26 := C h25 h5
  have h27 := C h26 h4
  have h28 := C (T (T h26 h2) h27) h4
  have h29 := C (C (T (T h2 h28) h22) h0) h5
  have h30 := C (T (T h11 h3) h10) h4
  have h31 := C (C (T (T h21 h30) h3) h0) h5
  have h32 := C (T (T (C h25 h0) h19) h31) h4
  have h33 := h v1 y v1
  have h34 := S h18
  have h35 := T h2 h27
  have h36 := C (C h35 h0) h15
  let v37 := M x y
  have h38 := h v13 v12 v37
  have h39 := S h38
  have h40 := R v37
  have h41 := h x y x
  have h42 := S h41
  let v43 := M x x
  have h44 := h v43 y v13
  have h45 := S h44
  have h46 := h x x v13
  have h47 := h v12 v1 z
  have h48 := S h47
  have h49 := R z
  have h50 := h z v12 z
  have h51 := h v12 z v1
  have h52 := h z x z
  have h53 := C (T (T h52 h51) (C (S h50) h4)) h49
  have h54 := h (M z x) z v13
  have h55 := S h52
  have h56 := h x z z
  let v57 := M x z
  have h58 := h v57 z v13
  have h59 := C h14 (T (T (T (T (T (T h58 (C (C (C h14 (T (T h56 (C (T (T (T h53 h48) h11) h3) h49)) h55)) h49) h14)) (S h54)) h53) h48) h11) h3)
  have h60 := h (M v57 z) x v13
  have h61 := h z z x
  have h62 := C h14 (T (T (T h61 h60) (C (C (T (T (T (T h59 h36) h34) h19) h31) h5) h14)) (S h46))
  have h63 := h x y v1
  have h64 := C (T h63 h62) h0
  have h65 := S h63
  have h66 := C (T (C h65 h0) h64) h14
  have h67 := h v1 y v13
  have h68 := C (T (T h61 h60) (C (T (C (T (T (T (T (T h59 h36) h34) h67) h66) h45) h5) h42) h14)) h15
  have h69 := h v1 v1 v12
  have h70 := S h69
  have h71 := C (T h2 h28) h15
  have h72 := h v1 x v12
  have h73 := C h35 h5
  have h74 := C (T (C h73 h15) (S h72)) h15
  have h75 := h x v12 v12
  have h76 := h x v12 v1
  have h77 := C (T (T (T (T (T (T (S h76) h75) h74) h71) h70) h24) h23) h15
  have h78 := h v12 v1 v12
  have h79 := h x v12 y
  have h80 := h y x v12
  have h81 := S h80
  have h82 := C (T (T (T (T h2 h27) h78) h77) h68) h40
  have h83 := T (T (T (T (T h82 h39) h36) h34) h19) h31
  have h84 := C h83 h15
  have h85 := h v37 v12 v12
  have h86 := C h65 h15
  have h87 := h y v1 v12
  let v88 := M y v1
  have h89 := h v88 y v13
  have h90 := S h87
  have h91 := C h63 h15
  have h92 := C (T (C (T (T (T (T (T (T h82 h39) h36) h34) h67) h66) h45) h5) h42) h15
  have h93 := h v37 x v12
  have h94 := C h14 (T (T (T h93 h92) h91) h90)
  let v95 := M v37 x
  have h96 := h v95 y v13
  have h97 := C h10 (T (T (T (T (T (T (T (T (T (T h96 (C (C h94 h0) h14)) (S h89)) (C (T (T (T h87 h86) h85) (C (T h84 h81) h15)) h0)) (S h79)) h75) h74) h71) h70) h24) h23)
  have h98 := C (T (T (T (T h97 h27) h78) h77) h68) h40
  have h99 := h x y v37
  have h100 := S h99
  have h101 := h (M v95 y) v37 v12
  have h102 := S h101
  have h103 := S h93
  have h104 := S h78
  have h105 := S h75
  have h106 := C (T h72 (C (C h16 h5) h15)) h15
  have h107 := C (T h30 h3) h15
  have h108 := C (T (T (T (T (T (T h8 h7) h69) h107) h106) h105) h76) h15
  have h109 := S h61
  have h110 := S h60
  have h111 := C (T (T (C h50 h4) (S h51)) h55) h49
  have h112 := C h14 (T (T (T (T (T (T h2 h27) h47) h111) h54) (C (C (C h14 (T (T h52 (C (T (T (T h2 h27) h47) h111) h49)) (S h56))) h49) h14)) (S h58))
  have h113 := S h67
  have h114 := C h14 (T (T (T h46 (C (C (T (T (T (T h29 h20) h18) h17) h112) h5) h14)) h110) h109)
  have h115 := C (T h114 h65) h0
  have h116 := C (T h115 (C h63 h0)) h14
  have h117 := C (T (T (C (T h41 (C (T (T (T (T (T h44 h116) h113) h18) h17) h112) h5)) h14) h110) h109) h15
  have h118 := C (T (T (T (T h117 h108) h104) h11) h3) h40
  have h119 := C (T h41 (C (T (T (T (T (T (T h44 h116) h113) h18) h17) h38) h118) h5)) h15
  have h120 := C h14 (T (T (T h87 h86) h119) h103)
  have h121 := T (T (T (T (T h29 h20) h18) h17) h38) h118
  have h122 := C h121 h15
  have h123 := C h26 (T (T (T (T (T (T (T (T (T (T h8 h7) h69) h107) h106) h105) h79) (C (T (T (T (C (T h80 h122) h15) (S h85)) h91) h90) h0)) h89) (C (C h120 h0) h14)) (S h96))
  have h124 := C (T (T (T (T h117 h108) h104) h11) h123) h40
  have h125 := S h33
  have h126 := C (T (T h29 h20) (C h9 h0)) h4
  have h127 := C h83 h4
  have h128 := C (T (T (T (T (T (T h127 h126) h125) h18) h17) h38) h124) h15
  have h129 := h v37 v1 v12
  have h130 := T (T (T h129 h128) h102) h100
  have h131 := C (T h2 h123) h130
  have h132 := S h129
  have h133 := C h121 h4
  have h134 := C (T (T (T (T (T (T h98 h39) h36) h34) h33) h32) h133) h15
  have h135 := T (T (T h99 h101) h134) h132
  have h136 := h v1 v1 v37
  have h137 := C (T (C (T (C (T (T (T (T h99 h101) h134) h132) (C h135 h4)) h130) (S h136)) h5) h26) h135
  have h138 := h (M v37 v1) x v37
  have h139 := h y v1 x
  have h140 := S (h v1 v1 x)
  have h141 := C (T h11 (C (T (T (T h26 h2) h28) h22) h4)) h5
  have h142 := T (T (T h80 h122) (C (T (T (T (T (T (T h82 h39) h36) h34) h33) h32) h133) h15)) h132
  have h143 := h (M y x) y v13
  have h144 := C (T (T (T (T (T (T h127 h126) h125) h18) h17) h38) h118) h15
  have h145 := T (T (T h129 h144) h84) h81
  have h146 := h (M v43 y) x v13
  have h147 := h v88 x v13
  have h148 := h (M v88 x) y v13
  have h149 := h v1 x y
  have h150 := C (T (T (T (T (T (T h149 h148) (C (C (T (C h14 (T (T (T (T (T (T (T h147 (C (C (T h120 (C h14 (T (T (T (T (T (T (T (T (T (T (T (T (T (T h93 h92) h91) h90) h139) h138) h137) h131) h98) h39) h36) h34) h67) h66) h45))) h5) h14)) (S h146)) h42) h99) h101) h134) h132)) (C h14 h145)) h0) h14)) (S h143)) (C h142 h0)) (C (T (T (T (T (T h129 h128) h102) h100) h63) h62) h0)) h115) h15
  have h151 := S h149
  have h152 := S h148
  have h153 := S h139
  have h154 := S h138
  have h155 := C (T h10 (C (T h136 (C (T (T (T (T (C h130 h4) h129) h128) h102) h100) h135)) h5)) h130
  have h156 := C (T h97 h3) h135
  have h157 := C (C (T (C h14 h142) (C h14 (T (T (T (T (T (T (T h129 h128) h102) h100) h41) h146) (C (C (T (C h14 (T (T (T (T (T (T (T (T (T (T (T (T (T (T h44 h116) h113) h18) h17) h38) h124) h156) h155) h154) h153) h87) h86) h119) h103)) h94) h5) h14)) (S h147)))) h0) h14
  have h158 := C h145 h0
  have h159 := C (T (T (T (T (T h114 h65) h99) h101) h134) h132) h0
  T (T (h x y v13) (h (M (M v13 x) y) v13 y)) (C (T (T (T (C (T (T (T (T (T (T (T (T (T (T (T (C h0 (T (T (T (T (T (T (T (C (T (T (T (T (T (T (T h29 h20) h18) h17) h38) h124) h156) (C h15 h145)) h0) (C (T (T (T (T (T (T (T (T (T (T (C h15 h142) h155) h154) h153) h87) h86) h119) h103) (C h63 h5)) (C (T (T (T (T (T (T (T (T (T h65 h99) h101) h134) h144) h84) h81) (h y x v37)) (C (T (T (T (T (T (C (T (T (T (T (T (T (T (T h64 h159) h158) h143) h157) h152) h151) h2) h27) h5) h141) h140) h69) h107) h150) h40)) (C (T (T (T (T (C (T (T (T (T (T (T h64 h159) h158) h143) h157) h152) h151) h15) h71) h70) h24) h23) h135)) h5)) (C (T (C (T (T (T (T h8 h7) h69) h107) h150) h130) (S (h y v12 v37))) h5)) h0)) (S (h v12 x y))) h73) h141) h140) h24) h23)) h139) h138) h137) h131) h98) h39) h36) h34) h33) h32) (C (T (T (T h29 h20) h18) h17) h4)) h14) (S (h v12 v1 v13))) h11) h3) h0)

