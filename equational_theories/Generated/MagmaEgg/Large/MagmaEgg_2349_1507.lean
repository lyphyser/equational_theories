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
theorem Equation2349_implies_Equation1507 (G: Type _) [Magma G] (h: Equation2349 G) : Equation1507 G := fun x y z =>
  let v0 := M z y
  let v1 := M z v0
  let v2 := M y x
  let v3 := M v2 v1
  have h4 := R y
  let v5 := M y v3
  have h6 := h v1 v3 z
  have h7 := S h6
  have h8 := R z
  let v9 := M x (M x (M v1 v1))
  have h10 := h v0 v9 z
  have h11 := S h10
  have h12 := h v1 x v1
  have h13 := R v9
  have h14 := C (T h12 (C h13 h12)) h8
  let v15 := M v0 v1
  let v16 := M v0 v15
  let v17 := M x (M x (M v0 v0))
  have h18 := h z v17 v16
  have h19 := S h18
  have h20 := R v16
  have h21 := h v0 v0 z
  have h22 := R v17
  have h23 := h v0 x v0
  have h24 := C (T h23 (C h22 (T h23 (C h22 h21)))) h20
  have h25 := T h24 h19
  have h26 := R v1
  have h27 := C h26 h25
  have h28 := T (T h27 h14) h11
  have h29 := C h8 h28
  have h30 := h v15 v0 v0
  have h31 := S h30
  have h32 := S h23
  have h33 := C (T (C h22 (T (C h22 (S h21)) h32)) h32) h20
  have h34 := T h18 h33
  have h35 := R v0
  have h36 := C h35 h34
  have h37 := C (T (C h22 h32) h32) h8
  have h38 := h y v17 z
  have h39 := T (T h38 h37) h36
  have h40 := C h39 h28
  have h41 := C h26 h34
  have h42 := S h12
  have h43 := C (T (C h13 h42) h42) h8
  have h44 := T (T h10 h43) h41
  have h45 := C h4 h44
  have h46 := C h35 (C h35 (T (T h45 h40) h31))
  have h47 := C h26 h46
  have h48 := C h8 h47
  have h49 := C h8 h48
  have h50 := C h4 h28
  have h51 := S h38
  have h52 := C (T h23 (C h22 h23)) h8
  have h53 := C h35 h25
  have h54 := T (T h53 h52) h51
  have h55 := C h54 h44
  have h56 := C h35 (C h35 (T (T h30 h55) h50))
  have h57 := C h26 h56
  have h58 := C h8 h57
  have h59 := C h8 h44
  let v60 := M y v0
  let v61 := M v0 (M v0 v60)
  have h62 := h v61 v1 v1
  have h63 := S h62
  have h64 := T (T (T h10 h43) h41) h57
  have h65 := C h35 h46
  have h66 := T (T (T h65 h53) h52) h51
  have h67 := C h8 h66
  have h68 := C h8 (T (T (T (T h67 h10) h43) h41) h57)
  have h69 := T (T h68 h48) h29
  have h70 := C h69 h64
  have h71 := h v61 z v0
  have h72 := C h26 (T h71 h70)
  have h73 := C (T (T (T (T h10 h43) h41) h57) h72) h26
  have h74 := h v60 v0 v0
  have h75 := C h35 h56
  have h76 := T (T (T h38 h37) h36) h75
  have h77 := S h71
  have h78 := T (T (T h47 h27) h14) h11
  have h79 := C h8 h76
  have h80 := C h8 (T (T (T (T h47 h27) h14) h11) h79)
  have h81 := T (T h59 h58) h80
  have h82 := C h81 h78
  have h83 := C h26 (T h82 h77)
  let v84 := M y v60
  let v85 := M x (M x (M y y))
  have h86 := h z v85 v84
  have h87 := R v84
  have h88 := h y y z
  have h89 := R v85
  have h90 := h y x y
  have h91 := C h4 h50
  have h92 := C h39 h78
  have h93 := C h4 (T h92 h55)
  have h94 := C h54 h64
  have h95 := C (T (T (T (T h83 h47) h27) h14) h11) h26
  have h96 := C h4 (T (T (T (T (T (T h18 h33) h56) h62) h95) h30) h94)
  have h97 := T (T h96 h93) h91
  have h98 := C h26 (T (T (T (T (T (T (T (C h4 h97) (C (T h90 (C h89 (T h90 (C h89 h88)))) h87)) (S h86)) h18) h33) h56) h71) h70)
  have h99 := C h81 (T (T (T (T (T h98 h83) h47) h27) h14) h11)
  have h100 := T (T (T (T h99 h77) h46) h24) h19
  have h101 := C h100 h76
  have h102 := h (M y z) v1 y
  have h103 := C h4 (T (T (T (T (T (T h92 h31) h73) h63) h46) h24) h19)
  have h104 := C h4 (T h40 h94)
  have h105 := C h4 h45
  have h106 := T (T h105 h104) h103
  have h107 := S h90
  have h108 := C h26 (T (T (T (T (T (T (T h82 h77) h46) h24) h19) h86) (C (T (C h89 (T (C h89 (S h88)) h107)) h107) h87)) (C h4 h106))
  have h109 := T (T (T (T (T (T (T (T h102 h101) h67) h10) h43) h41) h57) h72) h108
  have h110 := C h26 h109
  have h111 := C (T (T (T (T (T (T (T (T (T (C h76 (T (T (T (T (T (C h4 (C h26 h106)) (C h4 (T (T (T (T (T (T h110 h99) h77) h62) h95) h30) h94))) h103) h102) h101) h67)) (S h74)) h45) h40) h31) h73) h63) h46) h24) h19) (T h59 h58)
  have h112 := h v84 y v1
  have h113 := R v3
  have h114 := S h102
  have h115 := C h69 (T (T (T (T (T h10 h43) h41) h57) h72) h108)
  have h116 := T (T (T (T h18 h33) h56) h71) h115
  have h117 := C h116 h66
  have h118 := T (T (T (T (T (T (T (T h98 h83) h47) h27) h14) h11) h79) h117) h114
  have h119 := C (C h113 (T (T (T (T (C h113 h44) (C h113 h57)) (C h113 (T h72 h108))) (C h113 h118)) (C h113 (T (T (T (T (T (T h96 h93) h91) h112) h111) h49) (C h8 h29))))) h8
  have h120 := h y v3 z
  have h121 := T (T h120 h119) h7
  have h122 := S h120
  have h123 := S h112
  have h124 := C h26 h118
  have h125 := C (T (T (T (T (T (T (T (T (T h18 h33) h56) h62) h95) h30) h55) h50) h74) (C h66 (T (T (T (T (T h79 h117) h114) h96) (C h4 (T (T (T (T (T (T h92 h31) h73) h63) h71) h115) h124))) (C h4 (C h26 h97))))) (T h48 h29)
  have h126 := C h8 h58
  have h127 := C (C h113 (T (T (T (T (C h113 (T (T (T (T (T (T (C h8 h59) h126) h125) h123) h105) h104) h103)) (C h113 h109)) (C h113 (T h98 h83))) (C h113 h47)) (C h113 h28))) h8
  have h128 := C h35 (T (T h110 h99) h77)
  have h129 := T (T (T (T h128 h65) h53) h52) h51
  have h130 := C h116 h129
  have h131 := C h8 (T h130 h101)
  have h132 := C h35 (T (T h71 h115) h124)
  have h133 := T (T (T (T h38 h37) h36) h75) h132
  have h134 := C h100 h133
  let v135 := M x (M x (M v3 v3))
  have h136 := h v1 v135 v2
  have h137 := S h136
  have h138 := R v2
  have h139 := h v3 x v3
  have h140 := R v135
  have h141 := C (T h139 (C h140 h139)) h138
  have h142 := C h8 (T (T (T (T (T (T (T (T (C h8 (T (T h141 h137) h59)) h126) h125) h123) h105) h104) h103) h102) h134)
  have h143 := C (T (T (T (T (T (T (T h142 h131) h68) h48) h29) h6) h127) h122) h113
  have h144 := h v2 z v3
  let v145 := M x (M x (M v2 v2))
  have h146 := h x v145 y
  have h147 := h v2 x v2
  have h148 := R v145
  have h149 := T (T h6 h127) h122
  have h150 := R (M v2 (M z (M z (M v3 v2))))
  have h151 := S h139
  have h152 := C (T (C h140 h151) h151) h138
  have h153 := C h8 (T (T (T (T (T (T (T (T h130 h114) h96) h93) h91) h112) h111) h49) (C h8 (T (T h29 h136) h152)))
  have h154 := C h8 (T h117 h134)
  have h155 := R (M v2 (M v3 v5))
  have h156 := S h147
  T (T (h x y y) (C (T (C h4 (T (T (T (T (C h121 (C h121 (T (T (T h146 (C (T (C h148 h156) h156) h4)) (C h138 h133)) (C h138 (T (T (T (T (T (T (T (T (T (T (T (T h128 h65) h53) h52) h51) h120) h119) h7) h59) h58) h80) h154) h153))))) (C h149 (C h149 h150))) (C h121 (C h121 (C h138 (T (T (T (T (T (T (T h142 h131) h68) h48) h29) h136) h152) (C h113 (T h144 h143))))))) (C h149 (C h149 h155))) (C h121 (T (T (T (T (T (C h121 h155) (C h149 (C h138 (T (T (T (T (T (T (T (C h113 (T (C (T (T (T (T (T (T (T h120 h119) h7) h59) h58) h80) h154) h153) h113) (S h144))) h141) h137) h59) h58) h80) h154) h153)))) (C h121 h150)) (C h149 (T (T (T (C h138 (T (T (T (T (T (T (T (T (T (T (T (T h142 h131) h68) h48) h29) h6) h127) h122) h38) h37) h36) h75) h132)) (C h138 h129)) (C (T h147 (C h148 h147)) h4)) (S h146)))) h144) h143)))) (C h121 (R (M v1 v5)))) h4)) (S (h v3 v1 y))

