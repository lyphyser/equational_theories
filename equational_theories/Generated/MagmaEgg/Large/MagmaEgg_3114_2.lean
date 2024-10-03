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
theorem Equation3114_implies_Equation2 (G: Type _) [Magma G] (h: Equation3114 G) : Equation2 G := fun x y =>
  have h0 := R y
  have h1 := R x
  let v2 := M x y
  have h3 := h v2 x x
  have h4 := S h3
  let v5 := M (M x x) x
  let v6 := M v5 x
  have h7 := h x v6 v6
  have h8 := S h7
  have h9 := R v6
  have h10 := h x x x
  have h11 := C (C (C h10 h9) h1) h9
  have h12 := h v6 x y
  have h13 := S h12
  have h14 := C (C (C (S h10) h9) h1) h9
  have h15 := T h7 h14
  have h16 := C h15 h0
  have h17 := T h16 h13
  have h18 := C (C (C h1 h17) h1) h17
  have h19 := T (T h18 h11) h8
  have h20 := T h11 h8
  have h21 := C h20 h0
  have h22 := T h12 h21
  have h23 := C (C (C h1 h22) h1) h22
  have h24 := T (T h7 h14) h23
  have h25 := C h24 h19
  have h26 := C h1 h23
  have h27 := C h1 h15
  have h28 := C (T (T (T h27 h26) h25) h4) h1
  have h29 := C h1 h20
  have h30 := C h29 h1
  have h31 := C h1 h18
  have h32 := C h31 h1
  have h33 := C h19 h24
  have h34 := C (T (T (T (T (T (C h32 h18) (C h30 h20)) h12) h21) h3) h33) h1
  have h35 := h (M (M (M x v2) x) v2) x x
  let v36 := M (M (M y x) y) x
  have h37 := h x v36 v36
  have h38 := S h37
  have h39 := R v36
  have h40 := h x y x
  have h41 := C (C (C h40 h39) h1) h39
  have h42 := C (C (C h0 h20) h0) h20
  have h43 := C (C (C h0 h18) h0) h18
  have h44 := S h35
  have h45 := C h26 h1
  have h46 := C h27 h1
  have h47 := C (T (T (T (T (T h25 h4) h16) h13) (C h46 h15)) (C h45 h23)) h1
  have h48 := T (T (T h46 h45) h47) h44
  have h49 := C (C (C h0 h48) h0) h48
  let v50 := M (M (M y v5) y) v5
  have h51 := h v50 x x
  have h52 := S h51
  have h53 := T (T (T h35 h34) h32) h30
  have h54 := C (C (C h0 h53) h0) h53
  have h55 := C (C (C h0 h23) h0) h23
  have h56 := C (C (C h0 h15) h0) h15
  have h57 := T (T h56 h55) h54
  have h58 := C (C (C h1 h57) h1) h57
  have h59 := C (C (C (S h40) h39) h1) h39
  have h60 := C (T (T h37 h59) h58) (T (T (T (T (T (T h46 h45) h47) h44) h18) h11) h8)
  have h61 := T (T (T (T h60 h52) h49) h43) h42
  have h62 := C (C (C h1 h61) h1) h61
  let v63 := M x v5
  have h64 := h v63 x x
  have h65 := S h64
  have h66 := h v5 y x
  have h67 := S h66
  have h68 := C (T h60 h52) h1
  have h69 := T (T h49 h43) h42
  have h70 := C (C (C h1 h69) h1) h69
  have h71 := C (T (T h70 h41) h38) (T (T (T (T (T (T h7 h14) h23) h35) h34) h32) h30)
  have h72 := T (T (T (T h56 h55) h54) h51) h71
  have h73 := C (C (C h1 h72) h1) h72
  have h74 := C (T (T h37 h59) h73) (T (T (T (T (T (T (T (T h68 h67) h46) h45) h47) h44) h18) h11) h8)
  let v75 := M v63 x
  have h76 := R v75
  have h77 := h v75 y x
  have h78 := S h77
  have h79 := C (T h51 h71) h1
  have h80 := T h66 h79
  have h81 := C (C (C h0 h80) h0) h80
  have h82 := C (T (T (T (T h74 h65) h60) h52) h81) h1
  have h83 := C (T (T (T (T (T (T (T (T (T (T h82 h78) h68) h67) h46) h45) h47) h44) h18) h11) h8) h76
  have h84 := C (T (T h62 h41) h38) (T (T (T (T (T (T (T (T h7 h14) h23) h35) h34) h32) h30) h66) h79)
  have h85 := T h68 h67
  have h86 := C (C (C h0 h85) h0) h85
  have h87 := C (T (T (T (T h86 h51) h71) h64) h84) h1
  have h88 := C (T h77 h87) h80
  have h89 := T (T (T h88 h83) h74) h65
  have h90 := C (C (C h1 h89) h1) h89
  have h91 := C (T h82 h78) h85
  have h92 := C (T (T (T (T (T (T (T (T (T (T h7 h14) h23) h35) h34) h32) h30) h66) h79) h77) h87) h76
  have h93 := h v50 x y
  have h94 := S h93
  have h95 := C (T (T (T (T (T h18 h11) h8) h37) h59) h58) h0
  have h96 := h v2 x y
  have h97 := T (T (T (T (T (T (T (T (T (T (T (T h27 h26) h25) h4) h96) h95) h94) h51) h71) h64) h84) h92) h91
  have h98 := C (C (C h1 h97) h1) h97
  have h99 := S h96
  have h100 := C (T (T (T (T (T h70 h41) h38) h7) h14) h23) h0
  have h101 := T (T (T (T (T (T (T (T (T (T (T (T (T h98 h90) h62) h41) h38) h7) h14) h23) h35) h34) h32) h30) h66) h79
  have h102 := T (T (T (T (T (T (T (T (T (T (T (T h88 h83) h74) h65) h60) h52) h93) h100) h99) h3) h33) h31) h29
  have h103 := C (C (C h1 h102) h1) h102
  have h104 := T (T (T h64 h84) h92) h91
  have h105 := C (C (C h1 h104) h1) h104
  have h106 := C (T (T (T h3 h33) h31) h29) h1
  have h107 := T (T (T (T (T (T (T (T (T (T (T (T h106 h46) h45) h47) h44) h18) h11) h8) h37) h59) h73) h105) h103
  have h108 := T (T (T (T (T (T (T (T (T (C (C (C h0 h107) h0) h107) (C (C (C h0 h101) h0) h101)) h86) h93) h100) h99) h3) h33) h31) h29
  have h109 := C (C (C h1 h108) h1) h108
  let v110 := M v2 x
  have h111 := h (M (M (M y v110) y) v110) x x
  have h112 := S h111
  have h113 := T (T (T (T (T (T (T (T (T (T (T (T h98 h90) h62) h41) h38) h7) h14) h23) h35) h34) h32) h30) h28
  have h114 := T (T (T (T (T (T (T (T (T (T (T (T (T h68 h67) h46) h45) h47) h44) h18) h11) h8) h37) h59) h73) h105) h103
  have h115 := T (T (T (T (T (T (T (T (T h27 h26) h25) h4) h96) h95) h94) h81) (C (C (C h0 h114) h0) h114)) (C (C (C h0 h113) h0) h113)
  have h116 := C (C (C h1 h115) h1) h115
  have h117 := C (T (T (T (T (T h37 h59) h73) h105) h103) h116) (T (T (T (T (T (T (T h106 h46) h45) h47) h44) h18) h11) h8)
  have h118 := T h117 h112
  have h119 := C (C (C h1 h118) h1) h118
  let v120 := M x v110
  have h121 := h v120 x x
  have h122 := S h121
  have h123 := h v110 y x
  have h124 := S h123
  have h125 := C h118 h1
  have h126 := C (T (T (T (T (T h109 h98) h90) h62) h41) h38) (T (T (T (T (T (T (T h7 h14) h23) h35) h34) h32) h30) h28)
  have h127 := T h111 h126
  have h128 := C (T (T (T (T (T (T h37 h59) h73) h105) h103) h116) (C (C (C h1 h127) h1) h127)) (T (T (T (T (T (T (T (T (T h125 h124) h106) h46) h45) h47) h44) h18) h11) h8)
  let v129 := M v120 x
  have h130 := h v129 y x
  have h131 := C h127 h1
  have h132 := T h123 h131
  have h133 := T h125 h124
  have h134 := T (T (T (C (T h130 (C (T (T (T (T (C (C (C h0 h133) h0) h133) h111) h126) h121) (C (T (T (T (T (T (T h119 h109) h98) h90) h62) h41) h38) (T (T (T (T (T (T (T (T (T h7 h14) h23) h35) h34) h32) h30) h28) h123) h131))) h1)) h132) (C (T (T (T (T (T (T (T (T (T (T (T (C (T (T (T (T h128 h122) h117) h112) (C (C (C h0 h132) h0) h132)) h1) (S h130)) h125) h124) h106) h46) h45) h47) h44) h18) h11) h8) (R v129))) h128) h122
  T (T (T (T h10 (C h22 h1)) (h v110 x y)) (C (T (h (M v129 v110) x y) (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (C (C (C h1 h134) h1) h134) h119) h109) h98) h90) h62) h41) h38) h7) h14) h23) h35) h34) h32) h30) h28) h0)) h0)) (S (h y x y))

