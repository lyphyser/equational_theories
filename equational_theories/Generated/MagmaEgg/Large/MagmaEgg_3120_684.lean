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
theorem Equation3120_implies_Equation684 (G: Type _) [Magma G] (h: Equation3120 G) : Equation684 G := fun x y z =>
  let v0 := M y z
  let v1 := M v0 z
  let v2 := M x v1
  let v3 := M y v2
  have h4 := R v3
  have h5 := R v2
  have h6 := h v2 y v3
  have h7 := S h6
  have h8 := h y v3 v3
  have h9 := C (T h8 (C h7 h4)) h5
  have h10 := h v3 v2 v1
  have h11 := S h10
  have h12 := h v1 v1 v0
  have h13 := S h12
  have h14 := R v0
  have h15 := R v1
  have h16 := R z
  have h17 := h v0 v1 v1
  have h18 := S h17
  have h19 := h z v0 v1
  have h20 := C h19 h15
  have h21 := C (T h20 h18) h16
  have h22 := C (C h21 h15) h15
  have h23 := h v1 z v1
  have h24 := T h23 h22
  have h25 := C h24 h14
  have h26 := C h25 h14
  have h27 := C (T (T (T h26 h13) h23) h22) h14
  have h28 := h z v0 v0
  have h29 := h z y v0
  have h30 := S h29
  have h31 := C (T (T h30 h28) h27) h14
  have h32 := h y v0 v0
  have h33 := T (T h32 h31) h13
  have h34 := C h9 h15
  have h35 := h v3 v2 y
  have h36 := S h35
  have h37 := R y
  have h38 := C (C h9 h37) h37
  have h39 := C (T h38 h36) h33
  have h40 := h v2 y y
  have h41 := h v2 v1 v3
  have h42 := S h19
  have h43 := C h42 h15
  have h44 := C (T h17 h43) h16
  have h45 := S h23
  have h46 := C (C h44 h15) h15
  have h47 := T (T h46 h45) h44
  have h48 := h v1 v1 v1
  have h49 := S h48
  have h50 := C (C h24 h33) h15
  have h51 := S h32
  have h52 := S h28
  have h53 := T h46 h45
  have h54 := C h53 h14
  have h55 := C h54 h14
  have h56 := C (T (T (T h46 h45) h12) h55) h14
  have h57 := C (T (T h56 h52) h29) h14
  have h58 := T (T h12 h57) h51
  have h59 := C (C h53 h58) h15
  have h60 := h y v1 z
  have h61 := S h60
  have h62 := h v0 v1 y
  have h63 := S h62
  have h64 := R (M (M v1 v0) v1)
  have h65 := C (T (T h32 h31) h55) h14
  have h66 := C (T (T (T h65 h52) h19) (C h64 h58)) h37
  have h67 := h v0 y z
  have h68 := C (T (T h26 h57) h51) h14
  have h69 := C (T h28 h68) h37
  have h70 := C (T (T (T (T h69 h66) h63) h67) (C (T (T (T (C (T (T (T h66 h63) h17) h43) h16) h21) h48) h59) h16)) h16
  have h71 := T (T (T (T (T (T h70 h61) h32) h31) h13) h48) h59
  have h72 := C (T h65 h52) h37
  have h73 := C (T (T (T (C h64 h33) h42) h28) h68) h37
  have h74 := C (T (T (T (T (C (T (T (T h50 h49) h44) (C (T (T (T h20 h18) h62) h73) h16)) h16) (S h67)) h62) h73) h72) h16
  have h75 := h y z v1
  have h76 := S h75
  have h77 := R (M (M z y) z)
  have h78 := C (T (C (T h60 h74) h37) (C h77 h33)) h33
  have h79 := T (T (T h78 h76) h60) h74
  have h80 := C (T (C h77 h58) (C (T h70 h61) h37)) h58
  have h81 := h v1 z y
  have h82 := S h81
  have h83 := C (C (T (T (T h32 h31) h13) h44) h58) h37
  have h84 := T (T (T (T (T (T h83 h82) h12) h57) h51) h75) h80
  have h85 := C (C (T (T (T h21 h12) h57) h51) h33) h37
  have h86 := h v1 y v0
  have h87 := S h86
  have h88 := T (T (T (T (T (T h78 h76) h32) h31) h13) h81) h85
  have h89 := C h88 h14
  have h90 := T (T (T h70 h61) h75) h80
  have h91 := C h90 h14
  have h92 := T (T (T (T (T (T h50 h49) h12) h57) h51) h60) h74
  have h93 := C h92 h14
  have h94 := T (T (T (T h32 h31) h13) h48) h59
  have h95 := C h94 h14
  have h96 := h z v0 y
  have h97 := R (M (M y v0) y)
  have h98 := C (T (T (T (T (T (T (T (T (T (C (T h62 h73) h15) (C h97 h58)) (C (T h72 (C (T (T h28 h27) h54) h37)) h37)) (S h96)) h28) h68) h95) h93) h91) h89) h14
  have h99 := T (T (T h98 h87) h81) h85
  have h100 := T (T (T (T h50 h49) h12) h57) h51
  have h101 := C h100 h14
  have h102 := C h71 h14
  have h103 := C h79 h14
  have h104 := C h84 h14
  have h105 := C (T (T (T (T (T (T (T (T (T h104 h103) h102) h101) h65) h52) h96) (C (T (C (T (T h25 h56) h52) h37) h69) h37)) (C h97 h33)) (C (T h66 h63) h15)) h14
  have h106 := h v1 v0 v0
  have h107 := S h106
  have h108 := T (T (T h83 h82) h86) h105
  have h109 := h z y v1
  have h110 := R (M v0 y)
  have h111 := h v0 z y
  have h112 := C (T (T (T (T (T (T (T (T (C (T (T h111 (C (C (C (T (C h29 h14) h51) h16) h37) h37)) (C h110 h33)) h33) (S h109)) h28) h68) h95) h93) h91) h89) (C h108 h14)) h14
  have h113 := T (T (T h112 h107) h86) h105
  have h114 := C (T (T (T (T (T (T (T (T (C h99 h14) h104) h103) h102) h101) h65) h52) h109) (C (T (T (C h110 h58) (C (C (C (T h32 (C h30 h14)) h16) h37) h37)) (S h111)) h58)) h14
  have h115 := h y v2 v2
  have h116 := S h40
  have h117 := S h8
  have h118 := C (T (C h6 h4) h117) h5
  have h119 := C (C h118 h37) h37
  have h120 := C (T (T (C h118 h15) (C (T h35 h119) h58)) h116) h58
  have h121 := C (T h10 h120) h5
  have h122 := C h118 h5
  have h123 := h v3 v2 v2
  have h124 := C (T (T h40 h39) h34) h33
  have h125 := C (T (T (T (T (T (T (T (T (T (T (T h38 h36) h123) (C (T (T (T (T (T (T (T (T h122 h121) (C (T (T (T h124 h11) h123) (C (T h122 h121) h5)) h5)) (S h115)) h32) h31) h13) h106) h114) h5)) (C h113 h5)) (C h99 h5)) (C h84 h5)) (C h79 h5)) (C h71 h5)) (C (T (T (T h50 h49) h23) h22) h5)) (C h47 h5)) (C h21 h5)) h33
  have h126 := T (T (T h98 h87) h106) h114
  have h127 := T (T h21 h23) h22
  have h128 := S h123
  have h129 := C h9 h5
  have h130 := C (T h124 h11) h5
  have h131 := C (T (T (T (T (T (T (T (T (T (T (T (C h44 h5) (C h127 h5)) (C (T (T (T h46 h45) h48) h59) h5)) (C h92 h5)) (C h90 h5)) (C h88 h5)) (C h108 h5)) (C h126 h5)) (C (T (T (T (T (T (T (T (T h112 h107) h12) h57) h51) h115) (C (T (T (T (C (T h130 h129) h5) h128) h10) h120) h5)) h130) h129) h5)) h128) h35) h119) h58
  have h132 := h v2 v1 v2
  have h133 := C (C (T h131 h116) h5) h5
  have h134 := S (h v2 v2 x)
  have h135 := R x
  T (T (h x v1 v3) (C (T (T (C (T (T (C (T (T (T (T (T (T (T (T (T (C (T h48 h59) h135) (C h92 h135)) (C h90 h135)) (C h88 h135)) (C h108 h135)) (C h126 h135)) (C (T (T (T (T (T (T h112 h107) h12) h57) h51) (h y x x)) (C (T (T (T (C (C (T (T (C h135 h33) h132) h133) h135) h135) h134) h132) h133) h135)) h135)) h134) h132) h133) h58) (C (R (M (M v2 v2) v2)) h33)) (C (T (T (T (T (T (T (T (T (T (T (T (T (C (C (T h40 h125) h5) h5) (S h132)) h41) (C (T (T (T (T (T (T (C (T (T h131 h116) h6) h4) h117) h32) h31) h13) h106) h114) h4)) (C h113 h4)) (C h99 h4)) (C h84 h4)) (C h79 h4)) (C h71 h4)) (C h100 h4)) (C (T (T (T (T h32 h31) h13) h23) h22) h4)) (C h47 h4)) (C h21 h4)) h15)) h4) (C (C (T (T (C h44 h4) (C h127 h4)) (C (T (T (T (T h46 h45) h12) h57) h51) h4)) h58) h4)) (C (T (T (C (T (T (T (T (T (T (T (T (T (T (C h94 h4) (C h92 h4)) (C h90 h4)) (C h88 h4)) (C h108 h4)) (C h126 h4)) (C (T (T (T (T (T (T h112 h107) h12) h57) h51) h8) (C (T (T h7 h40) h125) h4)) h4)) (S h41)) h40) h39) h34) h33) h11) h9) h4)) h4)) (S (h v3 v2 v3))

