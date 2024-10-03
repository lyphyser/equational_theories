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
theorem Equation3120_implies_Equation1467 (G: Type _) [Magma G] (h: Equation3120 G) : Equation1467 G := fun x y z =>
  let v0 := M y z
  let v1 := M z v0
  let v2 := M x y
  let v3 := M v2 v1
  have h4 := R v3
  have h5 := R v1
  have h6 := h v1 v2 v3
  have h7 := S h6
  have h8 := h v2 v3 v3
  have h9 := C (T h8 (C h7 h4)) h5
  have h10 := h v3 v2 v1
  have h11 := R v2
  have h12 := S h8
  have h13 := R v0
  have h14 := h z v1 v1
  have h15 := h v0 z v1
  have h16 := C (T (C h15 h5) (S h14)) h13
  have h17 := C (T h16 h6) h4
  have h18 := C (T h17 h12) h4
  have h19 := h v1 v0 v3
  have h20 := C (T (C (C (C (T h19 h18) h11) h5) h5) (S h10)) h5
  have h21 := h v2 v1 v1
  have h22 := C (T h14 (C (S h15) h5)) h13
  have h23 := S h19
  have h24 := C (T h7 h22) h4
  have h25 := C (T h8 h24) h4
  have h26 := C (T (T (T (C (T h10 (C (C (C (T h25 h23) h11) h5) h5)) h5) (S h21)) h8) h24) h4
  have h27 := C (T (T h26 h23) h22) h4
  have h28 := C (T (T (T h17 h12) h21) h20) h4
  have h29 := h v1 v3 v1
  have h30 := S h29
  have h31 := C (C (T h19 h28) h5) h5
  have h32 := C (T (T (T h31 h30) h19) h28) h4
  have h33 := C (C (T h26 h23) h5) h5
  have h34 := h v1 z z
  have h35 := S h34
  have h36 := R z
  have h37 := h z v0 v0
  have h38 := S h37
  have h39 := h v0 z z
  have h40 := T h31 h30
  have h41 := h v1 v1 z
  have h42 := C (T (C (T (T (T h31 h30) h41) (C (C h40 h36) h36)) h36) (S h39)) h36
  have h43 := C (T (T (T h31 h30) h41) h42) h13
  have h44 := h v1 v1 v0
  have h45 := S h41
  have h46 := T h29 h33
  have h47 := C (T h39 (C (T (T (T (C (C h46 h36) h36) h45) h29) h33) h36)) h36
  have h48 := C (T (T (T h47 h45) h44) (C h43 h13)) h13
  have h49 := C h46 h13
  have h50 := C (T (T (T h49 h43) h48) h38) h5
  have h51 := h v0 v1 z
  have h52 := h v0 v1 v1
  have h53 := S h52
  have h54 := C h40 h13
  have h55 := C (T (T (T h47 h45) h29) h33) h13
  have h56 := C (T h55 h54) h5
  have h57 := h z v0 v1
  have h58 := C (T (T (T h48 h38) h57) (C h56 h5)) h5
  have h59 := C (T h49 h43) h5
  have h60 := C (T (T (T (C h55 h13) (S h44)) h41) h42) h13
  have h61 := C (T (T (T h37 h60) h55) h54) h5
  have h62 := C (T (T (T (T (T h61 h59) h58) h53) h51) (C (C h50 h36) h36)) h36
  have h63 := C (T (T (T h62 h35) h29) h33) h4
  have h64 := C (T (T (T (T (T (C (C h61 h36) h36) (S h51)) h52) (C (T (T (T (C h59 h5) (S h57)) h37) h60) h5)) h56) h50) h36
  have h65 := h v1 z v2
  have h66 := S h65
  have h67 := h v3 v2 v2
  have h68 := C (T (T (T (C (T h67 (C (T (T (T (C (C (T (T (T h25 h23) h34) h64) h11) h11) h66) h34) h64) h11)) h11) h66) h34) h64) h4
  have h69 := C (T (T (T h62 h35) h65) (C (T (C (T (T (T h62 h35) h65) (C (C (T (T (T h62 h35) h19) h18) h11) h11)) h11) (S h67)) h11)) h4
  have h70 := C (T (T (T h31 h30) h34) h64) h4
  have h71 := C (T (T (T h26 h23) h29) h33) h4
  have h72 := C (T (T h16 h19) h28) h4
  have h73 := h v2 v3 v2
  have h74 := S h73
  have h75 := C (C (T (T (T (T (T h8 h24) h72) h71) h70) h69) h11) h11
  have h76 := C (C (T (T (T (T (T h68 h63) h32) h27) h17) h12) h11) h11
  have h77 := h v2 v2 y
  have h78 := S h77
  have h79 := R y
  have h80 := h v2 v2 x
  have h81 := S h80
  have h82 := R x
  have h83 := T h73 h76
  have h84 := C (C h83 h82) h82
  have h85 := h y x x
  have h86 := C (T h85 (C (T (T (T h84 h81) h73) h76) h82)) h82
  have h87 := C (T (T (T h86 h81) h73) h76) h79
  have h88 := S h85
  have h89 := T h75 h74
  have h90 := C (C h89 h82) h82
  have h91 := C (T (C (T (T (T h75 h74) h80) h90) h82) h88) h82
  have h92 := C (T (T (T (C h87 h79) h78) h80) h91) h79
  have h93 := h x y y
  have h94 := h x y v2
  have h95 := S h94
  have h96 := C (T (T (T h75 h74) h80) h91) h79
  have h97 := C h83 h79
  have h98 := C (T h97 h96) h11
  have h99 := C (T (T (T (C h98 h11) h95) h93) h92) h11
  have h100 := h y v2 v2
  have h101 := C (T (T (T (T (C (T h100 h99) h11) h95) h93) h92) h87) h79
  have h102 := S h100
  have h103 := C h89 h79
  have h104 := C (T h87 h103) h11
  have h105 := S h93
  have h106 := C (T (T (T h86 h81) h77) (C h96 h79)) h79
  have h107 := C (T (T (T h106 h105) h94) (C h104 h11)) h11
  have h108 := C (T (T (T (T h96 h106) h105) h94) (C (T h107 h102) h11)) h79
  have h109 := C (T (T (T h84 h81) h77) h108) h82
  T (T (h x v1 v3) (C (C (T (T (T (T (T (T (C (T (C (T (T (T (T (T h34 h64) (C (T (T (T (T h61 h59) h58) h53) (C (T (T h100 h99) h104) h36)) h36)) (S (h y v2 z))) h85) h109) h82) (C (T (T (T (T (T (C (T (T (T h101 h78) h80) h90) h82) h88) h100) h99) h104) (C (T (T (T h97 h96) h106) h105) h11)) h82)) h5) (C (T (T (T (C (T (T (T (T (T (C (T (T (T h93 h92) h87) h103) h11) h98) h107) h102) h85) h109) h82) (S (h v2 y x))) h77) h108) h5)) (C (T (T (T h101 h78) h73) h76) h5)) (C (T (T (T (T (T (T (T h75 h74) h8) h24) h72) h71) h70) h69) h5)) (C (T (T (T (T (T (T (T (T h68 h63) h32) h27) h17) h12) h21) h20) (C h9 h5)) h5)) (S (h v3 v1 v1))) h9) h4) h4)) (S (h v3 v1 v3))

