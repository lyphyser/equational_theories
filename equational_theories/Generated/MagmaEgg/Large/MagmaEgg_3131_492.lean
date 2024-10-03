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
theorem Equation3131_implies_Equation492 (G: Type _) [Magma G] (h: Equation3131 G) : Equation492 G := fun x y z =>
  let v0 := M z y
  let v1 := M z v0
  let v2 := M x v1
  let v3 := M y v2
  have h4 := h v3 y v3
  have h5 := S h4
  have h6 := h y v0 v0
  have h7 := S h6
  have h8 := R v0
  have h9 := R y
  have h10 := h z v0 v3
  have h11 := S h10
  have h12 := R v3
  have h13 := R z
  have h14 := h v0 z v2
  have h15 := S h14
  have h16 := R v2
  have h17 := h v1 z z
  have h18 := S h17
  have h19 := R v1
  have h20 := h z v1 z
  have h21 := h v0 z z
  have h22 := C (C (T (C h21 h19) (S h20)) h19) h13
  have h23 := h y z v1
  have h24 := C (T h23 h22) h13
  have h25 := C h24 h13
  have h26 := h y v3 y
  have h27 := S h26
  have h28 := h v2 y y
  have h29 := C h28 h12
  have h30 := T h29 h27
  have h31 := C (T (T (C (C h30 h13) h13) h25) h18) h16
  have h32 := h v3 v2 z
  have h33 := C (T h32 h31) h16
  have h34 := C h33 h13
  have h35 := C (C (T h34 h15) h13) h12
  have h36 := h v2 v3 z
  have h37 := C (T h36 h35) h12
  have h38 := C h37 h8
  have h39 := S h28
  have h40 := C h39 h12
  have h41 := T h26 h40
  have h42 := C h41 h8
  have h43 := C (T (T h42 h38) h11) h9
  have h44 := C h43 h9
  have h45 := C h30 h8
  have h46 := S h36
  have h47 := S h32
  have h48 := S h23
  have h49 := C (C (T h20 (C (S h21) h19)) h19) h13
  have h50 := C (T h49 h48) h13
  have h51 := C h50 h13
  have h52 := C (T (T h17 h51) (C (C h41 h13) h13)) h16
  have h53 := C (T h52 h47) h16
  have h54 := C h53 h13
  have h55 := C (C (T h14 h54) h13) h12
  have h56 := C (T h55 h46) h12
  have h57 := C h56 h8
  have h58 := C (T (T h10 h57) h45) h9
  have h59 := h v0 y y
  have h60 := S h59
  have h61 := C h58 h9
  have h62 := C h61 h9
  have h63 := C (T (T h62 h60) h58) h9
  have h64 := C (T h63 h44) h8
  have h65 := h y v0 y
  have h66 := C (T (T (T (T h56 h29) h27) h65) h64) h8
  have h67 := C (T h10 h66) h8
  have h68 := T h67 h7
  have h69 := C (T (T (T (T (T h25 h18) h67) h7) h23) h22) h13
  have h70 := S h65
  have h71 := C h44 h9
  have h72 := C (T (T h43 h59) h71) h9
  have h73 := C (T h61 h72) h8
  have h74 := C (T (T (T (T h73 h70) h26) h40) h37) h8
  have h75 := C (T h74 h11) h8
  have h76 := h z y z
  have h77 := C (T (T (T (T (T h49 h48) h6) h75) h17) h51) h13
  have h78 := h z y y
  have h79 := C (T (T (T (T (T (T (C (T (T (T h67 h7) h65) h64) h8) h74) h11) h78) (C (T (T (T (C (T (T (T (T (C (T h24 h77) h9) (S h76)) h10) h57) h45) h9) h43) h59) h71) h9)) h63) h44) h8
  have h80 := h v0 z v0
  have h81 := C (T (T (T (T h34 h15) h80) (C (T (T (T (T (T (T h79 h73) h70) h6) h75) h17) h51) h13)) h69) h13
  have h82 := C (T (T (T (T (T (T (T h81 h18) h67) h7) h26) h40) h37) (C (T h55 (C (T (T (T h81 h18) h67) h7) h12)) h12)) h12
  have h83 := h v2 v1 v2
  have h84 := T h6 h75
  have h85 := C (T h36 h82) h9
  have h86 := C (T (T (T h85 h5) h32) h31) h16
  have h87 := C (T (T (T (T (T (T h61 h72) (C (T (T (T h62 h60) h58) (C (T (T (T (T h42 h38) h11) h76) (C (T h69 h50) h9)) h9)) h9)) (S h78)) h10) h66) (C (T (T (T h73 h70) h6) h75) h8)) h8
  have h88 := C (T (T (T (T h77 (C (T (T (T (T (T (T h25 h18) h67) h7) h65) h64) h87) h13)) (S h80)) h14) h54) h13
  have h89 := C (T (T (T (T (T (T (T (C (T (C (T (T (T h6 h75) h17) h88) h12) h35) h12) h56) h29) h27) h6) h75) h17) h88) h12
  have h90 := C (T h89 h46) h9
  have h91 := C (T (T (T h52 h47) h4) h90) h16
  have h92 := C (T h33 h91) h16
  have h93 := C (C (C h30 h16) h16) h16
  have h94 := h v3 v2 v2
  have h95 := C (T (T (T (C (T (T (T h94 h93) h92) (C h86 h16)) h84) (S h83)) h36) h82) h68
  have h96 := R (M v3 y)
  have h97 := C h96 h84
  have h98 := S h94
  have h99 := C (C (C h41 h16) h16) h16
  have h100 := C (T h86 h53) h16
  have h101 := C (T (T (T (C h91 h16) h100) h99) h98) h68
  have h102 := C (T (T h85 (C (T (T (T h89 h46) h83) h101) h84)) (C h96 h68)) h68
  have h103 := R (M v2 y)
  have h104 := C h103 h84
  have h105 := C (T (T (T (T h100 h99) h98) h4) h90) h16
  have h106 := h y v2 v2
  have h107 := R x
  T (T (T (T (T (T (h x y v3) (C (T (T (T (T (C (T (T (T (T (T (C (T (C (T (T (T h106 h105) h86) h53) h107) (C (T (T (T (T (T (T (T h33 h91) (C (T (T (T (T h85 h5) h94) h93) h92) h16)) (S h106)) h6) h75) (h v1 x y)) (C (T (T (T (T h104 h102) h39) h83) h101) h107)) h107)) h12) (S (h y v3 x))) h65) h64) h87) (C (T (C (T (T (T (T h67 h7) h65) h64) h87) h8) (C (T (T (T (T (T (T h79 h73) h70) h106) h105) h86) h53) h8)) h8)) h12) (S (h v2 v3 v0))) h28) (C (T (T h97 h95) h90) h84)) (C h103 h68)) h9)) (C h104 h84)) (C (T (T (T h102 h39) h83) h101) h68)) h97) h95) h5

