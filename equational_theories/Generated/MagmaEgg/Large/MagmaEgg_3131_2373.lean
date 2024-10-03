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
theorem Equation3131_implies_Equation2373 (G: Type _) [Magma G] (h: Equation3131 G) : Equation2373 G := fun x y z =>
  let v0 := M x z
  let v1 := M z v0
  let v2 := M y v1
  let v3 := M v2 y
  have h4 := h v3 y y
  have h5 := S h4
  have h6 := R y
  have h7 := R v3
  have h8 := h y v3 y
  have h9 := S h8
  have h10 := h v1 y y
  have h11 := C (C h10 h6) h7
  have h12 := R v0
  have h13 := h z v1 z
  have h14 := S h13
  have h15 := R v1
  have h16 := h v0 z z
  have h17 := C h16 h15
  have h18 := T h17 h14
  have h19 := C h18 h12
  have h20 := S h16
  have h21 := C h20 h15
  have h22 := h z v0 v2
  have h23 := S h22
  have h24 := R v2
  have h25 := R z
  have h26 := h v0 v1 v1
  have h27 := S h26
  have h28 := C h19 h12
  have h29 := T h13 h21
  have h30 := C h29 h12
  have h31 := h v1 v0 v0
  have h32 := S h31
  have h33 := C h30 h12
  have h34 := C h33 h12
  have h35 := C (T (T h34 h32) h30) h12
  have h36 := T h35 h28
  have h37 := C h36 h15
  have h38 := h v0 v1 v0
  have h39 := C (T (T h20 h38) h37) h15
  have h40 := C (T h13 h39) h15
  have h41 := C (T (T (T h40 h27) h38) h37) h15
  have h42 := h v1 z v1
  have h43 := C (T h42 (C (T (C h41 h15) h27) h25)) h24
  have h44 := S h10
  have h45 := C h44 h24
  have h46 := h y v2 y
  have h47 := C (T (T h46 h45) h43) h24
  have h48 := C h47 h12
  have h49 := C (T (C (T (T (T h48 h23) h13) h21) h12) h19) h6
  have h50 := h v2 y v0
  have h51 := h v2 y v2
  have h52 := S h51
  have h53 := S h46
  have h54 := C h10 h24
  have h55 := S h38
  have h56 := C h28 h12
  have h57 := C (T (T h19 h31) h56) h12
  have h58 := T h33 h57
  have h59 := C h58 h15
  have h60 := C (T (T h59 h55) h16) h15
  have h61 := C (T h60 h14) h15
  have h62 := C (T (T (T h59 h55) h26) h61) h15
  have h63 := C (T (C (T h26 (C h62 h15)) h25) (S h42)) h24
  have h64 := C (T (T h63 h54) h53) h24
  have h65 := C (T h50 h49) h7
  have h66 := C (T (T (T (T (T h65 h11) h9) h46) h45) h43) h24
  have h67 := C (C (T h66 h64) h24) h24
  have h68 := h v3 v2 v2
  have h69 := C (T h68 h67) h6
  have h70 := C (T (T (T h69 h52) h50) h49) h7
  have h71 := C (T (T h70 h11) h9) h7
  have h72 := S h68
  have h73 := S h50
  have h74 := C h64 h12
  have h75 := C (T h30 (C (T (T (T h17 h14) h22) h74) h12)) h6
  have h76 := C (T h75 h73) h7
  have h77 := C (C h44 h6) h7
  have h78 := C (T (T (T (T (T h63 h54) h53) h8) h77) h76) h24
  have h79 := C (C (T h47 h78) h24) h24
  have h80 := C (T h79 h72) h6
  have h81 := C (T (T (T h75 h73) h51) h80) h7
  have h82 := h y v3 v3
  have h83 := C (T (T h8 h77) h81) h7
  have h84 := h v3 y v3
  have h85 := C (T h69 (C (T (T (T h79 h72) h84) (C (T (C (T (T (T (T (C h83 h7) (S h82)) h8) h77) h81) h7) h71) h6)) h6)) h6
  have h86 := h v0 v1 v3
  have h87 := S h86
  have h88 := C (T (C (T (T (T (C (T h83 (C (T (T (T (T h70 h11) h9) h82) (C h71 h7)) h7)) h6) (S h84)) h68) h67) h6) h80) h6
  have h89 := T (T h4 h88) h44
  have h90 := T (T h10 h85) h5
  have h91 := C h36 h90
  have h92 := C (T (T (T h40 h27) h38) h91) h90
  have h93 := C (T (T (T h13 h39) h62) h92) h89
  have h94 := C h18 h7
  have h95 := C h29 h7
  have h96 := C h58 h89
  have h97 := C (T (T (T h96 h55) h26) h61) h89
  have h98 := C (T (T (T h97 h41) h60) h14) h90
  have h99 := C (T (T (T (T h96 h55) h86) h98) h95) h7
  have h100 := R (M z v3)
  have h101 := h v1 v2 v1
  have h102 := S h101
  have h103 := h y v3 v1
  have h104 := C (T (T (T (T h65 h11) h9) h103) (C (C (C (T h69 h52) h15) h15) h89)) h24
  have h105 := C (T (T (T (T (C (C (C (T h51 h80) h15) h15) h90) (S h103)) h8) h77) h76) h24
  have h106 := R x
  T (T (T (T (T (h x z z) (C (T (T (T (T (T (T (C (T (T (T (T (T (T (T (T (C (T (T (C (T (T (T h22 (C (T (T (T (T h78 h104) h102) h31) h56) h12)) h35) h28) h106) (C (T (T (T (T h33 h57) (C (T (T (T (T h34 h32) h101) h105) h66) h12)) h74) (C (T (T (T (T (T (T h47 h78) h104) h102) h10) h85) h5) h12)) h106)) (C (T (T (T (T (C (T (T (T (T (T (T h4 h88) h44) h101) h105) h66) h64) h12) h48) h23) (h z x v3)) (C (T (T (C (C (T h26 h61) h7) h7) (C (T (T (T (T (T (C (T (T (T (T h40 h27) h86) h98) h95) h7) (C (T (T (T (T h94 h93) h87) h38) h91) h7)) h97) h41) h60) h21) h7)) h94) h106)) h106)) h25) (S (h v3 z x))) h4) h88) h44) h101) h105) h66) h64) h25) (C (T (T (T (T (T (T (T (T h47 h78) h104) h102) h10) h85) h5) (h v3 z z)) (C (C (T (T (T (T (C (T (C (T (T (T (T (T (T h13 h39) h62) h92) h99) (C h94 h7)) (C h100 h89)) h89) (C (C h100 h90) h90)) h25) (S (h v3 z v3))) h4) h88) h44) h25) h25)) h25)) h20) h86) h98) h95) (C (T (T (T (T (T h17 h39) h62) h92) h99) (C (T (T (T (T h94 h93) h87) h26) h61) h7)) h7)) h25)) (S (h v1 z v3))) h10) h85) h5

