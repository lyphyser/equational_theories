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
theorem Equation3120_implies_Equation2279 (G: Type _) [Magma G] (h: Equation3120 G) : Equation2279 G := fun x y z =>
  let v0 := M z y
  let v1 := M y v0
  let v2 := M x v1
  let v3 := M v2 z
  have h4 := h v3 v2 v2
  have h5 := S h4
  have h6 := R v2
  have h7 := R v3
  have h8 := h v2 v3 v3
  have h9 := S h8
  have h10 := h z v2 v3
  have h11 := h z y v3
  have h12 := S h11
  have h13 := R y
  have h14 := R z
  have h15 := h y z z
  have h16 := h v0 v1 v0
  have h17 := S h16
  have h18 := R v0
  have h19 := R v1
  have h20 := h v1 v0 v1
  have h21 := S h20
  have h22 := h v0 y v1
  have h23 := h y v1 v1
  have h24 := C (T h23 (C (S h22) h19)) h18
  have h25 := C (C h24 h19) h19
  have h26 := T h25 h21
  have h27 := C h26 h18
  have h28 := C (T (C h22 h19) (S h23)) h18
  have h29 := C (C h28 h19) h19
  have h30 := h v1 v1 y
  have h31 := S h30
  have h32 := T h20 h29
  have h33 := h v0 y y
  have h34 := C (T h33 (C (T (T (T (C (C h32 h13) h13) h31) h20) h29) h13)) h13
  have h35 := C (T (T (T h34 h31) h20) h29) h18
  have h36 := C (T h35 h27) h19
  have h37 := C (T (C (T (T (T h25 h21) h30) (C (C h26 h13) h13)) h13) (S h33)) h13
  have h38 := h v1 v1 v0
  have h39 := C (T (T (T (C h35 h18) (S h38)) h30) h37) h18
  have h40 := h y v0 v0
  have h41 := h y v0 v1
  have h42 := C (T (T (T h25 h21) h30) h37) h18
  have h43 := C h32 h18
  have h44 := C (T h43 h42) h19
  have h45 := C (T (T (T (C h44 h19) (S h41)) h40) h39) h19
  have h46 := h v0 v1 v1
  have h47 := C (C (T (T h46 h45) h36) h18) h18
  have h48 := h v0 v0 z
  have h49 := S h46
  have h50 := S h40
  have h51 := C (T (T (T h34 h31) h38) (C h42 h18)) h18
  have h52 := C (T (T (T h51 h50) h41) (C h36 h19)) h19
  have h53 := C (T (T (T h40 h39) h35) h27) h19
  have h54 := C (C (C (T (T (T (T (T h53 h44) h52) h49) h48) (C (T (C (T (T (T h47 h17) h48) (C (C (T h47 h17) h14) h14)) h14) (S h15)) h14)) h13) h7) h7
  have h55 := h v1 y v3
  have h56 := h v1 v0 z
  have h57 := S h56
  have h58 := T (T h55 h54) h12
  have h59 := S h55
  have h60 := C (T (T (T h43 h42) h51) h50) h19
  have h61 := S h48
  have h62 := C (C (T (T h44 h52) h49) h18) h18
  have h63 := C (C (C (T (T (T (T (T (C (T h15 (C (T (T (T (C (C (T h16 h62) h14) h14) h61) h16) h62) h14)) h14) h61) h46) h45) h36) h60) h13) h7) h7
  have h64 := C (C (T (T (T h11 h63) h59) h24) h58) h14
  have h65 := C (T (C (T (T (T (T (T h64 h57) h55) h54) h12) h10) h7) h9) h7
  have h66 := h v1 z v3
  have h67 := C (T (T (T h64 h57) h66) h65) h6
  have h68 := C h67 h6
  have h69 := T (T h11 h63) h59
  have h70 := C (C (T (T (T h28 h55) h54) h12) h69) h14
  have h71 := S h66
  have h72 := S h10
  have h73 := C (T h8 (C (T (T (T (T (T h72 h11) h63) h59) h56) h70) h7)) h7
  have h74 := C (T (T (T h73 h71) h56) h70) h6
  have h75 := h v1 z v2
  have h76 := S h75
  have h77 := C (T (T h4 (C (T (T (T (C h74 h6) h76) h66) h65) h6)) h74) h6
  have h78 := C (T (T h67 (C (T (T (T h73 h71) h75) h68) h6)) h5) h6
  have h79 := h v2 v3 v2
  have h80 := S h79
  have h81 := C (C (T h8 (C (T (T (T (T (T h72 h11) h63) h59) h75) h78) h7)) h6) h6
  have h82 := T h81 h80
  have h83 := C (C (T (C (T (T (T (T (T h77 h76) h55) h54) h12) h10) h7) h9) h6) h6
  have h84 := h v2 v2 x
  have h85 := S h84
  have h86 := R x
  have h87 := h v1 x x
  have h88 := C (T (T (T h77 h76) h87) (C (T (T (T (C (C (T h79 h83) h86) h86) h85) h79) h83) h86)) h86
  have h89 := C (T (T (T h64 h57) h75) h78) h86
  have h90 := h v1 v1 z
  have h91 := S h90
  have h92 := C (C h32 h14) h58
  have h93 := C (T (T (T h92 h91) h56) h70) h86
  have h94 := C (C h26 h14) h69
  have h95 := h v1 y y
  have h96 := S h95
  have h97 := h v0 v1 y
  have h98 := C (T (T (T (T (T h53 h44) h52) h49) h97) (C (C h60 h13) h13)) h13
  have h99 := C (T (T (T h98 h96) h90) h94) h86
  have h100 := C (T (T (T (T (T (C (C h53 h13) h13) (S h97)) h46) h45) h36) h60) h13
  have h101 := C (T h95 h100) h86
  have h102 := h x v1 v2
  T (T (T h102 (C (T (T (T (C (T (T (T (C (T (T (T (T (T (T (T h101 h99) h93) h89) h88) h85) (h v2 v2 z)) (C (C (T (T (T (T (T (T (T h81 h80) h84) (C (T (T (T (C (T (T (T h81 h80) h84) (C (C h82 h86) h86)) h86) (S h87)) h75) h78) h86)) (C (T (T (T h77 h76) h56) h70) h86)) (C (T (T (T h64 h57) h90) h94) h86)) (C (T (T (T h92 h91) h95) h100) h86)) (C (T h98 h96) h86)) h69) h69)) h19) (S (h x v1 v1))) h102) (C (C (T (T (C (T (T (T (T (T (T (T h101 h99) h93) h89) h88) h85) h79) h83) h58) (C (R (M (M v2 v2) v2)) h69)) (C h82 h19)) h6) h6)) h6) (S (h v1 v2 v2))) h75) h78) h6)) (C (T h77 h68) h6)) h5

