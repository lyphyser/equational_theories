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
theorem Equation4176_implies_Equation3776 (G: Type _) [Magma G] (h: Equation4176 G) : Equation3776 G := fun x y z =>
  let v0 := M z x
  let v1 := M y z
  let v2 := M v1 v0
  have h3 := R v2
  have h4 := R v1
  have h5 := h v0 v2 x
  have h6 := R x
  have h7 := h x v1 v0
  have h8 := C h7 h6
  have h9 := C (T h8 (S h5)) h4
  have h10 := h x x v1
  have h11 := h x x y
  have h12 := S h11
  have h13 := R y
  have h14 := h x y z
  have h15 := C (S h14) h6
  have h16 := h z v1 x
  have h17 := h z v1 v1
  have h18 := S h17
  have h19 := R z
  have h20 := h y z x
  have h21 := S h20
  let v22 := M x y
  have h23 := h v0 y v22
  have h24 := S h23
  have h25 := R v22
  have h26 := R v0
  have h27 := h y v22 z
  have h28 := S h27
  have h29 := h z x y
  have h30 := C h29 h19
  have h31 := h v0 z x
  have h32 := h x v0 v0
  have h33 := h x v0 z
  have h34 := S h33
  have h35 := h z z x
  have h36 := C h35 h19
  have h37 := h z z z
  have h38 := S h37
  have h39 := C (S h35) h19
  have h40 := h x v0 x
  have h41 := S h40
  have h42 := h x z x
  have h43 := C (T (T (T (C h42 h6) h41) h33) h39) h19
  have h44 := h x x z
  have h45 := C (T (T h44 h43) h38) h19
  have h46 := S h10
  have h47 := S h7
  have h48 := C h47 h6
  have h49 := C (T h5 h48) h4
  have h50 := h v0 v2 y
  have h51 := h y v1 v0
  have h52 := C (T (C h51 h13) (S h50)) h4
  have h53 := h y y v1
  have h54 := h y y v22
  have h55 := S h54
  have h56 := h y v22 x
  have h57 := h x y y
  have h58 := C (T h57 (C (T (T (C (T (T (T h53 h52) h49) h46) h6) (C h11 h6)) (S h56)) h13)) h25
  have h59 := C (T (T (T (T (T h58 h55) h53) h52) h49) h46) h19
  have h60 := C (T (T (T (T (T h59 h45) h36) h34) h32) (C (T (T (S h31) h30) h28) h26)) h25
  have h61 := h z v22 v22
  have h62 := C (T (T h61 h60) h24) h6
  have h63 := S h61
  have h64 := S h53
  have h65 := C (T h50 (C (S h51) h13)) h4
  have h66 := C h12 h6
  have h67 := T (T (T (T (T h10 h9) h65) h64) h54) (C (T (C (T (T h56 h66) (C (T (T (T h10 h9) h65) h64) h6)) h13) (S h57)) h25)
  have h68 := C h67 h19
  have h69 := S h44
  have h70 := S h42
  have h71 := C (T (T (T h36 h34) h40) (C h70 h6)) h19
  have h72 := C (T (T h37 h71) h69) h19
  have h73 := h x z v22
  have h74 := S h32
  have h75 := C (T (T h27 (C (S h29) h19)) h31) h26
  have h76 := C (T (T h23 (C (T (T (T (T (T h75 h74) h33) h39) h72) h68) h25)) h63) h6
  have h77 := C (T (T (C (T h20 h76) h25) (S h73)) h42) h6
  have h78 := C (T (T (T (T (T h77 h41) h33) h39) h72) h68) h25
  have h79 := h x v1 v22
  have h80 := T (T (T (T h37 h71) h69) h10) (C (T (T (T h8 (C (T (T (T h47 h79) h78) h63) h6)) h62) h21) h4)
  have h81 := C h80 h19
  have h82 := C (T h62 h21) h25
  have h83 := T (C h14 h6) (S h16)
  have h84 := S (h x z z)
  have h85 := C (T (T (T (T (T (T (T (T h58 h55) h53) h52) h49) h46) h44) h43) h38) h6
  have h86 := C h67 h6
  have h87 := h z x v1
  have h88 := S h87
  let v89 := M x v1
  have h90 := T (T (h v22 z x) (C (T (h v0 v22 x) (C (T (T (C h83 h26) (C (T h17 (C (T (T (C (T (T (T (T (C (T (T (T h20 h76) (C (T (T (T h61 (C (T (T (T (T (T h59 h45) h36) h34) h40) (C (T (T h70 h73) h82) h6)) h25)) (S h79)) h7) h6)) h48) h4) h46) h44) h43) h38) h19) h36) h34) h4)) h26)) (S (h v1 x v0))) h6)) h6)) (S (h x v1 x))
  have h91 := C (T (T (T (T (T (T (T (T (C h4 h90) (h v1 v89 z)) (C h88 h19)) h30) h28) h56) h66) h86) h85) h19
  have h92 := h (M v22 z) y z
  let v93 := M v89 z
  have h94 := C (T (T (T (T (T (T (T (T (C (T (T (T h10 h9) (C (C h87 h3) h4)) (S (h v2 v93 v1))) h26) (S (h v93 v1 v0))) h88) h29) h92) h91) h84) h73) h82) h6
  have h95 := h v0 x x
  let v96 := M v0 v0
  have h97 := T (T (T (T (h v96 v1 v2) (C (C (R (M v1 v2)) (T (C (T (T (T (T (T h29 h92) h91) h84) h42) (C (T (T (T h95 h94) h77) h41) h6)) h26) (S (h x x v0)))) h3)) (S (h (M x x) v1 v2))) (C (T h11 (C h83 h13)) h4)) (S (h y z v1))
  let v98 := M v96 v1
  have h99 := h v1 v0 v0
  T (T (T (T (T (h x y v1) (C (T (T (T (T (C (T h51 (C (T (T (T (T (T (C (T (T h99 (h v98 v0 z)) (C (T (T (T (T (T (C (T (T (T (T (T (T h30 h28) h56) h66) h86) h85) (C h80 h6)) h97) (S (h x v1 v1))) h79) h78) h60) h24) h19)) h13) (S (h z v0 y))) (C h19 (T (T (T h29 h92) h91) h84))) (h z (M x z) z)) (C (T (S (h z x z)) h29) h19)) h28) h26)) h6) (C (T (T (T (T h75 h74) h33) h39) h72) h6)) (S (h z x x))) h29) (C h90 h13)) h4)) (S (h y x v1))) (h y x v2)) (C (T (T (T (T (C (T (T (h x v2 v1) (C (T (T (T (T (T (C (T (T (T (C (T (T (T h99 (h v98 v0 x)) (C (T (T (T (C (T (T (T (T (T (T h95 h94) h77) h41) h33) h39) h81) h97) h18) h16) h15) h6)) (C h83 h6)) h4) (S (h x z v1))) h73) h82) h6) h77) h41) h33) h39) h81) h4)) h18) h13) (C (T h16 h15) h13)) h12) h10) h9) h3)) (S (h v1 v0 v2))

