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
theorem Equation3120_implies_Equation3417 (G: Type _) [Magma G] (h: Equation3120 G) : Equation3417 G := fun x y z =>
  let v0 := M y x
  let v1 := M z v0
  let v2 := M z v1
  have h3 := h v2 v2 v2
  have h4 := S h3
  have h5 := R v2
  have h6 := R v1
  have h7 := h z v2 v2
  have h8 := S h7
  have h9 := h v1 z v2
  have h10 := C h9 h5
  have h11 := C (T h10 h8) h6
  have h12 := C (C h11 h5) h5
  have h13 := h v2 v1 v2
  have h14 := h v2 v2 z
  have h15 := S h14
  have h16 := R z
  have h17 := T h13 h12
  have h18 := C (C h17 h16) h16
  have h19 := h v1 z z
  have h20 := C (C (T (T (T (C (T h19 (C (T (T (T h18 h15) h13) h12) h16)) h16) h15) h13) h12) h5) h5
  have h21 := h v0 z v2
  have h22 := T (T h21 h20) h4
  have h23 := S h21
  have h24 := S h19
  have h25 := S h13
  have h26 := S h9
  have h27 := C h26 h5
  have h28 := C (T h7 h27) h6
  have h29 := C (C h28 h5) h5
  have h30 := T h29 h25
  have h31 := C (C h30 h16) h16
  have h32 := C (C (T (T (T h29 h25) h14) (C (T (C (T (T (T h29 h25) h14) h31) h16) h24) h16)) h5) h5
  have h33 := T (T h3 h32) h23
  have h34 := R x
  have h35 := R v0
  have h36 := h x y v0
  have h37 := h y v0 v0
  have h38 := C (T (T h37 (C (S h36) h35)) (C h34 h22)) h34
  let v39 := M x y
  have h40 := R v39
  have h41 := R y
  have h42 := h v2 z z
  have h43 := S h42
  have h44 := h z v2 v0
  have h45 := S h44
  have h46 := R (M (M v2 z) v2)
  have h47 := C (T (T (T (C (T (T (T (T h21 h20) h4) h14) h31) h16) h24) h9) (C h46 h33)) h35
  have h48 := T h47 h45
  have h49 := C h48 h5
  have h50 := C (T (T (T (C h46 h22) h26) h19) (C (T (T (T (T h18 h15) h3) h32) h23) h16)) h35
  have h51 := h z v0 v1
  have h52 := S h51
  have h53 := C (T (T (T h10 h8) h44) h50) h6
  have h54 := C (T (T (T h29 h25) h28) h53) h6
  have h55 := C h17 h6
  have h56 := C (T (T (T (T h55 h54) h52) h44) h50) h5
  have h57 := h v1 v2 z
  have h58 := h v1 v2 v2
  have h59 := S h58
  have h60 := C h30 h6
  have h61 := C (T (T (T h47 h45) h7) h27) h6
  have h62 := C (T (T (T h61 h11) h13) h12) h6
  have h63 := C (T (T (T (T h47 h45) h51) h62) h60) h5
  have h64 := R (M (M v0 z) v0)
  have h65 := C h64 h22
  have h66 := h z v0 v0
  have h67 := C (T (T (T (T h55 h54) h52) h66) (C (T h65 h63) h22)) h5
  have h68 := T h44 h50
  have h69 := C h68 h5
  have h70 := C (T (T (T (T (T h69 h63) h67) h59) h57) (C (C (T h56 h49) h16) h16)) h16
  have h71 := C h64 h33
  have h72 := C (T (T (T (T (C (T h56 h71) h33) (S h66)) h51) h62) h60) h5
  have h73 := C (T (T (T (T (T (C (C (T h69 h63) h16) h16) (S h57)) h58) h72) h56) h49) h16
  have h74 := h v2 v2 v0
  have h75 := S h74
  have h76 := C (C h17 h35) h33
  have h77 := C (C h30 h35) h22
  have h78 := h v2 v1 v0
  have h79 := S h78
  have h80 := C (C (T (T (T h21 h20) h4) h28) h33) h35
  have h81 := T (T (T h80 h79) h74) h77
  have h82 := C (C (T (T (T h11 h3) h32) h23) h22) h35
  have h83 := h v2 v0 v1
  have h84 := S h83
  have h85 := T (T (T h76 h75) h78) h82
  have h86 := h v2 z v1
  have h87 := h z v0 z
  have h88 := S h87
  have h89 := C (C h68 h16) h16
  have h90 := h z z v1
  have h91 := h z z v0
  have h92 := R (M (M z z) z)
  have h93 := C (C h48 h16) h16
  have h94 := C (T (T (T (T (C (T (T (T (T (T h58 h72) h56) h71) (C (T (T (T h47 h45) h87) h93) h22)) (C h92 h33)) h35) (S h91)) h90) (C (T (T (T (C (T (T (T h89 h88) h51) (C (T (T (T h61 h11) h42) h73) h6)) h6) (S h86)) h74) h77) h6)) (C h85 h6)) h6
  have h95 := C (T (T (T (T (C h81 h6) (C (T (T (T h76 h75) h86) (C (T (T (T (C (T (T (T h70 h43) h28) h53) h6) h52) h87) h93) h6)) h6)) (S h90)) h91) (C (T (T (T (T (T (C h92 h22) (C (T (T (T h89 h88) h44) h50) h33)) h65) h63) h67) h59) h35)) h6
  have h96 := h v0 v1 v2
  have h97 := S h96
  have h98 := R (M (M v1 v0) v1)
  have h99 := C (T (C (T (T (T (T h21 h20) h4) h83) h95) h35) (C h98 h22)) h22
  have h100 := C (T (C h98 h33) (C (T (T (T (T h94 h84) h3) h32) h23) h35)) h33
  have h101 := C (T (T (C h34 h33) (C h36 h35)) (S h37)) h34
  have h102 := C (C (T (T (T (T (T (T (C h38 h41) (C (T (T h101 h96) h100) h41)) (C (T (T (T (T (T (T h99 h97) h21) h20) h4) h83) h95) h41)) (C (T (T (T h94 h84) h78) h82) h41)) (C h81 h41)) (C (T (T (T h76 h75) h42) h73) h41)) (C (T h70 h43) h41)) h5) h5
  have h103 := h x y v2
  have h104 := C h101 h41
  T (T (h v39 v39 v0) (C (T (T (C (R (M (M v39 v39) v39)) h22) (C (T (T (C (C (C (T (T h103 h102) (C (T (T (C (T (T (T (T (T (T (C (T h42 h73) h41) (C (T (T (T h70 h43) h74) h77) h41)) (C h85 h41)) (C (T (T (T h80 h79) h83) h95) h41)) (C (T (T (T (T (T (T h94 h84) h3) h32) h23) h96) h100) h41)) (C (T (T h99 h97) h38) h41)) h104) h5) (C (T (T (T (C (T (T (T (T h21 h20) h4) (h v2 x y)) (C h104 h41)) h41) (S (h x y y))) h103) h102) h5)) (S (h y v2 v2))) h33)) h41) h40) h40) (S (h v0 y v39))) h38) h33)) (C (R (M (M x v2) x)) h22)) h22)) (S (h v2 x v2))

