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
theorem Equation4197_implies_Equation3323 (G: Type _) [Magma G] (h: Equation4197 G) : Equation3323 G := fun x y z =>
  let v0 := M z z
  let v1 := M y v0
  have h2 := h x v1 v0
  have h3 := S h2
  have h4 := R v0
  have h5 := R v1
  have h6 := R x
  have h7 := h z z y
  have h8 := S h7
  let v9 := M x v1
  let v10 := M y z
  have h11 := h (M v10 z) y v9
  have h12 := S h11
  have h13 := R v9
  have h14 := R y
  have h15 := h v10 z v9
  have h16 := S h15
  have h17 := R z
  have h18 := h y z v0
  have h19 := h z y z
  have h20 := C (C (C h13 (T (C h19 h4) (S h18))) h17) h13
  have h21 := h (M (M z y) v0) z v9
  have h22 := h y v0 z
  have h23 := C (C (C h13 (T (T (T h22 h21) h20) h16)) h14) h13
  have h24 := h v1 y v9
  have h25 := S h24
  have h26 := S h22
  have h27 := S h21
  have h28 := C (C (C h13 (T h18 (C (S h19) h4))) h17) h13
  have h29 := C h13 (T (T (T h15 h28) h27) h26)
  have h30 := C (C h29 h14) h13
  have h31 := h z z v0
  have h32 := S h31
  have h33 := h z z z
  have h34 := C h33 h4
  have h35 := h v0 v0 v1
  have h36 := S h35
  have h37 := h y z v1
  have h38 := S h33
  have h39 := T h34 h32
  have h40 := h z v0 z
  have h41 := T h40 (C h39 h17)
  have h42 := h v0 z z
  have h43 := h v0 z y
  have h44 := S h43
  have h45 := h z y v1
  have h46 := C (T (T h45 (C (T (T h44 h42) (C (T (T (T (T (T (C h41 h17) h38) h7) h11) h30) h25) h17)) h5)) (S h37)) h17
  have h47 := h z y y
  have h48 := h y z z
  have h49 := C h38 h4
  have h50 := T h31 h49
  have h51 := T (C h50 h17) (S h40)
  have h52 := C (T (T h37 (C (T (T (C (T (T (T (T (T h24 h23) h12) h8) h33) (C h51 h17)) h17) (S h42)) h43) h5)) (S h45)) h17
  have h53 := C (T (T (C h41 h14) (C (T h43 (C (T (C (T (T (T (T h22 h21) h20) h16) h52) h17) (S h48)) h14)) h14)) (S h47)) h17
  have h54 := h v0 y z
  have h55 := h v0 y v0
  have h56 := S h55
  have h57 := C (C h50 h14) h4
  have h58 := T (T (T (T (T (T (T (T h57 h56) h54) h53) h46) h15) h28) h27) h26
  have h59 := h v0 y v1
  have h60 := S h59
  have h61 := h v0 v0 y
  have h62 := C (T (T h31 h49) h61) h5
  let v63 := M (M v0 y) v0
  have h64 := h v63 v0 v0
  have h65 := h y v0 v0
  have h66 := C (T (T h65 h64) (C (C (T (T (T (T (T (T (T (T (T (C h4 h58) h62) h60) h54) h53) h46) h15) h28) h27) h26) h4) h4)) h58
  have h67 := C (C h39 h14) h4
  have h68 := S h54
  have h69 := C (T (T h47 (C (T (C (T h48 (C (T (T (T (T h46 h15) h28) h27) h26) h17)) h14) h44) h14)) (C h51 h14)) h17
  have h70 := T (T (T (T (T (T (T (T h22 h21) h20) h16) h52) h69) h68) h55) h67
  have h71 := C h5 h70
  have h72 := h v1 x v1
  have h73 := T (T (T (T (T (T (T (T h62 h60) h54) h53) h46) h15) h28) h27) h26
  have h74 := C h73 h6
  have h75 := C (T (T (T h74 h72) (C (C (T (T (T (T (T (T (T (T h71 h66) h36) h34) h32) h7) h11) h30) h25) h6) h5)) (C (C (T (T (T h24 h23) h12) h8) h6) h5)) h4
  have h76 := h v1 x v0
  let v77 := M x y
  have h78 := R v77
  have h79 := h y v0 x
  have h80 := h v0 x v77
  have h81 := T h80 (C (S h79) h78)
  have h82 := h v0 x v9
  have h83 := C (T (T (T h74 h76) h75) h3) h4
  have h84 := C (T (T (S h61) h34) h32) h5
  have h85 := T (T (T (T (T (T (T (T h22 h21) h20) h16) h52) h69) h68) h59) h84
  have h86 := C h85 h6
  have h87 := C h5 h58
  have h88 := S h65
  have h89 := C (T (T (C (C (T (T (T (T (T (T (T (T (T h22 h21) h20) h16) h52) h69) h68) h59) h84) (C h4 h70)) h4) h4) (S h64)) h88) h70
  have h90 := C (T (T (T (C (C (T (T (T h7 h11) h30) h25) h6) h5) (C (C (T (T (T (T (T (T (T (T h24 h23) h12) h8) h31) h49) h35) h89) h87) h6) h5)) (S h72)) h86) h4
  have h91 := h v9 x v1
  have h92 := C (T (T (T (T h71 h66) h36) h34) h32) h14
  have h93 := h v0 v0 v9
  have h94 := C (T (T (T (T (C (T (T h2 h90) (C (T (T h74 h76) h83) h4)) h13) (S h93)) h35) h89) h87) h14
  have h95 := h v9 y v9
  have h96 := h v1 y x
  have h97 := h v1 y v0
  have h98 := h v63 v0 v1
  have h99 := S h76
  have h100 := C (T (T (T h2 h90) h99) h86) h4
  have h101 := C (T (T (T (T h71 h66) h36) h93) (C (T (T (C (T (T h100 h99) h86) h4) h75) h3) h13)) h14
  have h102 := C (T (T (T (T h31 h49) h35) h89) h87) h14
  have h103 := C (T (T (T (T (T (T (T (T h22 h21) h20) h16) h52) h69) h68) h102) h101) h13
  have h104 := S h95
  let v105 := M x x
  T (T (T (T (T (T (h x y x) (h (M v105 y) x v9)) (C (C (T (T (C h13 (T (T (T (T (T (T (T (T (T (T (T (T (h v105 y v9) (C (C (C h13 (T (h x x v0) (C (T (T (C h81 h6) (C (T (T (T (T (T (T (T (C h79 h78) (S h80)) h82) (C (T (T (T (T (T (T (T (T (T (T (T (T (T (C (T (T h100 h75) h3) h6) h91) (C (T (T (T (C (T h103 h104) h6) (S h96)) h97) (C (T (T (T (T (T (T (T (T (C h73 h14) h24) h23) h12) h8) h31) h49) h35) h89) h4)) h5)) (S h98)) h88) h22) h21) h20) h16) h52) h69) h68) h102) h101) h13)) h104) (h v9 y v1)) (C (T (C (T (T h103 (C (T (T (T (T (T (T (T (T (T (T (T (T (T h94 h92) h54) h53) h46) h15) h28) h27) h26) h65) h98) (C (T (T (T (C (T (T (T (T (T (T (T (T h66 h36) h34) h32) h7) h11) h30) h25) (C h85 h14)) h4) (S h97)) h96) (C (T h95 (C (T (T (T (T (T (T (T (T h94 h92) h54) h53) h46) h15) h28) h27) h26) h13)) h6)) h5)) (S h91)) (C (T (T h2 h90) h83) h6)) h13)) (S h82)) h14) (C h81 h14)) h5)) (S (h v77 y v1))) h6)) (S (h y y x))) h4))) h14) h13)) (S (h (M (M y y) v0) y v9))) (S (h y v0 y))) h22) h21) h20) h16) h52) h69) h68) h55) h67)) (C h13 (T (T (T (T h57 h56) h54) h53) h46))) h29) h6) h13)) (S (h v1 x v9))) h76) h75) h3

