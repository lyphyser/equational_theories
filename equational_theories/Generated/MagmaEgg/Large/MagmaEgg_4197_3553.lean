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
theorem Equation4197_implies_Equation3553 (G: Type _) [Magma G] (h: Equation4197 G) : Equation3553 G := fun x y z =>
  let v0 := M x z
  let v1 := M v0 z
  have h2 := R v1
  have h3 := R y
  let v4 := M y v1
  have h5 := h y y v4
  have h6 := S h5
  have h7 := h y v1 v4
  have h8 := S h7
  have h9 := R v4
  have h10 := h (M v4 y) v1 y
  have h11 := h v0 z z
  have h12 := S h11
  let v13 := M z v0
  let v14 := M v13 z
  have h15 := h v14 z y
  have h16 := S h15
  have h17 := R z
  have h18 := h v13 z v4
  have h19 := h z v0 z
  have h20 := R v0
  have h21 := h z z x
  have h22 := S h21
  have h23 := h z x v0
  have h24 := h (M (M z x) z) z v4
  have h25 := h x z z
  have h26 := T (T (T h25 h24) (C (C (C h9 (T (C (T h23 (C h22 h20)) h17) (S h19))) h17) h9)) (S h18)
  have h27 := C (C h3 h26) h17
  have h28 := h (M y v0) z v4
  have h29 := S h28
  have h30 := h y v0 v1
  have h31 := h z y v0
  have h32 := C (C (C h9 (T (C h31 h2) (S h30))) h17) h9
  have h33 := h (M (M z y) v1) z v4
  have h34 := h y v1 z
  have h35 := C (T (T (T (T h34 h33) h32) h29) h27) h3
  have h36 := T (T h35 h16) h12
  have h37 := S h34
  have h38 := S h33
  have h39 := S h31
  have h40 := C (C (C h9 (T h30 (C h39 h2))) h17) h9
  have h41 := T (T (T h18 (C (C (C h9 (T h19 (C (T (C h21 h20) (S h23)) h17))) h17) h9)) (S h24)) (S h25)
  have h42 := C (C h3 h41) h17
  have h43 := C (T (T (T (T h42 h28) h40) h38) h37) h3
  have h44 := T (T h11 h15) h43
  have h45 := C (T (C (T (C h9 h44) (C (C h3 h44) h36)) h3) (S h10)) h9
  have h46 := h v1 y v4
  have h47 := T (T h46 h45) h8
  have h48 := h v1 y y
  have h49 := S h46
  have h50 := C (T h10 (C (T (C (C h3 h36) h44) (C h9 h36)) h3)) h9
  have h51 := C (T (T (T h7 h50) h49) h48) h47
  have h52 := C (T h51 h6) h2
  have h53 := T (T h7 h50) h49
  have h54 := C (T (T (T (S h48) h46) h45) h8) h53
  have h55 := h y y v1
  have h56 := S h55
  have h57 := C (T (T (T (T (T (T (T h42 h28) h40) h38) h37) h7) h50) h49) h3
  have h58 := C (T (T h11 h15) h57) h36
  have h59 := C (T (T (T h58 h56) h5) h54) h2
  have h60 := C (T (T (T (T (T (T (T h46 h45) h8) h34) h33) h32) h29) h27) h3
  have h61 := C (T (T h60 h16) h12) h44
  have h62 := h y y z
  have h63 := S h62
  have h64 := C h53 h41
  have h65 := C h9 h26
  have h66 := C (T (T h65 h64) h39) h3
  have h67 := h v1 v0 y
  have h68 := C h2 h41
  have h69 := C (T (T h68 h67) h66) h17
  have h70 := C (T (T (T h69 h63) h55) h61) h2
  have h71 := h v14 z v1
  have h72 := T (T (T (T h11 h71) h70) h59) h52
  have h73 := S h71
  have h74 := C h2 h26
  have h75 := S h67
  have h76 := C h9 h41
  have h77 := C h47 h26
  have h78 := C (T (T h31 h77) h76) h3
  have h79 := C (T (T h78 h75) h74) h17
  have h80 := C (T (T (T h58 h56) h62) h79) h2
  have h81 := h v1 v0 v0
  have h82 := C (T (T (T h51 h6) h55) h61) h2
  have h83 := C (T h5 h54) h2
  have h84 := h x z v0
  have h85 := S h84
  have h86 := h (M v0 x) z v4
  have h87 := h v0 x y
  have h88 := R x
  have h89 := h y v0 v4
  have h90 := h v0 y v4
  have h91 := h z y x
  have h92 := C (T (T (T (T h65 h64) h39) h91) (C (T (T h90 (C (T (T h75 h74) (C h44 h41)) h9)) (S h89)) h88)) h3
  have h93 := h (M v1 v0) z v4
  have h94 := C h2 h44
  have h95 := C (T (T (T (T (T (T (T (T h94 h58) h56) h62) h79) (C h68 h17)) h93) (C (C (C h9 (T (T h67 h92) (S h87))) h17) h9)) (S h86)) h20
  have h96 := h v1 v0 v1
  have h97 := C (T (T (T h96 (C (T h95 h85) h72)) (C h20 (T (T (T (T (T h83 h82) h80) h73) h15) h43))) (C h20 h36)) h20
  have h98 := h z v0 v0
  have h99 := h v0 v0 z
  have h100 := S h99
  have h101 := S h96
  have h102 := T (T (T (T h83 h82) h80) h73) h12
  have h103 := C h2 h36
  have h104 := S h91
  have h105 := C (T (T h89 (C (T (T (C h36 h26) h68) h67) h9)) (S h90)) h88
  have h106 := C (T h84 (C (T (T (T (T (T (T (T (T h86 (C (C (C h9 (T (T h87 (C (T (T (T (T h105 h104) h31) h77) h76) h3)) h75)) h17) h9)) (S h93)) (C h74 h17)) h69) h63) h55) h61) h103) h20)) h102
  have h107 := C h20 (T (T (T (T (T h35 h16) h71) h70) h59) h52)
  have h108 := C h20 h44
  have h109 := C (T (T (T h78 h75) h81) (C (T (C (T (T (T h108 h107) h106) h101) h20) (S h98)) h20)) h17
  T (T (T (h x y v1) (C (T (T (C h22 h3) (C (T (T (T (T (T (T (T (T h21 (h v1 x v1)) (C (T (T (T (T (T (T (T (T (C (T (T (T (T (T h94 h58) h56) h62) h109) h100) h88) (S (h z v0 x))) h98) h97) (C (T (T (T (T (T (T h108 h107) h106) h101) h67) h92) (C (T (T (T (T (T (T (T h105 h104) h31) h77) h76) (h v4 v0 v4)) (C (T (T (C (T (T (T (T (T (C h9 h53) h51) h6) h55) h61) h103) h20) h95) h85) h53)) (C h20 h47)) h3)) h20)) (S (h v4 y v0))) h35) h16) h12) h72)) (C (T (T h11 h71) h70) h102)) (C (T (T (T h80 h73) h15) h57) h2)) h56) h62) h109) h100) h3)) (C (T (T (T (T (T h99 (C (T (T (T (C (T h98 h97) h20) (S h81)) h67) h66) h17)) h63) h55) (C (T (T (T h60 h16) h71) h70) h2)) (C (T (T h80 h73) h12) h72)) h3)) h2)) (S (h (M (M y y) v1) y v1))) (S (h y v1 y))

