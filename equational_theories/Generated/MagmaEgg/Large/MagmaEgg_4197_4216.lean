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
theorem Equation4197_implies_Equation4216 (G: Type _) [Magma G] (h: Equation4197 G) : Equation4216 G := fun x y z =>
  let v0 := M x y
  let v1 := M z y
  let v2 := M v1 z
  have h3 := R v0
  have h4 := h y v2 x
  let v5 := M v2 x
  let v6 := M y v2
  have h7 := R v5
  have h8 := h y v2 v1
  have h9 := S h8
  have h10 := R v1
  have h11 := R v2
  have h12 := R y
  have h13 := h z y v2
  have h14 := S h13
  have h15 := h v2 z v1
  have h16 := S h15
  have h17 := h y v2 z
  have h18 := h y v2 v5
  have h19 := S h18
  have h20 := h x y v2
  have h21 := C h20 h7
  have h22 := C (T (T h21 h19) h17) h10
  have h23 := C (S h20) h7
  have h24 := T h18 h23
  have h25 := C h24 h10
  have h26 := T h21 h19
  have h27 := C h26 h10
  have h28 := C (T (T (S h17) h18) h23) h10
  have h29 := h y z z
  have h30 := h y z v2
  have h31 := R z
  have h32 := h v1 z v1
  have h33 := h y v1 z
  have h34 := h v1 v1 y
  have h35 := T h34 (C (T (C h33 h10) (S h32)) h12)
  have h36 := C h35 h31
  have h37 := C (T h33 h36) h11
  have h38 := C (T (T (T (T (T h37 (S h30)) h29) h15) h28) h27) h12
  have h39 := h v1 v2 y
  have h40 := h z y v1
  have h41 := S h40
  have h42 := C h41 h11
  have h43 := h y v1 v2
  have h44 := S h33
  have h45 := S h34
  have h46 := C (T h32 (C h44 h10)) h12
  have h47 := T h46 h45
  have h48 := C h47 h31
  have h49 := C (T (T (T (T (T (T h48 h44) h43) h42) h39) h38) (C (T (T h25 h22) h16) h12)) h11
  have h50 := C (T (T h37 h49) h14) h12
  have h51 := S h43
  have h52 := C h40 h11
  have h53 := S h39
  have h54 := C (T h48 h44) h11
  have h55 := C (T (T (T (T (T h25 h22) h16) (S h29)) h30) h54) h12
  have h56 := C (T (T (T (T (T (T (C (T (T h15 h28) h27) h12) h55) h53) h52) h51) h33) h36) h11
  have h57 := C (T (T (T (T (C h35 h10) h41) h13) h56) (C (T (T (T (T (T h48 h44) h43) h42) h39) h50) h11)) h10
  have h58 := h v1 v1 v1
  have h59 := h v1 v1 z
  have h60 := S h59
  have h61 := h z v1 v1
  have h62 := h v2 v1 y
  have h63 := S h62
  have h64 := C (T (T h13 h56) h54) h12
  have h65 := h y v1 v1
  have h66 := C (T (T (T (T (T (T h62 h55) h53) h52) h51) h65) (C (T (C (T (T h64 h38) h63) h10) (S h61)) h10)) h31
  have h67 := T (T (T (T h66 h60) h58) h57) h9
  have h68 := C h7 h67
  have h69 := C (T (T h62 h55) h50) h10
  have h70 := C (T (T (T (T (T (T (C (T h61 h69) h10) (S h65)) h43) h42) h39) h38) h63) h31
  have h71 := S h58
  have h72 := C (T (T (T (T (T h64 h53) h52) h51) h33) h36) h11
  have h73 := C (T (T (T (T h72 h49) h14) h40) (C h47 h10)) h10
  have h74 := R x
  have h75 := h v0 v2 v2
  have h76 := h v1 z v2
  have h77 := S h76
  have h78 := T (T (T (T h8 h73) h71) h59) h70
  have h79 := h v5 v2 v0
  have h80 := h x v2 v2
  have h81 := h v2 v2 x
  have h82 := C h7 (T (T (T (T (T (T (T h81 (C (T (C (T h80 (C (T h79 (C (T (T (C h26 h11) (C h78 h11)) h77) h3)) h11)) h11) (S h75)) h74)) (S h4)) h8) h73) h71) h59) h70)
  have h83 := S h81
  have h84 := C (T h75 (C (T (C (T (C (T (T h76 (C h67 h11)) (C h24 h11)) h3) (S h79)) h11) (S h80)) h11)) h74
  have h85 := h z v2 v5
  have h86 := S h85
  have h87 := h x z v2
  have h88 := h x z y
  have h89 := S h88
  have h90 := h y x v2
  have h91 := S h90
  have h92 := h v6 x v5
  have h93 := h (M v2 v2) x v5
  have h94 := C (T (T (T (T (T h93 (C (C (T h82 h68) h74) h7)) (S h92)) (C h24 h74)) (C (T (T (T (T h21 h19) h8) h73) h71) h74)) (C h35 h74)) h11
  have h95 := h v2 x v2
  have h96 := C (T (T (C (C (T (T h95 h94) h91) h31) h12) h89) h87) h7
  have h97 := h z y v5
  let v98 := M z v2
  have h99 := T (T (T (T (T (T h61 h69) (C (T (T (T (T (T (T h64 h53) h52) h51) h33) (C (T (T h58 h57) h9) h31)) (C (T h8 (C (T (T h72 h49) h14) (T (T h97 h96) h86))) h31)) h10)) (S (h v98 z v1))) (h v98 z v2)) (C (T (T (T (T (T (C (T (T (T (T (C (T h32 (C (T (T h44 h43) h42) h10)) (T (T h85 (C (T (T (S h87) h88) (C (C (T (T h90 (C (T (T (T (T (T (C h47 h74) (C (T (T (T (T h58 h57) h9) h18) h23) h74)) (C h26 h74)) h92) (C (C (T (C h7 h78) (C h7 (T (T (T (T (T (T (T h66 h60) h58) h57) h9) h4) h84) h83))) h74) h7)) (S h93)) h11)) (S h95)) h31) h12)) h7)) (S h97))) (S (h v2 v1 v1))) h62) h55) (C (T (T (T (T (T h37 h49) h14) h97) h96) h86) h12)) h31) (S (h v2 y z))) h46) h45) h59) h70) h11)) h77
  let v100 := M v0 x
  T (T (T (T (T (h x y v0) (h (M v100 y) v0 v5)) (C (C (T (T (C h7 (T (T (T (T (T (T (T (T (T (T (h v100 y v5) (C (C (T (C h7 (T (C (T (h x y v1) (C (T (C (T (h v1 x z) (C (T (T (T (C h99 h74) h95) h94) h91) h31)) h12) h89) h10)) h74) (S (h z v1 x)))) (C h7 h99)) h12) h7)) (S (h v2 y v5))) h46) h45) h58) h57) h9) h4) h84) h83)) h82) h68) h3) h7)) (S (h v6 v0 v5))) (C h4 h3)) (S (h v2 x v0))

