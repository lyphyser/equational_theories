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
theorem Equation4197_implies_Equation3620 (G: Type _) [Magma G] (h: Equation4197 G) : Equation3620 G := fun x y z =>
  let v0 := M z y
  let v1 := M v0 x
  let v2 := M z v1
  have h3 := h z v1 v2
  have h4 := S h3
  have h5 := R v2
  let v6 := M v2 z
  have h7 := h v6 v1 z
  have h8 := R z
  have h9 := h v0 x x
  have h10 := S h9
  let v11 := M x v0
  have h12 := h (M v11 x) x z
  have h13 := R x
  have h14 := h v11 x v2
  have h15 := S h14
  have h16 := h x v0 y
  have h17 := R y
  have h18 := R v0
  have h19 := h y x z
  have h20 := S h19
  have h21 := h x z v0
  have h22 := C (C (C h5 (T (C (T h21 (C h20 h18)) h17) (S h16))) h13) h5
  let v23 := M x z
  have h24 := h (M v23 y) x v2
  have h25 := h z y x
  have h26 := T (T (T h25 h24) h22) h15
  have h27 := h (M z v0) x v2
  have h28 := h z v0 v1
  have h29 := S h28
  have h30 := R v1
  have h31 := C h21 h30
  have h32 := h (M v23 v1) x v2
  have h33 := h z v1 x
  have h34 := T (T (C (T (T (T (T h33 h32) (C (C (C h5 (T h31 h29)) h13) h5)) (S h27)) (C (C h8 h26) h13)) h8) (S h12)) h10
  have h35 := S h33
  have h36 := S h21
  have h37 := C h36 h30
  have h38 := S h25
  have h39 := S h24
  have h40 := C (C (C h5 (T h16 (C (T (C h19 h18) h36) h17))) h13) h5
  have h41 := T (T (T h14 h40) h39) h38
  have h42 := C h8 h41
  have h43 := C (T (T (T (T (C h42 h13) h27) (C (C (C h5 (T h28 h37)) h13) h5)) (S h32)) h35) h8
  have h44 := T (T h9 h12) h43
  have h45 := C h5 h44
  have h46 := C (T (C (T h45 (C (C h8 h44) h34)) h8) (S h7)) h5
  have h47 := h v1 z v2
  have h48 := h z y v2
  have h49 := S h48
  have h50 := h v6 y v2
  have h51 := S h50
  have h52 := C (C h45 h17) h5
  have h53 := h v1 y v2
  have h54 := h v1 y z
  have h55 := C (T (T (T (S h54) h53) h52) h51) h5
  have h56 := h y z v2
  have h57 := T (T (T (T (T (T h56 h55) h49) h25) h24) h22) h15
  have h58 := C h57 h13
  have h59 := C (T h58 h10) h17
  have h60 := h z x y
  have h61 := h z x v0
  have h62 := S h61
  have h63 := T (T h56 h55) h49
  have h64 := C h63 h8
  have h65 := S h56
  have h66 := C h5 h34
  have h67 := C (T (T (T h50 (C (C h66 h17) h5)) (S h53)) h54) h5
  have h68 := h z y v0
  have h69 := h z z y
  have h70 := h z z v0
  have h71 := S h70
  have h72 := h y z z
  have h73 := C (T (T (T h48 h67) h65) h72) h41
  have h74 := C h18 h26
  have h75 := C h18 h41
  have h76 := C (T (T (T (S h72) h56) h55) h49) h26
  have h77 := C (T (T (T (T (T (C (T (T h70 h76) h75) h18) (C (T (T (T (T h74 h73) h71) h69) (C h64 h17)) h18)) (S h68)) h48) h67) h65) h8
  have h78 := h z v0 z
  have h79 := C (T h33 (C (T (T (T (T h31 h29) h78) h77) h64) h13)) h41
  have h80 := C h5 h26
  have h81 := T (T (T (T h80 h79) h62) h60) h59
  have h82 := h v1 v0 z
  let v83 := M y z
  have h84 := T (T (T (T (T (T h14 h40) h39) h38) h48) h67) h65
  have h85 := C h17 h84
  have h86 := C h17 h26
  have h87 := S (h y v0 z)
  have h88 := h v0 v0 v2
  have h89 := C h5 h41
  have h90 := S h69
  have h91 := T (T h48 h67) h65
  have h92 := C h91 h8
  have h93 := C (T (C (T (T (T (T h92 (C (T (T (T (T (T h56 h55) h49) h68) (C (T (T (T (T (C h92 h17) h90) h70) h76) h75) h18)) (C (T (T h74 h73) h71) h18)) h8)) (S h78)) h28) h37) h13) h35) h26
  have h94 := C (T h9 (C h84 h13)) h17
  have h95 := T (T (T (T h94 (S h60)) h61) h93) h89
  have h96 := h x y v0
  have h97 := C (T (C (T h96 (C h95 h18)) h5) (S h88)) h8
  have h98 := C (T (T (T (T (T (T (C (T (T (T (C h8 h57) h42) h78) h77) h17) h90) h70) h76) h75) h88) (C (T (C h81 h18) (S h96)) h5)) h8
  have h99 := h v83 y z
  let v100 := M x y
  have h101 := h z x v100
  have h102 := R v100
  have h103 := h y z x
  have h104 := C h8 h34
  T (T (T (T (T h96 (C (T (T (T (T h53 h52) h51) (h v6 y z)) (C (T (T (T (C (T (T (T (T (T (T h104 h3) (C (T h7 (C (T (C h104 h44) h66) h8)) h5)) (S h47)) h20) (h y x v1)) (C (T (T (T (T (T (T (T (C (T h94 (C (T (T (T (T (T (T (T (T h58 h12) h43) (h v2 z v0)) (C (T (T (C (T (T (T (T (T (T (C (T (T (T (T h48 h67) h65) (h y z v0)) (C (T (T (T (T (T (T (C (T (T (T (C (T (h z y y) (C (T (T (T (T (T h99 h98) h97) h87) h86) h85) h17)) h17) (S (h v83 y y))) (h v83 y v0)) (C (T (C (C h91 h63) h17) (S (h z v0 y))) h18)) h8) (S (h v0 v0 z))) h74) h73) h71) (h z z v2)) (C (T (T (T (S (h v1 z z)) h47) h46) h4) h5)) h18)) h5) (S (h v2 v0 v2))) h80) h79) h62) h60) h59) h8) (C h95 h8)) (C (T (T (T (T h80 h79) h62) h101) (C (T (T (T (S h103) h56) h55) h49) h102)) h8)) h18)) (C (T (C (T (T (T (T (C (T (T (T h48 h67) h65) h103) h102) (S h101)) h61) h93) h89) h8) (S h82)) h18)) (S (h x v0 v0))) (C h13 h26)) (C h13 h84)) h17)) h13) (S (h v83 y x))) h99) h98) h97) h87) h86) h85) h30)) h17) (S (h v83 v1 y))) (h v83 v1 v1)) (C (T (T (T (T (C (T (T (T (C h30 h57) (C h30 h41)) h82) (C h81 h8)) h30) (S (h y z v1))) h56) h55) h49) h30)) h8)) h18)) (S (h v1 z v0))) h47) h46) h4

