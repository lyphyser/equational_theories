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
theorem Equation4197_implies_Equation4424 (G: Type _) [Magma G] (h: Equation4197 G) : Equation4424 G := fun x y z =>
  let v0 := M z z
  have h1 := h v0 y v0
  have h2 := S h1
  have h3 := R v0
  have h4 := R y
  have h5 := h z z z
  have h6 := S h5
  have h7 := C h6 h3
  have h8 := h z z v0
  have h9 := C (T h8 h7) h4
  have h10 := C h9 h3
  let v11 := M v0 y
  have h12 := h v11 v0 v11
  have h13 := S h12
  have h14 := R v11
  have h15 := C (T (T h10 h2) h9) h3
  have h16 := C (T h15 h2) h14
  have h17 := h v0 v0 v11
  have h18 := C (T h8 (C (T (T (T (T h6 h8) h7) h17) h16) h3)) h14
  let v19 := M x y
  let v20 := M x v19
  have h21 := R v20
  have h22 := h x v19 v0
  have h23 := S h22
  have h24 := R v19
  have h25 := R x
  have h26 := S h8
  have h27 := C h5 h3
  have h28 := h v0 v0 v19
  have h29 := S h28
  have h30 := h v19 v0 v0
  have h31 := S h30
  have h32 := h x y y
  let v33 := M y x
  have h34 := h (M v33 y) y v11
  have h35 := h v33 y v11
  have h36 := h y x v0
  have h37 := T (T (T h18 h13) h10) h2
  have h38 := h v11 x v0
  have h39 := h (M v11 x) y v11
  have h40 := h y v0 v0
  have h41 := h v0 x y
  let v42 := M v0 x
  have h43 := h v42 y v11
  have h44 := T (T (T h43 (C (C (C h14 (T (T (T (T h41 (C (C (T (T h40 h15) h2) h25) h4)) h39) (C (C (C h14 (T (T h38 (C (C h37 h25) h3)) (S h36))) h4) h14)) (S h35))) h4) h14)) (S h34)) (S h32)
  have h45 := C h3 h44
  have h46 := C (C h45 h3) h3
  have h47 := h (M v42 y) v0 v0
  have h48 := h x y v0
  have h49 := C (T (T (T (T h48 h47) h46) h31) (C (T (T (T h48 h47) h46) h31) h3)) h24
  have h50 := h v19 x v19
  have h51 := S h48
  have h52 := S h47
  have h53 := S h43
  have h54 := S h40
  have h55 := C (T h27 h26) h4
  have h56 := C h55 h3
  have h57 := C (T (T h55 h1) h56) h3
  have h58 := S h17
  have h59 := C (T h1 h57) h14
  have h60 := T (T (T h1 h56) h12) (C (T (C (T (T (T (T h59 h58) h27) h26) h5) h3) h26) h14)
  have h61 := C (C (C h14 (T (T (T (T h35 (C (C (C h14 (T (T h36 (C (C h60 h25) h3)) (S h38))) h4) h14)) (S h39)) (C (C (T (T h1 h57) h54) h25) h4)) (S h41))) h4) h14
  have h62 := T (T (T h32 h34) h61) h53
  have h63 := C h3 h62
  have h64 := C (C h63 h3) h3
  have h65 := h v19 v0 v19
  have h66 := C (T (T (T (T (C (T (T (T h30 h64) h52) h51) h3) h30) h64) h52) h51) h24
  have h67 := h z z v11
  have h68 := S h67
  let v69 := M (M v11 z) z
  have h70 := h v69 v11 v11
  have h71 := h y v0 z
  have h72 := S h71
  have h73 := R z
  have h74 := h z y z
  have h75 := S h74
  have h76 := h v11 z v0
  have h77 := T (T (T (T (T (C h75 h73) (C (T (T h74 h76) (C (T (C h37 h73) h75) h3)) h73)) h72) h40) h15) h2
  have h78 := T (T (T (T (T h1 h57) h54) h71) (C (T (T (C (T h74 (C h60 h73)) h3) (S h76)) h75) h73)) (C h74 h73)
  have h79 := h y z v0
  have h80 := h (M (M y z) z) y v11
  have h81 := h z z y
  have h82 := C (T (T (T (T (T (T (C (C (T (T h81 h80) (C (C (T (T (T (T (C h14 (T (T (T (T (C (T h79 (C h75 h3)) h73) h72) h40) h15) h2)) h59) h58) h27) h26) h4) h78)) h77) h14) (S h70)) h68) h8) h7) h28) h66) h3
  have h83 := h v69 v11 v0
  have h84 := C (T (T (T (T (T (T h63 (C (T (T h67 h83) h82) h44)) (S h65)) h30) h64) h52) h51) h25
  have h85 := C (T (T h84 h50) (C (C (T (T (T h49 h29) h27) h26) h25) h24)) h3
  have h86 := h v19 x v0
  have h87 := C (T (T (T h84 h86) h85) h23) h3
  have h88 := S h50
  have h89 := C (T (T (T h8 h7) h28) h66) h25
  have h90 := h v20 v0 v20
  have h91 := S h83
  have h92 := C (T (T (T (T (T (T h49 h29) h27) h26) h67) h70) (C (C (T (T (C (C (T (T (T (T h8 h7) h17) h16) (C h14 (T (T (T (T h1 h57) h54) h71) (C (T (C h74 h3) (S h79)) h73)))) h4) h77) (S h80)) (S h81)) h78) h14)) h3
  have h93 := C (T (T (T (T (T (T h48 h47) h46) h31) h65) (C (T (T h92 h91) h68) h62)) h45) h25
  have h94 := S h86
  have h95 := C (T (T (C h89 h24) h88) h93) h3
  have h96 := h v0 v0 v20
  T (T (T (T (T (T (h x v19 v20) (C (T (h (M v20 x) v19 v11) (C (T (T (T (C (T (T (T (T (C h14 (T (T (T (T (T (T (T (T (T (T (C (T (T (T (T h22 h95) h87) h90) (C (T (T (T (C (T (T (T (C (T (T h22 h95) (C (T (T h84 h86) h87) h3)) h21) (S h96)) h28) h66) h3) h92) h91) h68) h21)) h25) (C (T (C (T (T (T h67 h83) h82) (C (T (T (T h49 h29) h96) (C (T (T (C (T (T (C (T (T (T h22 h95) h94) h93) h3) h94) h93) h3) h85) h23) h21)) h3)) h21) (S h90)) h25)) (S (h v19 v0 x))) h30) h64) h52) h51) h32) h34) h61) h53)) (C h14 h44)) (C (T (T (T h1 h57) h54) (h y v0 x)) h24)) (S (h v0 x v19))) h89) h24) h88) h86) h87) h14)) h21)) (S (h v0 v11 v20))) h18) h13) h10) h2

