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
theorem Equation4176_implies_Equation3770 (G: Type _) [Magma G] (h: Equation4176 G) : Equation3770 G := fun x y z =>
  let v0 := M y z
  let v1 := M x z
  have h2 := R v0
  have h3 := S (h x z v0)
  let v4 := M (M z v0) x
  have h5 := R x
  have h6 := S (h z v0 v0)
  have h7 := h y z v1
  have h8 := S h7
  let v9 := M z v1
  let v10 := M v9 y
  have h11 := h v10 v1 v0
  let v12 := M v0 v1
  have h13 := h v9 y v12
  have h14 := R v12
  have h15 := h z v1 x
  have h16 := R z
  have h17 := h x z v1
  have h18 := h v1 v9 x
  have h19 := h v9 x z
  have h20 := h z v1 v0
  have h21 := h v0 x z
  have h22 := h v0 x y
  have h23 := S h22
  have h24 := h y z z
  have h25 := S h24
  have h26 := R y
  have h27 := h z z v0
  have h28 := S h27
  have h29 := h z v0 v1
  have h30 := S h29
  have h31 := h v1 v12 z
  have h32 := C (T h31 (C h30 h16)) h2
  have h33 := h v1 v12 y
  have h34 := S h33
  have h35 := h y v0 v1
  have h36 := C h35 h26
  have h37 := C (T h36 h34) h2
  have h38 := h y y v0
  have h39 := T (T (T h38 h37) h32) h28
  have h40 := C h39 h26
  have h41 := h y y z
  have h42 := C (S h41) h26
  have h43 := h z v0 y
  have h44 := C (T (T (T h30 h43) h42) h40) h16
  have h45 := h (M v1 v12) v0 x
  have h46 := S h31
  have h47 := C (T (C h29 h16) h46) h2
  have h48 := h (M z z) x v12
  have h49 := R (M x v12)
  let v50 := M y y
  have h51 := h v50 x v12
  have h52 := R (M y v12)
  have h53 := h (M v50 x) y v12
  have h54 := h x y y
  have h55 := T (T (T h54 h53) (C (C h52 (T (T (T (T h51 (C (C h49 h39) h14)) (S h48)) (C (T (T (T (T (T h27 h47) h45) (C (T (T (C h22 (T (T h31 h44) h25)) (C (T h23 h21) h2)) (S h20)) h5)) h19) (C (T h18 (C (S h17) h5)) h16)) h5)) (S h15))) h14)) (S h13)
  have h56 := h v1 v0 v1
  have h57 := S h56
  have h58 := R v1
  have h59 := T (C h55 h58) h8
  have h60 := C (C h59 h58) h58
  let v61 := M x y
  have h62 := h v1 v61 v1
  have h63 := C (T h62 h60) h58
  have h64 := h v1 v1 v61
  have h65 := C (T (T (T (T h36 h34) h31) h44) h25) h2
  have h66 := C (S h35) h26
  have h67 := C (T h33 h66) h2
  have h68 := h z z v61
  have h69 := S h68
  have h70 := R v61
  have h71 := h z v61 v1
  have h72 := T (T (T h27 h47) h67) (S h38)
  have h73 := S h43
  have h74 := C h41 h26
  have h75 := C (T (T (T (C h72 h26) h74) h73) h29) h16
  have h76 := T (T (T h13 (C (C h52 (T (T (T (T h15 (C (T (T (T (T (T (C (T (C h17 h5) (S h18)) h16) (S h19)) (C (T (T h20 (C (T (S h21) h22) h2)) (C h23 (T (T h24 h75) h46))) h5)) (S h45)) h32) h28) h5)) h48) (C (C h49 h72) h14)) (S h51))) h14)) (S h53)) (S h54)
  have h77 := T h7 (C h76 h58)
  have h78 := C (T (C (C h77 h16) h58) (S h71)) h16
  have h79 := h v1 v0 z
  have h80 := h v1 v61 x
  let v81 := M y v0
  have h82 := C (T (T (T h63 h57) h79) h78) h70
  have h83 := C (T (T (T (C (T (T (T (T (T h64 h82) h69) h27) h47) h67) h26) (S (h v0 v81 y))) (h v0 v81 x)) (C (S (h x y v0)) h5)) h58
  have h84 := h y v1 v1
  have h85 := C (T (T (T (C (T h84 h83) h5) (S h80)) h62) h60) h58
  have h86 := h x y v1
  have h87 := S h64
  have h88 := S h62
  have h89 := C (C h77 h58) h58
  have h90 := C (T h89 h88) h58
  have h91 := S h79
  have h92 := C (T h71 (C (C h59 h16) h58)) h16
  have h93 := h z v0 x
  have h94 := S h93
  have h95 := h x y z
  have h96 := C h95 h5
  have h97 := C (T (T h64 h82) (C (T (T (T (T h92 h91) h56) (C (T (T (T h89 h88) h80) (C (T (C (T (T (T (T (T h96 h94) h43) h42) (C (T h38 h65) h26)) (C (T (T (T (T (T (T (C (T (T (T (T h24 h75) h46) h33) h66) h2) h37) h32) h28) h68) (C (T (T (T h92 h91) h56) h90) h70)) h87) h26)) h58) (S h84)) h5)) h58)) (S h86)) h70)) h16
  have h98 := h v1 x z
  have h99 := C (T (T h98 h97) (C (T (T (T (T (T (C (T (T (T (T h86 h85) h57) h79) h78) h70) h69) h27) h47) h67) h65) h16)) (T (T (C (T h64 (C (T h63 h57) h55)) h2) (S h11)) h8)
  have h100 := T (T (h v0 v1 v1) (h (M (M v1 v1) v0) v1 x)) (C (T h99 h6) h5)
  let v101 := M z v61
  T (T (T (T (T h86 h85) h57) (C (T (T (h x z z) (C (T (T (T (T (T (T (C h72 h5) (C (T (h y y y) (C (T (T (T h74 h73) h93) (C (S h95) h5)) h26)) h5)) (S (h y v61 x))) (h y v61 v0)) (C h23 h2)) (C (T (T (T (T (C (T (T (T (T h7 (h v10 v1 x)) (C (T (C (T h98 h97) h76) (S (h z v61 v61))) h5)) (h v101 x y)) (C (T (h v61 v101 x) (C (S (h x z v61)) h5)) h26)) h5) (S (h y v1 x))) h84) h83) (C (T h96 h94) h58)) h2)) (S (h v1 z v0))) h16)) (S (h z x z))) h2)) (C (T (T (T (T (h z x v12) (C (T (C (T (T (T (T (T (T (T (T (C h5 h100) (h x v4 v0)) (C (C h3 h5) h2)) (C (R (M v1 x)) (T (T h7 h11) (C (T (C (T h56 h90) h76) h87) h2)))) h99) h6) h43) h42) h40) h16) h25) h14)) (C h2 h100)) (h v0 v4 v0)) (C (C h3 h2) h2)) h2)) (S (h v0 v1 v0))

