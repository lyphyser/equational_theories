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
theorem Equation895_implies_Equation1384 (G: Type _) [Magma G] (h: Equation895 G) : Equation1384 G := fun x y z =>
  let v0 := M z x
  have h1 := h z y x
  have h2 := R y
  let v3 := M z z
  let v4 := M v3 x
  have h5 := h v4 v4 (M v0 (M v4 x))
  have h6 := S h5
  have h7 := h z v4 x
  have h8 := R v4
  have h9 := C h8 (C h7 h7)
  let v10 := M v4 v3
  have h11 := h v10 x v4
  have h12 := S h11
  have h13 := h x x (M v0 (M x x))
  have h14 := h z x x
  have h15 := R x
  have h16 := T (C h15 (C h14 h14)) (S h13)
  have h17 := h v3 v3 (M v0 v4)
  have h18 := S h17
  have h19 := h z v3 x
  have h20 := R v3
  have h21 := C h20 (C h19 h19)
  have h22 := h v3 v4 v3
  have h23 := S h22
  have h24 := T h9 h6
  have h25 := C h24 h20
  have h26 := T h21 h18
  have h27 := C h25 h26
  have h28 := S h19
  have h29 := C h20 (C h28 h28)
  have h30 := T h17 h29
  have h31 := C h30 (T h27 h25)
  have h32 := h v10 v3 v3
  have h33 := C (T (T h25 h9) h6) (T h32 h31)
  have h34 := S h7
  have h35 := C h8 (C h34 h34)
  have h36 := T h5 h35
  have h37 := C h36 h20
  have h38 := C h37 h36
  have h39 := C h36 h8
  have h40 := T (T h38 h33) h23
  have h41 := C h40 (T (T (T h39 h38) h33) h23)
  let v42 := M v4 v4
  have h43 := R v42
  have h44 := C h39 h43
  let v45 := M v4 y
  let v46 := M y v45
  have h47 := h (M v42 v42) v46 v4
  have h48 := S h47
  have h49 := h v46 v46 (M v0 (M v46 x))
  have h50 := h z v46 x
  have h51 := R v46
  have h52 := C h24 h8
  have h53 := C h52 h43
  have h54 := C h25 h24
  have h55 := S h32
  have h56 := C h37 h30
  have h57 := C h26 (T h37 h56)
  have h58 := T (T h5 h35) h37
  have h59 := C h58 (T h57 h55)
  have h60 := T (T h22 h59) h54
  have h61 := C h60 (T (T (T h22 h59) h54) h52)
  have h62 := C (T (T (T h17 h29) h61) h53) (T (T (T h27 h25) h9) h6)
  have h63 := h v46 v4 v3
  have h64 := C h51 (T h63 (C (T (T (T h5 h35) h32) h62) (C (T (C h51 (C h50 h50)) (S h49)) h24)))
  have h65 := h (M v46 v46) v45 v4
  have h66 := S h65
  have h67 := h v45 v45 (M v0 (M v45 x))
  have h68 := h z v45 x
  have h69 := R v45
  have h70 := S h50
  have h71 := C (T (T (T h44 h41) h21) h18) (T (T (T h5 h35) h37) h56)
  have h72 := C h51 (T (C (T (T (T h71 h55) h9) h6) (C (T h49 (C h51 (C h70 h70))) h36)) (S h63))
  have h73 := C (T h47 h72) h8
  have h74 := h v45 v4 v3
  have h75 := C h69 (T h74 (C (T (T (T (T h5 h35) h32) h62) h73) (C (T (C h69 (C h68 h68)) (S h67)) h24)))
  let v76 := M v45 v45
  have h77 := h v76 v3 v4
  have h78 := S h77
  have h79 := h v10 v4 v4
  have h80 := C (T h64 h48) h8
  have h81 := C (T h75 h66) h8
  have h82 := T (T (T (T (T h81 h80) h71) h55) h9) h6
  have h83 := S h68
  have h84 := C h69 (T (C (T (T (T (T h80 h71) h55) h9) h6) (C (T h67 (C h69 (C h83 h83))) h36)) (S h74))
  have h85 := T (T (T (T (T h5 h35) h32) h62) h73) (C (T h65 h84) h8)
  have h86 := h v76 v4 v4
  have h87 := C (T (T (T (T (T (T (T h75 h66) h64) h48) h44) h41) h21) h18) (T (T (T (T (T (T (T (T (T h17 h29) h61) h53) h47) h72) h65) h84) h86) (C h85 (T (T (T (T (C h82 (T (T (T (T (T (T h39 h38) h33) h23) h17) h29) h61)) (S h79)) h32) h31) (C h26 h24))))
  have h88 := C h15 (C (T (T (T (T (T (T (T (T (T h87 h78) h75) h66) h64) h48) h44) h41) h21) h18) h16)
  have h89 := h v76 x v3
  have h90 := T h87 h78
  have h91 := C h60 (T (T (T (T (C h90 h26) h87) h78) h89) h88)
  have h92 := h v76 v3 v3
  have h93 := C h15 (T (T (T (T (T (T (T (T (T h17 h29) h61) h53) h47) h72) h65) h84) h92) h91)
  let v94 := M x v3
  have h95 := S h89
  have h96 := S h14
  have h97 := C h15 (C h96 h96)
  have h98 := C (T (T (T (T (T (T (T h17 h29) h61) h53) h47) h72) h65) h84) (T (T (T (T (T (T (T (T (T (C h82 (T (T (T (T (C h30 h36) h57) h55) h79) (C h85 (T (T (T (T (T (T h41 h21) h18) h22) h59) h54) h52)))) (S h86)) h75) h66) h64) h48) h44) h41) h21) h18)
  have h99 := C h15 (C (T (T (T (T (T (T (T (T (T h17 h29) h61) h53) h47) h72) h65) h84) h77) h98) (T h13 h97))
  have h100 := C h15 (T (T (T (T (T (T (T (T (T (C h40 (T (T (T (T h99 h95) h77) h98) (C (T h77 h98) h30))) (S h92)) h75) h66) h64) h48) h44) h41) h21) h18)
  T (T (T h13 h97) (h v94 y v3)) (C h2 (C (T (T (T (T (T (C h16 (T (T (T (T (T (T (T (T (T (T (T h17 h29) h61) h53) h47) h72) h65) h84) h92) h91) (C (T (T (T (T (T (T (T (T (T (T (T (T (T h38 h33) h23) h17) h29) h61) h53) h47) h72) h65) h84) (h v76 v4 v3)) (C h58 (T (T (T (T (T (T (C h90 h24) h81) h80) h71) h55) h11) h100))) (C (T (T h25 h11) h100) (T (T (T h93 h12) h9) h6))) (T (T (T (T (T (T (T (T (T (T (T (T (T h99 h95) h75) h66) h64) h48) h44) h41) h21) h18) h22) h59) h54) h52))) (C (R (M v94 v4)) (T (T (T (T (T (T (T (T (T (T (T (T (T h39 h38) h33) h23) h17) h29) h61) h53) h47) h72) h65) h84) h89) h88)))) (S (h v94 x v4))) h93) h12) h9) h6) (T (C h2 (C h1 h1)) (S (h y y (M v0 (M y x)))))))

