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
theorem Equation887_implies_Equation31 (G: Type _) [Magma G] (h: Equation887 G) : Equation31 G := fun x y =>
  let v0 := M y y
  let v1 := M v0 x
  have h2 := S (h v1 v0 x)
  let v3 := M x x
  let v4 := M v1 v0
  let v5 := M v4 v3
  have h6 := h v0 x v0
  have h7 := S h6
  have h8 := R v0
  have h9 := h v0 x (M v1 v1)
  have h10 := S h9
  have h11 := h v1 v1 v1
  have h12 := R x
  have h13 := C h12 h11
  have h14 := R v1
  have h15 := h x v4 y
  have h16 := S h15
  have h17 := h v0 x y
  have h18 := R v4
  have h19 := C h18 (C h17 h8)
  have h20 := C (T h19 h16) h14
  have h21 := C (T (T h20 h13) h10) h8
  have h22 := C h14 h21
  let v23 := M v0 v0
  let v24 := M v4 v23
  have h25 := h v24 v1 y
  have h26 := S h17
  have h27 := C h18 (C h26 h8)
  have h28 := T (T (T h15 h27) h25) h22
  have h29 := S h25
  have h30 := C (T h15 h27) h14
  have h31 := C h12 (S h11)
  have h32 := C (T (T h9 h31) h30) h8
  have h33 := C h14 h32
  have h34 := T (T (T h33 h29) h19) h16
  have h35 := C h34 h28
  have h36 := T (T (C h28 h12) h35) h7
  have h37 := R v3
  have h38 := h v0 y y
  have h39 := h y y v23
  have h40 := S h39
  have h41 := h v0 v0 v0
  have h42 := R y
  have h43 := C h42 h41
  have h44 := C (T h43 h40) h36
  have h45 := C h8 (T (T h44 h43) h40)
  have h46 := h y v0 x
  have h47 := C h34 h12
  have h48 := C h28 h34
  have h49 := T (T h6 h48) h47
  have h50 := S h41
  have h51 := C h42 h50
  have h52 := S h46
  have h53 := C (T h39 h51) h49
  have h54 := C h8 (T (T h39 h51) h53)
  let v55 := M v0 y
  have h56 := h v55 y x
  have h57 := S h56
  have h58 := R (M v55 y)
  have h59 := C h58 h49
  have h60 := T h46 h45
  have h61 := C (T (T h35 h7) (C h60 h42)) h36
  have h62 := R (M (M v1 v23) x)
  have h63 := C h62 h49
  have h64 := C (T h33 h29) h14
  have h65 := C (T (T (T (T (T h64 h20) h13) h10) h6) h48) h8
  have h66 := C (T h25 h22) h14
  have h67 := C h66 h8
  have h68 := T h54 h52
  have h69 := C h68 (T (T (T (T (T h32 h67) h65) h63) h61) h59)
  have h70 := C (T (T (T (T (T h69 h57) h54) h52) h39) h51) h49
  have h71 := C (T (T (T (T (T h70 h44) h43) h40) h46) h45) h36
  let v72 := M v55 v23
  have h73 := R (M v72 v0)
  have h74 := C h73 h49
  have h75 := C h68 h42
  have h76 := C h60 (T (T (T (T (T (C h58 h36) (C (T (T h75 h6) h48) h49)) (C h62 h36)) (C (T (T (T (T (T h35 h7) h9) h31) h30) h66) h8)) (C h64 h8)) h21)
  have h77 := C (T (T (T (T (T h43 h40) h46) h45) h56) h76) h36
  have h78 := C (T (T (T (T (T (T (T h69 h57) h54) h52) h39) h51) h53) h77) h8
  have h79 := T (T (T (T (T (T h39 h51) h53) h77) h78) h74) h71
  have h80 := C (T (T (T (T (T (T (T h70 h44) h43) h40) h46) h45) h56) h76) h8
  have h81 := C h73 h36
  have h82 := C (T (T (T (T (T h54 h52) h39) h51) h53) h77) h49
  have h83 := T (T (T (T (T (T (T (T h82 h81) h80) h70) h44) h43) h40) h46) h45
  have h84 := C h83 h8
  let v85 := M v55 v0
  have h86 := R (M v85 v0)
  have h87 := T (T (T (T (T (T (T (T h54 h52) h39) h51) h53) h77) h78) h74) h71
  have h88 := C h87 h8
  have h89 := T (T (T (T (T (T h82 h81) h80) h70) h44) h43) h40
  have h90 := h v0 y v0
  have h91 := C (T h69 h57) h42
  have h92 := C (R (M v72 y)) h49
  have h93 := C (C (T h56 h76) h42) h36
  have h94 := C h36 h12
  have h95 := C h18 h49
  have h96 := R (M v23 v23)
  have h97 := C h18 (T (C h26 h96) h50)
  have h98 := h x v4 v23
  have h99 := S h98
  have h100 := C h18 (T h41 (C h17 h96))
  have h101 := C h18 h36
  have h102 := R (M v3 x)
  have h103 := C h49 h12
  have h104 := C h8 (T (C (T (T (T (C (T (T (C h103 h37) (C h102 h36)) (C h94 h8)) h49) h101) h100) h99) (T (T (T (T (T (T (T (T (T (T h32 h67) h65) h63) h61) h59) h93) h92) (C (T (T (T (T (T (T h91 h75) h9) h31) h30) h66) (C (T (T (T (T (T (T h33 h29) h19) h16) h98) h97) h95) h14)) h36)) (C (R (M v5 v1)) h49)) (C (T (T (T (T (T (T (T (T (T (C (T (T (T (T (T (T h101 h100) h99) h15) h27) h25) h22) h14) h64) h20) h13) h10) h6) h48) h47) (h v3 x v0)) (C (T (T h98 h97) h95) (T (T (T (C h94 (T (T (T (T (T (T (T (T (T (T (T (T h32 h67) h65) h63) h61) h59) h93) h92) (C (T (T (T h91 h75) h90) (C h79 (T (T (T h69 h57) h54) h52))) h36)) (C (R (M v85 y)) h49)) (C (T (T (T (C h89 (T (T (T h46 h45) h56) h76)) (S h90)) h38) (C (T (T (T (T (T (T (T (T (T (T (T h39 h51) h53) h77) h78) h74) h71) h88) (C h88 h8)) (C h86 h49)) (C h84 h37)) (C h83 h37)) h89)) h36)) (C (R (M (M v55 v3) y)) h49)) (C (T (T (T (T (C (T (T (T (T (T (T (T (T (T (T (T (C h87 h37) (C h88 h37)) (C h86 h36)) (C h84 h8)) h84) h82) h81) h80) h70) h44) h43) h40) h79) (S h38)) h9) h31) h30) h37))) (S (h v24 v1 x))) h19) h16))) h36))) (S (h v5 x y)))
  have h105 := h (M v1 v3) v0 v0
  T (T (T (T (T (T (T h98 h97) h95) (C (T (T (C h103 h8) (C h102 h49)) (C h94 h37)) h36)) (C (T (T h105 h104) h2) h49)) h105) h104) h2

