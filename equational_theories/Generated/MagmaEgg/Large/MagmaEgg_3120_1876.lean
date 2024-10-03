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
theorem Equation3120_implies_Equation1876 (G: Type _) [Magma G] (h: Equation3120 G) : Equation1876 G := fun x y z =>
  let v0 := M y z
  let v1 := M x v0
  let v2 := M z y
  let v3 := M v1 v2
  have h4 := h v3 v1 v1
  have h5 := S h4
  have h6 := R v1
  have h7 := R v3
  have h8 := h v1 v3 v3
  have h9 := S h8
  have h10 := h v2 v1 v3
  have h11 := h v2 v0 y
  have h12 := S h11
  have h13 := R y
  have h14 := h v0 y y
  have h15 := S h14
  have h16 := R v0
  have h17 := h y v0 z
  have h18 := S h17
  have h19 := R z
  have h20 := h v0 z y
  have h21 := S h20
  have h22 := h z y v0
  have h23 := S h22
  have h24 := h y v0 v0
  have h25 := C (T h24 (C h23 h16)) h19
  have h26 := C (C h25 h13) h13
  have h27 := C (T h26 h21) h13
  have h28 := h z y y
  have h29 := C (T (T h23 h28) h27) h16
  have h30 := T h24 h29
  have h31 := C (C h30 h19) h19
  have h32 := C (T h31 h18) h16
  have h33 := C h32 h13
  have h34 := h z v0 y
  have h35 := C (T h34 (C h33 h13)) h13
  have h36 := T h35 h15
  have h37 := R v2
  have h38 := S h24
  have h39 := C (T (C h22 h16) h38) h19
  have h40 := C (C h39 h37) h36
  have h41 := h v0 z v2
  have h42 := h v0 z v0
  have h43 := S h42
  have h44 := C (C (T (T h35 h15) h25) h16) h36
  have h45 := T (T (T h44 h43) h41) h40
  have h46 := C h45 h13
  have h47 := S h28
  have h48 := C (C h39 h13) h13
  have h49 := C (T h20 h48) h13
  have h50 := C (T (T h49 h47) h22) h16
  have h51 := T h50 h38
  have h52 := C (C h51 h19) h19
  have h53 := C (T h17 h52) h16
  have h54 := C h53 h13
  have h55 := C (T (C h54 h13) (S h34)) h13
  have h56 := T h14 h55
  have h57 := C (C (T (T h39 h14) h55) h16) h56
  have h58 := C (T (T (T h26 h21) h42) h57) h13
  have h59 := h z v0 v0
  have h60 := C (T (T (T h44 h43) h20) h48) h13
  have h61 := S h41
  have h62 := C (C h25 h37) h56
  have h63 := T (T (T h62 h61) h42) h57
  have h64 := C h63 h13
  have h65 := C (T (T (T (C (T (T (T h35 h15) h41) h40) h13) h64) h60) h27) h36
  have h66 := C (T (T (T (T h65 h50) h38) h17) h52) h36
  have h67 := h y v2 v2
  have h68 := C (T (T (T h49 h58) h46) (C (T (T (T h62 h61) h14) h55) h13)) h56
  have h69 := C (T (T (T (T h31 h18) h24) h29) h68) h56
  have h70 := C (T (T (T (T (T (T h53 h69) (C (T (T (T (T h65 h50) h38) h67) (C h66 h36)) h36)) (S h59)) h28) h58) h46) h13
  have h71 := R (M (M v2 y) v2)
  have h72 := h y v2 y
  have h73 := S h72
  have h74 := C (C (T (T h24 h29) h68) h13) h13
  have h75 := R (M (M y y) y)
  have h76 := C (C (T (T h65 h50) h38) h13) h13
  have h77 := C (T (T (T (T (T (C h30 h37) (C (T (T (T h50 h38) h72) h76) h36)) (C h75 h56)) (C (T (T (T (T h74 h73) h24) h29) h68) h36)) (C h71 h56)) h66) h13
  have h78 := C (T (C (T (T (T (T h77 h33) h70) h12) h10) h7) h9) h7
  have h79 := h v2 y v3
  have h80 := C (T (T (T (T (T h77 h33) h70) h12) h79) h78) h6
  have h81 := C h80 h6
  have h82 := h v2 y v1
  have h83 := S h82
  have h84 := C (T (T (T (T (T h69 (C h71 h36)) (C (T (T (T (T h65 h50) h38) h72) h76) h56)) (C h75 h36)) (C (T (T (T h74 h73) h24) h29) h56)) (C h51 h37)) h13
  have h85 := C (T (T (T (T (T (T h64 h60) h47) h59) (C (T (T (T (T (C h69 h56) (S h67)) h24) h29) h68) h56)) h66) h32) h13
  have h86 := S h79
  have h87 := S h10
  have h88 := C (T h8 (C (T (T (T (T h87 h11) h85) h54) h84) h7)) h7
  have h89 := C (T (T (T (T (T h88 h86) h11) h85) h54) h84) h6
  have h90 := T (C (T (T (C (T (T h4 (C (T (T (T (C h89 h6) h83) h79) h78) h6)) h89) h6) h83) h10) h7) h9
  have h91 := C (T (T h87 h82) (C (T (T h80 (C (T (T (T h88 h86) h82) h81) h6)) h5) h6)) h7
  have h92 := h v1 v3 v1
  have h93 := S h92
  have h94 := C (C (T h8 h91) h6) h6
  have h95 := C (C h90 h6) h6
  have h96 := h v1 v1 x
  have h97 := S h96
  have h98 := R x
  have h99 := h v0 x x
  have h100 := C (T (T (T (T (T (T (T h77 h33) h70) h12) h35) h15) h99) (C (T (T (T (C (C (T h92 h95) h98) h98) h97) h92) h95) h98)) h98
  have h101 := C (T h54 h84) h98
  have h102 := C (T (T (T (T (T h62 h61) h14) h55) h11) h85) h98
  have h103 := C h45 h98
  have h104 := C (T h42 h57) h98
  have h105 := h x v0 v1
  T (T h105 (C (T (T (T (T (T (C (T (T (T (C (T (T (T (T (T (T (T h104 h103) h102) h101) h100) h97) (h v1 v1 v0)) (C (C (T (T (T (T (T (T (T h94 h93) h96) (C (T (T (T (T (T (T (T (C (T (T (T h94 h93) h96) (C (C (T h94 h93) h98) h98)) h98) (S h99)) h14) h55) h11) h85) h54) h84) h98)) (C (T h77 h33) h98)) (C (T (T (T (T (T h70 h12) h35) h15) h41) h40) h98)) (C h63 h98)) (C (T h44 h43) h98)) h16) h16)) h16) (S (h x v0 v0))) h105) (C (C (T (T (T (C (T (T (T (T (T (T (T h104 h103) h102) h101) h100) h97) h92) h95) h16) (C (R (M (M v1 v1) v1)) h56)) (C (T (T (T h94 h93) h8) h91) h37)) (C h90 h36)) h6) h6)) h6) (S (h v0 v1 v1))) h14) h55) h82) h81) h6)) h5

