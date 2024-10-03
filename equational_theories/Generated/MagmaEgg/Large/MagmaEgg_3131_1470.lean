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
theorem Equation3131_implies_Equation1470 (G: Type _) [Magma G] (h: Equation3131 G) : Equation1470 G := fun x y z =>
  let v0 := M z y
  let v1 := M z v0
  let v2 := M x y
  let v3 := M v2 v1
  have h4 := R y
  have h5 := h y v0 v1
  have h6 := R v0
  have h7 := R v1
  have h8 := h z y z
  have h9 := S h8
  have h10 := R z
  have h11 := h y z v1
  have h12 := S h11
  have h13 := h v0 z z
  have h14 := C (S h13) h7
  have h15 := h z v1 z
  have h16 := T h15 h14
  have h17 := h v1 z z
  have h18 := C (C (T h17 (C (C (T (C (C h16 h7) h10) h12) h10) h10)) h10) h4
  have h19 := C (T h18 h9) h4
  have h20 := S h15
  have h21 := C h13 h7
  have h22 := T h21 h20
  have h23 := C (C (T (C (C (T h11 (C (C h22 h7) h10)) h10) h10) (S h17)) h10) h4
  have h24 := h z v0 v0
  have h25 := S h24
  have h26 := h v0 v1 v1
  have h27 := C h22 h6
  have h28 := C h27 h6
  have h29 := C h16 h6
  have h30 := h v1 v0 v0
  have h31 := S h30
  have h32 := C h29 h6
  have h33 := C h32 h6
  have h34 := C (T (T h33 h31) h29) h6
  have h35 := C (T h34 h28) h7
  have h36 := h v0 v1 v0
  have h37 := C (T (T h19 h36) h35) h7
  have h38 := h z v1 y
  have h39 := C (T (C (T (T (T h21 h20) h38) h37) h7) (S h26)) h10
  have h40 := T h11 h39
  have h41 := h y z z
  have h42 := h z v0 z
  have h43 := C (T (T (T h33 h31) h29) (C (T (T (T (T h21 h20) h42) (C (S h41) h6)) (C h40 h6)) h6)) h6
  have h44 := C h28 h6
  have h45 := C (T (T h27 h30) h44) h6
  have h46 := h v0 v1 y
  have h47 := S h36
  have h48 := C (T h32 h45) h7
  have h49 := T (T h30 (C (T (T (T (T (T h45 h43) h25) h38) h37) (C (T (T (T h48 h47) h46) (C (C (T (C (T (T (T (T (T h32 h45) h43) h25) h8) h23) h4) h19) h4) h7)) h7)) h6)) (S h5)
  have h50 := R v3
  have h51 := S h38
  have h52 := C (T h8 h23) h4
  have h53 := C (T (T h48 h47) h52) h7
  have h54 := C (T h26 (C (T (T (T h53 h51) h15) h14) h7)) h10
  have h55 := T h54 h12
  have h56 := C h55 h50
  have h57 := h y v2 y
  have h58 := S h57
  have h59 := R v2
  have h60 := h v2 v3 v2
  have h61 := S h60
  have h62 := h v1 v2 v2
  have h63 := C h62 h50
  have h64 := T h63 h61
  have h65 := C (C (C h64 h4) h4) h49
  have h66 := h v3 v1 y
  have h67 := C (T (T (T (C (T h66 h65) h59) h58) h11) h39) h50
  have h68 := S h66
  have h69 := C (T (T (T (C (T (T (T (T (C h55 h6) (C h41 h6)) (S h42)) h15) h14) h6) h27) h30) h44) h6
  have h70 := T (T h5 (C (T (T (T (T (T (C (T (T (T (C (C (T h52 (C (T (T (T (T (T h18 h9) h24) h69) h34) h28) h4)) h4) h7) (S h46)) h36) h35) h7) h53) h51) h24) h69) h34) h6)) h31
  have h71 := C (S h62) h50
  have h72 := T h60 h71
  have h73 := C (C (C h72 h4) h4) h70
  have h74 := C (T h73 h68) h59
  have h75 := h y v3 y
  have h76 := S h75
  have h77 := h v3 y v3
  have h78 := S h77
  have h79 := C (T (C h67 h50) (C h56 h50)) h50
  have h80 := h v2 v3 v3
  have h81 := C (T h80 h79) h4
  have h82 := S h80
  have h83 := C (T (C (C h40 h50) h50) (C (C (T (T (T h54 h12) h57) h74) h50) h50)) h50
  have h84 := C (T h83 h82) h4
  have h85 := h v2 y v2
  have h86 := S h85
  have h87 := C (T (T (T h81 h78) h66) h65) h59
  have h88 := C (T h87 h58) h59
  have h89 := h y v2 v2
  have h90 := C (T (T (T h73 h68) h77) h84) h59
  have h91 := C (T h57 h90) h59
  have h92 := C (T h91 (C (T (T (T h87 h58) h89) (C h88 h59)) h59)) h4
  have h93 := h v2 y y
  have h94 := C (T (T (T h63 h61) h93) (C (T (C (T (T (T h92 h86) h93) (C (T (C (T (T (T h92 h86) h80) h79) h4) h84) h70)) h70) (C (C (T h81 h78) h49) h49)) h4)) h50
  have h95 := C h72 h50
  have h96 := C (T (T (T (T h95 h94) h76) h57) h74) h50
  have h97 := C h64 h50
  have h98 := R x
  have h99 := S h93
  have h100 := C (T (C (T (T (T (C h91 h59) (S h89)) h57) h90) h59) h88) h4
  T (T (h x y y) (C (C (T (T (T (C (T (C (T (T h75 (C (T (T (T (C (T (C (C (T h77 h84) h70) h70) (C (T (T (T (C (T h81 (C (T (T (T h83 h82) h85) h100) h4)) h49) h99) h85) h100) h49)) h4) h99) h60) h71) h50)) h97) h98) (C (T (T (T (T h95 h94) h76) (h y x v3)) (C (T (T h96 h67) h56) h98)) h98)) h4) (S (h v3 y x))) (h v3 v1 v3)) (C (T (T (T (C h97 h50) h96) h67) h56) h49)) h4) h4)) (S (h v3 y y))

