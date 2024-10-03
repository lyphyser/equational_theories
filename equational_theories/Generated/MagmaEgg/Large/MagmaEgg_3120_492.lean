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
theorem Equation3120_implies_Equation492 (G: Type _) [Magma G] (h: Equation3120 G) : Equation492 G := fun x y z =>
  let v0 := M z y
  let v1 := M z v0
  let v2 := M x v1
  let v3 := M y v2
  have h4 := R v3
  have h5 := R v2
  have h6 := h v2 y v3
  have h7 := S h6
  have h8 := h y v3 v3
  have h9 := C (T h8 (C h7 h4)) h5
  have h10 := h v3 v2 v1
  have h11 := S h10
  have h12 := h v1 v1 v3
  have h13 := S h12
  have h14 := R v1
  have h15 := R v0
  have h16 := h z v1 v1
  have h17 := S h16
  have h18 := h v0 z v1
  have h19 := C h18 h14
  have h20 := C (T h19 h17) h15
  have h21 := C (C h20 h14) h14
  have h22 := h v1 v0 v1
  have h23 := h v1 v1 z
  have h24 := S h23
  have h25 := R z
  have h26 := C (T h22 h21) h25
  have h27 := C (T (T (T (C h26 h25) h24) h22) h21) h25
  have h28 := h v0 z z
  have h29 := C (T h28 h27) h25
  have h30 := C (T (T (T h29 h24) h22) h21) h4
  have h31 := C h30 h4
  have h32 := h y z v3
  have h33 := T (T h32 h31) h13
  have h34 := C h9 h14
  have h35 := h v3 v2 y
  have h36 := S h35
  have h37 := R y
  have h38 := C (C h9 h37) h37
  have h39 := C (T h38 h36) h33
  have h40 := h v2 y y
  have h41 := h v2 v1 v3
  have h42 := S h18
  have h43 := C h42 h14
  have h44 := C (T h16 h43) h15
  have h45 := S h22
  have h46 := C (C h44 h14) h14
  have h47 := T (T h46 h45) h44
  have h48 := h v0 z y
  have h49 := S h32
  have h50 := S h28
  have h51 := C (T h46 h45) h25
  have h52 := C (T (T (T h46 h45) h23) (C h51 h25)) h25
  have h53 := C (T h52 h50) h25
  have h54 := C (T (T (T h46 h45) h23) h53) h4
  have h55 := C h54 h4
  have h56 := T (T h12 h55) h49
  have h57 := C (T (T (T h42 h28) h27) h51) h56
  have h58 := C (T (T (T (C (T h16 h57) h56) (S h48)) h28) h27) h25
  have h59 := C (T (T (T h26 h52) h50) h18) h33
  have h60 := C (T (T (T h52 h50) h48) (C (T h59 h17) h33)) h25
  have h61 := h v1 z y
  have h62 := S h61
  have h63 := T h23 h60
  have h64 := C (C h63 h37) h56
  have h65 := C (C (T h58 h24) h37) h33
  have h66 := C (T (T (C (T (T h28 h27) h51) h37) h59) h43) h15
  have h67 := T (T (T h66 h20) h61) h65
  have h68 := C (T (T h19 h57) (C (T (T h26 h52) h50) h37)) h15
  have h69 := h y z y
  have h70 := S h69
  have h71 := C (C (T (T (T (T h32 h31) h13) h23) h53) h37) h37
  have h72 := T (T (T (T (T (T h71 h70) h32) h31) h13) h44) h68
  have h73 := C (C (T (T (T (T h29 h24) h12) h55) h49) h37) h37
  have h74 := T (T (T (T h32 h31) h13) h23) h60
  have h75 := C (C h74 h56) h37
  have h76 := T (T (T (T (T (T h75 h62) h12) h55) h49) h69) h73
  have h77 := T (T (T (T h58 h24) h12) h55) h49
  have h78 := C (C h77 h33) h37
  have h79 := h y v2 v2
  have h80 := S h40
  have h81 := S h8
  have h82 := C (T (C h6 h4) h81) h5
  have h83 := C (C h82 h37) h37
  have h84 := C (T (T (C h82 h14) (C (T h35 h83) h56)) h80) h56
  have h85 := C (T h10 h84) h5
  have h86 := C h82 h5
  have h87 := h v3 v2 v2
  have h88 := C (T (T h40 h39) h34) h33
  have h89 := C (T (T (T (T (T (T (T (T (T (T h38 h36) h87) (C (T (T (T (T (T (T (T (T h86 h85) (C (T (T (T h88 h11) h87) (C (T h86 h85) h5)) h5)) (S h79)) h32) h31) h13) h61) h78) h5)) (C h76 h5)) (C h72 h5)) (C h67 h5)) (C (T (T (T h64 h62) h23) h60) h5)) (C (T (T (T h58 h24) h22) h21) h5)) (C h47 h5)) (C h20 h5)) h33
  have h90 := T (T (T (T (T (T h71 h70) h32) h31) h13) h61) h78
  have h91 := T (T (T (T (T (T h66 h20) h12) h55) h49) h69) h73
  have h92 := T (T (T h64 h62) h44) h68
  have h93 := T (T h20 h22) h21
  have h94 := S h87
  have h95 := C h9 h5
  have h96 := C (T h88 h11) h5
  have h97 := T (T (T h58 h24) h61) h65
  have h98 := C (T (T (T (T (T (T (T (T (T (T (C h44 h5) (C h93 h5)) (C (T (T (T h46 h45) h23) h60) h5)) (C h97 h5)) (C h92 h5)) (C h91 h5)) (C h90 h5)) (C (T (T (T (T (T (T (T (T h75 h62) h12) h55) h49) h79) (C (T (T (T (C (T h96 h95) h5) h94) h10) h84) h5)) h96) h95) h5)) h94) h35) h83) h56
  have h99 := h v2 v1 v2
  have h100 := C (C (T h98 h80) h5) h5
  have h101 := S (h v2 v2 x)
  have h102 := R x
  T (T (h x v1 v3) (C (T (T (C (T (T (C (T (T (T (T (T (T (T (T (C h63 h102) (C h97 h102)) (C h92 h102)) (C h91 h102)) (C h90 h102)) (C (T (T (T (T (T (T h75 h62) h12) h55) h49) (h y x x)) (C (T (T (T (C (C (T (T (C h102 h33) h99) h100) h102) h102) h101) h99) h100) h102)) h102)) h101) h99) h100) h56) (C (R (M (M v2 v2) v2)) h33)) (C (T (T (T (T (T (T (T (T (T (T (T (T (C (C (T h40 h89) h5) h5) (S h99)) h41) (C (T (T (T (T (T (T (C (T (T h98 h80) h6) h4) h81) h32) h31) h13) h61) h78) h4)) (C h76 h4)) (C h72 h4)) (C h67 h4)) (C (T (T (T (T h64 h62) h12) h55) h49) h4)) (C h74 h4)) (C (T h58 h53) h4)) h30) (C h47 h4)) (C h20 h4)) h14)) h4) (C (C (T (T (T (T (C h44 h4) (C h93 h4)) h54) (C (T h29 h60) h4)) (C h77 h4)) h56) h4)) (C (T (T (C (T (T (T (T (T (T (T (T (C (T (T (T (T h32 h31) h13) h61) h65) h4) (C h92 h4)) (C h91 h4)) (C h90 h4)) (C (T (T (T (T (T (T h75 h62) h12) h55) h49) h8) (C (T (T h7 h40) h89) h4)) h4)) (S h41)) h40) h39) h34) h33) h11) h9) h4)) h4)) (S (h v3 v2 v3))

