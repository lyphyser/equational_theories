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
theorem Equation572_implies_Equation2196 (G: Type _) [Magma G] (h: Equation572 G) : Equation2196 G := fun x y z =>
  let v0 := M x y
  let v1 := M y z
  let v2 := M v1 z
  let v3 := M v2 v0
  have h4 := h y z v2
  have h5 := S h4
  have h6 := h v1 z z
  have h7 := R v2
  have h8 := C h7 (S h6)
  have h9 := h z v2 z
  have h10 := h z v2 y
  have h11 := h v2 z z
  have h12 := S h11
  have h13 := S h9
  have h14 := C h7 h6
  have h15 := T h14 h13
  have h16 := R z
  have h17 := C h16 (C h7 h15)
  have h18 := C h16 (T h4 h17)
  have h19 := C h16 h18
  have h20 := C h16 (T h19 h12)
  have h21 := R y
  have h22 := h z y z
  have h23 := h v1 v2 v1
  have h24 := S h23
  have h25 := R v1
  have h26 := C h25 h15
  have h27 := C h25 h26
  have h28 := C h25 h27
  have h29 := h v2 v1 v1
  have h30 := C h25 (T (T h26 h29) h28)
  have h31 := T h9 h8
  have h32 := C h25 h31
  have h33 := C h25 h32
  have h34 := C h7 (T h33 h30)
  have h35 := h v1 v2 v2
  have h36 := C h16 (T h35 (C h7 (T (T (T (C h7 (T (T h34 h24) (C h21 (T h22 (C h21 h20))))) (S h10)) h9) h8)))
  have h37 := T h36 h5
  have h38 := R v3
  have h39 := C h38 h37
  have h40 := S h29
  have h41 := C h25 h33
  have h42 := C h25 (T (T h41 h40) h32)
  have h43 := C h7 (T h42 h27)
  have h44 := C h16 (C h7 h31)
  have h45 := C h16 (T h44 h5)
  have h46 := C h16 h45
  have h47 := C h16 (T h11 h46)
  have h48 := C h16 (T (C h7 (T (T (T h14 h13) h10) (C h7 (T (T (C h21 (T (C h21 h47) (S h22))) h23) h43)))) (S h35))
  have h49 := h y z z
  have h50 := S h49
  have h51 := C h16 (T h44 h48)
  have h52 := C h16 h51
  have h53 := h v2 v3 y
  have h54 := S h53
  have h55 := h x y v2
  have h56 := C h38 (C h21 h55)
  have h57 := C h38 (T (T (T (T (T (T h56 h54) h11) h52) h50) h4) h48)
  have h58 := C h38 (C h21 (S h55))
  have h59 := C h38 (T h53 h58)
  have h60 := C h38 (T h56 h54)
  have h61 := h v2 v0 v0
  have h62 := C h38 (T (T (S h61) h53) h58)
  have h63 := h v0 v3 v0
  have h64 := h v0 y v2
  have h65 := R v0
  have h66 := C h65 h37
  have h67 := C h16 (T h36 h17)
  have h68 := T (T (T (T (T (T h41 h40) h11) h52) h50) h4) h48
  have h69 := C h16 h68
  have h70 := C h16 (T (T (T h19 h12) h29) h28)
  have h71 := C h16 (T (T (T h41 h40) h11) h46)
  have h72 := h v1 z v1
  have h73 := h v1 z v3
  have h74 := C h38 (T (T h63 h62) h60)
  have h75 := C h65 (T (T (T (T (T (T (C h16 (T (T (T (T (C h16 h74) (S h73)) h72) h71) h20)) (C h16 (T (T (T (T h47 h70) h69) h67) h45))) h19) h52) h50) h4) h48)
  have h76 := h v3 v0 z
  have h77 := h v3 y x
  have h78 := S h77
  have h79 := R x
  have h80 := h y x v3
  have h81 := C h21 (C h79 (T h80 (C h79 (T h57 h39))))
  have h82 := C h16 h67
  have h83 := T (T h49 h82) h12
  have h84 := C h83 (C h83 (T (T (T (T h81 h78) h76) h75) h66))
  have h85 := R (M y v0)
  have h86 := T (T h11 h52) h50
  have h87 := T h4 h48
  have h88 := C h21 (C h79 (T (C h79 (T (C h38 h87) (C h38 (T (T (T (T (T (T h36 h5) h49) h82) h12) h53) h58)))) (S h80)))
  have h89 := T h77 h88
  have h90 := R (M y v3)
  have h91 := C h83 h90
  have h92 := C h86 h90
  have h93 := h y v3 v2
  have h94 := h v1 y v1
  have h95 := S h94
  have h96 := C h25 h37
  have h97 := C h25 h68
  have h98 := T (T (T (T (T (T h36 h5) h49) h82) h12) h29) h28
  have h99 := C h25 h98
  have h100 := C h25 h87
  have h101 := C h86 (T (T (T h100 h99) (C h25 (T h41 (C h25 (T h30 h97))))) (C h25 (C h25 h96)))
  have h102 := C h86 (T h101 h95)
  have h103 := C h21 h102
  have h104 := h v1 y v2
  have h105 := C h83 (T (T (T (C h25 (C h25 h100)) (C h25 (T (C h25 (T h99 h42)) h28))) h97) h96)
  have h106 := C h83 (T h94 h105)
  have h107 := R (M v1 y)
  have h108 := R (M v1 v2)
  have h109 := S h72
  have h110 := C h16 h98
  have h111 := C h86 (T (T (T (T (T (T h18 h51) h110) h109) h23) h43) (C h86 h108))
  have h112 := S h63
  have h113 := C h38 (T (T h56 h54) h61)
  have h114 := C h16 (T (T (T (T h47 h70) h109) h73) (C h16 (C h38 (T (T h59 h113) h112))))
  have h115 := C h16 (T (T (T (T h18 h51) h110) h71) h20)
  have h116 := S h76
  have h117 := C h65 (T (T (T (T (T (T h36 h5) h49) h82) h46) h115) h114)
  have h118 := C h65 h87
  T (T (T (h x y y) h84) (C h86 (T (T (T (T (C h86 (T (T (T (T h118 h117) h116) (h v3 v0 v0)) (C h65 (C h65 (T (T (C h65 (T (T (T (T (T (T (T h74 (C h38 (T (T (T (T (T h59 h113) h112) h64) (C h21 (T (T (T (C h86 (C h86 (T (T (T (T h118 h117) h116) h77) h88))) (C h83 (C h83 h85))) (C h7 (C h86 (T h81 h78)))) h92))) (C h83 h91)))) (S h93)) h49) h82) h46) h115) h114)) h75) h66))))) (S (h v0 y v0))) (h v0 v3 v1)) (C h38 (T (T (T (T (C h25 (T (T (T (T (T (T (T (T (C h25 (T (C h65 h89) (C h65 (T (T (T h81 h78) h76) h75)))) (S (h z v1 v0))) (h z y v2)) (C h83 (T (T (T (T (T (C h7 h111) (S (h v1 v2 y))) h72) h69) h67) h45))) h111) (C h21 (T (T (T (T (T (C h83 h108) h34) h24) h94) h105) (C h86 h107)))) (C h21 (T (T (T (T (C h83 h107) h101) h95) h104) h103))) (C h83 (T (T (T (C h21 h106) (S h104)) h94) h105))) h102)) (C h25 (T h106 (C h86 (T (T (T h101 h95) h104) h103))))) (S (h y v1 y))) h93) (C h38 (T (T (T (T (T (C h86 h92) (C h21 (T (T (T h91 (C h7 (C h83 h89))) (C h86 (C h86 h85))) h84))) (S h64)) h63) h62) h60))))) (C h38 (T (C h38 (T h59 h57)) (C h38 h39)))))) (S (h v3 y v3))

