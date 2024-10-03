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
theorem Equation3404_implies_Equation3398 (G: Type _) [Magma G] (h: Equation3404 G) : Equation3398 G := fun x y z =>
  let v0 := M x z
  let v1 := M y v0
  have h2 := h z v1 z
  have h3 := S h2
  let v4 := M z z
  have h5 := h y y v1
  have h6 := S h5
  have h7 := h v1 y z
  have h8 := S h7
  have h9 := R y
  have h10 := C h9 h8
  let v11 := M z v1
  have h12 := h v11 z y
  have h13 := h v11 z z
  have h14 := S h13
  have h15 := h v1 z z
  have h16 := R z
  have h17 := C h16 h15
  have h18 := R v1
  have h19 := C h18 (T (T (T h17 h14) h12) h10)
  have h20 := h z z v1
  have h21 := h z z v11
  have h22 := h v1 z v0
  have h23 := h y v0 x
  have h24 := R v0
  have h25 := C h24 (S h23)
  let v26 := M x y
  have h27 := h v26 x v0
  have h28 := T h27 h25
  have h29 := h v26 x y
  have h30 := S h29
  have h31 := h y y x
  have h32 := T (T (C h9 (T (T h20 h19) h6)) (C h9 h31)) h30
  have h33 := h z y z
  have h34 := C h16 (T (C h24 (T (T h33 (C h16 h32)) (C h16 h28))) (S h22))
  have h35 := h y v0 z
  have h36 := h y v0 v1
  have h37 := h v1 (M v0 (M v1 y)) v1
  have h38 := R (M v1 v1)
  have h39 := h v0 z y
  have h40 := h z z v0
  have h41 := h v1 v4 v1
  have h42 := R v11
  have h43 := S h41
  have h44 := C h18 (C (T (C h24 (T h7 (C h16 (S h39)))) (S h40)) h38)
  have h45 := S h35
  have h46 := S h20
  have h47 := C h16 (S h15)
  have h48 := S h12
  have h49 := C h9 h7
  have h50 := C h18 (T (T (T h49 h48) h13) h47)
  have h51 := T (T h5 h50) h46
  have h52 := S h31
  have h53 := S h27
  have h54 := C h24 h23
  have h55 := T h54 h53
  have h56 := C h16 (T h22 (C h24 (T (T (C h16 h55) (C h16 (T (T h29 (C h9 h52)) (C h9 h51)))) (S h33))))
  have h57 := h v11 z x
  have h58 := h v1 x z
  have h59 := R x
  have h60 := C h18 (T (T (T (C h59 h58) (S h57)) h12) h10)
  have h61 := h x x v1
  have h62 := h x x v26
  have h63 := S h62
  have h64 := C h18 (T h35 h34)
  have h65 := C h9 (T (T (T h64 h19) h6) h31)
  have h66 := C h18 (T h56 h45)
  have h67 := C h9 (T (T (T h61 h60) h50) h66)
  have h68 := T (T h67 h65) h30
  have h69 := h x y x
  have h70 := T h69 (C h59 h68)
  have h71 := R v26
  have h72 := C h71 h70
  have h73 := T (T (T (T (T (T (T h72 h63) h61) h60) h50) h46) h21) (C h42 (T (C h16 (T (T (T (T (T (T (T h13 h47) h56) h45) h36) h37) h44) h43)) h3))
  have h74 := C h16 h73
  have h75 := S h69
  have h76 := S h61
  have h77 := C h18 (T (T (T h49 h48) h57) (C h59 (S h58)))
  have h78 := T (T (T h64 h19) h77) h76
  have h79 := C h9 h78
  have h80 := C h9 (T (T (T h52 h5) h50) h66)
  have h81 := T (T h29 h80) h79
  have h82 := C h59 h81
  have h83 := T h82 h75
  have h84 := C h71 h83
  have h85 := T h62 h84
  have h86 := C h16 h85
  have h87 := C h16 h78
  have h88 := C h16 (T h20 h66)
  have h89 := C h18 (T h13 h47)
  let v90 := M v11 z
  have h91 := h v1 v90 v0
  have h92 := h v0 v1 y
  have h93 := T (T (T h35 h34) h17) h14
  have h94 := h v1 y v1
  have h95 := h v1 y v0
  have h96 := h v26 x z
  have h97 := h y z x
  have h98 := h z z y
  have h99 := h v0 (M y y) v11
  have h100 := R (M v11 v0)
  have h101 := h v1 v90 z
  have h102 := h z v1 x
  have h103 := h v0 x v1
  have h104 := h v0 (M z (M v0 x)) v11
  have h105 := h x z v0
  have h106 := C h16 (T (T (T (C h24 (T (T (T (T (T (T (T h105 h104) (C h42 (C (T (T (T (T (C h16 (T (T h103 (C h18 (S h102))) (C h93 h42))) (S h101)) h89) h19) h6) h100))) (S h99)) (C h24 (T (T (T (T (T h5 h50) h46) h98) (C h9 (T (C h16 h97) (S h96)))) (C h9 h28)))) (S h95)) h94) (C h93 (S h92)))) (S h91)) h89) h46)
  have h107 := S h103
  have h108 := C h18 h102
  have h109 := T (T (T h13 h47) h56) h45
  have h110 := C h18 (T h17 h14)
  have h111 := S h98
  have h112 := C h9 (T h96 (C h16 (S h97)))
  have h113 := C h16 (T (T (T (T (S (h z z x)) h20) h110) h91) (C h24 (T (T (T (T (T (T (T (C h109 h92) (S h94)) h95) (C h24 (T (T (T (T (T (C h9 h55) h112) h111) h20) h19) h6))) h99) (C h42 (C (T (T (T (T h5 h50) h110) h101) (C h16 (T (T (C h109 h42) h108) h107))) h100))) (S h104)) (S h105))))
  have h114 := h v0 x z
  let v115 := M v26 x
  have h116 := h v115 v26 y
  have h117 := h x y v26
  have h118 := R v115
  have h119 := R v4
  let v120 := M y x
  have h121 := R v120
  T (T (T (h x y y) (C h9 (T (T (T (T (T (T (T (T (T (T (T (h y v120 x) (C h59 (C h121 h70))) (S (h v115 v120 x))) (h v115 v120 y)) (C h9 (T (T (T (T (T (T (C h121 (T (T (T (T h112 h111) h20) h19) h6)) (C h121 h51)) (h v120 v4 x)) (C h59 (T (T (T (T (T (T (T (T (T (C h119 (T (T (T (C h59 (h y x x)) (S (h v26 x x))) h27) h25)) (C h119 h55)) (h v4 v115 y)) (C h9 (T (T (T (T (T (T (T (T (T (C h81 h32) (C h68 h118)) (h v115 v115 x)) (C h59 (T (T (C h118 h83) h116) (C h9 (S h117))))) h52) h5) h77) h76) h62) h84))) (C h9 (T h72 h63))) h67) h65) h30) h27) h25))) (C h59 h55)) h82) h75))) (C h9 (T h117 (R (M v26 (M y v115)))))) (S h116)) (h v115 v26 v11)) (C h42 (T (T (T (T (T (T (T (T (T (S (h x v11 v26)) (h x v11 v0)) (C h24 (T (T (T (T (T (C h42 (T (T (T (T (T (T h114 h113) h106) h88) h87) h86) h74)) (S (h v11 z v11))) h13) h47) h56) h45))) h54) h53) h29) h80) h79) (C h9 h85)) (C h9 h73)))) (S (h v11 y v11))) (h v11 y v1)) (C (T (T (T h36 h37) h44) h43) (T (T (C h9 (T h108 h107)) (C h9 (T (T (T (T (T (T (T h114 h113) h106) h88) h87) h86) h74) (C h16 (T (T (T (T (C h42 (T h2 (C h16 (T (T (T (T (T (T (T h41 (C h18 (C (T h40 (C h24 (T (C h16 h39) h8))) h38))) (S h37)) (S h36)) h35) h34) h17) h14)))) (S h21)) h20) h19) h6))))) (S (h y z y))))))) (S (h z (M v1 v4) y))) h3

