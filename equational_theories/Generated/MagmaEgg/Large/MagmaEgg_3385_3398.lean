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
theorem Equation3385_implies_Equation3398 (G: Type _) [Magma G] (h: Equation3385 G) : Equation3398 G := fun x y z =>
  let v0 := M x z
  let v1 := M y v0
  have h2 := h z v1 v1
  have h3 := S h2
  let v4 := M z v1
  have h5 := R v4
  have h6 := h v1 v1 v0
  have h7 := h v1 v0 v1
  have h8 := R v1
  have h9 := h x z y
  have h10 := S h9
  let v11 := M z y
  have h12 := h y (M x v11) v4
  have h13 := S h12
  have h14 := h z y v0
  have h15 := S h14
  have h16 := h y x z
  have h17 := R v0
  have h18 := R x
  have h19 := C h18 (T (C h17 h16) h15)
  have h20 := h v0 y x
  have h21 := R y
  have h22 := C h5 (C h21 (C (T h20 h19) h5))
  have h23 := h y (M v0 y) v4
  have h24 := h v0 y v1
  have h25 := h y y v0
  have h26 := C h21 (T (C h8 h25) (S h24))
  have h27 := h v1 y y
  have h28 := T (T (T (T (T h27 h26) h23) h22) h13) h10
  have h29 := C h28 h8
  have h30 := h y v0 y
  have h31 := S h30
  have h32 := C h21 (T h27 h26)
  let v33 := M v1 y
  have h34 := h y v33 x
  have h35 := S h34
  have h36 := S h27
  have h37 := C h21 (T h24 (C h8 (S h25)))
  have h38 := S h23
  have h39 := S h20
  have h40 := S h16
  have h41 := C h18 (T h14 (C h17 h40))
  have h42 := C h5 (C h21 (C (T h41 h39) h5))
  have h43 := T (T (T (T (T h9 h12) h42) h38) h37) h36
  have h44 := C h43 h18
  have h45 := h v0 x v1
  have h46 := h x y v0
  have h47 := T (C h8 h46) (S h45)
  have h48 := h v1 x y
  have h49 := h v1 x v4
  have h50 := h x z v1
  have h51 := C h43 (T (T (T (T (C h18 (T (C h5 h50) (S h49))) (C h18 (T (T h48 (C h21 h47)) (C h21 h44)))) h35) h32) h31)
  have h52 := h x v4 v0
  have h53 := T (T h52 h51) h29
  have h54 := h v1 y v0
  have h55 := h v0 v1 v1
  have h56 := R z
  have h57 := C h56 (T (C h28 (T h50 (C h8 (T (T (T (T (T h52 h51) h29) h55) (C h8 (T (T (T (T (T (T (T (T (S h54) h27) h26) h23) h22) h13) h10) h50) (C h8 h53)))) (S h7))))) (S h6))
  have h58 := h x z v0
  have h59 := h z v0 v0
  have h60 := h v0 x z
  have h61 := h v0 v0 x
  have h62 := h v0 v0 v0
  have h63 := C h56 (T h62 (C h43 (T (C h17 (T h61 (C h18 (T (C h17 h60) (S h59))))) (S h58))))
  have h64 := h v0 x v4
  have h65 := S h52
  have h66 := S h50
  have h67 := T h45 (C h8 (S h46))
  have h68 := C h28 h18
  have h69 := C h28 (T (T (T (T h30 (C h21 (T h37 h36))) h34) (C h18 (T (T (C h21 h68) (C h21 h67)) (S h48)))) (C h18 (T h49 (C h5 h66))))
  have h70 := C h43 h8
  have h71 := T (T h70 h69) h65
  have h72 := h v0 y v0
  have h73 := h x v11 v4
  have h74 := S h73
  have h75 := C h28 h5
  have h76 := h z v1 y
  have h77 := h z v33 v4
  have h78 := S h77
  have h79 := C h43 h5
  have h80 := C h5 (T (C h56 h15) (C h56 (T h14 h79)))
  have h81 := h z v0 v4
  have h82 := C h43 (T (C h21 (T (T h81 h80) h78)) (S h76))
  have h83 := h y z v0
  have h84 := C h5 (C h18 (T (C (T (T h83 h82) h75) h5) (C h15 h5)))
  have h85 := h x (M y z) v4
  have h86 := S h83
  have h87 := T h76 (C h21 (T (T h77 (C h5 (T (C h56 (T h75 h15)) (C h56 h14)))) (S h81)))
  have h88 := C h28 h87
  have h89 := h z y y
  let v90 := M x y
  have h91 := h y y v90
  have h92 := h y x y
  have h93 := R v90
  have h94 := C h93 (T h40 h92)
  have h95 := S h92
  have h96 := C h93 (T h95 h16)
  have h97 := h v1 v1 v90
  have h98 := S h60
  have h99 := C h56 (T (C h28 (T h58 (C h17 (T (C h18 (T h59 (C h17 h98))) (S h61))))) (S h62))
  have h100 := C h56 (T h6 (C h43 (T (C h8 (T (T (T (T (T h7 (C h8 (T (T (T (T (T (T (T (T (C h8 h71) h66) h9) h12) h42) h38) h37) h36) h54))) (S h55)) h70) h69) h65)) h66)))
  have h101 := C h21 (T (T (T (T (T (C h56 (T h91 h96)) (C h56 (T (T h94 (C h93 (T (T (T (T h95 h16) h2) (C h8 (T (T h100 h99) h98))) (C h8 h67)))) (S h97)))) h100) h99) h98) h44)
  have h102 := S h85
  have h103 := C h5 (C h18 (T (C h14 h5) (C (T (T h79 h88) h86) h5)))
  have h104 := h z v0 y
  have h105 := h x y z
  let v106 := M y v1
  T (T (T (T (h x y v1) (h v1 (M x v106) v4)) (C h5 (C h8 (C (T (T (T (T (T (h x v106 v4) (C h5 (T (T (T (T (T (T (T (T (C h18 (T (T (T (T (T (C (T (T (T (T (h y v1 z) (C h56 (T (T (C h21 (T (T (h v1 z v0) (C h17 (T (T (T (T (T (C h8 (T h104 (C h21 (T (C h56 (T (T (T (T h20 h19) h73) h103) h102)) (S h105))))) (C h8 (T (T (T (T (T (T (C h21 (T h105 (C h56 (T (T (T (T h85 h84) h74) h41) h39)))) (S h104)) h81) h80) h78) (h z v33 v0)) (C h17 (T (T (T h99 h98) h64) (C h5 (T (T (T (T (T (T (T (T (T (T (C h17 h53) (S h72)) h20) h19) h73) h103) h102) (C h18 (T (T (T (T (T h83 h82) h75) h15) h89) h101))) h35) h32) h31))))))) (S (h v0 v4 v1))) h79) h88) h86))) (C h17 (T (T (T h83 h82) h75) h15)))) (S (h v0 z y))) (C h43 h56)))) (C h56 (C h28 h56))) (C h56 (T (h v0 z x) (C h18 (T (C h17 (h z x z)) (S (h z z v0))))))) (S (h x z z))) h87) h82) h75) h15) h89) h101)) (C h18 (T (T (T (T (T (C h21 (T (T (T (T (T h68 h60) h63) h57) (C h56 (T (T h97 (C h93 (T (T (T (T (C h8 h47) (C h8 (T (T h60 h63) h57))) h3) h40) h92))) h96))) (C h56 (T h94 (S h91))))) (S h89)) h14) h79) h88) h86))) h85) h84) h74) h41) h39) h72) (C h17 h71)))) (S h64)) h60) h63) h57) h5)))) (S (h v1 (M z (M v1 v1)) v4))) h3

