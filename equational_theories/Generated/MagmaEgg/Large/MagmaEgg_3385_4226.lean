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
theorem Equation3385_implies_Equation4226 (G: Type _) [Magma G] (h: Equation3385 G) : Equation4226 G := fun x y z =>
  let v0 := M z z
  let v1 := M v0 x
  have h2 := h v1 y v0
  have h3 := S h2
  have h4 := h z z x
  have h5 := S h4
  let v6 := M v1 y
  let v7 := M z x
  have h8 := h x (M z v7) v6
  have h9 := S h8
  have h10 := R v6
  have h11 := h z v7 v6
  have h12 := S h11
  have h13 := h z x v0
  have h14 := h x z z
  have h15 := R v0
  have h16 := R z
  have h17 := C h10 (C h16 (C (T (C h15 h14) (S h13)) h10))
  have h18 := h z (M v0 (M x z)) v6
  have h19 := h v0 x z
  have h20 := R x
  have h21 := C h10 (C h20 (C (T (T (T h19 h18) h17) h12) h10))
  have h22 := h x v1 v6
  have h23 := R y
  have h24 := R v1
  have h25 := S h22
  have h26 := S h19
  have h27 := S h18
  have h28 := C h10 (C h16 (C (T h13 (C h15 (S h14))) h10))
  have h29 := C (T (T (T h11 h28) h27) h26) h10
  have h30 := C h10 (C h20 h29)
  have h31 := h z z v0
  have h32 := S h31
  have h33 := h z z z
  have h34 := C h15 h33
  have h35 := h v0 v0 v1
  have h36 := S h35
  have h37 := h z x v1
  have h38 := S h33
  have h39 := T h34 h32
  have h40 := h v0 z z
  have h41 := T h40 (C h16 h39)
  have h42 := h z v0 z
  have h43 := h z v0 x
  have h44 := S h43
  have h45 := h x z v1
  have h46 := C h16 (T (T h45 (C h24 (T (T h44 h42) (C h16 (T (T (T (T (T (C h16 h41) h38) h4) h8) h30) h25))))) (S h37))
  have h47 := h x z x
  have h48 := h z x z
  have h49 := C h15 h38
  have h50 := T h31 h49
  have h51 := T (C h16 h50) (S h40)
  have h52 := C h16 (T (T h37 (C h24 (T (T (C h16 (T (T (T (T (T h22 h21) h9) h5) h33) (C h16 h51))) (S h42)) h43))) (S h45))
  have h53 := C h16 (T (T (C h20 h41) (C h20 (T h43 (C h20 (T (C h16 (T (T (T (T h19 h18) h17) h12) h52)) (S h48)))))) (S h47))
  have h54 := h x v0 z
  have h55 := h x v0 v1
  have h56 := S h55
  have h57 := h v0 v0 x
  have h58 := C h24 (T (T h31 h49) h57)
  have h59 := h x v0 v0
  have h60 := S h59
  have h61 := C h15 (C h20 h50)
  have h62 := T (T (T (T (T (T (T (T h61 h60) h54) h53) h46) h11) h28) h27) h26
  let v63 := M v0 (M x v0)
  have h64 := h v0 v63 v0
  have h65 := h v0 x v0
  have h66 := C h62 (T (T h65 h64) (C h15 (C h15 (T (T (T (T (T (T (T (T (T (C h62 h15) h58) h56) h54) h53) h46) h11) h28) h27) h26))))
  have h67 := C h15 (C h20 h39)
  have h68 := S h54
  have h69 := C h16 (T (T h47 (C h20 (T (C h20 (T h48 (C h16 (T (T (T (T h46 h11) h28) h27) h26)))) h44))) (C h20 h51))
  have h70 := T (T (T (T (T (T (T (T h19 h18) h17) h12) h52) h69) h68) h59) h67
  have h71 := C h70 h24
  have h72 := h y v1 v1
  have h73 := T (T (T (T (T (T (T (T h58 h56) h54) h53) h46) h11) h28) h27) h26
  have h74 := C h23 h73
  have h75 := C h15 (T (T (T h74 h72) (C h24 (C h23 (T (T (T (T (T (T (T (T h71 h66) h36) h34) h32) h4) h8) h30) h25)))) (C h24 (C h23 (T (T (T h22 h21) h9) h5))))
  have h76 := h y v1 v0
  let v77 := M x y
  have h78 := h v0 x y
  have h79 := R v77
  have h80 := h y v0 v77
  have h81 := T h80 (C h79 (S h78))
  have h82 := h y v0 v6
  have h83 := C h15 (T (T (T h74 h76) h75) h3)
  have h84 := C h24 (T (T (S h57) h34) h32)
  have h85 := T (T (T (T (T (T (T (T h19 h18) h17) h12) h52) h69) h68) h55) h84
  have h86 := C h23 h85
  have h87 := C h62 h24
  have h88 := S h65
  have h89 := C h70 (T (T (C h15 (C h15 (T (T (T (T (T (T (T (T (T h19 h18) h17) h12) h52) h69) h68) h55) h84) (C h70 h15)))) (S h64)) h88)
  have h90 := C h15 (T (T (T (C h24 (C h23 (T (T (T h4 h8) h30) h25))) (C h24 (C h23 (T (T (T (T (T (T (T (T h22 h21) h9) h5) h31) h49) h35) h89) h87)))) (S h72)) h86)
  have h91 := h y v6 v1
  have h92 := C h20 (T (T (T (T h71 h66) h36) h34) h32)
  have h93 := h v0 v0 v6
  have h94 := C h20 (T (T (T (T (C h10 (T (T h2 h90) (C h15 (T (T h74 h76) h83)))) (S h93)) h35) h89) h87)
  have h95 := h x v6 v6
  have h96 := h x v1 y
  have h97 := h x v1 v0
  have h98 := h v0 v63 v1
  have h99 := S h76
  have h100 := C h15 (T (T (T h2 h90) h99) h86)
  have h101 := C h20 (T (T (T (T h71 h66) h36) h93) (C h10 (T (T (C h15 (T (T h100 h99) h86)) h75) h3)))
  have h102 := C h20 (T (T (T (T h31 h49) h35) h89) h87)
  have h103 := C h10 (T (T (T (T (T (T (T (T h19 h18) h17) h12) h52) h69) h68) h102) h101)
  have h104 := S h95
  let v105 := M y y
  T (T (T (T (T (T (h x y y) (h y (M x v105) v6)) (C h10 (C h23 (T (T (C (T (T (T (T (T (T (T (T (T (T (T (T (h x v105 v6) (C h10 (C h20 (C (T (h y y v0) (C h15 (T (T (C h23 h81) (C h23 (T (T (T (T (T (T (T (C h79 h78) (S h80)) h82) (C h10 (T (T (T (T (T (T (T (T (T (T (T (T (T (C h23 (T (T h100 h75) h3)) h91) (C h24 (T (T (T (C h23 (T h103 h104)) (S h96)) h97) (C h15 (T (T (T (T (T (T (T (T (C h20 h73) h22) h21) h9) h5) h31) h49) h35) h89))))) (S h98)) h88) h19) h18) h17) h12) h52) h69) h68) h102) h101))) h104) (h x v6 v1)) (C h24 (T (C h20 (T (T h103 (C h10 (T (T (T (T (T (T (T (T (T (T (T (T (T h94 h92) h54) h53) h46) h11) h28) h27) h26) h65) h98) (C h24 (T (T (T (C h15 (T (T (T (T (T (T (T (T h66 h36) h34) h32) h4) h8) h30) h25) (C h20 h85))) (S h97)) h96) (C h23 (T h95 (C h10 (T (T (T (T (T (T (T (T h94 h92) h54) h53) h46) h11) h28) h27) h26))))))) (S h91)) (C h23 (T (T h2 h90) h83))))) (S h82))) (C h20 h81)))) (S (h x v77 v1))))) (S (h x x y))))) h10)))) (S (h x (M v0 (M x x)) v6))) (S (h v0 x x))) h19) h18) h17) h12) h52) h69) h68) h59) h67) h10) (C (T (T (T (T h61 h60) h54) h53) h46) h10)) h29)))) (S (h y v1 v6))) h76) h75) h3

