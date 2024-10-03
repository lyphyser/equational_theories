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
theorem Equation3385_implies_Equation3756 (G: Type _) [Magma G] (h: Equation3385 G) : Equation3756 G := fun x y z =>
  let v0 := M z z
  let v1 := M y x
  have h2 := h v1 v0 v0
  have h3 := S h2
  have h4 := h z z z
  have h5 := R v0
  have h6 := C h5 (S h4)
  have h7 := h z z v0
  have h8 := T h7 h6
  have h9 := R v1
  have h10 := C h9 h8
  have h11 := S h7
  have h12 := C h5 h4
  have h13 := h v0 v0 x
  have h14 := S h13
  have h15 := h v0 x v0
  have h16 := S h15
  have h17 := T h12 h11
  have h18 := R x
  have h19 := C h5 (C h18 h17)
  have h20 := h x v0 v0
  have h21 := C h5 (T h20 h19)
  have h22 := C h18 (T h15 (C h5 (T h21 h16)))
  let v23 := M v1 v0
  have h24 := h x v0 v23
  have h25 := S h24
  have h26 := C h9 h17
  have h27 := C h5 h26
  have h28 := T h2 h27
  have h29 := C h5 h10
  have h30 := C h5 (T (T h29 h3) h10)
  have h31 := h v0 v1 v0
  have h32 := C h18 (T (T h31 h30) h3)
  have h33 := h v0 y x
  have h34 := h v0 y v23
  have h35 := S h34
  have h36 := h y v1 v0
  have h37 := h y v1 v23
  have h38 := h v1 v23 v0
  have h39 := h v0 v1 z
  have h40 := h v1 z z
  have h41 := h z v1 v0
  have h42 := R z
  have h43 := T (T (T (T (C h42 (T h41 (C h5 (S h40)))) (S h39)) h31) h30) h3
  let v44 := M z (M z v1)
  have h45 := h v1 v44 v0
  have h46 := h z z v1
  have h47 := R y
  have h48 := C h47 (T (T (T h46 h45) (C h5 (C h9 (C h43 h5)))) (S h38))
  have h49 := h v0 v0 v23
  have h50 := S h49
  have h51 := C h5 (T (T h26 h2) h27)
  have h52 := R v23
  have h53 := C h52 (T h2 h51)
  have h54 := C h52 (T (C h47 (T (T (T h53 h50) h12) h11)) h48)
  have h55 := h y v23 v23
  have h56 := T h29 h3
  have h57 := C h52 (T (T (T (T (C h47 h56) h55) h54) (S h37)) h36)
  have h58 := h y v0 v23
  have h59 := S h46
  have h60 := S h45
  have h61 := S h31
  have h62 := T (T (T (T h2 h51) h61) h39) (C h42 (T (C h5 h40) (S h41)))
  have h63 := C h47 (T (T (T h38 (C h5 (C h9 (C h62 h5)))) h60) h59)
  have h64 := C h52 (T (T (T (T (T (T h63 h58) h57) h35) h33) h32) (C h18 h28))
  have h65 := C h18 (T (T (T (T (T (T (T h55 h54) h64) h25) h20) h19) h21) h16)
  have h66 := C (T (T (T (T h65 h22) h14) h12) h11) h10
  let v67 := M y v23
  have h68 := h x v67 v23
  have h69 := S h68
  have h70 := S h55
  have h71 := C h52 (T h30 h3)
  have h72 := C h52 (T h63 (C h47 (T (T (T h7 h6) h49) h71)))
  have h73 := S h58
  have h74 := C h52 (T (T (T (T (S h36) h37) h72) h70) (C h47 h28))
  have h75 := S h33
  have h76 := C h18 (T (T h2 h51) h61)
  have h77 := C h52 (T (T (T (T (T (T (C h18 h56) h76) h75) h34) h74) h73) h48)
  have h78 := h x v0 y
  let v79 := M x y
  have h80 := h y v0 v79
  have h81 := h v0 x y
  have h82 := h v0 x x
  have h83 := h x x v1
  have h84 := S h83
  have h85 := h x y x
  have h86 := C h9 h85
  have h87 := h x y v23
  have h88 := h v23 (M x v67) v23
  have h89 := S h20
  have h90 := C h5 (C h18 h8)
  have h91 := C h5 (T h90 h89)
  have h92 := C h18 (T (T (T (T (T (T (T h15 h91) h90) h89) h24) h77) h72) h70)
  have h93 := C h18 (T (C h5 (T h15 h91)) h16)
  have h94 := h v1 v44 v23
  have h95 := C h5 (C h9 (T (T (C h43 (T (T h46 h94) (C h52 (T (T (C h9 (T (T (T (T (C h43 h52) h53) h50) h12) h11)) h2) (C (T (T (T (T h7 h6) h13) h93) h92) h26))))) (S h88)) (S h87)))
  have h96 := h v0 v0 y
  have h97 := h v0 v1 v79
  have h98 := S h97
  have h99 := R v79
  have h100 := h x v79 v0
  have h101 := h x x y
  have h102 := h x v1 v79
  have h103 := C h52 (C h18 (C (T (T (T (T (T (C h47 (T h85 (C h18 (T (T (T (T (T h102 (C h99 (T (T (C h18 (T (T (T (T (T (T (T (T (T (T h86 h84) h101) (C h47 (T h100 (C h5 (T (T (C h18 (T (T (T (T (C h99 (T (T h46 h45) h95)) h98) h31) h30) h3)) h76) h75))))) (S h96)) h12) h11) h46) h45) h95) (C h5 (T h86 h84)))) (S h82)) h81))) (S h80)) h58) h57) h35)))) (S h78)) h24) h77) h72) h70) h52))
  let v104 := M y v79
  have h105 := h x v104 v23
  have h106 := S h85
  have h107 := C h9 h106
  have h108 := S h101
  have h109 := C h5 (C h9 (T (T h87 h88) (C h62 (T (T (C h52 (T (T h66 h3) (C h9 (T (T (T (T h7 h6) h49) h71) (C h62 h52))))) (S h94)) h59))))
  have h110 := C h47 (T (C h5 (T (T h33 h32) (C h18 (T (T (T (T h2 h51) h61) h97) (C h99 (T (T h109 h60) h59)))))) (S h100))
  T (T (T (T (T (h x y v79) (h v79 (M x v104) v0)) (C (T (T (T (T (T (T (T h7 h6) h13) h93) h92) h68) (C h52 (C h18 (C (T (T (T (T (T h55 h54) h64) h25) h78) (C h47 (T (C h18 (T (T (T (T (T h34 h74) h73) h80) (C h99 (T (T (S h81) h82) (C h18 (T (T (T (T (T (T (T (T (T (T (C h5 (T h83 h107)) h109) h60) h59) h7) h6) h96) h110) h108) h83) h107))))) (S h102))) h106))) h52)))) (S h105)) (T (T (T (T (C h99 (C (T (T (T (T (T (T (T h105 h103) h69) h65) h22) h14) h12) h11) (T (T (T (T (T (T h7 h6) h96) h110) h108) h83) h107))) h98) h31) h30) h3))) (C (T (T h105 h103) h69) h52)) h66) h3

