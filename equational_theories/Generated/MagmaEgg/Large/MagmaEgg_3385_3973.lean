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
theorem Equation3385_implies_Equation3973 (G: Type _) [Magma G] (h: Equation3385 G) : Equation3973 G := fun x y z =>
  let v0 := M z x
  let v1 := M y v0
  have h2 := h v1 z x
  have h3 := S h2
  let v4 := M v1 z
  have h5 := R v4
  have h6 := R v0
  have h7 := h y v0 z
  have h8 := S h7
  let v9 := M v0 z
  have h10 := h z (M y v9) v4
  have h11 := S h10
  have h12 := h y v9 v4
  have h13 := S h12
  have h14 := h v0 z v1
  have h15 := S h14
  have h16 := h z y v0
  have h17 := R v1
  have h18 := R y
  have h19 := C h5 (C h18 (C (T (C h17 h16) h15) h5))
  have h20 := h y (M v1 (M z y)) v4
  have h21 := h v1 z y
  have h22 := R z
  have h23 := C h5 (C h22 (C (T (T (T h21 h20) h19) h13) h5))
  have h24 := h z v4 v4
  have h25 := T (T (T h24 h23) h11) h8
  have h26 := h z x x
  have h27 := S h26
  have h28 := h x x v0
  have h29 := h x z x
  have h30 := h v0 x z
  have h31 := h v0 x v0
  have h32 := S h31
  have h33 := h x v0 v0
  have h34 := S h33
  have h35 := h v0 z x
  have h36 := C h6 h35
  have h37 := h z y z
  have h38 := h y z x
  have h39 := h x v1 v0
  have h40 := S h39
  have h41 := C h6 h2
  have h42 := T h41 h40
  have h43 := h v0 v1 z
  have h44 := C h17 (T (T (C h22 (T (T h43 (C h22 h42)) (C h22 (S h38)))) (S h37)) h16)
  have h45 := h z v0 v1
  have h46 := C h6 (T (T h45 h44) h15)
  have h47 := C h6 (T (T h46 h36) h34)
  have h48 := h v0 z v0
  have h49 := C h6 (T (T (T (T h45 h44) h15) h48) h47)
  have h50 := S h45
  have h51 := C h6 h3
  have h52 := T h39 h51
  have h53 := S h16
  have h54 := C h17 (T (T h53 h37) (C h22 (T (T (C h22 h38) (C h22 h52)) (S h43))))
  have h55 := C h6 (T (T h14 h54) h50)
  have h56 := C h6 (S h35)
  have h57 := R x
  have h58 := C h57 (T (T (T (T (T (T h33 h56) h55) h49) h32) h30) (C h22 (T (C h6 h29) (S h28))))
  have h59 := S h48
  have h60 := C h6 (T (T h33 h56) h55)
  have h61 := C h6 (T (T (T (T h60 h59) h14) h54) h50)
  have h62 := C (T (T (T h12 (C h5 (C h18 (C (T h14 (C h17 h53)) h5)))) (S h20)) (S h21)) h5
  have h63 := h v1 z v4
  have h64 := S h63
  have h65 := h v1 (M z v4) z
  have h66 := S h24
  have h67 := C h5 (C h22 h62)
  have h68 := T (T (T h7 h10) h67) h66
  have h69 := C h5 (T (C h22 (T (C h68 h5) (C h25 (C h68 h22)))) (S h65))
  have h70 := h z v1 v4
  have h71 := T (T h29 h58) h27
  have h72 := C h22 (C h18 h71)
  have h73 := h y x z
  let v74 := M y x
  have h75 := h x v74 v0
  have h76 := S h75
  have h77 := h x z y
  have h78 := S h70
  have h79 := C h5 (T h65 (C h22 (T (C h68 (C h25 h22)) (C h25 h5))))
  have h80 := T (T h63 h79) h78
  have h81 := T (T (T (T h73 h72) h70) h69) h64
  have h82 := S h29
  have h83 := C h57 (T (T (T (T (T (T (C h22 (T h28 (C h6 h82))) (S h30)) h31) h61) h46) h36) h34)
  have h84 := T (T h26 h83) h82
  have h85 := C h57 (T (T (C h84 h81) (C h71 h80)) h53)
  have h86 := h v0 y x
  let v87 := M x y
  have h88 := h v0 y v87
  have h89 := S h88
  have h90 := h x y v0
  have h91 := S h90
  have h92 := T (T h70 h69) h64
  have h93 := h v0 z y
  have h94 := h x v0 z
  have h95 := h v0 v0 x
  have h96 := h v0 v0 v4
  have h97 := R v87
  have h98 := C h97 (T (T (T (T (T (T (C h22 (T (T (T (C h5 (T h90 (C h6 h52))) (S h96)) h95) (C h57 (T (C h6 (T h31 h61)) h59)))) (S h94)) h33) h56) h55) h49) (C h6 (T (T (T h60 h59) h93) (C h18 (T (C h6 (T (T (T h16 (C h6 h92)) h41) h40)) h91)))))
  have h99 := h z v4 v87
  have h100 := h y v1 z
  have h101 := T (T (T (T h63 h79) h78) (C h22 (C h18 h84))) (S h73)
  have h102 := h z y v4
  have h103 := C h71 (T (T (T (T (T (T (T (T (T h7 h10) h67) h66) h99) h98) h89) h86) h85) (C h57 (T h102 (C h101 (T (T (T (T (T (S h100) (C h18 (T (T (T (T (T (T (T (T h7 h10) h67) h66) h99) h98) h89) h86) h85))) (S h77)) h29) h58) h27)))))
  have h104 := C h84 h17
  have h105 := S h99
  have h106 := C h97 (T (T (T (T (T (T (C h6 (T (T (T (C h18 (T h90 (C h6 (T (T (T h39 h51) (C h6 h80)) h53)))) (S h93)) h48) h47)) h61) h46) h36) h34) h94) (C h22 (T (T (T (C h57 (T h48 (C h6 (T h49 h32)))) (S h95)) h96) (C h5 (T (C h6 h42) h91)))))
  have h107 := S h86
  have h108 := C h57 (T (T h16 (C h84 h92)) (C h71 h101))
  T (T (T (T (h x y x) (h x (M x v74) v4)) (C h5 (C h57 (T (C (T (T h75 (C h84 (T (T (T (T (T (T (T (T (T (C h57 (T (C h81 (T (T (T (T (T h26 h83) h82) h77) (C h18 (T (T (T (T (T (T (T (T h108 h107) h88) h106) h105) h24) h23) h11) h8))) h100)) (S h102))) h108) h107) h88) h106) h105) h24) h23) h11) h8))) (C h71 h17)) h5) (C (T (T (T (T (T h104 h103) h76) (h x v74 v1)) (C h68 (T (T (C h57 (T (T (T (T (T (T (C h81 (T (T (T (T (T (T (T (T h7 h10) h67) h66) h99) h98) h89) (h v0 y v0)) (C h6 (T (T (T (T (T h104 h103) h76) (h x v74 v4)) (C h5 (C h57 (T (T (C (T h73 h72) h5) (C (T (T (T (T (T (T h70 h69) h64) h21) h20) h19) h13) h5)) h62)))) (S (h x v4 v4)))))) (S (h v0 x v4))) h31) h61) h46) h36) h34)) h58) h27))) (C h25 h6)) h5))))) (S (h x (M v1 v0) v4))) h3

