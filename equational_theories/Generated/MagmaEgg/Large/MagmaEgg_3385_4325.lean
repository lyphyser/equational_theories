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
theorem Equation3385_implies_Equation4325 (G: Type _) [Magma G] (h: Equation3385 G) : Equation4325 G := fun x y z =>
  let v0 := M z z
  have h1 := h y v0 v0
  have h2 := S h1
  have h3 := h z z z
  have h4 := S h3
  have h5 := R v0
  have h6 := C h5 h4
  have h7 := h z z v0
  have h8 := T h7 h6
  have h9 := R y
  have h10 := C h9 h8
  have h11 := C h5 h10
  have h12 := C h5 (T (T h11 h2) h10)
  have h13 := h v0 y v0
  let v14 := M y v0
  have h15 := h v0 y v14
  have h16 := S h15
  have h17 := h y v14 v0
  have h18 := S h17
  have h19 := h v0 y z
  have h20 := h y z z
  have h21 := h z y v0
  have h22 := R z
  have h23 := T (T (T (T (C h22 (T h21 (C h5 (S h20)))) (S h19)) h13) h12) h2
  have h24 := C h23 h5
  have h25 := C h9 h24
  have h26 := C h5 h25
  let v27 := M z (M z y)
  have h28 := h y v27 v0
  have h29 := h z z y
  have h30 := C h5 (T (T (T (T h4 h29) h28) h26) h18)
  have h31 := S h29
  have h32 := S h28
  have h33 := S h13
  have h34 := S h7
  have h35 := T (C h5 h3) h34
  have h36 := C h9 h35
  have h37 := C h5 h36
  have h38 := C h5 (T (T h36 h1) h37)
  have h39 := T (T (T (T h1 h38) h33) h19) (C h22 (T (C h5 h20) (S h21)))
  have h40 := C h39 h5
  have h41 := C h9 h40
  have h42 := C h5 h41
  have h43 := C h5 (T (T (T (T h17 h42) h32) h31) h3)
  have h44 := C h39 (T h43 h34)
  have h45 := T h1 h37
  have h46 := h z z x
  have h47 := S h46
  have h48 := h z x x
  have h49 := h x x z
  have h50 := h x z z
  have h51 := h x v0 v14
  have h52 := S h51
  have h53 := R x
  have h54 := h x v14 v0
  have h55 := S h54
  have h56 := C h5 (C h53 (T (T (T (T (T h1 h38) h33) h15) h44) h24))
  have h57 := R v14
  have h58 := C h57 (T (T h56 h55) (C h53 h45))
  have h59 := h v0 x v14
  have h60 := h z v0 x
  have h61 := C h22 h35
  have h62 := h v0 z z
  have h63 := h z v0 z
  have h64 := C h22 (T (C h53 (T (T (T h62 h61) h63) (C h22 (T (C h22 (T (T (T h62 h61) h60) (C h53 (T (C h22 (T (T h59 h58) h52)) (S h50))))) (S h49))))) (S h48))
  have h65 := h x v0 z
  have h66 := C h53 (T h65 h64)
  have h67 := C h5 (T (T (T (T (T (T (T (T h66 h47) h29) h28) h26) h18) (C h9 h45)) (C h9 (T (T (T (T h11 h38) h33) h15) h44))) h25)
  have h68 := h x x v0
  let v69 := M y x
  have h70 := h x x v69
  have h71 := S h70
  have h72 := h x y x
  have h73 := h x y v0
  have h74 := C h23 (T h7 h30)
  have h75 := C h5 (C h53 (T (T (T (T (T h40 h74) h16) h13) h12) h2))
  have h76 := R v69
  have h77 := C h76 (T (T (T h54 h75) (S h73)) h72)
  have h78 := C h57 (T (T (T (T (T (T (T (T h77 h71) h68) h67) h42) h32) h31) h7) h30)
  have h79 := S h72
  have h80 := C h76 (T (T (T h79 h73) h56) h55)
  have h81 := S h68
  have h82 := S h62
  have h83 := C h22 h8
  have h84 := T h11 h2
  have h85 := C h53 (T (C h22 (T h48 (C h53 (T (T (T (C h22 (T h49 (C h22 (T (T (T (C h53 (T h50 (C h22 (T (T h51 (C h57 (T (T (C h53 h84) h54) h75))) (S h59))))) (S h60)) h83) h82)))) (S h63)) h83) h82)))) (S h65))
  let v86 := M x v69
  have h87 := h x x v86
  have h88 := h x v86 v14
  have h89 := h v69 x v14
  have h90 := h v69 x v69
  have h91 := S h90
  have h92 := R v86
  have h93 := C h92 (T (T (T (T (T (T h91 h89) h78) h16) h13) h12) h2)
  have h94 := h v69 v69 v86
  have h95 := h v69 y x
  have h96 := h v69 y v0
  have h97 := h v0 v69 v14
  have h98 := h v0 y x
  have h99 := S h89
  have h100 := C h5 (T (T (T (T (T (T (T (T h41 (C h9 (T (T (T (T h74 h16) h13) h12) h37))) (C h9 h84)) h17) h42) h32) h31) h46) h85)
  have h101 := C h57 (T (T (T (T (T (T (T (T h43 h34) h29) h28) h26) h100) h81) h70) h80)
  have h102 := C h92 (T (T (T (T (T (T h1 h38) h33) h15) h101) h99) h90)
  have h103 := C h57 (T (T (T (C h5 (T (T (T (T (T (T (T (T (T h102 (C h92 (T (T (T (T (T (T h91 h89) h78) h16) h98) (C h53 (T (T (T h97 (C h57 (T (T (S h96) h95) (C h53 (T h94 h93))))) (S h88)) h79))) (C h53 h72)))) (S h87)) h68) h67) h42) h32) h31) h46) h85)) h81) h70) h80)
  have h104 := C h5 (T (T (T (T (T (T (T (T (T h66 h47) h29) h28) h26) h100) h81) h87) (C h92 (T (T (T (T (T (T (C h53 h79) (C h53 (T (T (T h72 h88) (C h57 (T (T (C h53 (T h102 (S h94))) (S h95)) h96))) (S h97)))) (S h98)) h15) h101) h99) h90))) h93)
  have h105 := h v0 v86 v14
  have h106 := T (T (T (T (T (T h1 h38) h33) h15) h101) (C h57 (T (T (T h77 h71) h68) h104))) (S h105)
  let v107 := M v69 v14
  T (T (T (T (T (T (T (T (h x v69 v14) (h v14 (M x v107) v14)) (C h57 (T (T (T (T (T (C h57 (T (T (T (C (T (T (T (h x v107 v14) (C h57 (C h53 (C (T (T (T (T (T (T (C h76 h106) (S (h v0 x v69))) h59) h58) h52) h65) h64) h57)))) (S (h x (M z (M z x)) v14))) h47) h106) (C h5 (T (T (T (T (T (T (T h105 h103) h78) h16) h13) h12) h2) h10))) h2) (C h9 (T (T (T (T h7 h6) (h v0 v0 v14)) (C h57 (T h12 h2))) (C h39 h57))))) (S (h y v27 v14))) h28) h26) h100) h104))) h103) h78) h16) h13) h12) h2

