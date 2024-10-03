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
theorem Equation3385_implies_Equation4515 (G: Type _) [Magma G] (h: Equation3385 G) : Equation4515 G := fun x y z =>
  let v0 := M x z
  have h1 := h v0 y x
  have h2 := S h1
  have h3 := h y x z
  have h4 := S h3
  have h5 := R v0
  have h6 := C h5 h4
  have h7 := h z y v0
  let v8 := M y z
  have h9 := h y y z
  have h10 := R v8
  let v11 := M v0 y
  have h12 := h y y v11
  have h13 := h y v0 y
  have h14 := h y v0 v11
  have h15 := S h14
  have h16 := R v11
  have h17 := h x z y
  have h18 := S h17
  have h19 := h y (M x (M z y)) v11
  have h20 := S h19
  have h21 := R x
  have h22 := T h1 (C h21 (T (C h5 h3) (S h7)))
  have h23 := C h22 h16
  have h24 := R y
  have h25 := C h16 (C h24 h23)
  have h26 := h y v11 v11
  have h27 := T (T (T h26 h25) h20) h18
  have h28 := C h27 h24
  have h29 := S h26
  have h30 := T (C h21 (T h7 h6)) h2
  have h31 := C h30 h16
  have h32 := C h16 (C h24 h31)
  have h33 := T (T (T h17 h19) h32) h29
  let v34 := M y v11
  have h35 := h v0 v34 y
  have h36 := C h16 (T h35 (C h24 (T (C h33 h28) (C h27 h16))))
  have h37 := h v0 y v11
  have h38 := S h37
  have h39 := S h35
  have h40 := C h33 h24
  have h41 := C h16 (T (C h24 (T (C h33 h16) (C h27 h40))) h39)
  have h42 := h v8 z v0
  have h43 := S h42
  have h44 := h z v0 v8
  have h45 := S h44
  have h46 := h v0 y z
  have h47 := C h10 h46
  have h48 := h y z x
  have h49 := h x (M y (M z x)) v11
  have h50 := h z x v8
  have h51 := h x y z
  have h52 := h v8 x y
  let v53 := M v8 x
  have h54 := h x v53 v11
  have h55 := T (T (T h54 (C h16 (C h21 (C (T h52 (C h24 (T (C h10 h51) (S h50)))) h16)))) (S h49)) (S h48)
  have h56 := C h55 h16
  have h57 := T (T h14 h41) h38
  have h58 := T (T (T h48 h49) (C h16 (C h21 (C (T (C h24 (T h50 (C h10 (S h51)))) (S h52)) h16)))) (S h54)
  have h59 := h v0 y y
  let v60 := M y y
  have h61 := h y (M v0 v60) v11
  have h62 := h v0 v60 v11
  have h63 := S h62
  have h64 := h y y x
  have h65 := S h64
  have h66 := T (T h37 h36) h15
  have h67 := R z
  have h68 := h z v0 y
  have h69 := C h21 (T (T (T (T h56 h47) h45) h68) (C h24 (T (C h67 h66) h4)))
  have h70 := C h58 h16
  have h71 := C h10 (S h46)
  have h72 := C h21 (T (T h44 h71) h70)
  have h73 := C h16 (C h5 (C (T (T h72 h69) h65) h16))
  have h74 := h v0 (M x (M z v0)) v11
  have h75 := h x z v0
  have h76 := T (T (T h75 h74) h73) h63
  have h77 := h v0 v34 v0
  have h78 := S h75
  have h79 := S h74
  have h80 := C h21 (T (T h56 h47) h45)
  have h81 := C h21 (T (T (T (T (C h24 (T h3 (C h67 h57))) (S h68)) h44) h71) h70)
  have h82 := C h16 (C h5 (C (T (T h64 h81) h80) h16))
  have h83 := T (T (T (T (T (T (T h62 h82) h79) h78) h17) h19) h32) h29
  have h84 := C h83 h24
  have h85 := C h24 (T h84 h28)
  have h86 := T (T (T (T (T (T (T h26 h25) h20) h18) h75) h74) h73) h63
  have h87 := C h86 h24
  have h88 := C h24 (T (T (T (T h14 h41) h38) h40) h87)
  have h89 := h y y v0
  have h90 := h x (M x v53) v11
  have h91 := h x v8 x
  have h92 := R (M x v8)
  have h93 := h v8 x v8
  have h94 := C h5 (T h93 (C h10 (T (T (T (T (T (C h58 h92) (C h55 (T (T (T (T (T (T (T h91 h90) (C h16 (T (T (T (T (T (T h69 h65) h89) (C h5 (T (T (T (T (T (T (T h88 h85) h26) h25) h20) h18) h75) (C h5 (T (T (T (T (T h72 h69) h65) h89) (C h76 (T (T (T (T (T h88 h85) h26) h25) h20) h18))) (C h83 h5)))))) (S h77)) h35) (C h24 (C h76 h28))))) (S h61)) (S h59)) h37) h36) h15))) (C h58 h57)) h56) h47) h45)))
  have h95 := h v8 x z
  have h96 := C h5 (S h95)
  have h97 := h z v8 v0
  have h98 := h z v8 z
  have h99 := T (T (T h97 h96) h94) h43
  have h100 := h z y z
  have h101 := h z z y
  have h102 := S h97
  have h103 := C h5 h95
  have h104 := S h89
  have h105 := C h24 (T (T (T (T h84 h28) h37) h36) h15)
  have h106 := C h24 (T h40 h87)
  have h107 := T (T (T h62 h82) h79) h78
  have h108 := C h5 (T (C h10 (T (T (T (T (T h44 h71) h70) (C h55 h66)) (C h58 (T (T (T (T (T (T (T h14 h41) h38) h59) h61) (C h16 (T (T (T (T (T (T (C h24 (C h107 h40)) h39) h77) (C h5 (T (T (T (T (T (T (T (C h5 (T (T (T (T (T (C h86 h5) (C h107 (T (T (T (T (T h17 h19) h32) h29) h106) h105))) h104) h64) h81) h80)) h78) h17) h19) h32) h29) h106) h105))) h104) h64) h81))) (S h90)) (S h91)))) (C h55 h92))) (S h93))
  T (C h21 (T (T (T (T (T (T (h y z v8) (C h10 (T (T (T (T (T (T (T (T (C h24 h99) (C h24 (T (T (T (T (T h42 h108) h103) h102) h98) (C h67 (T (C h67 (T (T (T h42 h108) h103) h102)) (S h100)))))) (S h101)) (h z z z)) (C h67 (T (C h67 (T h101 (C h24 (T (T (T (T (T (C h67 (T h100 (C h67 h99))) (S h98)) h97) h96) h94) h43)))) (S (h y v8 z))))) (S h9)) h12) (C h22 (T (T (T (S h13) h14) h41) h38))) h31))) (C h10 (T (T h23 (C h30 (T (T (T h37 h36) h15) h13))) (S h12)))) (C h10 h9)) (S (h z y v8))) h7) h6)) h2

