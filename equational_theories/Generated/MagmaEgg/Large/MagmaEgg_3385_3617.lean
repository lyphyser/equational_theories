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
theorem Equation3385_implies_Equation3617 (G: Type _) [Magma G] (h: Equation3385 G) : Equation3617 G := fun x y z =>
  let v0 := M z x
  let v1 := M v0 y
  have h2 := R v0
  have h3 := h v0 y z
  have h4 := S h3
  let v5 := M z v1
  have h6 := h z (M v0 (M y z)) v5
  have h7 := S h6
  have h8 := R v5
  have h9 := h y z v1
  have h10 := S h9
  have h11 := h z v0 y
  have h12 := R v1
  have h13 := C h12 h11
  have h14 := h v1 z v0
  have h15 := R z
  have h16 := C h8 (C h15 (C (T h14 (C h2 (T h13 h10))) h8))
  have h17 := h z (M v1 z) v5
  have h18 := T (T (T h17 h16) h7) h4
  let v19 := M x y
  have h20 := h z x v19
  have h21 := h x v19 v1
  have h22 := S h21
  have h23 := h v0 y x
  have h24 := S h23
  have h25 := h y x v1
  have h26 := S h25
  have h27 := h x v0 y
  have h28 := C h12 h27
  have h29 := C h2 (T h28 h26)
  have h30 := h v1 x v0
  have h31 := R x
  have h32 := C h31 (T h30 h29)
  have h33 := S h30
  have h34 := S h27
  have h35 := C h12 h34
  have h36 := h x v0 v5
  have h37 := S h36
  have h38 := h z x y
  have h39 := S h38
  have h40 := h y (M z v19) v5
  have h41 := h x y v0
  have h42 := h y z x
  have h43 := C h18 h15
  have h44 := C h15 (T (T (T h43 h14) (C h2 (T (T h13 h10) h42))) (S h41))
  have h45 := S h17
  have h46 := S h14
  have h47 := C h12 (S h11)
  have h48 := C h8 (C h15 (C (T (C h2 (T h9 h47)) h46) h8))
  have h49 := T (T (T h3 h6) h48) h45
  have h50 := C h49 h15
  have h51 := C h15 h50
  have h52 := R y
  have h53 := h y v1 v5
  have h54 := C h8 (C h31 (C (T (T (T h53 (C h8 (C h52 (T (C h49 h8) (C (T h51 h44) h8))))) (S h40)) h39) h8))
  have h55 := h x (M y v1) v5
  have h56 := C h12 (T (T (T h55 h54) h37) h27)
  have h57 := h x y v1
  have h58 := T (T (C h31 (T (C h2 (T (T h57 h56) h35)) h33)) h32) h24
  have h59 := R v19
  have h60 := C h59 h58
  have h61 := h x v0 v19
  have h62 := C h31 (T h61 h60)
  have h63 := h x z x
  have h64 := C h12 (T h63 h62)
  have h65 := h v1 x z
  have h66 := C h2 (T h25 h35)
  let v67 := M y x
  have h68 := h v0 v67 v19
  have h69 := h x y x
  have h70 := S h69
  have h71 := h x v67 v5
  have h72 := S h71
  have h73 := T (T h57 h56) h26
  have h74 := C h8 (C h31 (C h73 h8))
  have h75 := h x v19 v5
  have h76 := C h31 (T (T h75 h74) h72)
  have h77 := S h75
  have h78 := S h57
  have h79 := S h55
  have h80 := S h53
  have h81 := C h15 h43
  have h82 := S h42
  have h83 := C h15 (T (T (T h41 (C h2 (T (T h82 h9) h47))) h46) h50)
  have h84 := C h8 (C h52 (T (C (T h83 h81) h8) (C h18 h8)))
  have h85 := C h8 (C h31 (C (T (T (T h38 h40) h84) h80) h8))
  have h86 := C h12 (T (T (T h34 h36) h85) h79)
  have h87 := T (T h25 h86) h78
  have h88 := C h8 (C h31 (C h87 h8))
  have h89 := C h31 (T (T h71 h88) h77)
  have h90 := h y x y
  have h91 := h y y v19
  have h92 := h y y v1
  have h93 := h y v0 y
  have h94 := h v1 y v0
  have h95 := h v1 y x
  have h96 := S h61
  have h97 := C h31 (T h66 h33)
  have h98 := T (T h23 h97) (C h31 (T h30 (C h2 (T (T h28 h86) h78))))
  have h99 := C h59 h98
  have h100 := h v1 v19 v1
  have h101 := h x v1 v19
  have h102 := h x v1 x
  have h103 := h x z v19
  have h104 := S h63
  have h105 := C h31 (T h99 h96)
  have h106 := h x v67 v1
  T (T (T h41 (C h2 (T (T h82 (h y z v19)) (C h73 h39)))) (C h2 (T (T (T (T (C h87 (T (T (T (T (T h38 h40) h84) h80) (h y v1 v1)) (C h12 (T (T (T (T (T (T (S (h v1 v0 y)) (C h49 h2)) (C h18 (T (T (T (T (T h20 (C h59 (T (T (T (T (T (T (T (T (C h15 (T h21 (C h12 (T h105 h104)))) (S h65)) h30) h29) h68) (C h59 (T (T (T (T (C h2 (T (T (C h87 (T h69 h89)) (C h59 (T (T (T (T (T h76 h70) h57) h56) h26) h90))) (S h91))) (C h2 (T h92 (C h12 (S h93))))) (S h94)) h95) (C h31 (T (C h12 (T (T h25 h86) (C h12 (T (T (T (T h55 h54) h37) h61) h60)))) (S h100)))))) (S h101)) h102) (C h31 (T (T (T (T (T (T (T h32 h24) h3) h6) h48) h45) h51) h44))))) (S h103)) h63) h62) (C h31 (T h99 (C h73 h58)))))) (S h106)) h71) h88) h77)))) (S (h v1 x v19))) h65) (C h15 (T (T (T (T (T (T h64 h22) h75) h74) h72) h106) (C h49 (T (T (T (T (T (C h31 (T (C h87 h98) h60)) h105) h104) h103) (C h59 (T (T (T (T (T (T (T (T (C h31 (T (T (T (T (T (T (T h83 h81) h17) h16) h7) h4) h23) h97)) (S h102)) h101) (C h59 (T (T (T (T (C h31 (T h100 (C h12 (T (T (C h12 (T (T (T (T h99 h96) h36) h85) h79)) h56) h26)))) (S h95)) h94) (C h2 (T (C h12 h93) (S h92)))) (C h2 (T (T h91 (C h59 (T (T (T (T (T (S h90) h25) h86) h78) h69) h89))) (C h73 (T h76 h70))))))) (S h68)) h66) h33) h65) (C h15 (T h64 h22))))) (S h20)))))) (C h15 (C h18 h2))))) (S (h z v1 v0))

