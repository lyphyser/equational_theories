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
theorem Equation3385_implies_Equation4182 (G: Type _) [Magma G] (h: Equation3385 G) : Equation4182 G := fun x y z =>
  let v0 := M y z
  let v1 := M v0 z
  have h2 := h v1 x v1
  have h3 := S h2
  let v4 := M v1 x
  let v5 := M x v1
  have h6 := h v1 v5 v4
  have h7 := S h6
  have h8 := h v1 x v4
  have h9 := S h8
  let v10 := M x v4
  have h11 := h v1 v10 x
  have h12 := R x
  have h13 := h x v4 v4
  have h14 := S h13
  have h15 := R v4
  have h16 := h v1 x v0
  have h17 := h x v0 z
  have h18 := S h17
  have h19 := R v1
  have h20 := h z x v1
  have h21 := R v0
  have h22 := C h15 (C h12 (C (T (C h21 (T h20 (C h19 h18))) (S h16)) h15))
  have h23 := h x (M v0 (M z x)) v4
  have h24 := h v0 z x
  have h25 := T (T (T h24 h23) h22) h14
  have h26 := C h25 h12
  have h27 := S h24
  have h28 := S h23
  have h29 := C h15 (C h12 (C (T h16 (C h21 (T (C h19 h17) (S h20)))) h15))
  have h30 := T (T (T h13 h29) h28) h27
  have h31 := C h30 h26
  have h32 := C h25 h15
  have h33 := C h15 (T (C h12 (T h32 h31)) (S h11))
  have h34 := h x v1 v4
  have h35 := h x v1 x
  have h36 := S h34
  have h37 := C h30 h12
  have h38 := C h25 h37
  have h39 := C h15 (T h11 (C h12 (T h38 (C h30 h15))))
  have h40 := T (T h8 h39) h36
  have h41 := h x x v4
  have h42 := C h19 (T h41 (C h40 (T (T (T (S h35) h34) h33) h9)))
  have h43 := h v1 (M x x) v4
  have h44 := S h43
  have h45 := h x x v0
  have h46 := S h45
  have h47 := R z
  have h48 := T (C h47 h40) h18
  have h49 := h z v1 x
  have h50 := C h21 (T h49 (C h12 h48))
  have h51 := C h15 (C h19 (C (T h50 h46) h15))
  have h52 := h v1 (M v0 (M z v1)) v4
  have h53 := h v0 z v1
  have h54 := T (T h34 h33) h9
  have h55 := C h54 (T (T (T (T h53 h52) h51) h44) h42)
  have h56 := C h19 (T h55 h7)
  have h57 := S h53
  have h58 := S h52
  have h59 := T h17 (C h47 h54)
  have h60 := C h21 (T (C h12 h59) (S h49))
  have h61 := C h15 (C h19 (C (T h45 h60) h15))
  have h62 := S h41
  have h63 := C h54 (T (T (T h8 h39) h36) h35)
  have h64 := C h40 (T (T (T (T (C h19 (T h63 h62)) h43) h61) h58) h57)
  have h65 := h v1 v5 v1
  have h66 := S h65
  have h67 := C h19 (T (T h37 h2) (C h19 (T h6 h64)))
  have h68 := C h19 (T (T (T (T h31 h67) h66) h6) h64)
  let v69 := M x y
  have h70 := h x y z
  have h71 := C h40 (T (C h47 h48) (S h70))
  have h72 := h z z v4
  have h73 := C h47 h59
  have h74 := R v69
  have h75 := h x y v4
  have h76 := S h75
  have h77 := h y v1 x
  have h78 := R y
  have h79 := C h15 (T (C h78 h30) h77)
  have h80 := h y x v4
  have h81 := h y x y
  have h82 := S h81
  have h83 := h y v69 v1
  have h84 := h x x v69
  have h85 := S h84
  have h86 := h x v69 v4
  have h87 := h v1 x y
  have h88 := S h87
  have h89 := C h74 h88
  have h90 := h y v1 v69
  have h91 := T h90 h89
  have h92 := S h90
  have h93 := C h74 h87
  have h94 := h x (M y x) v4
  have h95 := h x y x
  have h96 := C h74 (T h95 (C h12 (T (T h94 (C h15 (T (C h12 (T (T (C (T (T h80 h79) h76) h15) h93) h92)) (C h12 h91)))) (S h86))))
  have h97 := h v1 v69 v69
  have h98 := C h78 (T h97 (C h74 (T (C h19 (T (T (T h96 h85) h45) h60)) h57)))
  have h99 := C h78 (T (T (T (T (C h40 h19) h55) h7) (C h19 (T (T (T (T h34 h33) h9) h87) h98))) (S h83))
  have h100 := C h54 h19
  have h101 := h y v4 v1
  have h102 := S h97
  have h103 := S h80
  have h104 := C h15 (T (S h77) (C h78 h25))
  have h105 := C h74 (T h53 (C h19 (T (T (T h50 h46) h84) (C h74 (T (C h12 (T (T h86 (C h15 (T (C h12 (T h93 h92)) (C h12 (T (T h90 h89) (C (T (T h75 h104) h103) h15)))))) (S h94))) (S h95))))))
  have h106 := C h12 h54
  have h107 := h x x v1
  T (T (T (T (T (T (T h75 h104) h103) (h y x v1)) (C h19 (T (T (T (T (T (T (T (T (T (T (C h78 h54) h101) (C (T (T (T h53 h52) h51) h44) (T (T (T (T h99 h82) h80) h79) h76))) (C (T (T (T (T (T (T (T h43 h61) h58) h57) h24) h23) h22) h14) h74)) (C h30 h74)) h97) (C h74 (C h19 (T (T (T (T (T (T (T (T (T (T (T (T h96 h85) h107) (C h19 (T (T (T (T (T (T (T (T (T (T h106 h13) h29) h28) h27) h53) h52) h51) h44) h42) (C h19 (T (T (T h63 h62) h107) (C h25 (T (T (T (T h106 h13) h29) h28) h27))))))) (S (h v1 v10 v1))) (h v1 v10 v4)) (C h15 (T (T (T (T (T h68 h56) h3) h87) h98) (C h78 (T (T (T (T (T h105 h102) (C h25 h74)) (C (T (T (T (T (T (T (T h13 h29) h28) h27) h53) h52) h51) h44) h74)) (C (T (T (T h43 h61) h58) h57) (T (T (T (T h75 h104) h103) h81) (C h78 (T (T (T (T h83 (C h19 (T (T (T (T (C h78 (T h105 h102)) h88) h8) h39) h36))) h6) h64) h100))))) (S h101)))))) (S (h y y v4))) (h y y z)) (C h47 (T (T (T (h y v0 z) (C h47 h91)) (C h47 (T (T (T (T (T h93 h92) (h y v1 v4)) (C h15 (T (T (T (T (T (T (T (C h78 (T (T (T (T (T (T h32 h31) h67) h66) h6) h64) h100)) h99) h82) h80) h79) h76) h70) h73))) h71) (C h54 h74)))) (C h47 (T (T (C h40 h74) (C h54 (T h70 h73))) (S h72)))))) (S (h z z z))) h72) h71)))) (S (h v1 v5 v69))) h65) (C h19 (T (T h56 h3) h26))) h38))) h68) h56) h3

