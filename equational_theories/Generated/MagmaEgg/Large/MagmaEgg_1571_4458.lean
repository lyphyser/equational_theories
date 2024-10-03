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
theorem Equation1571_implies_Equation4458 (G: Type _) [Magma G] (h: Equation1571 G) : Equation4458 G := fun x y z =>
  let v0 := M z y
  let v1 := M v0 z
  have h2 := S (h x v0 z)
  have h3 := R v1
  let v4 := M y x
  let v5 := M x v4
  let v6 := M x (M v5 x)
  let v7 := M x x
  have h8 := h v7 v7 v6
  have h9 := S h8
  have h10 := h v5 x x
  have h11 := R v7
  have h12 := h y x x
  have h13 := C h10 (T h12 (C h11 h10))
  have h14 := h (M v5 y) v5 v5
  have h15 := S h14
  have h16 := h v5 v5 (M x v5)
  have h17 := S h16
  have h18 := h x x v4
  have h19 := R v5
  have h20 := C h18 (C h19 h18)
  have h21 := T h20 h17
  have h22 := S h12
  have h23 := S h10
  have h24 := C h23 (T (C h11 h23) h22)
  have h25 := C (T h8 h24) h21
  have h26 := T h10 h25
  have h27 := C h19 h26
  let v28 := M v5 v5
  have h29 := h v28 y x
  have h30 := S h29
  have h31 := S h18
  have h32 := R v28
  have h33 := h x v5 v5
  have h34 := R y
  have h35 := R v4
  have h36 := C h35 (C h34 (T h33 (C h32 h31)))
  let v37 := M v4 v4
  have h38 := h v37 z y
  have h39 := S h38
  have h40 := h y y x
  have h41 := R v37
  have h42 := h y v4 v4
  have h43 := R z
  have h44 := R v0
  have h45 := C h44 (C h43 (T h42 (C h41 (S h40))))
  have h46 := h v0 v1 v1
  have h47 := h v0 v0 z
  let v48 := M v1 v1
  have h49 := R v48
  have h50 := C (T (T (T h45 h39) h36) h30) (T (T (T (T (T (C h44 (T (C h49 h47) (S h46))) h45) h39) h36) h30) h27)
  have h51 := h v48 v0 v0
  have h52 := h z v0 v0
  have h53 := h z z y
  let v54 := M v0 v0
  have h55 := R v54
  have h56 := C h3 (C h44 (T (C h55 h53) (S h52)))
  have h57 := h v54 v0 z
  have h58 := S h57
  have h59 := S h53
  have h60 := C h3 (C h44 (T h52 (C h55 h59)))
  have h61 := C h44 (C h43 (T (C h41 h40) (S h42)))
  have h62 := C h35 (C h34 (T (C h32 h18) (S h33)))
  have h63 := C h31 (C h19 h31)
  have h64 := T h16 h63
  have h65 := C (T h13 h9) h64
  have h66 := T h65 h23
  have h67 := C h19 h66
  have h68 := C (T (T (T (T (T (T h8 h24) h14) (C (T (T (T h29 h62) h38) h61) (T (T (T (T (T h67 h29) h62) h38) h61) (C h44 (T h46 (C h49 (S h47))))))) (S h51)) h60) h58) h21
  have h69 := h v6 v1 y
  have h70 := S h69
  have h71 := C h11 h21
  have h72 := C (T (T (T (T (T (T h57 h56) h51) h50) h15) h13) h9) h64
  have h73 := T h65 h68
  have h74 := T (T (T (T (T (T h45 h39) h36) h30) h27) (C h19 h73)) (C h64 (T (T (T (T h72 h23) h10) h71) h22))
  have h75 := h v1 v0 z
  have h76 := S h75
  have h77 := h v1 v1 (M v0 (M v1 z))
  have h78 := T (T h77 (C h76 (T (T (C h3 h76) h60) h58))) (C h3 h74)
  let v79 := M v1 y
  have h80 := R v79
  have h81 := T (T (T (T (T (C h80 h78) h70) h20) h17) h10) h68
  have h82 := T h72 h25
  have h83 := C h11 h64
  have h84 := T (T (T (T (T (T (C h21 (T (T (T (T h12 h83) h23) h10) h68)) (C h19 h82)) h67) h29) h62) h38) h61
  have h85 := T (T (C h3 h84) (C h75 (T (T h57 h56) (C h3 h75)))) (S h77)
  have h86 := C h80 h85
  have h87 := h v79 z v1
  have h88 := h v0 v0 (M z v0)
  have h89 := C (T (C (T h88 (C h59 (C h44 h59))) (T (T (C h43 h26) (C h43 h73)) (C h43 (T (T (T (T (T h72 h23) h16) h63) h69) h86)))) (S h87)) h78
  have h90 := T (C h53 (C h44 h53)) (S h88)
  have h91 := C (T h87 (C h90 (T (T (C h43 h81) (C h43 h82)) (C h43 h66)))) h85
  have h92 := h v6 v0 y
  have h93 := S h92
  have h94 := h v0 z y
  have h95 := S h94
  let v96 := M v0 y
  have h97 := h v0 v0 (M z v96)
  have h98 := R v96
  have h99 := C h98 (T (T h97 (C h95 (C h44 h95))) (C h44 h74))
  have h100 := C h98 (T (T (C h44 h84) (C h94 (C h44 h94))) (S h97))
  have h101 := h v6 y y
  have h102 := R (M v6 y)
  have h103 := T (T h10 h71) h22
  have h104 := h v5 x v4
  have h105 := S h104
  have h106 := h v5 v5 (M x (M v5 v4))
  let v107 := M y y
  have h108 := R v107
  T (T (T (T (T (T h16 h63) h69) h91) (C (T (T (h (M v0 (M z v5)) z v1) (C h90 (T (C h43 (T (T (T h89 h70) h92) h100)) (C h43 (T (T (T (T h99 h93) h101) (C h108 (T (T (T (C (T (T h12 h83) h23) h102) (C h19 h84)) (C h104 (T (T (T (T h45 h39) h36) h30) (C h19 h104)))) (S h106)))) (C h108 h103)))))) (S (h v107 z y))) h3)) (C (T (T (T (T (T (T (T (T (T (h v107 v1 v5) (C (R (M v1 v5)) (T (T (T (C h3 (T (T (T (C h108 (T (T (T h106 (C h105 (T (T (T (T (C h19 h105) h29) h62) h38) h61))) (C h19 h74)) (C h103 h102))) (S h101)) h92) h100)) (C h3 (T (T (T h99 h93) h69) h91))) (C h3 (T h89 h86))) (C h3 h81)))) (S (h v54 v1 v5))) h57) h56) h51) h50) h15) h13) h9) (T (h v1 v1 (M v0 (M x z))) (C h2 (C h3 h2))))) (S (h v1 x x))

