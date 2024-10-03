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
theorem Equation1571_implies_Equation14 (G: Type _) [Magma G] (h: Equation1571 G) : Equation14 G := fun x y =>
  let v0 := M x y
  let v1 := M y v0
  let v2 := M v1 v0
  have h3 := h v1 v1 (M y v2)
  have h4 := S h3
  have h5 := h v1 y v0
  have h6 := R v1
  let v7 := M v1 v1
  have h8 := h v7 x y
  have h9 := S h8
  have h10 := h y y v0
  have h11 := S h10
  have h12 := R v7
  have h13 := h y v1 v1
  have h14 := R x
  have h15 := R v0
  have h16 := C h15 (C h14 (T h13 (C h12 h11)))
  have h17 := C h5 (T (T h16 h9) (C h6 h5))
  have h18 := C h15 (C h14 (T (C h12 h10) (S h13)))
  have h19 := T h17 h4
  have h20 := C h19 h6
  have h21 := T (T h20 h8) h18
  have h22 := C h6 h21
  have h23 := S h5
  have h24 := C h23 (T (T (C h6 h23) h8) h18)
  have h25 := T h3 h24
  have h26 := C h25 h6
  let v27 := M v0 v0
  have h28 := h v27 v0 v1
  have h29 := S h28
  have h30 := C (T h8 h18) (T (T h22 h17) h4)
  let v31 := M v1 v27
  have h32 := h v31 v1 v1
  have h33 := T (T (T h3 h24) h32) h30
  let v34 := M v0 v1
  have h35 := h v34 v1 v0
  have h36 := S h35
  let v37 := M v0 y
  have h38 := h v0 v0 (M x v37)
  have h39 := S h38
  have h40 := h v0 x y
  have h41 := C h40 (C h15 h40)
  have h42 := C h15 h21
  have h43 := R v34
  have h44 := C h43 (T (T h42 h41) h39)
  have h45 := h v31 v0 v1
  have h46 := S h32
  have h47 := T (T h16 h9) h26
  have h48 := C h6 h47
  have h49 := C (T h16 h9) (T (T h3 h24) h48)
  have h50 := C h6 (T (T (T h49 h46) h45) h44)
  have h51 := C h19 h33
  have h52 := R v2
  have h53 := C h52 (T (T h26 h51) h50)
  have h54 := h y v1 v0
  have h55 := C (T (T h54 h53) h36) (T (T (T h54 h53) h36) (C h15 h33))
  have h56 := C h6 (T (T (T (T h55 h29) h16) h9) h26)
  let v57 := M y y
  let v58 := M v1 v57
  have h59 := S h54
  have h60 := T (T (T h49 h46) h17) h4
  have h61 := C h25 h60
  have h62 := S h45
  have h63 := C h15 h47
  have h64 := S h40
  have h65 := C h64 (C h15 h64)
  have h66 := C h43 (T (T h38 h65) h63)
  have h67 := C h6 (T (T (T h66 h62) h32) h30)
  have h68 := C h52 (T (T h67 h61) h20)
  have h69 := T (T (T h56 h22) h17) h4
  have h70 := C h69 (T (T (T h3 h24) h45) h44)
  have h71 := h v58 v0 x
  have h72 := h x v0 v0
  have h73 := h x x y
  have h74 := T h55 h29
  have h75 := T (C h74 h73) (S h72)
  have h76 := T (T h35 h68) h59
  have h77 := C h76 (T (T (T (C h15 h60) h35) h68) h59)
  have h78 := C h6 (T (T (T (T h20 h8) h18) h28) h77)
  have h79 := T (T (T h3 h24) h48) h78
  have h80 := T h28 h77
  have h81 := T h72 (C h80 (S h73))
  have h82 := h x y y
  have h83 := h v1 y y
  have h84 := S h83
  have h85 := R v57
  let v86 := M v1 y
  have h87 := h v57 v57 (M y v86)
  have h88 := T (T (T (T (T (T (T (T (T (T (T h70 h67) h61) h20) h8) h18) h28) h77) h87) (C h84 (T (C h85 h84) (S h82)))) (C h6 h81)) (C h79 h75)
  have h89 := C h79 (T (T (T h66 h62) h17) h4)
  let v90 := M v0 x
  have h91 := R v90
  have h92 := C h52 (T (C h79 (T (T (T (T (T (C h91 (T (T (T (T h38 h65) h63) (C h15 (T (T h51 h50) h89))) (C h15 h88))) (S h71)) h56) h22) h17) h4)) h70)
  have h93 := h v90 v1 v0
  have h94 := h v90 v1 v1
  have h95 := S h94
  have h96 := S h87
  have h97 := C h83 (T h82 (C h85 h83))
  have h98 := C h6 h75
  have h99 := C h69 h81
  have h100 := T (T (T h54 h53) (C h52 (T h89 (C h69 (T (T (T (T (T h3 h24) h48) h78) h71) (C h91 (T (T (T (T (C h15 (T (T (T (T (T (T (T (T (T (T (T h99 h98) h97) h96) h55) h29) h16) h9) h26) h51) h50) h89)) (C h15 (T (T h70 h67) h61))) h42) h41) h39))))))) (S h93)
  have h101 := R y
  have h102 := C (T (T (T h55 h29) h16) h9) (T h10 (C h6 (T (C h101 h33) (C h100 h60))))
  have h103 := T (T (T (T (T h102 h95) h93) h92) h68) h59
  have h104 := C h80 h101
  have h105 := h y x y
  have h106 := C h74 h101
  have h107 := T (T (T h93 h92) h68) h59
  have h108 := C (T (T (T h8 h18) h28) h77) (T (C h6 (T (C h107 h33) (C h101 h60))) h11)
  T (T (T (T (T (T (h x v0 y) (C (R v37) (T (h v27 v1 y) (C (T (T (T (h v86 v0 v1) (C h76 (T (T (C h15 (T (T (T (T (C (R v86) (T (T (T (T (T (T h3 h24) h48) h78) (C h6 (T (T (T (T (T (T (T h55 h29) h16) h9) h26) h51) h50) h89))) (C h6 h88)) (C h6 (T (T (T (T (T (T (T h99 h98) h97) h96) (h v57 v0 x)) (C h107 (T (T (C h15 h75) h94) h108))) (C h101 h106)) (C h100 (T (T (T (T (T (T h104 h102) h95) h93) h92) h68) h59)))))) (S (h v90 v1 y))) h94) h108) h106)) (C h15 h104)) (C h15 h103)))) (C h105 (C h15 h105))) (S (h v0 v0 (M x v57)))) (T (C h6 h104) (C h79 h103)))))) (S (h v58 v0 y))) h56) h22) h17) h4

