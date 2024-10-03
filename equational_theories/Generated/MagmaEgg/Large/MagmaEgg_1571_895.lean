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
theorem Equation1571_implies_Equation895 (G: Type _) [Magma G] (h: Equation1571 G) : Equation895 G := fun x y z =>
  let v0 := M y z
  let v1 := M x z
  let v2 := M v1 v0
  let v3 := M y v2
  let v4 := M v3 v2
  have h5 := h v3 y v2
  have h6 := R v3
  have h7 := h v2 x x
  have h8 := h x v1 v0
  have h9 := S h8
  have h10 := h y x z
  have h11 := R v2
  have h12 := T (C h11 h10) h9
  have h13 := h v2 v2 y
  let v14 := M x x
  have h15 := R v14
  have h16 := R y
  have h17 := C h6 (C h16 (T (C h15 (T h13 (C h12 (C h11 h12)))) (S h7)))
  have h18 := h v14 y v2
  have h19 := S (h y y v2)
  have h20 := h y v2 y
  have h21 := h y v0 v1
  have h22 := S h21
  have h23 := h x y z
  let v24 := M v0 v1
  have h25 := h v24 v1 x
  have h26 := S h25
  have h27 := S h23
  have h28 := R v24
  have h29 := R v1
  let v30 := M v1 x
  have h31 := h v30 v3 v2
  let v32 := M v0 z
  have h33 := h v0 v0 (M y v32)
  have h34 := S h33
  have h35 := h v0 y z
  have h36 := R v0
  let v37 := M v0 v0
  have h38 := h v37 v2 y
  have h39 := h y y z
  have h40 := R v37
  have h41 := h y v0 v0
  have h42 := S h10
  have h43 := T h8 (C h11 h42)
  have h44 := C h35 (T (T (C h43 (T h8 (C h11 (T (T h42 h41) (C h40 (S h39)))))) (S h38)) (C h36 h35))
  let v45 := M v0 v14
  have h46 := h v45 v3 v3
  have h47 := S h46
  have h48 := S h35
  have h49 := C h48 (T (T (C h36 h48) h38) (C h12 (T (C h11 (T (T (C h40 h39) (S h41)) h10)) h9)))
  have h50 := T h33 h49
  have h51 := h v3 y z
  have h52 := S h51
  have h53 := h v0 v0 (M y (M v3 z))
  have h54 := C (T h18 h17) (T (T h53 (C h52 (C h36 h52))) (C h6 (C h50 h6)))
  have h55 := T h44 h34
  have h56 := T (C h6 (C h16 (T h7 (C h15 (T (C h43 (C h11 h43)) (S h13)))))) (S h18)
  have h57 := C h56 (T (T (C h6 (C h55 h6)) (C h51 (C h36 h51))) (S h53))
  have h58 := h v45 z v2
  have h59 := h v0 x z
  have h60 := S h59
  have h61 := h v1 v1 (M x v32)
  have h62 := R z
  have h63 := h z v2 y
  let v64 := M z y
  let v65 := M v2 v64
  have h66 := R v65
  have h67 := T (C h43 h66) (S h63)
  have h68 := R x
  have h69 := h x x v65
  let v70 := M z v2
  have h71 := R v70
  have h72 := R v30
  have h73 := h v70 v1 x
  have h74 := R v4
  have h75 := h z v3 v2
  have h76 := C (T (T h75 (C h74 (C h6 (T h73 (C h72 (T (C h29 (T (T (T (C h71 (T (T h69 (C h67 (C h68 h67))) (C h62 (T (T h61 (C h60 (C h29 h60))) (C h50 h11))))) (S h58)) h46) h57)) (C h29 (T (T (T h54 h47) h44) h34)))))))) (S h31)) (C h29 (T h21 (C h28 h27)))
  have h77 := C (T h76 h26) h23
  have h78 := h (M z (M v1 y)) z x
  have h79 := S h78
  have h80 := T h63 (C h12 h66)
  have h81 := C (T (T h31 (C h74 (C h6 (T (C h72 (T (C h29 (T (T (T h33 h49) h46) h57)) (C h29 (T (T (T h54 h47) h58) (C h71 (T (T (C h62 (T (T (C h55 h11) (C h59 (C h29 h59))) (S h61))) (C h80 (C h68 h80))) (S h69))))))) (S h73))))) (S h75)) (C h29 (T (C h28 h23) h22))
  have h82 := C (T h25 h81) h27
  have h83 := h y v1 z
  have h84 := S h83
  have h85 := h v2 v1 z
  have h86 := S h85
  let v87 := M v1 z
  have h88 := R v87
  have h89 := h v87 v87 (M v1 (M v2 z))
  have h90 := h z x z
  have h91 := S h90
  have h92 := h v1 v1 (M x (M z z))
  have h93 := C (T h92 (C h91 (T (T (T (C h29 h91) h89) (C h86 (T (T (C h88 h86) h84) h10))) h9))) (C h62 (T h21 h82))
  have h94 := C (T h93 h79) h68
  have h95 := h v2 v2 (M v1 (M y v0))
  have h96 := h y v1 v0
  have h97 := C (T (C h96 (T h8 (C h11 (T h42 h96)))) (S h95)) (C h16 (T (T h94 h77) h22))
  have h98 := h (M v1 v64) y x
  have h99 := S h89
  have h100 := C h85 (T (T h42 h83) (C h88 h85))
  have h101 := C (T (C h90 (T (T (T h8 h100) h99) (C h29 h90))) (S h92)) (C h62 (T h77 h22))
  have h102 := C h6 (C (T (C h43 (T (T (T (T (T h25 h81) h78) h101) h98) h97)) (S h20)) h6)
  have h103 := C h56 (T h102 h19)
  have h104 := h (M x v24) v3 v3
  have h105 := S h98
  have h106 := C h16 (T (T h21 h82) (C (T h78 h101) h68))
  have h107 := S h96
  have h108 := C (T h95 (C h107 (T (C h11 (T h107 h10)) h9))) h106
  have h109 := C h12 (T (T (T (T (T h108 h105) h93) h79) h76) h26)
  T (T (T (T (T (T (T h8 h100) h99) (h v87 y v2)) (C h6 (C h16 h84))) (C h6 (T (T (T h106 (C h16 (C (T h98 h97) h68))) (C (T (T (T h20 h109) h104) h103) (T (T (T (T (T (T (T (C (T h108 h105) h68) h94) h77) h22) h20) h109) h104) (C h56 (T (T (T (T (T h102 h19) h20) h109) h104) h103))))) (S (h v14 v14 y))))) (C h5 (T (T h18 h17) (C h6 h5)))) (S (h v3 v3 (M y v4)))

