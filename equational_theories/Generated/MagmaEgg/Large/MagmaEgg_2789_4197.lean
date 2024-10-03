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
theorem Equation2789_implies_Equation4197 (G: Type _) [Magma G] (h: Equation2789 G) : Equation4197 G := fun x y z =>
  let v0 := M x y
  let v1 := M z x
  let v2 := M v1 y
  let v3 := M v2 z
  have h4 := h y v1 v1
  have h5 := S h4
  have h6 := R v1
  have h7 := R v2
  have h8 := h v1 x v2
  have h9 := S h8
  let v10 := M x v1
  let v11 := M x v2
  have h12 := h v2 (M v11 v10) v2
  have h13 := T h12 (C (C h9 h9) h7)
  have h14 := C h13 h6
  have h15 := T h14 h5
  have h16 := R x
  have h17 := C h16 h15
  have h18 := h (M v2 v1) x x
  have h19 := S h18
  have h20 := T (C (C h8 h8) h7) (S h12)
  have h21 := C h20 h6
  have h22 := T h4 h21
  have h23 := C h16 h22
  let v24 := M x x
  have h25 := R v24
  have h26 := C h25 h23
  have h27 := R v0
  have h28 := h x x v0
  have h29 := S h28
  have h30 := C (C h29 h29) h27
  have h31 := h v0 (M (M x v0) v24) v0
  have h32 := C (T (T h31 h30) h26) h16
  have h33 := T h32 h19
  have h34 := C h16 h33
  let v35 := M v0 x
  have h36 := h v35 x y
  have h37 := S h36
  have h38 := C (T (T (C h25 h17) (C (C h28 h28) h27)) (S h31)) h16
  have h39 := T h18 h38
  have h40 := C h16 h39
  have h41 := C (T (C h27 h23) (C h27 h40)) (T (T (T h32 h19) h14) h5)
  have h42 := T h41 h37
  have h43 := C h16 h42
  have h44 := h (M (M v0 v0) v35) x v1
  have h45 := S h44
  have h46 := h x v0 v0
  have h47 := S h46
  have h48 := C (T (C h27 h34) (C h27 h17)) (T (T (T h4 h21) h18) h38)
  have h49 := C (T (T (T (T (T h4 h21) h18) h38) h36) h48) h27
  have h50 := R z
  have h51 := C h50 (T h49 h47)
  have h52 := h (M y v0) z z
  have h53 := S h52
  have h54 := C (T (T (T (T (T h41 h37) h32) h19) h14) h5) h27
  have h55 := C h50 (T h46 h54)
  have h56 := R (M z z)
  have h57 := h z x v1
  have h58 := S h57
  have h59 := h v1 (M v10 (M x z)) v1
  have h60 := C (T (T h59 (C (C h58 h58) h6)) (C h56 h55)) h50
  have h61 := C h50 (T h60 h53)
  let v62 := M v1 z
  have h63 := h v62 z x
  have h64 := S h63
  have h65 := C (T (T (C h56 h51) (C (C h57 h57) h6)) (S h59)) h50
  have h66 := C h50 (T h52 h65)
  have h67 := T h55 h66
  have h68 := C (C h6 h67) (T (T (T h60 h53) h49) h47)
  have h69 := C h50 (T h68 h64)
  have h70 := T h36 h48
  have h71 := C h16 h70
  have h72 := R v10
  have h73 := C (T (T (T (T (T h68 h64) h60) h53) h49) h47) h6
  have h74 := h z v1 v1
  have h75 := T h74 h73
  have h76 := C (T (C h75 (T h23 h40)) (C h72 h71)) (T (T h69 h61) h51)
  have h77 := T (T (T h46 h54) h52) h65
  have h78 := T h61 h51
  have h79 := C (C h6 h78) h77
  have h80 := T h63 h79
  have h81 := C h50 h80
  let v82 := M z v0
  have h83 := R v82
  have h84 := C h83 h81
  have h85 := C h83 h67
  have h86 := T (T (T h85 h84) h76) h45
  have h87 := R (M y v3)
  let v88 := M v1 v1
  have h89 := h (M v88 v62) z v3
  have h90 := R v3
  have h91 := R (M z v3)
  have h92 := h z v2 z
  have h93 := S h74
  have h94 := C (T (T (T (T (T h46 h54) h52) h65) h63) h79) h6
  have h95 := h v10 v2 v2
  have h96 := R (M v2 v2)
  have h97 := h v2 x v3
  have h98 := S h97
  have h99 := h v3 (M (M x v3) v11) v3
  have h100 := R (M v3 v3)
  have h101 := h (M v88 v2) v3 v3
  have h102 := R v88
  have h103 := h (M v82 v1) v1 v1
  have h104 := C h83 h78
  have h105 := C h83 h69
  have h106 := T h94 h93
  have h107 := C (T (C h72 h43) (C h106 (T h34 h17))) (T (T h55 h66) h81)
  have h108 := T (T (T h44 h107) h105) h104
  have h109 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (C h91 h69) (C h91 h61)) (C (T (T (T (T (T (C (T h92 (C h100 (T (T (T h74 h73) h95) (C (T (T (C h96 (C h7 h106)) (C (C h97 h97) h90)) (S h99)) h13)))) h90) (S h101)) (C h102 (C h6 h22))) (C h102 (C h6 h39))) (C h102 (C h6 h70))) (C h102 (C h6 h108))) h51)) (S h103)) h85) h84) h76) h45) h41) h37) h32) h19) h14) h5) h90
  T (T (T (T (T (T (T h31 h30) h26) (C h25 h40)) (C h25 h71)) (C h25 (C h16 h108))) (C (T (T (T (T (C h16 h77) (C h16 h80)) (C h16 (T h89 h109))) (C (T (T (T (T (T (T (T h46 h54) h52) h65) h63) h79) h89) h109) h87)) (C (T (T (T (T (T (C (T (T (T (T (T (T (T (T (T (T (T (T (T h4 h21) h18) h38) h36) h48) h44) h107) h105) h104) h103) (C (T (T (T (T (T (C h102 (C h6 h86)) (C h102 (C h6 h42))) (C h102 (C h6 h33))) (C h102 (C h6 h15))) h101) (C (T (C h100 (T (T (T (C (T (T h99 (C (C h98 h98) h90)) (C h96 (C h7 h75))) h20) (S h95)) h94) h93)) (S h92)) h90)) h55)) (C h91 h66)) (C h91 h81)) h90) (S h89)) h68) h64) h60) h53) h87)) (T (T (T (C h16 h86) h43) h34) h17))) (S (h v3 y v0))

