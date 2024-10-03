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
theorem Equation2399_implies_Equation2180 (G: Type _) [Magma G] (h: Equation2399 G) : Equation2180 G := fun x y z =>
  let v0 := M x z
  let v1 := M y z
  let v2 := M v1 y
  let v3 := M v2 v0
  have h4 := R v3
  let v5 := M x v0
  let v6 := M x v5
  let v7 := M v0 v6
  have h8 := h v0 v2 v7
  have h9 := S h8
  have h10 := R v2
  have h11 := h v0 v0 x
  have h12 := R v7
  have h13 := C (C h10 (T h11 (C h12 h11))) h10
  have h14 := R y
  have h15 := h z z x
  have h16 := S h15
  let v17 := M z v5
  have h18 := R v17
  have h19 := C (C h14 (T (C h18 h16) h16)) h14
  have h20 := h z y v17
  have h21 := h z v3 y
  have h22 := S h21
  have h23 := h v1 v2 y
  have h24 := S h23
  let v25 := M y v1
  let v26 := M y v25
  have h27 := R v26
  have h28 := h z y y
  have h29 := h y y x
  have h30 := S h29
  let v31 := M y (M x (M x y))
  have h32 := R v31
  have h33 := T (C h32 h30) h30
  have h34 := C (T (T (T (C h27 h33) (S h28)) h20) h19) h27
  have h35 := h y v26 v31
  have h36 := C (T h35 h34) h10
  have h37 := h (M y v2) v3 v2
  have h38 := S h37
  have h39 := S h35
  have h40 := T h29 (C h32 h29)
  have h41 := S h20
  have h42 := C (C h14 (T h15 (C h18 h15))) h14
  have h43 := C (T (T (T h42 h41) h28) (C h27 h40)) h27
  have h44 := C (T h43 h39) h10
  have h45 := R v1
  have h46 := h y v1 v31
  have h47 := T h20 h19
  have h48 := R (M v2 v26)
  have h49 := T h42 h41
  have h50 := C (C h4 (T (C h49 h48) (C h47 (T (T (T (T h43 h39) h46) (C (C h45 h33) h45)) (C h10 (T h23 h44)))))) h4
  have h51 := h v26 v3 v2
  have h52 := C h14 (T (T (T (T h51 h50) h38) h36) h24)
  have h53 := C h4 h52
  have h54 := C h53 h4
  have h55 := h v25 v3 y
  have h56 := C h4 (T (T (T (T h55 h54) h22) h20) h19)
  have h57 := C (T (T (T h53 h56) h13) h9) h4
  have h58 := S h51
  have h59 := C (C h4 (T (C h49 (T (T (T (T (C h10 (T h36 h24)) (C (C h45 h40) h45)) (S h46)) h35) h34)) (C h47 h48))) h4
  have h60 := h v1 z y
  have h61 := C h14 (T (T (T (T h23 h44) h37) h59) h58)
  have h62 := C h4 h61
  have h63 := S h55
  have h64 := C h62 h4
  have h65 := C h4 (T (T (T (T h42 h41) h21) h64) h63)
  have h66 := S h11
  have h67 := C (C h10 (T (C h12 h66) h66)) h10
  have h68 := C (T (T (T h8 h67) h65) h62) h4
  have h69 := C h14 (T (T (T (T (T (T (C (T (T h35 h34) (C h49 h27)) (T (T h68 h54) h22)) (S h60)) h23) h44) h37) h59) h58)
  have h70 := T (T (T h69 h52) h55) h57
  have h71 := C h14 (T (T (T (T (T (T h51 h50) h38) h36) h24) h60) (C (T (T (C h47 h27) h43) h39) (T (T h21 h64) h57)))
  have h72 := h v2 x v17
  have h73 := S h72
  have h74 := R x
  have h75 := R v5
  have h76 := C (C h49 h75) h10
  have h77 := h z v2 x
  let v78 := M x (M x (M x x))
  have h79 := h x v6 v78
  have h80 := S h79
  have h81 := R v6
  have h82 := h x x x
  have h83 := R v78
  have h84 := h z x x
  have h85 := C (T (T (T h42 h41) h84) (C h81 (T h82 (C h83 h82)))) h81
  have h86 := C h10 (C h74 (C h74 (T (T h56 h13) h9)))
  have h87 := h (M v3 v25) v2 x
  have h88 := S h87
  have h89 := C h10 (C h74 (C h74 (T (T h8 h67) h65)))
  have h90 := S h82
  have h91 := C (T (T (T (C h81 (T (C h83 h90) h90)) (S h84)) h20) h19) h81
  have h92 := C (T (T h79 h91) h89) (T (T (T (T h68 h54) h22) h20) h19)
  have h93 := C h74 h70
  have h94 := C h74 (T (T (T (T (T (T h42 h41) h21) h64) h63) h61) h71)
  let v95 := M x v2
  have h96 := R (M x (M x v95))
  have h97 := h v95 z x
  have h98 := C h74 (T (T (T (T (T (T h69 h52) h55) h54) h22) h20) h19)
  have h99 := T (T (T h68 h63) h61) h71
  have h100 := C h74 h99
  have h101 := C (T (T h86 h85) h80) (T (T (T (T h42 h41) h21) h64) h57)
  have h102 := C (T (T (T (T (T (T (T (T h8 h67) h65) h87) h101) h100) h98) h97) (C (T (T (T (T (C h47 h96) (C h10 (T (C h74 (C h74 (T h94 h93))) (C h74 (C h74 (T h92 h88)))))) h86) h85) h80) (T (T h77 h76) (C h18 (T (T (T h42 h41) h77) h76))))) h74
  have h103 := R v0
  have h104 := S h77
  have h105 := C (C h47 h75) h10
  T (T (h x v3 v0) (C (C h4 (T (C h103 (T (T (T (T (T (T (T (T (T h102 h73) h42) h41) h21) h64) h63) h61) h71) (C h14 (T (C h14 h99) (C h14 (T (T (T (T (T (T (T (T h69 h52) h55) h54) h22) h20) h19) h72) (C (T (T (T (T (T (T (T (T (C (T (T (T (T h79 h91) h89) (C h10 (T (C h74 (C h74 (T h87 h101))) (C h74 (C h74 (T h100 h98)))))) (C h49 h96)) (T (T (C h18 (T (T (T h105 h104) h20) h19)) h105) h104)) (S h97)) h94) h93) h92) h88) h56) h13) h9) h74))))))) (C h103 (T (T (T (T (C h14 (T (C h14 (T (T (T (T (T (T (T (T h102 h73) h42) h41) h21) h64) h63) h61) h71)) (C h14 h70))) h69) h52) h55) h57)))) h4)) (S (h v3 v3 v0))

