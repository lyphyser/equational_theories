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
theorem Equation895_implies_Equation2180 (G: Type _) [Magma G] (h: Equation895 G) : Equation2180 G := fun x y z =>
  let v0 := M y z
  let v1 := M v0 y
  let v2 := M x z
  let v3 := M v1 v2
  have h4 := h v3 v3 v1
  have h5 := S h4
  have h6 := h v1 z v2
  have h7 := S h6
  let v8 := M v2 x
  have h9 := h v2 v2 (M (M z x) v8)
  have h10 := S h9
  have h11 := h z v2 x
  have h12 := R v2
  have h13 := C h12 (C h11 h11)
  have h14 := T h13 h10
  have h15 := R z
  have h16 := C h15 h14
  have h17 := h x z z
  have h18 := T h17 h16
  have h19 := R v3
  have h20 := h z v2 v2
  have h21 := S h20
  have h22 := C h14 h12
  have h23 := S h11
  have h24 := C h12 (C h23 h23)
  have h25 := S h17
  have h26 := T h9 h24
  have h27 := C h15 h26
  have h28 := T h27 h25
  have h29 := C h28 h15
  have h30 := C (T (T h29 h9) h24) h12
  have h31 := C h18 (T h30 h22)
  let v32 := M z v2
  have h33 := h v32 x z
  have h34 := C h14 (T (T (T h17 h16) h33) h31)
  have h35 := C (T h34 h21) (C h19 h18)
  have h36 := C h19 (T h35 h7)
  let v37 := M z z
  have h38 := h (M v2 v37) v3 x
  have h39 := T (T (T h9 h24) h38) h36
  let v40 := M v3 v1
  have h41 := R v40
  have h42 := S h33
  have h43 := C h18 h15
  have h44 := C (T (T h13 h10) h43) h12
  have h45 := C h26 h12
  have h46 := C h28 (T h45 h44)
  have h47 := C (T h46 h42) h15
  have h48 := C (T h33 h31) h15
  let v49 := M v3 x
  have h50 := R v49
  have h51 := R x
  have h52 := C h26 h51
  have h53 := C h52 h50
  have h54 := C (C (T (T h53 h35) h7) h12) (T (T (T (T h45 h44) (C h48 h12)) (C (T (T (T (T (T h47 h29) h9) h24) h38) h36) h12)) (C h41 h39))
  let v55 := M v2 v2
  have h56 := R v55
  have h57 := C h14 h51
  have h58 := C h57 h50
  have h59 := T (T (T h46 h42) h27) h25
  have h60 := C h26 h59
  have h61 := C (T h20 h60) (C h19 h28)
  have h62 := h v1 v1 v2
  have h63 := S h62
  let v64 := M v3 v3
  have h65 := R v64
  have h66 := h (M v8 v49) v2 v2
  have h67 := S h66
  have h68 := C h47 h12
  have h69 := S h38
  have h70 := C h19 (T h6 h61)
  have h71 := C (T (T (T (T (T h70 h69) h13) h10) h43) h48) h12
  have h72 := T (T (T h70 h69) h13) h10
  have h73 := C h41 h72
  have h74 := C (T (T h6 h61) h58) h12
  have h75 := C h72 (T h4 (C h74 (T (T (T (T h73 h71) h68) h30) h22)))
  have h76 := C (T (T (T (T h75 h67) h53) h35) h7) h65
  have h77 := C (T h38 h36) h19
  have h78 := C h77 h65
  have h79 := C h26 h19
  have h80 := C h79 h65
  have h81 := C (C (T (T (T (T (T (T h80 h78) h76) h63) h6) h61) h58) h12) h56
  have h82 := C h14 h19
  have h83 := C h82 h65
  have h84 := C (T h70 h69) h19
  have h85 := C h84 h65
  have h86 := C h39 (T h54 h5)
  have h87 := C (T (T (T (T h6 h61) h58) h66) h86) h65
  have h88 := h v3 v1 v1
  have h89 := R v1
  have h90 := T (T (T (T (T (T h79 h77) h75) h67) h53) h35) h7
  have h91 := h v40 v2 v3
  have h92 := T (T (T (T (T h9 h24) h38) h36) h91) (C h39 (T (C (T (T (T (T (T (T (T (T h75 h67) h53) h35) h7) h62) h87) h85) h83) h90) (C (T (T (T h80 h78) h76) h63) h89)))
  have h93 := S h91
  have h94 := T (T (T (T (T (T h6 h61) h58) h66) h86) h84) h82
  have h95 := C h72 (T (C (T (T (T h62 h87) h85) h83) h89) (C (T (T (T (T (T (T (T (T h80 h78) h76) h63) h6) h61) h58) h66) h86) h94))
  let v96 := M x v3
  have h97 := R v96
  let v98 := M v2 v3
  let v99 := M v32 v55
  have h100 := h v99 z z
  have h101 := R v37
  T (T (T (T (T (T (T (T (T h17 h16) h33) h31) (h v99 v3 v1)) (C (T h88 (C h94 (T (T (T (T (T h95 h93) h70) h69) h13) h10))) (T (T (T (T (T (T (C (T (C h59 (T (T (T (T (C (R v0) (T (h y x z) (C (T (T (T (T (T (T h17 h16) h33) h31) h100) (C (T (T h20 h60) h57) (T (T (T (C h47 h101) (C h29 h101)) h13) h10))) (C (T (h v8 v1 v2) (C h94 (T (C (T (C (T (T h52 h34) h21) (T (T (T h9 h24) (C h43 h101)) (C h48 h101))) (S h100)) h19) (C h59 h19)))) h12)) (R (M v0 v2))))) (S (h (M v98 v96) v0 v2))) (C h79 h97)) (C h77 h97)) (C (T (T (T (T (T (T (T (T (T (T h75 h67) h53) h35) h7) h62) h87) h85) h83) (h (M v98 v64) v2 v2)) (C h92 (T (T h81 h54) h5))) h97))) (S (h (M v40 (M v1 v1)) x v3))) h72) (C (T h95 h93) h39)) h73) h71) h68) h30) h22))) (C (T (T (T (C h90 h92) (S h88)) h74) (C (T (T (T (T (T (T h53 h35) h7) h62) h87) h85) h83) h12)) h56)) h81) h54) h5

