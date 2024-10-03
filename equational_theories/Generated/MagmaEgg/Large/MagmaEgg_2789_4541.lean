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
theorem Equation2789_implies_Equation4541 (G: Type _) [Magma G] (h: Equation2789 G) : Equation4541 G := fun x y z =>
  let v0 := M z x
  let v1 := M v0 y
  have h2 := h v1 y y
  have h3 := S h2
  have h4 := h y v0 v0
  have h5 := S h4
  have h6 := R v0
  have h7 := R v1
  have h8 := h v0 x v1
  have h9 := S h8
  have h10 := C (C h9 h9) h7
  have h11 := h v1 (M (M x v1) (M x v0)) v1
  have h12 := T h11 h10
  have h13 := C h12 h6
  let v14 := M v1 v0
  have h15 := h v14 v0 y
  have h16 := S h15
  have h17 := T h13 h5
  have h18 := S h11
  have h19 := C (C h8 h8) h7
  have h20 := T h19 h18
  have h21 := C h20 h6
  have h22 := T h4 h21
  have h23 := C h6 h22
  have h24 := C h7 (T (T h19 h18) h23)
  have h25 := C h7 h12
  have h26 := C (T h25 h24) h17
  let v27 := M y z
  let v28 := M v1 v1
  let v29 := M v28 v14
  have h30 := h v29 v0 v27
  have h31 := R v27
  have h32 := C h7 h20
  have h33 := C h6 h17
  have h34 := C h7 (T (T h33 h11) h10)
  have h35 := C (T h34 h32) h22
  have h36 := T h15 h35
  have h37 := C h6 h36
  have h38 := h v0 v1 v1
  have h39 := S h38
  have h40 := C (T (T (T h4 h21) h15) h35) h20
  have h41 := R y
  have h42 := C h41 h12
  have h43 := T (T h42 h40) h39
  have h44 := h z y v1
  have h45 := C h41 h20
  let v46 := M y y
  have h47 := R v46
  have h48 := C h47 h45
  have h49 := C (T (T (T h26 h16) h13) h5) h12
  have h50 := T h26 h16
  have h51 := h v29 v0 v0
  have h52 := S h51
  have h53 := R (M v0 v0)
  have h54 := C (T (T (T h11 h10) (C h53 h23)) (C h53 h37)) h43
  have h55 := C (T (T (C h17 (T h54 h52)) (C h41 h50)) (C h41 h17)) (T h38 h49)
  let v56 := M y v1
  have h57 := h v56 v1 v0
  have h58 := C (T (T (T (T (T h38 h49) h45) h57) h55) h48) (T (T (T (T (T (C (T h44 (C (C h43 h31) (T h23 h37))) h31) (S h30)) h26) h16) h13) h5)
  let v59 := M z v27
  let v60 := M v0 v59
  have h61 := h v27 z x
  have h62 := S h61
  have h63 := R x
  have h64 := S h44
  have h65 := C h6 h50
  have h66 := T (T h38 h49) h45
  have h67 := C h66 h31
  have h68 := C (T (C h67 (T h65 h33)) h64) h31
  have h69 := S h57
  have h70 := C (T (T (T (C h53 h65) (C h53 h33)) h19) h18) h66
  have h71 := C (T (T (C h41 h22) (C h41 h36)) (C h22 (T h51 h70))) (T h40 h39)
  have h72 := C h47 h42
  have h73 := C (T (T (T (T (T h72 h71) h69) h42) h40) h39) (T (T (T (T (T h4 h21) h15) h35) h30) h68)
  have h74 := T h2 h73
  have h75 := C h74 h63
  have h76 := h (M v1 x) x x
  have h77 := S h76
  have h78 := T h58 h3
  have h79 := C h78 h63
  have h80 := T h61 h79
  have h81 := C h63 h80
  let v82 := M x x
  have h83 := R v82
  let v84 := M x v27
  have h85 := R v84
  have h86 := h x x v84
  have h87 := S h86
  have h88 := h v84 (M (M x v84) v82) v84
  have h89 := C (T (T h88 (C (C h87 h87) h85)) (C h83 h81)) h63
  let v90 := M v84 x
  have h91 := h v90 x v27
  have h92 := S h91
  have h93 := T h75 h62
  have h94 := C h63 h93
  have h95 := C (T (T (C h83 h94) (C (C h86 h86) h85)) (S h88)) h63
  have h96 := T h76 h95
  have h97 := C h63 h96
  have h98 := C (T (C h85 h81) (C h85 h97)) (T (T (T h89 h77) h75) h62)
  have h99 := T (T (T (T (T h98 h92) h89) h77) h75) h62
  have h100 := h v29 v0 y
  have h101 := R v28
  have h102 := h (M v46 v56) v1 v1
  have h103 := T h89 h77
  have h104 := h x v84 v84
  have h105 := C (T (C h85 (C h63 h103)) (C h85 h94)) (T (T (T h61 h79) h76) h95)
  have h106 := T h91 h105
  have h107 := R z
  T (T (T (T (T (T h81 h97) (C h63 h106)) (C (T (T (T h104 (C h99 h85)) (h (M v27 v84) v1 v0)) (C (T (T (T (C h17 (T (C (T (T (T (T (T h2 h73) (h v60 y y)) (C (T (T (T (T (T (T (C h47 (T (T (T (T (C (T (T (T (T (T (T h4 h21) h15) h35) h100) (C (T (T (C h7 h65) h34) h32) (T (T (T (T (T h4 h21) h15) h35) h51) h70))) (C h101 (C h7 (T (T h57 h55) h48)))) h78) (S h102)) h72) h71) h69)) h72) h71) h69) h42) h40) h39) (T (T (T (T (T (T (T h4 h21) h15) h35) h30) h68) (h v59 v0 v27)) (C (T (C h67 h78) h64) h80)))) (C h6 (C h107 h96))) (C h6 (C h107 h106))) (T (C (T (T (T (T (T h61 h79) h76) h95) h91) h105) h85) (S h104))) (S (h (M (M v84 v84) v90) z x)))) (C h41 (T h98 h92))) (C h41 h103)) (C h41 h93)) (T (T (T (T (T (T (T h38 h49) h45) h57) h55) h48) h102) (C (T (T (T (T (T (T (C h101 (C h7 (T (T h72 h71) h69))) (C (T (T h25 h24) (C h7 h37)) (T (T (T (T (T h54 h52) h26) h16) h13) h5))) (S h100)) h26) h16) h13) h5) h74)))) h99)) (S (h v60 y v27))) h58) h3

