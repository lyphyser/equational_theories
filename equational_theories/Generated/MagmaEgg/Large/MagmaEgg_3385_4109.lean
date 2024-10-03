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
theorem Equation3385_implies_Equation4109 (G: Type _) [Magma G] (h: Equation3385 G) : Equation4109 G := fun x y z =>
  let v0 := M y z
  let v1 := M v0 z
  have h2 := h v1 y v0
  have h3 := S h2
  let v4 := M v1 y
  have h5 := h v0 (M v1 (M y v0)) v4
  have h6 := S h5
  have h7 := R v4
  have h8 := h y v0 z
  have h9 := S h8
  have h10 := R v1
  have h11 := C h10 h9
  have h12 := h z y v1
  have h13 := h v0 z v1
  have h14 := S h13
  let v15 := M v0 (M z v1)
  have h16 := h v1 v15 v4
  have h17 := h z v1 v1
  have h18 := S h17
  have h19 := h v1 v0 z
  have h20 := R v0
  have h21 := h v0 z y
  have h22 := S h21
  let v23 := M z y
  have h24 := h y (M v0 v23) v4
  have h25 := S h24
  have h26 := h v0 v23 v4
  have h27 := R y
  have h28 := C h7 (C h27 (C (T (T (T h2 h5) (C h7 (C h20 (C (T (C h10 h8) (S h12)) h7)))) (S h26)) h7))
  have h29 := h y v4 v4
  have h30 := T (T (T h29 h28) h25) h22
  have h31 := C h10 (T (C h30 h20) h19)
  have h32 := C h20 (T h31 h18)
  let v33 := M y v4
  have h34 := h v1 v33 v0
  have h35 := T h34 h32
  have h36 := C h35 h7
  have h37 := h v1 y v4
  have h38 := S h37
  have h39 := h v1 v33 y
  have h40 := S h39
  have h41 := S h29
  have h42 := C h7 (C h27 (C (T (T (T h26 (C h7 (C h20 (C (T h12 h11) h7)))) h6) h3) h7))
  have h43 := T (T (T h21 h24) h42) h41
  have h44 := C h43 h27
  have h45 := C h30 h44
  have h46 := C h43 h7
  have h47 := C h27 (T h46 h45)
  have h48 := C h7 (T h47 h40)
  have h49 := C h30 h27
  have h50 := C h27 (T (C h43 h49) (C h30 h7))
  have h51 := S h34
  have h52 := C h10 (T (S h19) (C h43 h20))
  have h53 := h z v1 y
  have h54 := h y v1 v4
  have h55 := T (T h54 h48) h38
  have h56 := R z
  have h57 := C h56 h55
  have h58 := T h8 h57
  have h59 := C h20 (T (T (T (C h27 h58) (S h53)) h17) h52)
  have h60 := h y y v0
  have h61 := h y y z
  have h62 := S h61
  have h63 := S h54
  have h64 := C h7 (T h39 h50)
  have h65 := T (T h37 h64) h63
  have h66 := C h56 h65
  have h67 := T h66 h9
  have h68 := C h56 h67
  have h69 := C h7 (T (T (T (T (T (T h68 h62) h60) h59) h51) h39) h50)
  have h70 := h z z v4
  have h71 := h z z z
  have h72 := S h71
  have h73 := S h70
  have h74 := C h56 h58
  have h75 := S h60
  have h76 := C h20 (T (T (T h31 h18) h53) (C h27 h67))
  have h77 := C h7 (T (T (T (T (T (T h47 h40) h34) h76) h75) h61) h74)
  have h78 := C h56 (T h66 (C h56 (T (T h54 h77) h73)))
  have h79 := C h56 (T (C h56 (T (T h70 h69) h63)) h57)
  have h80 := C (T (T (T (T (T (T (T (T (T (T h37 h64) h77) h73) h71) h79) h68) h62) h60) h59) h51) (T (T (T (T (T (T (T (T (T (T (T (T h47 h40) h34) h76) h75) h61) h74) h78) h72) h70) h69) h48) h38)
  have h81 := h v1 v15 v1
  have h82 := S h81
  have h83 := C h35 h10
  have h84 := C (T (T (T (T (T (T (T (T (T h54 h77) h73) h71) h79) h68) h62) h60) h59) h51) h10
  have h85 := C h10 (C h10 (T h84 h83))
  have h86 := h v1 (M y v1) v1
  have h87 := T (T (T h86 h85) h82) h14
  have h88 := h y y v1
  have h89 := S h88
  have h90 := C h87 (T (T (T (T h21 h24) h42) h41) (C h27 h65))
  have h91 := S h86
  have h92 := C (T (T (T (T (T (T (T (T (T h34 h76) h75) h61) h74) h78) h72) h70) h69) h63) h10
  have h93 := C h20 (T h17 h52)
  have h94 := T h93 h51
  have h95 := C h94 h10
  have h96 := C h10 (C h10 (T h95 h92))
  have h97 := T (T (T h13 h81) h96) h91
  have h98 := C h97 (T (T (T (T (C h27 h55) h29) h28) h25) h22)
  have h99 := C (T (T (T (T (T (T (T h86 h85) h82) h14) h21) h24) h42) h41) h27
  have h100 := C (T (T (T (T (T (T (T h29 h28) h25) h22) h13) h81) h96) h91) h27
  have h101 := R x
  have h102 := C h10 (T (T (T (T (T (T (T (T (T (T (T (T h99 h49) h37) h64) h77) h73) h71) h79) h68) h62) h60) h59) h32)
  have h103 := C h10 (T (T (T (T (T (T (T (T (T (T (T h90 h89) h61) h74) h78) h72) h70) h69) h48) h38) h44) h100)
  have h104 := C h87 (T (T (T (T (T (T (T (T (T h37 h64) h77) h73) h71) h79) h68) h62) h88) h98)
  have h105 := C h97 (T (T (T (C h94 h7) (C (T (T (T (T (T (T (T (T (T (T h34 h76) h75) h61) h74) h78) h72) h70) h69) h48) h38) (T (T (T (T (T (T (T (T (T (T (T (T h37 h64) h77) h73) h71) h79) h68) h62) h60) h59) h51) h39) h50))) h48) h38)
  T (T (T (T (h x x v0) (h v0 (M x (M x v0)) v4)) (C h7 (C h20 (C (T (T (T (C h101 (T (h x v0 z) (C h56 (T (T (h x v1 v4) (C h7 (T (T (C h101 (T (T (T (T (T (T (T (T (T (T (T h46 h45) (C h10 (T (T (T (T h49 h37) h64) h80) h36))) h105) h104) h103) h102) h16) (C (T (T (T (T (T (T (T (T (T (T h37 h64) h77) h73) h71) h79) h68) h62) h60) h59) h32) (T (T (T (T h105 h104) h103) h102) h14))) h95) h92) (C h55 h10))) (C h101 (T (T (T (T (T (C h65 h10) h84) h83) (C (T (T (T (T (T (T (T (T (T (T h93 h76) h75) h61) h74) h78) h72) h70) h69) h48) h38) (T (T (T (T h13 (C h10 (T (T (T (T (T (T (T (T (T (T (T (T h93 h76) h75) h61) h74) h78) h72) h70) h69) h48) h38) h44) h100))) (C h10 (T (T (T (T (T (T (T (T (T (T (T h99 h49) h37) h64) h77) h73) h71) h79) h68) h62) h88) h98))) (C h97 (T (T (T (T (T (T (T (T (T h90 h89) h61) h74) h78) h72) h70) h69) h48) h38))) (C h87 (T (T (T h37 h64) h80) h36))))) (S h16)) h14))) (h x v1 y)))) (S (h y x v4)))))) (S (h z y x))) h12) h11) h7)))) h6) h3

