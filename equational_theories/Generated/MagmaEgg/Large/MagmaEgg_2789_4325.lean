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
theorem Equation2789_implies_Equation4325 (G: Type _) [Magma G] (h: Equation2789 G) : Equation4325 G := fun x y z =>
  let v0 := M z z
  let v1 := M y v0
  let v2 := M x z
  have h3 := R v1
  have h4 := h z x v1
  let v5 := M y x
  let v6 := M x v5
  have h7 := h x v6 v6
  have h8 := S h7
  let v9 := M x v6
  have h10 := h v6 (M v9 v2) v6
  have h11 := S h10
  have h12 := R v6
  have h13 := h z x v6
  have h14 := C (C h13 h13) h12
  have h15 := T h14 h11
  have h16 := R x
  have h17 := h v5 (M v6 v2) v5
  have h18 := S h17
  have h19 := R v5
  have h20 := h z x v5
  have h21 := C (C h20 h20) h19
  have h22 := T h21 h18
  have h23 := R v0
  have h24 := C h23 h22
  let v25 := M x v0
  have h26 := h v0 (M v25 v2) v0
  have h27 := h z x v0
  have h28 := T (C (C h27 h27) h23) (S h26)
  have h29 := C h28 h24
  have h30 := S h20
  have h31 := C (C h30 h30) h19
  have h32 := T h17 h31
  have h33 := C h23 h32
  have h34 := h (M v0 v5) v0 v0
  have h35 := S h34
  have h36 := S h27
  have h37 := T h26 (C (C h36 h36) h23)
  have h38 := C h37 h33
  have h39 := C (T (T (T h17 h31) h33) h38) h23
  have h40 := C h37 (T (T h39 h35) h33)
  let v41 := M x x
  have h42 := h x (M v41 v2) x
  have h43 := S h42
  have h44 := h z x x
  have h45 := C (C h44 h44) h16
  have h46 := T h45 h43
  have h47 := C h46 (T (T (T (T h40 h29) h24) h21) h18)
  have h48 := C h47 h16
  have h49 := h (M v5 v0) v0 x
  have h50 := C (T (T (T h29 h24) h21) h18) h23
  have h51 := C h28 (T (T (T (T h40 h29) h24) h34) h50)
  have h52 := C h28 (T (T h24 h34) h50)
  have h53 := S h49
  have h54 := S h44
  have h55 := C (C h54 h54) h16
  have h56 := T h42 h55
  have h57 := C h56 (T (T (T (T h17 h31) h33) h38) h52)
  have h58 := C h57 h16
  have h59 := C h37 (T (T (T (T (T (T h58 h53) h39) h35) h33) h38) h52)
  have h60 := R (M v0 x)
  have h61 := C h28 (T (T (T (T (T (T h40 h29) h24) h34) h50) h49) h48)
  have h62 := C h37 (T (T (T (T h39 h35) h33) h38) h52)
  have h63 := T (T (T (T (T (T (T (T h58 h53) h39) h35) h33) h38) h52) h62) h61
  have h64 := T (T (C h56 h63) (C h60 (T h59 h51))) h47
  have h65 := C (C h12 h64) (T (T (T (T (T h17 h31) h34) h50) h49) h48)
  let v66 := M v6 x
  have h67 := h v66 x v5
  have h68 := C (T (T (T (T (T h34 h50) h49) h48) h67) h65) h15
  have h69 := S h13
  have h70 := C (C h69 h69) h12
  have h71 := T h10 h70
  have h72 := C h32 h71
  have h73 := h (M v5 v6) v0 v0
  have h74 := S h73
  have h75 := C h22 h15
  have h76 := S h67
  have h77 := T (T (T (T (T (T (T (T h59 h51) h40) h29) h24) h34) h50) h49) h48
  have h78 := C (C h12 (T (T h57 (C h60 (T h62 h61))) (C h46 h77))) (T (T (T (T (T h58 h53) h39) h35) h21) h18)
  have h79 := C (T (T (T (T (T h78 h76) h58) h53) h39) h35) h71
  have h80 := C h23 (T (T h7 h79) h75)
  have h81 := C h37 (T (T (T (T (T h72 h68) h8) h42) h55) h80)
  have h82 := C (T (T (T h42 h55) h80) h81) h23
  have h83 := h v6 v0 v5
  have h84 := S h83
  have h85 := h v25 v0 y
  have h86 := h y (M (M x y) v2) y
  have h87 := S h86
  have h88 := R y
  have h89 := h z x y
  have h90 := C (C h89 h89) h88
  have h91 := T h90 h87
  have h92 := C h23 (T (T h72 h68) h8)
  have h93 := C h28 (T (T (T (T (T h92 h45) h43) h7) h79) h75)
  have h94 := C (T (T (T h93 h92) h45) h43) h23
  have h95 := T (T (T (T h42 h55) h80) h81) (C h28 (T (T (T (T (T (T (T h92 h45) h43) h7) h79) h75) h73) h94))
  have h96 := S h89
  have h97 := C (C h96 h96) h88
  have h98 := T h86 h97
  have h99 := C (T (T (T (T (C (T (T h21 h18) (C h98 h95)) h91) (S h85)) h82) h74) h72) h19
  have h100 := h y v0 v5
  have h101 := C h28 (T (T (T (T h90 h87) h100) h99) h84)
  have h102 := h y v0 v0
  have h103 := S h102
  have h104 := S h100
  have h105 := C (T (T (T (T h75 h73) h94) h85) (C (T (T (C h91 (T (T (T (T (C h37 (T (T (T (T (T (T (T h82 h74) h72) h68) h8) h42) h55) h80)) h93) h92) h45) h43)) h17) h31) h98)) h19
  have h106 := C h37 (T (T (T (T h83 h105) h104) h86) h97)
  have h107 := C (T (T h10 h70) h106) h23
  have h108 := h x x v6
  have h109 := R v41
  have h110 := C (T (T h101 h14) h11) h23
  T (T (T (T (T (T (T (T h83 h105) h104) h102) h110) (h (M v6 v0) v5 v1)) (C (T (C (R (M v5 v1)) (T (T (T (T (T (T (T (C h32 (T (T (T (T (T (T (T (T h107 h103) h100) h99) h84) h10) h70) h106) (C h28 (T (T (T h90 h87) h102) h110)))) (C (T (T (T (T (T (T (T h34 h50) h49) h48) h67) h65) (h (M (M v6 v6) v66) x x)) (C (T (T (T (T (T (C h109 (T (C h56 (T (T (T (T (T (T (T (T (T (T (T (T h78 h76) h58) h53) h39) h35) h33) h38) h52) h62) h61) (C h37 h63)) (C h28 (T (T (T (T (T (T (T (T (T (T h59 h51) h40) h29) h24) h34) h50) h49) h48) h67) h65)))) (C h46 (T (T (T (T (T (T (T (T (T (T (C h37 (T (T (T (T (T (T (T (T (T (T h78 h76) h58) h53) h39) h35) h33) h38) h52) h62) h61)) (C h28 h77)) h59) h51) h40) h29) h24) h34) h50) h49) h48)))) (C h109 h64)) (C (C h108 h108) h12)) (S (h v6 (M v9 v41) v6))) h10) h70) h95)) (T (T (T (C h37 (T (T (T h107 h103) h86) h97)) h101) h14) h11))) (S (h v25 v0 v6))) h82) h74) h72) h68) h8)) (S (h v0 y x))) h3)) (C (C h4 h4) h3)) (S (h v1 (M (M x v1) v2) v1))

