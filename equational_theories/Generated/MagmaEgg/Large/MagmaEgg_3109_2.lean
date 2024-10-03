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
theorem Equation3109_implies_Equation2 (G: Type _) [Magma G] (h: Equation3109 G) : Equation2 G := fun x y =>
  let v0 := M y y
  have h1 := h y v0 y
  have h2 := S h1
  have h3 := R v0
  have h4 := h y y y
  have h5 := C h4 h3
  have h6 := C (T (T h5 h2) h4) h3
  let v7 := M y v0
  let v8 := M v7 v0
  have h9 := h v8 y y
  have h10 := S h9
  have h11 := R y
  have h12 := C (S h4) h3
  have h13 := T h1 h12
  have h14 := C h13 h3
  have h15 := T (T h1 h12) h14
  have h16 := T h6 h2
  have h17 := C h16 h15
  have h18 := T h5 h2
  have h19 := C h11 h18
  have h20 := C h18 h3
  have h21 := C h11 h20
  have h22 := C h13 (T (T h17 h21) h19)
  let v23 := M v8 y
  have h24 := R v23
  have h25 := C (T (C (T (T (T h22 h20) h5) h2) h24) h22) h11
  have h26 := C (T h25 h17) h15
  have h27 := h v23 y y
  have h28 := C (T (T h25 h27) h26) h11
  have h29 := C (T h27 h28) h11
  have h30 := h v0 y y
  have h31 := h v7 y y
  have h32 := S h31
  have h33 := C h15 h16
  have h34 := C h11 h14
  have h35 := C h11 h13
  have h36 := C h18 (T (T h35 h34) h33)
  have h37 := C (T h36 (C (T (T (T h1 h12) h14) h36) h24)) h11
  have h38 := C (T h33 h37) h16
  have h39 := C (T h38 h28) h11
  have h40 := C (C h34 h14) h11
  have h41 := C (C h35 h13) h11
  have h42 := T (T (T (T (T (T h41 h40) h39) h10) h20) h5) h2
  have h43 := C (C h21 h20) h11
  have h44 := C (T (C (T (T h38 (S h27)) h37) h11) h26) h11
  have h45 := C (T (T (T (T (T h1 h12) h14) h9) h44) h43) h42
  let v46 := M (M v0 y) y
  let v47 := M y v46
  have h48 := h v47 y y
  have h49 := S h48
  have h50 := T (T (T h45 h32) h5) h2
  have h51 := R v47
  have h52 := C (C h19 h18) h11
  have h53 := T (T (T (T (T (T h1 h12) h14) h9) h44) h43) h52
  have h54 := C (T (T (T (T (T h40 h39) h10) h20) h5) h2) h53
  have h55 := C h11 (T (T (T (T (T (T h41 h40) h39) h10) h20) h31) h54)
  have h56 := C (T (T (T (T h1 h12) h31) h54) h55) h51
  have h57 := C (T (T h55 h56) (C h56 h50)) h42
  have h58 := T (T (T (T (T h57 h49) h45) h32) h5) h2
  have h59 := C h58 h11
  let v60 := M v47 v46
  let v61 := M v60 y
  have h62 := R x
  have h63 := T (T (T h1 h12) h31) h54
  have h64 := C h63 (T (T (T (T (T (T (T (T h57 h49) h45) h32) h14) h9) h44) h43) h52)
  have h65 := R v60
  have h66 := C (T (T (T (T (T (T h64 h57) h49) h45) h32) h5) h2) h65
  have h67 := C h11 (T (T (T (T (T (T h45 h32) h14) h9) h44) h43) h52)
  have h68 := C (T (T (T (T h67 h45) h32) h5) h2) h51
  have h69 := C (T (T (C h68 h63) h68) h67) h53
  have h70 := T (T (T (T (T h1 h12) h31) h54) h48) h69
  have h71 := C (T (T (C h66 h70) h66) h64) h11
  have h72 := h v60 y y
  have h73 := T (T (T (T (T (T (T h1 h12) h31) h54) h48) h69) h72) h71
  let v74 := M y x
  have h75 := h x v74 y
  have h76 := S h75
  have h77 := R v74
  have h78 := h x y x
  have h79 := C h78 h77
  have h80 := C h50 (T (T (T (T (T (T (T (T h41 h40) h39) h10) h20) h31) h54) h48) h69)
  have h81 := C (T (T (T (T (T (T h1 h12) h31) h54) h48) h69) h80) h65
  have h82 := S h72
  have h83 := C (T (T h80 h81) (C h81 h58)) h11
  have h84 := T (T (T (T (T h59 h30) h29) h10) h6) h2
  have h85 := C h70 h84
  have h86 := R v61
  have h87 := C (T (T (T (T (T (T (T (T h85 h83) h82) h57) h49) h45) h32) h5) h2) h86
  have h88 := C h58 h73
  have h89 := C (T (T (T (T (T (T (T (T h1 h12) h31) h54) h48) h69) h72) h71) h88) h86
  have h90 := C (T (T (T h72 h71) h88) h89) h62
  have h91 := C h62 (T (T (T h90 (C (T (T (T (T (T h87 h85) h83) h82) h80) h81) h62)) (C (T (T (T (T (T h66 h64) h57) h49) h55) h56) h62)) (C (T (T (T (T (T h68 h67) h45) h32) h5) h2) h62))
  let v92 := M v60 x
  have h93 := R v92
  have h94 := T (T h91 h79) h76
  have h95 := C h94 h93
  have h96 := T (T (T h95 h91) h79) h76
  have h97 := h v92 x x
  have h98 := S h97
  have h99 := C (T (T (T h87 h85) h83) h82) h62
  have h100 := C (T (T (T (T (T h66 h64) h72) h71) h88) h89) h62
  have h101 := C (T (T (T (T (T h68 h67) h48) h69) h80) h81) h62
  have h102 := C (T (T (T (T (T h1 h12) h31) h54) h55) h56) h62
  have h103 := C h62 (T (T (T h102 h101) h100) h99)
  have h104 := C (S h78) h77
  have h105 := T (T h75 h104) h103
  have h106 := C h105 h93
  have h107 := T (T (T h75 h104) h103) h106
  have h108 := C h105 (T (C (C h107 h62) h62) h98)
  have h109 := h (M x (M (M x x) x)) x y
  have h110 := T (T (T (T h108 h95) h91) h79) h76
  have h111 := C (C h96 h62) h62
  have h112 := C h94 (T h97 h111)
  have h113 := T (T (T (T h75 h104) h103) h106) h112
  have h114 := C (C h96 h113) h113
  have h115 := C (T (T h99 h97) h114) h11
  have h116 := h v61 y x
  have h117 := C (C h107 h110) h110
  have h118 := S h116
  have h119 := C (T (T h117 h98) h90) h11
  T (T (T (T (T (T (T (T (T (T (T h75 h104) (C h62 (T (T (T (T (T h102 h101) h100) h99) h97) h111))) h109) (C (T (T (T h119 h118) (h v61 x y)) (C (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (C (T (T (T (C h107 h84) (C (T (T (T (T (T h112 h109) (C (T (T (T (T (T (T (T (T (T h119 h118) h83) h82) h57) h49) h45) h32) h5) h2) h113)) (C h70 h110)) h97) h114) h11)) h119) h118) h84) (S (h v46 y y))) h41) h40) h39) h10) h20) h31) h54) h48) h69) h72) h71) h116) h115) (C (T (T (T (T (T h117 h98) (C h58 h113)) (C (T (T (T (T (T (T (T (T (T h1 h12) h31) h54) h48) h69) h72) h71) h116) h115) h110)) (S h109)) h108) h11)) (C h96 h73)) h73) h62)) h62)) (S (h v61 x x))) h59) h30) h29) h10) h6) h2

