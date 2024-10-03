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
theorem Equation3120_implies_Equation2180 (G: Type _) [Magma G] (h: Equation3120 G) : Equation2180 G := fun x y z =>
  let v0 := M x z
  have h1 := R v0
  let v2 := M y z
  let v3 := M v2 y
  have h4 := h v3 v2 v2
  have h5 := S h4
  have h6 := R v2
  let v7 := M v3 v0
  have h8 := h v3 y v7
  have h9 := S h8
  have h10 := R v7
  have h11 := R y
  have h12 := R v3
  have h13 := h y v2 v3
  have h14 := S h13
  have h15 := C h14 h12
  have h16 := h v2 v3 v3
  have h17 := C (T h16 h15) h11
  have h18 := C (C h17 h10) h10
  have h19 := h z y v7
  have h20 := T (T h19 h18) h9
  have h21 := h v2 v3 z
  have h22 := S h21
  have h23 := S h19
  have h24 := S h16
  have h25 := C h13 h12
  have h26 := C (T h25 h24) h11
  have h27 := C (C h26 h10) h10
  have h28 := T (T h8 h27) h23
  let v29 := M v3 v2
  have h30 := R (M v29 v3)
  have h31 := h y v2 v2
  have h32 := S h31
  have h33 := h z y v2
  have h34 := h z y v3
  have h35 := S h34
  have h36 := C (T h35 h33) h6
  have h37 := C (T (T (T h8 h27) h23) h34) h6
  have h38 := C (T (T (T (T h37 h36) h32) h13) (C h30 h28)) h28
  have h39 := R v29
  have h40 := C h39 h20
  have h41 := C (T (T h40 h38) h22) h20
  have h42 := h y v2 z
  have h43 := h y v2 y
  have h44 := S h43
  have h45 := C (T (T (T h35 h19) h18) h9) h6
  have h46 := S h33
  have h47 := C (T h46 h34) h6
  have h48 := C (C (T (T h31 h47) h45) h11) h11
  have h49 := C (T (T (T h48 h44) h42) h41) h6
  have h50 := h y y v2
  have h51 := C (T (T (T h48 h44) h50) (C h49 h6)) h6
  have h52 := C (C (T (T h37 h36) h32) h11) h11
  have h53 := S h42
  have h54 := C h39 h28
  have h55 := C (T (T (T (T (C h30 h20) h14) h31) h47) h45) h20
  have h56 := C (T (T h21 h55) h54) h28
  have h57 := C (T (T (T h56 h53) h43) h52) h6
  have h58 := T (T h57 h51) h5
  have h59 := C (T (T (T (C h57 h6) (S h50)) h43) h52) h6
  have h60 := h v3 v3 v3
  have h61 := S h60
  have h62 := C (C h34 h12) h20
  have h63 := T (T (T (T h62 h61) h4) h59) h49
  have h64 := C (C h35 h12) h28
  have h65 := h v3 z v2
  have h66 := S h65
  have h67 := h y y v3
  have h68 := S h67
  have h69 := C (T (T (T (T h37 h36) h32) h43) h52) h20
  have h70 := h v2 v3 y
  have h71 := C (T h42 h41) h6
  have h72 := C (T (T (T (T (T (C (T (T (T (T (T h71 h57) h51) h5) h17) (C (T (T (T h25 h24) h21) h55) h11)) h11) (S h70)) h21) h55) h54) h69) h12
  have h73 := R (M (M y v2) y)
  have h74 := C h73 h20
  have h75 := R z
  have h76 := C (T h56 h53) h6
  have h77 := C (T (T (C h34 h11) (C (T (T (T (T (T (T h35 h19) h18) h9) h4) h59) h49) h11)) (C h76 h11)) h75
  have h78 := h y z v2
  have h79 := h y z v3
  have h80 := C (T (T (C h71 h11) (C (T (T (T (T (T (T h57 h51) h5) h8) h27) h23) h34) h11)) (C h35 h11)) h75
  have h81 := C h73 h28
  have h82 := C (T (T (T (T h48 h44) h31) h47) h45) h28
  have h83 := C (T (T (T (T (T h82 h40) h38) h22) h70) (C (T (T (T (T (T (C (T (T (T h38 h22) h16) h15) h11) h26) h4) h59) h49) h76) h11)) h12
  have h84 := R (M (M y y) y)
  have h85 := C (T (T (T (C (T (T (T (T (T h21 h55) h54) h69) (C h84 h28)) (C (T (T (T (T (T h48 h44) h67) h83) h81) h80) h20)) h20) (S h79)) h78) (C (T (T (T (T (T (T (C (T (T (T (T (T (T h77 h74) h72) h68) h31) h47) h45) h6) h46) h19) h18) h9) h60) h64) h6)) h6
  have h86 := T (T (T h85 h66) h60) h64
  have h87 := C (T (T (T (C (T (T (T (T (T (T h62 h61) h8) h27) h23) h33) (C (T (T (T (T (T (T h37 h36) h32) h67) h83) h81) h80) h6)) h6) (S h78)) h79) (C (T (T (T (T (T (C (T (T (T (T (T h77 h74) h72) h68) h43) h52) h28) (C h84 h20)) h82) h40) h38) h22) h28)) h6
  have h88 := h z y x
  have h89 := R x
  have h90 := C h58 h89
  have h91 := C h63 h89
  have h92 := C h86 h89
  have h93 := h z x x
  have h94 := h v0 v7 v0
  have h95 := S h94
  have h96 := h z y v0
  have h97 := h z v2 v7
  have h98 := S h96
  have h99 := h v0 v7 v7
  have h100 := C (C (T h99 (C (T (T (C (C (T (T (T (T (T h98 h19) h18) h9) h65) h87) h10) h10) (S h97)) h96) h10)) h1) h1
  have h101 := T h100 h95
  have h102 := h v0 v0 x
  have h103 := C (T (T (T (T (T (T (C (T (T (T h100 h95) h102) (C (C h101 h89) h89)) h89) (S h93)) h19) h18) h9) h65) h87) h89
  have h104 := h v0 v0 z
  have h105 := S h104
  have h106 := C (C (T (C (T (T h98 h97) (C (C (T (T (T (T (T h85 h66) h8) h27) h23) h96) h10) h10)) h10) (S h99)) h1) h1
  have h107 := S h102
  have h108 := C (T (T (T (T (T (T h85 h66) h8) h27) h23) h93) (C (T (T (T (C (C (T h94 h106) h89) h89) h107) h94) h106) h89)) h89
  have h109 := C (T (T (T h62 h61) h65) h87) h89
  have h110 := C (T (T (T (T h57 h51) h5) h60) h64) h89
  have h111 := C (T (T h4 h59) h49) h89
  have h112 := C (T (T (T (T (T (T h111 h110) h109) h108) h107) h94) h106) h28
  have h113 := h x v3 v3
  have h114 := S h113
  have h115 := C (T (T (T (T (T (T h100 h95) h102) h103) h92) h91) h90) h20
  have h116 := C (T (T (T (T (T (T h111 h110) h109) h108) h107) h104) (C h115 h20)) h12
  have h117 := h x v3 v0
  T (T (T (T (T h117 (C (T (T (T (C (T (T (T h116 h114) h117) (C (T (C (T (T (T h112 (C (R (M (M v0 v0) v0)) h20)) (C h101 h28)) (C h1 h20)) h1) (C (C h1 h28) h1)) h1)) h1) (S (h z v0 v0))) h88) (C (T (T (T (T (T (T h111 h110) h109) h108) h107) h104) (C (T (T h115 h116) h114) h20)) h89)) h1)) (C (T (T (T (T (T (T (C (T (T (T (T (T (T (C (T (T h113 (C (T (T (T (T (T (T (C h112 h28) h105) h102) h103) h92) h91) h90) h12)) h112) h28) h105) h102) h103) h92) h91) h90) h89) (S h88)) h19) h18) h9) h65) h87) h1)) (C h86 h1)) (C h63 h1)) (C h58 h1)

