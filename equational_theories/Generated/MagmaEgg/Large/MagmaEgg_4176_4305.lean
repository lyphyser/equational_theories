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
theorem Equation4176_implies_Equation4305 (G: Type _) [Magma G] (h: Equation4176 G) : Equation4305 G := fun x y z =>
  let v0 := M x y
  let v1 := M y z
  have h2 := h z v1 v0
  have h3 := S h2
  have h4 := R v0
  have h5 := h v0 y z
  have h6 := R x
  have h7 := h y x y
  have h8 := S h7
  have h9 := R y
  have h10 := S (h y v0 x)
  have h11 := h x y z
  have h12 := S h11
  have h13 := C h12 h6
  have h14 := h z v1 x
  have h15 := T h14 h13
  have h16 := C h15 h9
  let v17 := M z v1
  have h18 := h v17 y z
  have h19 := S h18
  have h20 := R z
  have h21 := h v1 v17 y
  have h22 := S h21
  have h23 := h y z v1
  have h24 := C h23 h9
  have h25 := h y z z
  let v26 := M z z
  have h27 := h y (M v26 y) z
  have h28 := h v26 y y
  let v29 := M x v0
  have h30 := h z z v29
  have h31 := S h30
  have h32 := R v29
  have h33 := h x v0 x
  have h34 := h (M (M v0 x) x) x v17
  have h35 := R v17
  have h36 := h v17 x y
  have h37 := h v0 v17 y
  have h38 := S h37
  have h39 := S h14
  have h40 := h x y v0
  let v41 := M y v0
  have h42 := h v0 v41 x
  have h43 := C (T (T h42 (C (T (S h40) h11) h6)) h39) h9
  have h44 := h v41 x y
  have h45 := h y v0 v0
  have h46 := h v0 x y
  have h47 := C h11 h6
  have h48 := h v0 x v0
  have h49 := h v0 v29 v0
  have h50 := h x y x
  have h51 := S h50
  let v52 := M y x
  let v53 := M v52 x
  have h54 := h v29 v53 x
  have h55 := h v53 x v0
  have h56 := C (T (T h50 h55) (C (T (T (T h54 (C (T (T (T (T (C h51 h32) h49) (C (T (T (S h48) h47) h39) h4)) (C (T (T h14 h13) h46) h4)) (S h45)) h6)) h44) h43) h4)) h9
  have h57 := R (M x v17)
  have h58 := h v52 x v17
  have h59 := T (T (T h58 (C (C h57 (T (T (T h7 (C (T h56 h38) h9)) (S h36)) (C h15 h6))) h35)) (S h34)) (S h33)
  have h60 := h z v53 x
  have h61 := h x v0 z
  have h62 := h x v0 v17
  have h63 := h (M v0 v17) x v29
  have h64 := S h5
  have h65 := T (T h64 h56) h38
  have h66 := R (M x v29)
  have h67 := h (M (M v1 v0) z) x v29
  have h68 := h y v53 x
  have h69 := S h46
  have h70 := S h44
  have h71 := C (T (T h14 (C (T h12 h40) h6)) (S h42)) h9
  have h72 := C (T (T (C (T (T (T h71 h70) (C (T (T (T (T h45 (C (T (T h69 h47) h39) h4)) (C (T (T h14 h13) h48) h4)) (S h49)) (C h50 h32)) h6)) (S h54)) h4) (S h55)) h51) h9
  have h73 := T (T (T h33 h34) (C (C h57 (T (T (T (C (T h47 h39) h6) h36) (C (T h37 h72) h9)) h8)) h35)) (S h58)
  have h74 := C (T (T (T (C (T (T (T (T (T (C h9 h73) h68) (C (T (C h51 h9) h5) h6)) h67) (C (C h66 h65) h32)) (S h63)) h35) (S h62)) h61) (C (T (T (C (C h50 h20) h6) (S h60)) (C h20 h59)) h20)) h32
  have h75 := h v17 y v29
  have h76 := h y v0 v1
  have h77 := R v1
  have h78 := h v1 x y
  have h79 := C (T (C h78 h77) (S h76)) h6
  have h80 := h v1 v1 x
  have h81 := h y y z
  have h82 := S h81
  have h83 := h (M v1 y) z z
  have h84 := S h83
  have h85 := C (S h23) h9
  have h86 := R v26
  have h87 := C (C h86 (T h21 h85)) h20
  have h88 := h (M v1 v17) z z
  have h89 := S h75
  have h90 := T (T h37 h72) h5
  have h91 := C (T (T (T (C (T (T (C h20 h73) h60) (C (C h51 h20) h6)) h20) (S h61)) h62) (C (T (T (T (T (T h63 (C (C h66 h90) h32)) (S h67)) (C (T h64 (C h50 h9)) h6)) (S h68)) (C h9 h59)) h35)) h32
  have h92 := S h80
  have h93 := C (T h76 (C (S h78) h77)) h6
  have h94 := h v1 v1 v29
  have h95 := S h94
  have h96 := h v1 v53 x
  have h97 := h x v0 v1
  have h98 := C (T h97 (C (T (T (C (C h50 h77) h6) (S h96)) (C h77 h59)) h77)) h32
  let v99 := M v17 y
  have h100 := R v99
  have h101 := C (T (C (T (T (C h77 h73) h96) (C (C h51 h77) h6)) h77) (S h97)) h32
  have h102 := C (T (C h5 h4) h3) h9
  have h103 := h v0 v0 y
  have h104 := h v0 v0 v17
  have h105 := S h104
  have h106 := C (T h2 (C h65 h4)) h35
  have h107 := C (T (C h90 h4) h3) h35
  have h108 := S h103
  have h109 := C (T h2 (C h64 h4)) h9
  have h110 := h v99 v17 y
  have h111 := h z v1 v17
  have h112 := S h88
  have h113 := C (C h86 (T h24 h22)) h20
  have h114 := h x v0 v0
  let v115 := M y v29
  T (T h114 (C (T (T (T (T (T (T (T (T (C (T (T h103 h102) h16) h6) h10) h45) (C h69 h4)) (C (T (C (h x y v29) h6) (S (h v29 v115 x))) h4)) (S (h v115 x v0))) (C (T (h y v29 v0) (C (T (C (T (C (T h114 (C (T (T (T (T (T (h (M v0 v0) x v17) (C (C h57 (T (T (T (T (T (T h103 h102) h18) h88) h87) h84) h82)) h35)) (C (C h57 (T (T (T (T (T (T h81 h83) h113) h112) (C (T (T h21 h85) (C h25 h9)) h20)) (S h27)) (C h9 (T (T (T (T h28 (C (T (T (T (C (T (T (T (T (T (T (T h81 h83) h113) h112) h19) h75) h74) h31) (T (T (T (T (T (T h30 h91) h89) h71) h70) h93) h92)) (C (T (T (T (T (T (T (T (T h30 h91) h89) h71) h70) h93) h92) h94) h101) (T (T (T h80 h79) h44) h43))) (C (T (T (T (T (T (T (T (T (T h98 h95) h80) h79) h44) h43) h109) h108) h104) h107) h100)) (C (T (T (T h106 h105) h103) h102) h100)) h9)) (S h110)) (C h18 h35)) (S h111))))) h35)) (S (h (M y v17) x v17))) (C (T (T (T (T (C h9 (T (T (T (T h111 (C h19 h35)) h110) (C (T (T (T (C (T (T (T h109 h108) h104) h107) h100) (C (T (T (T (T (T (T (T (T (T h106 h105) h103) h102) h71) h70) h93) h92) h94) h101) h100)) (C (T (T (T (T (T (T (T (T h98 h95) h80) h79) h44) h43) h75) h74) h31) (T (T (T h71 h70) h93) h92))) (C (T (T (T (T (T (T (T h30 h91) h89) h18) h88) h87) h84) h82) (T (T (T (T (T (T h80 h79) h44) h43) h75) h74) h31))) h9)) (S h28))) h27) (C (T (T (C (S h25) h9) h24) h22) h20)) h19) h16) h6)) h10) h4)) h4) (S (h v0 y v0))) h9) h8) h4)) h6)) (S (h v0 y x))) h5) h4)) h3

