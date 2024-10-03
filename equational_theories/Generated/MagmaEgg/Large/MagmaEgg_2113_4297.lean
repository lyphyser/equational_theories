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
theorem Equation2113_implies_Equation4297 (G: Type _) [Magma G] (h: Equation2113 G) : Equation4297 G := fun x y z =>
  let v0 := M z z
  let v1 := M y v0
  let v2 := M x y
  let v3 := M x v2
  have h4 := h v1 v3 v1
  have h5 := S h4
  let v6 := M v3 v1
  have h7 := R v6
  have h8 := R v1
  have h9 := h v6 v1 v0
  let v10 := M v1 v0
  have h11 := R v10
  have h12 := R v0
  have h13 := h v1 (M (M y v1) v0) v1
  have h14 := S h13
  have h15 := h v1 y v0
  have h16 := C (C h15 h8) h15
  let v17 := M v1 v1
  have h18 := h v17 v3 v0
  have h19 := S h18
  let v20 := M v3 v0
  have h21 := R v20
  have h22 := R v17
  have h23 := h v3 (M (M x v1) v2) v3
  have h24 := S h23
  have h25 := h v1 x v2
  have h26 := R v3
  have h27 := C (C h25 h26) h25
  have h28 := h v3 (M (M x z) v2) v3
  have h29 := S h28
  have h30 := h z x v2
  have h31 := C (C h30 h26) h30
  have h32 := T h31 h29
  have h33 := C h8 h32
  have h34 := C h33 h8
  have h35 := C (T (T h34 h27) h24) h22
  let v36 := M (M z v3) z
  have h37 := h v36 v1 v1
  have h38 := R z
  have h39 := C (C h38 h32) h38
  have h40 := C (T (T h39 h37) h35) h12
  have h41 := h v36 z z
  have h42 := S h30
  have h43 := C (C h42 h26) h42
  have h44 := C (T (T (T h28 h43) h41) h40) h21
  have h45 := C (T h44 h19) h8
  have h46 := h v20 v3 v1
  have h47 := S h37
  have h48 := T h28 h43
  have h49 := C h8 h48
  have h50 := C h49 h8
  have h51 := S h25
  have h52 := C (C h51 h26) h51
  have h53 := C (T (T h23 h52) h50) h22
  have h54 := C (T (T (T h53 h47) h31) h29) h12
  have h55 := S h41
  have h56 := C (C h38 h48) h38
  have h57 := C (T (T h53 h47) h56) h12
  have h58 := C (T (T (T h28 h43) h37) h35) h12
  have h59 := T (T h58 h57) h55
  have h60 := h v20 z z
  have h61 := C (C (T (C (T (T (T (T (T (T h28 h43) h41) h40) h54) h60) (C (T (T (T (T (T (T (C (C h38 h59) h38) h39) h41) h40) h54) h46) (C (T (T h45 h16) h14) h7)) h12)) h11) (S h9)) h8) h7
  have h62 := h v10 v3 v1
  have h63 := h v10 v1 v2
  have h64 := S h63
  let v65 := M v1 v2
  have h66 := R v65
  have h67 := R v2
  have h68 := S h62
  have h69 := T (T h41 h40) h54
  have h70 := C (T (T (T h57 h55) h31) h29) h21
  have h71 := C (T h18 h70) h8
  have h72 := S h15
  have h73 := C (C h72 h8) h72
  have h74 := C (C (T h9 (C (T (T (T (T (T (T (C (T (T (T (T (T (T (C (T (T h13 h73) h71) h7) (S h46)) h58) h57) h55) h56) (C (C h38 h69) h38)) h12) (S h60)) h58) h57) h55) h31) h29) h11)) h8) h7
  have h75 := C h8 (T (T h4 h74) h68)
  have h76 := h v2 x y
  have h77 := S h76
  have h78 := h y v2 v2
  let v79 := M v2 v2
  have h80 := R v79
  have h81 := h y x y
  have h82 := h v79 y v0
  have h83 := h v2 (M v3 y) v2
  have h84 := C (T (T h83 (C (T (T (C h77 h67) h82) (C (C (T (C h81 h80) (S h78)) h12) h8)) h77)) (C h75 h67)) h66
  have h85 := h v65 v2 v0
  have h86 := R (M v2 v0)
  have h87 := S h83
  have h88 := C (T (T (C (C (T h78 (C (S h81) h80)) h12) h8) (S h82)) (C h76 h67)) h76
  have h89 := C h8 (T (T h62 h61) h5)
  have h90 := C h89 h67
  have h91 := C (T (T h90 h88) h87) h66
  have h92 := h v10 v1 v1
  have h93 := S h92
  have h94 := C (T (T (T h13 h73) h71) (C (T (T h44 h19) h75) h8)) h22
  have h95 := C (T (T (T (C (T (T h89 h18) h70) h8) h45) h16) h14) h22
  have h96 := h y v3 v2
  have h97 := S h96
  let v98 := M v3 v2
  have h99 := R v98
  have h100 := h v98 v2 v0
  have h101 := T (T (T h100 (C (C (T (C h76 h99) h97) h12) h86)) (C (T (T (T (T h4 h74) h68) (C (T (T (T (T h4 h74) h68) h92) h95) h12)) (C (T (T (T h94 h93) h63) h91) h12)) h86)) (S h85)
  have h102 := C h8 h59
  have h103 := C h8 h69
  have h104 := R y
  T (T (T (T (T (T (T (T (T (T (T (T h23 h52) h50) (C h103 h8)) (C h102 (T (T (T (T (T (T h4 h74) h68) h63) h91) (C h76 (T (T (T h85 (C (T (T (T (T (C (T (T (T h84 h64) h92) h95) h12) (C (T (T (T (T h94 h93) h62) h61) h5) h12)) h62) h61) h5) h86)) (C (C (T h96 (C h77 h99)) h12) h86)) (S h100)))) h97))) (C h33 h104)) (h (M (M v1 v3) y) v3 v2)) (C (T (T (T (C (T (T (T (C h26 (T (T (T (T (T (T (T (T (T (T (C h49 h104) (C h103 (T (T (T (T (T (T h96 (C h77 h101)) h84) h64) h62) h61) h5))) (C h102 h8)) h34) h27) h24) h28) h43) h41) h40) h54)) h44) h19) h75) h67) h90) h88) h87) h101)) h84) h64) h62) h61) h5

