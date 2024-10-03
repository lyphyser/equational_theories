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
theorem Equation2170_implies_Equation2573 (G: Type _) [Magma G] (h: Equation2170 G) : Equation2573 G := fun x y z =>
  let v0 := M z x
  let v1 := M v0 y
  let v2 := M y v1
  let v3 := M v2 z
  let v4 := M v3 v0
  have h5 := R v4
  let v6 := M v0 v3
  have h7 := h (M v6 v3) v1 v2
  have h8 := R (M v2 v1)
  have h9 := R v3
  let v10 := M v1 v2
  have h11 := h v6 v1 v10
  let v12 := M v10 v1
  have h13 := R v12
  have h14 := R v6
  have h15 := R v10
  have h16 := h v1 y v1
  have h17 := S h16
  have h18 := C h17 h15
  let v19 := M v1 y
  have h20 := h v19 v2 v1
  have h21 := h y z x
  have h22 := S h21
  have h23 := h v1 x z
  have h24 := C (S h23) h22
  let v25 := M x z
  have h26 := h v0 v25 v1
  have h27 := h v0 v2 z
  have h28 := S h27
  let v29 := M z v2
  have h30 := h v29 v3 v0
  have h31 := h v12 z v2
  have h32 := T h31 (C (T (C (T h30 (C (T (T (T (T h28 h26) h24) h20) h18) h14)) h13) (S h11)) h9)
  have h33 := h v10 v0 y
  have h34 := S h33
  let v35 := M y v0
  have h36 := h v35 v1 v10
  have h37 := R v0
  have h38 := h y v0 y
  have h39 := S h38
  have h40 := R v35
  have h41 := C h16 h15
  have h42 := C (T h41 (S h20)) h40
  have h43 := T (T h33 h42) h39
  have h44 := C h43 h37
  have h45 := h v0 v1 v2
  have h46 := h x z x
  have h47 := h v25 v0 y
  have h48 := S h47
  have h49 := T (T (T h33 h42) h39) h21
  have h50 := C h49 h40
  have h51 := h v2 v0 y
  have h52 := R v1
  have h53 := C h43 h52
  have h54 := T (T (T h53 h51) h50) h48
  let v55 := M v0 x
  have h56 := R v55
  have h57 := C (T h20 h18) h40
  have h58 := T (T h38 h57) h34
  have h59 := C h58 h52
  let v60 := M z v3
  have h61 := R v60
  have h62 := R z
  have h63 := h z y v1
  have h64 := T h26 h24
  have h65 := h v4 v2 z
  have h66 := S h65
  have h67 := R v29
  have h68 := h v3 z x
  have h69 := S h68
  have h70 := h v25 v0 v3
  have h71 := h v12 v1 v2
  have h72 := S h71
  have h73 := C (T (T h44 h36) (C h34 h13)) h8
  have h74 := S h26
  have h75 := C h23 h21
  have h76 := h v19 v2 v3
  have h77 := S h76
  let v78 := M v3 v2
  have h79 := R v78
  have h80 := h v3 y v1
  have h81 := C (T (T (T (T (T (T (T (T (T (T (T (T (C h80 h79) h77) h75) h74) h45) h73) h72) h53) h51) h50) h48) h70) (C h69 h5)) h67
  have h82 := h v78 v2 z
  have h83 := C h9 (T (T (T (T h82 h81) h66) (C h9 h64)) (S h63))
  have h84 := S h80
  have h85 := C h84 h79
  have h86 := S h45
  have h87 := C h58 h37
  have h88 := S h36
  have h89 := C (T (T (C h33 h13) h88) h87) h8
  have h90 := T (T h45 h73) h72
  have h91 := T h75 h74
  have h92 := S h82
  have h93 := S h51
  have h94 := C (T (T (T h22 h38) h57) h34) h40
  have h95 := C (T (T (T (T (T (T (T (T (T (T h47 h94) h93) h59) h71) h89) h86) h26) h24) h76) h85) h67
  have h96 := C (T (C h68 h5) (S h70)) h67
  have h97 := C h9 h91
  have h98 := h z z x
  have h99 := T (T h51 h50) h48
  have h100 := R (M v0 z)
  have h101 := C h80 (T (T (T (T (T (T (T (C h100 h99) (S h98)) h63) h97) h65) h96) h95) h92)
  have h102 := T (T (T h47 h94) h93) h59
  have h103 := C h9 (T (T h98 (C h100 h102)) (C h100 h53))
  have h104 := C h14 h54
  have h105 := C h14 h59
  have h106 := S h30
  let v107 := M v2 v3
  have h108 := R v107
  have h109 := h v6 z x
  have h110 := R v25
  have h111 := h v25 z v2
  have h112 := C h108 h91
  have h113 := T (T (T (T (T (T h47 h94) h93) h59) h71) h89) h86
  have h114 := C h108 h64
  let v115 := M v107 v0
  let v116 := M v55 v2
  T (T (T (T (T h46 (C h56 h102)) (C h56 h53)) (h v116 v0 v3)) (C (T (T (T (T (C (C (T (T (T h45 h73) h72) h53) h9) (R v116)) (C (T (T (T (C h99 h9) (h (M v25 v3) v3 z)) (C (T (T (T (T (T (C (R (M v3 z)) (C h113 h9)) (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h103 h101) h77) h75) h74) h45) h73) h72) h53) (h v2 v0 v3)) (C (T (T (T (T (T (T h105 h104) h69) h80) h112) (h v115 v3 z)) (C (T (T (C (T (T (T (T (T (T (T h103 h101) h77) h75) h74) h45) h73) h72) (R v115)) (C h13 (T h114 h84))) (C (T (T h71 h89) h86) h9)) h61)) h5)) (S (h v60 v0 v3))) (C (T (T (T (T (T h63 h97) h65) h96) h95) h92) h9)) (C h79 (T h80 h112))) (C h79 (T (T (T h114 h84) h68) (C h14 h113)))) (C h79 (T (T (T (T (T (T (C h14 (T (T (T (T (T (T h45 h73) h72) h53) h51) h50) h48)) h69) h80) h112) (C h108 h90)) (C h108 h32)) (C h108 (T (T (T (T (C (T h109 (C (T (C h27 h14) h106) h110)) h9) (S h111)) h47) h94) h93))))) (C h79 (T (T (T (T (C h108 (T (T (T (T h51 h50) h48) h111) (C (T (C (T h30 (C h28 h14)) h110) (S h109)) h9))) (C h108 (T (T (T (T h7 (C (T (T (C h33 (T (C (T h11 (C (T (C (T (T (T h41 (C (T h17 h23) h49)) h74) h27) h14) h106) h13)) h9) (S h31))) h88) h87) h8)) h86) h26) h24))) h84) h68) (C h14 (T (T h47 h94) h93))))) (C (T (T h82 h81) h66) (R (M v6 v2)))) (C h5 (T (T (T h105 h104) h69) (C (T (T (T (T (T (T (T (T h59 h71) h89) h86) h26) h24) h76) h85) h83) h62)))) (C h5 (C (T (T h103 h101) h77) h62))) h14)) (S (h (M v19 z) v3 v0))) (C h91 h62)) (C h90 h62)) (C (T (T (T (T (T (T (T h71 h89) h86) h26) h24) h76) h85) h83) h62)) h61)) (S (h z v3 z))) (T (T (C h56 h59) (C h56 h54)) (S h46)))) h45) (C (T (T h44 h36) (C h34 h32)) h8)) (S h7)) h5)) (S (h v3 v0 v3))

