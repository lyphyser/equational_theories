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
theorem Equation2519_implies_Equation16 (G: Type _) [Magma G] (h: Equation2519 G) : Equation16 G := fun x y =>
  let v0 := M y x
  let v1 := M x y
  let v2 := M v1 v0
  have h3 := h v0 y v2
  have h4 := S h3
  have h5 := R v2
  have h6 := h x v0 y
  have h7 := R y
  have h8 := C (C h7 h6) h5
  have h9 := h (M v0 v2) x y
  have h10 := S h9
  have h11 := R x
  have h12 := h x x v0
  have h13 := S h12
  have h14 := C h13 h11
  have h15 := C h12 h11
  have h16 := h x x y
  have h17 := C h11 (T (C (S h16) h11) h15)
  have h18 := C (T h17 (C h11 (T h14 (C h6 h11)))) h7
  have h19 := C h11 (T h14 (C h16 h11))
  have h20 := h x y y
  have h21 := S h20
  have h22 := C (T (C h11 (T (C h21 h11) h15)) h19) h7
  let v23 := M y (M v1 y)
  have h24 := h v23 x y
  have h25 := h v23 x x
  have h26 := S h25
  have h27 := S h24
  have h28 := C (T h17 (C h11 (T h14 (C h20 h11)))) h7
  have h29 := S h6
  have h30 := C (T (C h11 (T (C h29 h11) h15)) h19) h7
  have h31 := C (C h7 h29) h5
  have h32 := T (T (T (T (T h3 h31) h9) h30) h28) h27
  have h33 := C h32 h11
  have h34 := C h11 (C h33 h11)
  let v35 := M v0 x
  have h36 := h (M x (M v35 x)) x x
  have h37 := S h36
  have h38 := h v0 x x
  have h39 := C (C h11 (C h38 h11)) h11
  have h40 := h y x x
  have h41 := C (T (T (T h40 h39) h37) h34) (T (C h32 h7) h21)
  have h42 := h (M y (M v0 y)) x x
  have h43 := S h42
  have h44 := h y y x
  have h45 := C (C h11 (C h44 h11)) h11
  have h46 := S h40
  have h47 := C (C h11 (C h46 h11)) h11
  have h48 := h (M x v35) x x
  have h49 := T (T (T (T (T h24 h22) h18) h10) h8) h4
  have h50 := C h49 h11
  let v51 := M y v0
  have h52 := h y v51 x
  have h53 := S h52
  have h54 := C (C h11 (C h53 h11)) h11
  let v55 := M v0 v51
  let v56 := M v51 v55
  have h57 := h v56 x x
  have h58 := h v56 v0 x
  have h59 := S h58
  have h60 := R v0
  have h61 := C (C h60 (C h52 h60)) h11
  have h62 := h v55 v51 v0
  have h63 := S h62
  have h64 := R v51
  have h65 := h v55 x v51
  have h66 := S h65
  have h67 := h y v0 v51
  have h68 := S h67
  let v69 := M v0 (M (M y v51) v0)
  have h70 := h v69 v0 v51
  have h71 := h v69 x v51
  have h72 := C (C h11 (T (C (T (C (C h11 (C h67 h11)) h64) (S h71)) h11) (C (T h70 (C (C h60 (C h68 h60)) h64)) h11))) h64
  let v73 := M x v0
  have h74 := h v73 x v51
  have h75 := C h11 (T (T (T (T (T (T (T (T (T h45 h43) h41) h26) h24) h22) h18) h10) h8) h4)
  have h76 := C (C h64 (T (C h13 h64) (C (T h12 (C (T (T (T h75 h74) h72) h66) h60)) h64))) h60
  let v77 := M x (M v73 x)
  have h78 := h v77 v51 v0
  have h79 := h v77 x v0
  have h80 := S h79
  have h81 := h x y v0
  have h82 := C (C h11 (T (C (S h81) h11) h15)) h60
  let v83 := M y (M v73 y)
  have h84 := h v83 x v0
  have h85 := C (T (T (T (T (T h84 h82) h80) h78) h76) h63) h11
  have h86 := C (T (T (T (T (T (T (T (T h85 h61) h59) h57) h54) h45) h43) h41) h26) h11
  have h87 := C h11 (T h86 h50)
  have h88 := S h84
  have h89 := C (C h11 (T h14 (C h81 h11))) h60
  have h90 := S h78
  have h91 := C (C h11 (C (S h44) h11)) h11
  have h92 := C (C h11 (C (S h38) h11)) h11
  have h93 := C h11 (C h50 h11)
  have h94 := C (T (T (T h93 h36) h92) h46) (T h20 (C h49 h7))
  have h95 := C h11 (T (T (T (T (T (T (T (T (T h3 h31) h9) h30) h28) h27) h25) h94) h42) h91)
  have h96 := S h74
  have h97 := C (C h11 (T (C (T (C (C h60 (C h67 h60)) h64) (S h70)) h11) (C (T h71 (C (C h11 (C h68 h11)) h64)) h11))) h64
  have h98 := C (C h64 (T (C (T (C (T (T (T h65 h97) h96) h95) h60) h13) h64) (C h12 h64))) h60
  have h99 := C (T (T (T (T (T h62 h98) h90) h79) h89) h88) h11
  have h100 := C (C h60 (C h53 h60)) h11
  have h101 := S h57
  have h102 := C (C h11 (C h52 h11)) h11
  have h103 := C (T (T (T (T (T (T (T h87 h48) h47) h102) h101) h58) h100) h99) h11
  have h104 := h v83 x x
  have h105 := S h104
  have h106 := C (T (T (T (T (T (T (T (T h25 h94) h42) h91) h102) h101) h58) h100) h99) h11
  have h107 := C h11 (T h33 h106)
  have h108 := S h48
  have h109 := C (C h11 (C h40 h11)) h11
  have h110 := C (T (T (T (T (T (T (T h85 h61) h59) h57) h54) h109) h108) h107) h11
  have h111 := C (T (T h106 h110) h105) h11
  have h112 := C h13 h7
  have h113 := C h7 (T (T (T (T (T (T (T (T (T (T (T (T (T (T h112 (C h11 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h40 h39) h37) h34) (C h11 (T (T (T (T (T h111 h85) h61) h59) h57) h54))) h75) h74) h72) h66) h62) h98) h90) h79) h89) h88) h104) h103))) h87) h48) h47) h45) h43) h41) h26) h24) h22) h18) h10) h8) h4)
  have h114 := C h12 h7
  have h115 := C (T (T h104 h103) h86) h11
  have h116 := C h11 (T (T (T (T (T h102 h101) h58) h100) h99) h115)
  have h117 := T (T (T (T (T (T (T (T (T (T (T (T (T (T h3 h31) h9) h30) h28) h27) h25) h94) h42) h91) h109) h108) h107) (C h11 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h110 h105) h84) h82) h80) h78) h76) h63) h65) h97) h96) h95) h116) h93) h36) h92) h46))) h114
  have h118 := h x v0 v51
  have h119 := S h118
  let v120 := M x v51
  have h121 := h (M v0 (M v120 v0)) x v51
  have h122 := h x v51 v51
  have h123 := S h122
  let v124 := M v51 (M v120 v51)
  have h125 := h v124 x v51
  have h126 := h v124 y v51
  have h127 := C (T (T (T (T (C (T (C (T (T (T (T (C (T (C h7 h117) (C h7 (T h112 (C h122 h7)))) h64) (S h126)) h125) (C (T (C h11 (T (C h123 h11) h15)) (C h11 (T h14 (C h118 h11)))) h64)) (S h121)) h64) h119) (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h3 h31) h9) h30) h28) h27) h25) h94) h42) h91) h102) h101) h58) h100) h99) h115)) h93) h36) h92) h46) h117
  have h128 := C (T (T (T (T h121 (C (T (C h11 (T (C h119 h11) h15)) (C h11 (T h14 (C h122 h11)))) h64)) (S h125)) h126) (C (T (C h7 (T (C h123 h7) h114)) h113) h64)) h64
  T (T (T (T (T h118 h128) (h (M (M v51 v51) v51) v0 v0)) (C (T (T (T (T (T (T (C h60 (T h127 h113)) h65) h97) h96) h95) h116) (C (T h118 h128) (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h111 h85) h61) h59) h57) h54) h45) h43) h41) h26) h24) h22) h18) h10) h8) h4))) h60)) h127) h113

