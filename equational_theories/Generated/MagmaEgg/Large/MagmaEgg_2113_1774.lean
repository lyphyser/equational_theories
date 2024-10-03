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
theorem Equation2113_implies_Equation1774 (G: Type _) [Magma G] (h: Equation2113 G) : Equation1774 G := fun x y z =>
  let v0 := M y x
  let v1 := M v0 z
  let v2 := M y z
  let v3 := M v2 v1
  let v4 := M v0 v3
  have h5 := R v4
  have h6 := R v3
  have h7 := h x y z
  have h8 := R v2
  have h9 := h v1 (M (M v0 v1) z) v1
  have h10 := S h9
  have h11 := h v1 v0 z
  have h12 := R v1
  let v13 := M v1 v1
  have h14 := h v13 z x
  let v15 := M z x
  have h16 := R v15
  have h17 := R x
  have h18 := R v13
  have h19 := h z v0 z
  have h20 := h z v1 v1
  have h21 := h z v2 v2
  have h22 := S h21
  let v23 := M v2 v2
  have h24 := R v23
  have h25 := h z y z
  have h26 := C h25 h24
  have h27 := h v23 z x
  let v28 := M v2 v0
  have h29 := h v23 z v28
  have h30 := S h29
  have h31 := R v28
  have h32 := h z y x
  have h33 := S h32
  have h34 := h x v2 v0
  have h35 := C (S h25) h24
  have h36 := C (T h34 (C (T (T h33 h21) h35) h31)) (T h34 (C h33 h31))
  have h37 := C (T (T (T (T (T h36 h30) h27) (C (T (C (T h26 h22) h17) (C (T h20 (C (S h19) h18)) h17)) h16)) (S h14)) (C h11 h12)) h11
  let v38 := M v0 v2
  have h39 := h v1 (M v38 z) v1
  have h40 := S h39
  have h41 := h v2 v0 z
  have h42 := C (C h41 h12) h41
  have h43 := T h42 h40
  have h44 := S h34
  have h45 := C (T (C (T (T h26 h22) h32) h31) h44) (T (C h32 h31) h44)
  let v46 := M y v0
  have h47 := h v2 (M v46 z) v2
  have h48 := S h47
  have h49 := h v0 y z
  have h50 := h v38 (M (M v0 x) v2) v38
  have h51 := h x v0 v2
  have h52 := R v38
  have h53 := S h7
  have h54 := h z v0 v2
  have h55 := C (T (T (C (T h54 (C (T h53 h51) h52)) h51) (S h50)) (C h49 h8)) h49
  have h56 := T h55 h48
  have h57 := C h8 h56
  have h58 := S h49
  have h59 := S h51
  have h60 := C (T (T (C h58 h8) h50) (C (T (C (T h59 h7) h52) (S h54)) h59)) h58
  have h61 := T h47 h60
  let v62 := M v15 v0
  have h63 := h v62 v2 v3
  let v64 := M v2 v3
  have h65 := R v64
  have h66 := C h8 h61
  have h67 := h v3 v2 v1
  have h68 := S h67
  let v69 := M x x
  have h70 := h v69 v2 v1
  have h71 := R v69
  have h72 := h v2 v1 v2
  have h73 := h v2 x x
  have h74 := h v3 (M v64 v1) v3
  have h75 := T (T (T (C (T (T h74 (C (T (T (C h68 h6) (C (C (T h73 (C (T (C (C h7 h8) h7) (S h72)) h71)) h12) h6)) (S h70)) h68)) (C (T (T h36 h30) h66) h6)) h65) (S h63)) h55) h48
  have h76 := C (T (T (T (C h75 h61) h57) h29) h45) h43
  have h77 := h v64 v3 v2
  have h78 := C (T (T (C (T (T h57 h29) h45) h6) (C (T (T h70 (C (C (T (C (T h72 (C (C h53 h8) h53)) h71) (S h73)) h12) h6)) (C h67 h6)) h67)) (S h74)) h65
  have h79 := h v62 v3 v3
  have h80 := S h79
  have h81 := R (M v3 v3)
  have h82 := C h6 h61
  have h83 := S h41
  have h84 := C (C h83 h12) h83
  have h85 := h v64 v3 v1
  have h86 := S h85
  let v87 := M v3 v1
  have h88 := R v87
  have h89 := T (T (T h47 h60) h63) h78
  have h90 := C (C h89 h12) h88
  have h91 := C (T (T (T (T (T (T (T (T h90 h86) h77) h76) h37) h10) h39) h84) h82) h6
  have h92 := C h91 h81
  have h93 := h v87 v3 v3
  have h94 := h v87 v2 v1
  have h95 := S h94
  have h96 := S h93
  have h97 := C (C h75 h12) h88
  have h98 := S h77
  have h99 := T h39 h84
  have h100 := C h89 h56
  have h101 := C (T (T (T h36 h30) h66) h100) h99
  have h102 := S h11
  have h103 := C (T (T (T (T (T (C h102 h12) h14) (C (T (C (T (C h19 h18) (S h20)) h17) (C (T h21 h35) h17)) h16)) (S h27)) h29) h45) h102
  have h104 := C h6 h56
  have h105 := C (T (T (T (T (T (T (T (T h104 h42) h40) h9) h103) h101) h98) h85) h97) h6
  have h106 := C h105 h81
  have h107 := T (T (T (T h47 h60) h79) h106) h96
  have h108 := C h75 h107
  have h109 := C (T (T (T h90 h86) h77) (C h108 h43)) h6
  have h110 := C (T h85 h97) h6
  have h111 := h (M v64 v3) v1 v3
  have h112 := T (T h104 h42) h40
  have h113 := T (T (T (T h93 h92) h80) h55) h48
  have h114 := C (T (T (T (C (C h89 h113) h99) h98) h85) h97) h6
  have h115 := C (T h90 h86) h6
  have h116 := T (T (T (T (T (T (C h6 (T (T h110 h109) h95)) h90) h86) h77) h76) h37) h10
  have h117 := T (T (T (T (T (T h9 h103) h101) h98) h85) h97) (C h6 (T (T h94 h114) h115))
  have h118 := T (T h39 h84) h82
  let v119 := M (M v2 z) v0
  have h120 := h v28 v119 v28
  have h121 := h z v2 v0
  have h122 := R v0
  have h123 := S (h v0 y x)
  have h124 := S (h x v0 v0)
  let v125 := M v0 v0
  have h126 := R v125
  have h127 := h x y x
  have h128 := C h127 h126
  have h129 := S (h v2 y x)
  have h130 := S h121
  T (T (h x v0 v3) (C (C (T (C (T (T (h v0 (M (M y v2) x) v0) (C (T (T (C h129 h122) h120) (C (T (C (T h130 h32) h31) h44) (T (R (M v119 v28)) h130))) h129)) (C (T (h (M x z) v0 v3) (C (T (T (T (T (T (C (T (T (T (T (T (T (T (T (T (T (T (C (T (T (h v0 (M v46 x) v0) (C (T (T (C h123 h122) (h v125 x v125)) (C (T (C (T (T h128 h124) h127) h126) h124) (T h128 h124))) h123)) (C (T (T (T (T (T h36 h30) h66) h100) h108) (C h8 (T (T (T (T h94 h114) h115) h111) (C (T (T (C (T (C h117 (T (T (T (T (T (T (T h110 h109) h95) h93) h92) h80) h55) h48)) (C h116 h107)) h6) (C (C h12 (T (T h93 h92) h80)) h6)) (C (T (T (C h118 h56) (C h112 h8)) h53) h6)) (T (T (T (T (T (T (T (T (C h118 h6) h105) h109) h95) h93) h92) h80) h55) h48))))) h122)) (T (C (T h34 (C (T h33 h121) h31)) h121) (S h120))) (S (h (M (M x v3) v2) v2 v0))) (C (T (T (C (T (T h7 (C h118 h8)) (C h112 h61)) h6) (C (C h12 (T (T h79 h106) h96)) h6)) (C (T (C h117 h113) (C h116 (T (T (T (T (T (T (T h47 h60) h79) h106) h96) h94) h114) h115))) h6)) (T (T (T (T (T (T (T (T h47 h60) h79) h106) h96) h94) h114) h91) (C h112 h6)))) (S h111)) h110) h109) h95) h93) h92) h80) h63) h78) h6) (C h75 h6)) h77) h76) h37) h10) h5)) h8)) h7) (S (h v4 v1 v2))) h6) h5)) (S (h v3 v0 v3))

