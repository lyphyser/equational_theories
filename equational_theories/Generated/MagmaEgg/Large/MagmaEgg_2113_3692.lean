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
theorem Equation2113_implies_Equation3692 (G: Type _) [Magma G] (h: Equation2113 G) : Equation3692 G := fun x y z =>
  let v0 := M z z
  let v1 := M y y
  let v2 := M v1 v0
  let v3 := M v2 v0
  have h4 := h v2 v3 v2
  have h5 := S h4
  have h6 := h v0 v1 v0
  have h7 := R v2
  have h8 := C (C h6 h7) h6
  have h9 := h z v0 v0
  have h10 := S h9
  let v11 := M v0 v0
  have h12 := R v11
  have h13 := h z z z
  have h14 := C h13 h12
  have h15 := h v11 z v11
  have h16 := h v0 v2 v2
  have h17 := S h16
  let v18 := M v2 v2
  have h19 := R v18
  have h20 := C h6 h19
  have h21 := h v18 v0 v18
  have h22 := T (T (T h21 (C (T (C (T (T h20 h17) h6) h19) h17) (T h20 h17))) h15) (C (T (C (T (T h14 h10) h13) h12) h10) (T h14 h10))
  have h23 := h v0 (M (M z v1) z) v0
  have h24 := h v1 z z
  have h25 := R v0
  have h26 := h v1 (M (M y x) y) v1
  have h27 := S h26
  have h28 := h x y y
  have h29 := R v1
  have h30 := C (C h28 h29) h28
  have h31 := C (C (T (T (C h7 (T h30 h27)) (C (C h24 h25) h24)) (S h23)) h7) h22
  have h32 := h (M (M x v1) x) v2 v2
  have h33 := S h28
  have h34 := C (C h33 h29) h33
  have h35 := h y v1 v1
  have h36 := S h35
  let v37 := M v1 v1
  have h38 := R v37
  have h39 := h y y y
  have h40 := C h39 h38
  have h41 := C (T (C (T (T h40 h36) h39) h38) h36) (T h40 h36)
  have h42 := h v37 y v37
  have h43 := S h32
  have h44 := S h6
  have h45 := C h44 h19
  have h46 := S h13
  have h47 := C h46 h12
  have h48 := T (T (T (C (T h9 (C (T (T h46 h9) h47) h12)) (T h9 h47)) (S h15)) (C (T h16 (C (T (T h44 h16) h45) h19)) (T h16 h45))) (S h21)
  have h49 := S h24
  have h50 := C (C (T (T h23 (C (C h49 h25) h49)) (C h7 (T h26 h34))) h7) h48
  have h51 := C (C h44 h7) h44
  let v52 := M v1 y
  have h53 := h v2 (M v52 v0) v2
  have h54 := S h53
  have h55 := h y v1 v0
  have h56 := C (C h55 h7) h55
  have h57 := T (T (T (T (T h4 h51) h50) h43) h30) h27
  have h58 := C h57 (T (T (T (T (T (T (T h56 h54) h4) h51) h50) h43) h30) h27)
  have h59 := S h55
  have h60 := C (C h59 h7) h59
  have h61 := C (T (T (T (T (T (T (T (T h58 h42) h41) h26) h34) h32) h31) h8) h5) (T h53 h60)
  have h62 := T (T (T (T (T h26 h34) h32) h31) h8) h5
  have h63 := C h62 (T (T (T (T (T (T (T h26 h34) h32) h31) h8) h5) h53) h60)
  have h64 := S h42
  have h65 := S h39
  have h66 := C h65 h38
  have h67 := C (T h35 (C (T (T h65 h35) h66) h38)) (T h35 h66)
  let v68 := M (M y v2) y
  have h69 := h v68 v2 v0
  have h70 := S h69
  have h71 := R v3
  have h72 := C h61 h22
  have h73 := h v68 v2 v2
  have h74 := C (T (T (T (T (T (T (T (T (T h26 h34) h32) h31) h8) h5) h53) h60) h73) h72) h71
  have h75 := T (T (T (T (T (T (T (T (T (T (T (T h74 h70) h56) h54) h4) h51) h50) h43) h30) h27) h67) h64) h63
  have h76 := C h75 h7
  have h77 := S h73
  have h78 := C (T (T (T (T (T (T (T (T h4 h51) h50) h43) h30) h27) h67) h64) h63) (T h56 h54)
  have h79 := C h78 h48
  have h80 := C (T (T (T (T (T (T (T (T (T h79 h77) h56) h54) h4) h51) h50) h43) h30) h27) h71
  have h81 := C h75 h25
  have h82 := C (T (T (T (T h81 h79) h77) h69) h80) h7
  have h83 := T (T (T (T (T (T (T (T (T (T (T (T h58 h42) h41) h26) h34) h32) h31) h8) h5) h53) h60) h69) h80
  have h84 := C h83 h25
  have h85 := h v3 v1 v0
  have h86 := h v3 v1 v2
  have h87 := S h86
  let v88 := M v1 v2
  have h89 := R v88
  have h90 := C h83 h7
  have h91 := C (T (T (T (T h67 h64) h63) h78) h90) h89
  have h92 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h91 h87) h85) h82) h76) h61) h58) h42) h41) h26) h34) h32) h31) h8) h5) h53) h60) h73) h72) h84) h7
  have h93 := C (T (T (T (T h76 h61) h58) h42) h41) h89
  have h94 := S h85
  have h95 := R (M v1 v88)
  have h96 := C (T (T (T (T (C h95 h62) h92) h94) h86) h93) (T (T (T (T (T (T (T h42 h41) h26) h34) h32) h31) h8) h5)
  have h97 := h v88 v1 v1
  have h98 := h v88 y y
  have h99 := S h98
  have h100 := R y
  have h101 := S h97
  have h102 := C (T (T (T (T h74 h70) h73) h72) h84) h7
  have h103 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h81 h79) h77) h56) h54) h4) h51) h50) h43) h30) h27) h67) h64) h63) h78) h90) h102) h94) h86) h93) h7
  have h104 := C (T (T (T (T h91 h87) h85) h103) (C h95 h57)) (T (T (T (T (T (T (T h4 h51) h50) h43) h30) h27) h67) h64)
  have h105 := T (T (T (T (T (T (T (T h67 h64) h63) h78) h90) h102) h103) h104) h101
  have h106 := C (C h100 h105) h100
  have h107 := C (C h65 h29) h65
  have h108 := h v1 v52 v1
  let v109 := M x x
  have h110 := h v88 v2 v109
  have h111 := S h110
  let v112 := M v2 v109
  have h113 := R v112
  have h114 := R v109
  have h115 := R x
  have h116 := T (T (T (T (T (T (T (T h97 h96) h92) h82) h76) h61) h58) h42) h41
  have h117 := C (C h115 h116) h115
  have h118 := h v88 x x
  have h119 := C (T (T (T (T (T (T (T (T (T (T h67 h64) h63) h78) h90) h102) h103) h104) h101) h118) (C (T (T (T (T (T (T (T (T (T (T (T h117 h30) h27) h67) h64) h63) h78) h90) h102) h94) h86) (C (T (T (T (T (T (T (T (T (T (T h76 h61) h58) h42) h41) h26) h34) h32) h31) h8) h5) h89)) h114)) h113
  have h120 := C (T (T (T (T (T (T (T (T (T (T (T (T (T h119 h111) h97) h96) h92) h82) h76) h61) h58) h42) h41) h108) h107) h106) h57
  have h121 := C (C h115 h105) h115
  have h122 := C (T (T (T (T (T (T (T (T (T (T (C (T (T (T (T (T (T (T (T (T (T (T (C (T (T (T (T (T (T (T (T (T (T h4 h51) h50) h43) h30) h27) h67) h64) h63) h78) h90) h89) h87) h85) h82) h76) h61) h58) h42) h41) h26) h34) h121) h114) (S h118)) h97) h96) h92) h82) h76) h61) h58) h42) h41) h113
  have h123 := C (T (T (T h120 h99) h110) h122) (T (T (T (T (T (T (T (T (T (T (T (T (T (T h97 h96) h92) h82) h76) h61) h58) h42) h41) h26) h34) h32) h31) h8) h5)
  have h124 := h v112 v1 v2
  have h125 := h v112 y y
  have h126 := S h125
  have h127 := S h124
  have h128 := S h108
  have h129 := C (C h39 h29) h39
  have h130 := C (C h100 h116) h100
  have h131 := C (T (T (T (T (T (T (T (T (T (T (T (T (T h130 h129) h128) h67) h64) h63) h78) h90) h102) h103) h104) h101) h110) h122) h62
  have h132 := C (T (T (T h119 h111) h98) h131) (T (T (T (T (T (T (T (T (T (T (T (T (T (T h4 h51) h50) h43) h30) h27) h67) h64) h63) h78) h90) h102) h103) h104) h101)
  have h133 := T (T (T h98 h131) h132) h127
  have h134 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h124 h123) h120) h99) h97) h96) h92) h82) h76) h61) h58) h42) h41) h108) h107) h106) (C (C h100 h133) h100)) h57
  let v135 := M v112 v2
  have h136 := R z
  have h137 := T (T (T h124 h123) h120) h99
  have h138 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (C (C h100 h137) h100) h130) h129) h128) h67) h64) h63) h78) h90) h102) h103) h104) h101) h98) h131) h132) h127) h62
  have h139 := T h125 h138
  have h140 := S (h z y y)
  have h141 := h v135 v2 v109
  have h142 := h v112 x x
  T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (h v109 v2 v2) (C (T h141 (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h4 h51) h50) h43) h30) h27) h67) h64) h63) h78) h90) h102) h103) h104) h101) h98) h131) h132) h127) (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h134 h126) h124) h123) h120) h99) h97) h96) h92) h82) h76) h61) h58) h42) h41) h26) h34) h32) h31) h8) h5)) h134) h126) h124) h123) h120) h99) h97) h96) h92) h82) h76) h61) h58) h42) h41) h26) h34) h121) (C (C h115 h133) h115)) h114) (S h142)) h124) h123) h120) h99) h97) h96) h92) h82) h76) h61) h58) h42) h41) h139)) h22)) (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T h67 h64) h63) h78) h90) h102) h103) h104) h101) h98) h131) h132) h127) h142) (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (C (C h115 h137) h115) h117) h30) h27) h67) h64) h63) h78) h90) h102) h103) h104) h101) h98) h131) h132) h127) h125) h138) (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h124 h123) h120) h99) h97) h96) h92) h82) h76) h61) h58) h42) h41) h26) h34) h32) h31) h8) h5) (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h4 h51) h50) h43) h30) h27) h67) h64) h63) h78) h90) h102) h103) h104) h101) h98) h131) h132) h127) h125) h138))) h114)) (T h134 h126)) (S h141)) h134) h126) h124) h123) h120) h99) h97) h96) h92) h82) h76) h61) h58) h42) h41) (h v1 (M (M y z) y) v1)) (C (C h140 h29) h140)) (C (C h136 h105) h136)) (C (C h136 h133) h136)) (C (C h136 h139) h136)) h25)) (S (h v135 z z))) h134) h126) h124) h123) h120) h99) h97) h96) h92) h82) h76) h61) h58) h42) h41) h26) h34) h32) h31) h8) h5

