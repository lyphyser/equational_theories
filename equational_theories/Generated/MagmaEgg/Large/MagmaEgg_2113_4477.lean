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
theorem Equation2113_implies_Equation4477 (G: Type _) [Magma G] (h: Equation2113 G) : Equation4477 G := fun x y z =>
  let v0 := M y y
  let v1 := M x v0
  let v2 := M x z
  let v3 := M v2 z
  have h4 := h v3 v1 v1
  have h5 := S h4
  let v6 := M v1 v2
  let v7 := M v1 v1
  have h8 := h v7 v0 v6
  have h9 := S h8
  have h10 := R v6
  have h11 := h v0 x z
  have h12 := S h11
  have h13 := h z v1 v2
  have h14 := R v7
  have h15 := h v0 x v0
  have h16 := h v0 v1 v1
  have h17 := C (T h13 (C (T (T h12 h16) (C (S h15) h14)) h10)) (T h13 (C h12 h10))
  let v18 := M z z
  have h19 := h v18 v2 z
  have h20 := S h19
  have h21 := R v3
  have h22 := R z
  have h23 := R v18
  have h24 := h v2 v3 v2
  have h25 := h z x z
  have h26 := R v2
  have h27 := h v2 z z
  have h28 := C (C (T h27 (C (T (C (C h25 h26) h25) (S h24)) h23)) h22) h21
  let v29 := M v3 v3
  have h30 := h v29 v1 x
  have h31 := S h30
  have h32 := h x y y
  have h33 := S h32
  have h34 := R v0
  have h35 := C (C h33 h34) h33
  have h36 := h v0 (M (M y x) y) v0
  have h37 := R x
  have h38 := R v29
  let v39 := M x v3
  have h40 := h v1 (M v39 v0) v1
  have h41 := h v3 x v0
  have h42 := R v1
  let v43 := M v2 v0
  have h44 := h v1 v43 v1
  have h45 := S h44
  have h46 := h z x v0
  have h47 := C (C h46 h42) h46
  have h48 := h (M (M z v1) z) v3 v3
  have h49 := S h46
  have h50 := C (C h49 h42) h49
  have h51 := T (T (T h44 h50) h48) (C (T (T (C (C h21 (T h47 h45)) h21) (C (C h41 h42) h41)) (S h40)) h38)
  have h52 := C (T (T h36 h35) (C h51 h37)) (T h36 h35)
  let v53 := M v0 v0
  have h54 := h v53 y v53
  have h55 := S h54
  have h56 := R v53
  have h57 := h y y y
  have h58 := S h57
  have h59 := C h58 h56
  have h60 := h y v0 v0
  have h61 := C (T h60 (C (T (T h58 h60) h59) h56)) (T h60 h59)
  have h62 := T (T (T (T (T (T (T h61 h55) h52) h31) h28) h20) h17) h9
  have h63 := h v1 v2 z
  have h64 := S h63
  let v65 := M v2 v1
  have h66 := h v3 (M v65 z) v3
  have h67 := C (T h66 (C (C h64 h21) h64)) h62
  have h68 := h (M v3 v0) v3 v2
  have h69 := S h68
  have h70 := S h60
  have h71 := C h57 h56
  have h72 := C (T (C (T (T h71 h70) h57) h56) h70) (T h71 h70)
  have h73 := S h36
  have h74 := C (C h32 h34) h32
  have h75 := S h41
  have h76 := T (T (T (C (T (T h40 (C (C h75 h42) h75)) (C (C h21 (T h44 h50)) h21)) h38) (S h48)) h47) h45
  have h77 := C (T (T (C h76 h37) h74) h73) (T h74 h73)
  have h78 := S h25
  have h79 := C (C (T (C (T h24 (C (C h78 h26) h78)) h23) (S h27)) h22) h21
  have h80 := S h13
  have h81 := C (T (C (T (T (C h15 h14) (S h16)) h11) h10) h80) (T (C h11 h10) h80)
  have h82 := T (T (T (T (T (T (T h8 h81) h19) h79) h30) h77) h54) h72
  have h83 := C (T (C (C h63 h21) h63) (S h66)) h82
  have h84 := T h4 h83
  have h85 := C h21 h84
  have h86 := T (T (T (T h61 h55) h52) h31) h85
  have h87 := C (C h86 h26) h25
  have h88 := h (M (M v0 v2) z) v3 v0
  have h89 := S h88
  have h90 := T h67 h5
  have h91 := C h21 h90
  have h92 := T (T (T (T h91 h30) h77) h54) h72
  have h93 := C (C h92 h26) h78
  have h94 := C h21 (T h68 h93)
  have h95 := C (T (T (T (T (T (T (C h76 h42) h8) h81) h19) h79) h85) h94) h82
  have h96 := h v29 v1 v1
  have h97 := C h21 (T h87 h69)
  have h98 := C (T (T (T h97 h91) h96) h95) h84
  have h99 := C h94 h21
  have h100 := C h86 h21
  let v101 := M v0 v3
  have h102 := h v101 v3 v0
  have h103 := S h102
  have h104 := C h92 h21
  have h105 := C h97 h21
  have h106 := S h96
  have h107 := C (T (T (T (T (T (T h97 h91) h28) h20) h17) h9) (C h51 h42)) h62
  have h108 := C (T (T (T h107 h106) h85) h94) h90
  have h109 := C h21 (T (T (T h88 h108) h105) h104)
  have h110 := C h21 (T (T (T h100 h99) h98) h89)
  have h111 := T (T (T (T (T (T (T h4 h83) h68) h93) h88) h108) h105) h104
  have h112 := h v101 z v2
  let v113 := M z v2
  have h114 := R v113
  have h115 := C h22 h111
  have h116 := h v3 x z
  have h117 := S h116
  have h118 := C (T (C h117 h26) h78) h117
  have h119 := h v2 (M v39 z) v2
  let v120 := M v2 v2
  have h121 := h v120 z x
  have h122 := R (M z x)
  have h123 := R v120
  have h124 := h z v2 v2
  have h125 := h z v3 v3
  have h126 := h z v2 z
  have h127 := h v29 z x
  have h128 := C (T (T (T (T (T (T (C (T (T (T (T (T (T (T (T (T (C (T (T (T (T (T (T (T h61 h55) h52) h31) h127) (C (T (C (T (C h126 h38) (S h125)) h37) (C (T h124 (C h78 h123)) h37)) h122)) (S h121)) (C (T (T h119 h118) h115) h26)) h114) (S h112)) h100) h99) h98) h89) h87) h69) h67) h5) h111) h110) h97) h91) h96) h95) (C h109 h34)) (T (T (T (T (T h100 h99) h98) h89) h87) h69)
  have h129 := h v113 v0 v3
  have h130 := h v2 v0 v3
  have h131 := h v0 v2 v1
  have h132 := S h131
  have h133 := R v65
  have h134 := h v65 z v2
  have h135 := h v65 (M v3 v1) v65
  have h136 := h z v2 v1
  have h137 := C h21 (T (C (T (T (T (C (T h131 (C (T h49 h136) h133)) h136) (S h135)) h134) (C (C (T (C h46 h133) h132) h26) (T (T (T (T (T (T (T (T (T (T h129 h128) h103) h100) h99) h98) h89) h87) h69) h67) h5))) h111) (S h130))
  have h138 := h (M (M v0 z) v3) v3 v3
  have h139 := T (T (T (T (T (T (T h100 h99) h98) h89) h87) h69) h67) h5
  have h140 := S h136
  have h141 := C (T (C (T h140 h46) h133) h132) h140
  have h142 := S h119
  have h143 := C (T h25 (C h116 h26)) h116
  have h144 := C h22 h139
  have h145 := C (T (T (T (C (C (T h131 (C h49 h133)) h26) (T (T (T (T (T (T (T (T (T (T h4 h83) h68) h93) h88) h108) h105) h104) h102) (C (T (T (T (T (T (T (C h110 h34) h107) h106) h85) h94) h109) (C (T (T (T (T (T (T (T (T (T h4 h83) h68) h93) h88) h108) h105) h104) h112) (C (T (T (T (T (T (T (T (C (T (T h144 h143) h142) h26) h121) (C (T (C (T (C h25 h123) (S h124)) h37) (C (T h125 (C (S h126) h38)) h37)) h122)) (S h127)) h30) h77) h54) h72) h114)) h139)) (T (T (T (T (T h68 h93) h88) h108) h105) h104))) (S h129))) (S h134)) h135) h141) h139
  have h146 := S (h v2 x v0)
  T (T (T (T (T (T (T (T (T (T (T (h v1 (M (M x v2) v0) v1) (C (T (T (C h146 h42) h135) h141) h146)) (C (T (C (T (T (T (T (T h61 h55) h52) h31) h85) h94) h22) (C h109 h22)) (T (T (T (T (T h130 h145) h138) (C (T (T (T (C (T h137 h78) h111) h144) h143) h142) (T (T (T h30 h77) h54) h72))) (h v43 v3 v2)) (C (T (T (T (T (T (T (T (T (T (T (T (C (T (T (C h21 (T (C (T (T (T h119 h118) h115) (C (T h25 (C h21 (T h130 h145))) h139)) (T (T (T h61 h55) h52) h31)) (S h138))) h137) h78) h26) h129) h128) h103) h100) h99) h98) h89) h87) h69) h67) h5) h78)))) (S (h v101 v3 z))) h100) h99) h98) h89) h87) h69) h67) h5

