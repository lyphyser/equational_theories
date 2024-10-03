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
theorem Equation2914_implies_Equation2 (G: Type _) [Magma G] (h: Equation2914 G) : Equation2 G := fun x y =>
  have h0 := h y x x
  have h1 := S h0
  have h2 := R x
  let v3 := M y x
  have h4 := C (C (C h2 (S (h v3 x x))) h2) h2
  let v5 := M x (M v3 x)
  have h6 := h (M v5 x) x x
  have h7 := h v5 y x
  have h8 := R y
  let v9 := M x v3
  let v10 := M v9 x
  have h11 := h v10 x x
  have h12 := S h11
  have h13 := C h2 h0
  have h14 := h y y x
  have h15 := C (C (T (C h2 (S h14)) h13) h2) h2
  let v16 := M y y
  let v17 := M y v16
  let v18 := M v17 y
  have h19 := h v18 x x
  have h20 := h v16 y y
  let v21 := M v16 y
  let v22 := M (M y v21) y
  have h23 := h v22 y x
  have h24 := h v22 x x
  have h25 := h v16 y x
  have h26 := h v16 x x
  have h27 := S h26
  let v28 := M x (M v16 x)
  have h29 := h (M v28 x) x x
  have h30 := T (T (T (T (T h29 (C (C (C h2 (T h27 h25)) h2) h2)) (S h24)) h23) (C (T (T (T (C (C h8 (S h20)) h8) h19) h15) h12) h2)) h1
  have h31 := C h30 h2
  have h32 := C (T h26 h31) h2
  have h33 := C h2 h32
  have h34 := h v28 x y
  have h35 := S h34
  have h36 := S h19
  have h37 := C h2 h1
  have h38 := C (C (T h37 (C h2 h14)) h2) h2
  have h39 := T (T (T (T (T h0 (C (T (T (T h11 h38) h36) (C (C h8 h20) h8)) h2)) (S h23)) h24) (C (C (C h2 (T (S h25) h26)) h2) h2)) (S h29)
  have h40 := C (T h37 (C h2 h39)) h2
  have h41 := h (M (M x (M v10 x)) x) x x
  have h42 := S h41
  have h43 := C (C (C h2 h11) h2) h2
  have h44 := h v9 x x
  have h45 := C (T (T (T h44 h43) h42) h40) h8
  let v46 := M v9 y
  have h47 := h v46 y x
  have h48 := S h47
  have h49 := S h44
  have h50 := C (C (C h2 h12) h2) h2
  have h51 := C (T (C h2 h30) h13) h2
  have h52 := C (T (T (T h51 h41) h50) h49) h8
  have h53 := T h34 h52
  have h54 := C h53 h8
  have h55 := C h8 h54
  have h56 := C h55 h8
  have h57 := h v46 x x
  have h58 := S h57
  have h59 := C (T (T (T (T h44 h43) h42) h40) (C (C h2 (C h53 h2)) h2)) h2
  have h60 := C (T (T (T h59 h58) h45) h35) h8
  have h61 := h y x y
  have h62 := C h8 (T h61 h60)
  have h63 := C h62 h8
  have h64 := h v21 x x
  have h65 := S h64
  have h66 := S h61
  have h67 := h v10 y x
  have h68 := C (C (C h2 (T h67 (C (C (C h8 h66) h8) h2))) h2) h2
  have h69 := h v9 x y
  have h70 := S h69
  let v71 := M x v10
  let v72 := M v71 x
  have h73 := h v72 x x
  have h74 := S h73
  have h75 := h v9 y x
  have h76 := S h75
  have h77 := C (C (C h2 (T h76 h44)) h2) h2
  have h78 := h (M (M y v46) y) x x
  have h79 := C (C h8 (T (T (T (T h19 h15) h12) h59) h58)) h8
  let v80 := M (M y v18) y
  have h81 := h v80 x x
  have h82 := h v17 y x
  have h83 := h v17 x x
  let v84 := M x (M v17 x)
  have h85 := h (M v84 x) x x
  have h86 := T (T (T (T (T (T h85 (C (C (C h2 (T (S h83) h82)) h2) h2)) (S h81)) h79) h78) h77) h74
  have h87 := C h86 h8
  have h88 := h v17 x y
  have h89 := C (T (T (T (T (T (T (T h88 h87) h70) h44) h68) h65) h63) h56) h2
  have h90 := C (T (T (T (T h89 h48) h45) h35) h33) h8
  have h91 := S h88
  have h92 := S h82
  have h93 := T h45 h35
  have h94 := C (T (T (T (T (C (C h2 (C h93 h2)) h2) h51) h41) h50) h49) h2
  have h95 := C (C h8 (T (T (T (T h57 h94) h11) h38) h36)) h8
  have h96 := S h78
  have h97 := C (C (C h2 (T h49 h75)) h2) h2
  have h98 := T (T (T (T (T (T h73 h97) h96) h95) h81) (C (C (C h2 (T h92 h83)) h2) h2)) (S h85)
  have h99 := C h98 h8
  have h100 := C (C (C h2 (T (C (C (C h8 h61) h8) h2) (S h67))) h2) h2
  have h101 := C (T (T (T h34 h52) h57) h94) h8
  have h102 := C h8 (T h101 h66)
  have h103 := C h102 h8
  have h104 := C h93 h8
  have h105 := C h8 h104
  have h106 := C h105 h8
  have h107 := C (T (T (T (T (T (T (T h106 h103) h64) h100) h49) h69) h99) h91) h2
  have h108 := C (T h47 h107) h8
  have h109 := T (T (T (T h61 h60) h54) h108) h90
  have h110 := C h30 h109
  have h111 := h v16 x y
  have h112 := C (T h89 h48) h8
  have h113 := C h8 h112
  have h114 := C (T (T (T (T h113 h105) h102) h111) h110) h8
  have h115 := C h8 h108
  have h116 := C h115 h8
  have h117 := h v80 y y
  have h118 := S h117
  have h119 := C h39 h2
  have h120 := C (T h119 h27) h2
  have h121 := C h2 h120
  have h122 := C (T (T (T (T h121 h34) h52) h47) h107) h8
  have h123 := T (T (T (T h122 h112) h104) h101) h66
  have h124 := h v17 y y
  have h125 := C h113 h8
  have h126 := S h111
  have h127 := C h39 h123
  have h128 := C (T (T (T (T h127 h126) h62) h55) h115) h8
  have h129 := h x x y
  have h130 := C h8 (S h129)
  have h131 := C (T (T (T (T h130 h119) h27) h111) h110) h8
  have h132 := C h8 h129
  let v133 := M y (M v3 y)
  have h134 := h v133 y x
  have h135 := h (M v133 y) x x
  have h136 := h v3 y x
  have h137 := C (T (T (T (T (T (T (T h121 h34) h52) h57) h94) (C (T (T (T h44 h68) h65) (C (C h8 (T (T h0 (C (C (C h2 h136) h2) h2)) (S h135))) h8)) h2)) (S h134)) (C h8 (T (T (T (T (T (T (T (T (T (T (T (T (C h132 h8) h131) h128) h125) h106) h103) h64) h100) h49) h69) h99) h91) h124))) h8
  have h138 := C (T (T (T (T (T h61 h60) h54) h108) h90) h137) h123
  have h139 := C (T (T (T (T (T (T h119 h27) h111) h110) h138) h118) h79) h2
  have h140 := C (T (T (T (C (C h8 (T (T h135 (C (C (C h2 (S h136)) h2) h2)) h1)) h8) h64) h100) h49) h2
  have h141 := C h8 (T (T (T (T (T (T (T (T (T (T (T (T (S h124) h88) h87) h70) h44) h68) h65) h63) h56) h116) h114) (C (T (T (T (T h127 h126) h26) h31) h132) h8)) (C h130 h8))
  have h142 := C (T (T (T (T (T (C (T (T (T (T (T (T (T h141 h134) h140) h59) h58) h45) h35) h33) h8) h122) h112) h104) h101) h66) h109
  have h143 := C (T (T (T (T (T (T h95 h117) h142) h127) h126) h26) h31) h2
  have h144 := h v71 x y
  T (T (T (T (T (T (T (T h129 (C (T (T (T (T (T (T (T (T (h (M (M x (M x x)) x) y y) (C h131 h8)) (S (h v5 y y))) h121) (h v28 x x)) (C h51 h2)) h38) h36) (C (C h8 (T (T (T (T (T (T (T (T (T (T h111 h110) h138) h118) h79) h78) h77) h74) (h v72 x y)) (C (T (T (T (T (T (T (T (T (T (T (T (T (C (C h2 (T (T (T (T h49 h69) h99) h91) h82)) h2) (C (C h2 (T (T (T (T (T h92 h88) h87) h70) h75) h143)) h2)) h6) h4) h1) h61) h60) h54) h108) h90) h137) (C (T (T (T (T (T (T (T (T (T (T (T h141 h134) h140) h59) h58) h45) h35) h33) h7) (C (T (T (T (T (T (T (T (T h128 h125) h106) h103) h64) h100) h49) h75) h143) h2)) (C h120 h2)) (C (T (T (T h32 h139) h76) (C h2 (T (T (T (T (T (T (T (T (T h119 h27) h111) h110) h138) h118) h79) h78) h77) h74))) h2)) h8)) (S h144)) h8)) (C (T (T h144 (C (C (C h2 h98) h2) h8)) (S (h v84 x y))) h8))) h8)) h8)) (S (h v84 y y))) (h v84 x x)) (C (C (C h2 h86) h2) h2)) (C (T (T (T (C (T (T (T (C h2 (T (T (T (T (T (T (T (T (T h73 h97) h96) h95) h117) h142) h127) h126) h26) h31)) h75) h143) h120) h2) (C h32 h2)) (C (T (T (T (T (T (T (T (T h139 h76) h44) h68) h65) h63) h56) h116) h114) h2)) (S h7)) h2)) h6) h4) h1

