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
theorem Equation2944_implies_Equation2925 (G: Type _) [Magma G] (h: Equation2944 G) : Equation2925 G := fun x y z =>
  let v0 := M x z
  let v1 := M y v0
  let v2 := M v1 y
  let v3 := M v2 z
  have h4 := R v3
  let v5 := M v0 v3
  let v6 := M v0 v5
  have h7 := h v0 z x
  have h8 := S h7
  have h9 := R x
  let v10 := M z v0
  let v11 := M (M z v10) x
  have h12 := h v11 x x
  have h13 := S h12
  let v14 := M (M x (M x x)) x
  have h15 := h x v14 z
  have h16 := S h15
  have h17 := R z
  have h18 := h x x x
  have h19 := R v14
  have h20 := T h18 (C h19 h18)
  have h21 := C (C h20 h17) h17
  have h22 := h z v2 v3
  have h23 := S h22
  have h24 := h v2 x v2
  have h25 := S h24
  let v26 := M (M x (M x v2)) v2
  have h27 := R v26
  have h28 := h v2 v26 v3
  have h29 := T h28 (C (C (T (C h27 h25) h25) h4) h4)
  have h30 := C h29 h4
  have h31 := T h30 h23
  have h32 := R v0
  have h33 := C h32 h31
  let v34 := M v2 v3
  have h35 := h v34 x x
  have h36 := S h35
  have h37 := h x v14 v0
  have h38 := S h37
  have h39 := C (C h20 h32) h32
  have h40 := C h9 h31
  have h41 := C (C h9 h40) h32
  have h42 := T (C (C (T h24 (C h27 h24)) h4) h4) (S h28)
  have h43 := C h42 h4
  have h44 := T h22 h43
  have h45 := C h9 h44
  have h46 := C (T (T h41 h39) h38) h45
  have h47 := h v34 x v0
  have h48 := T (T (T h22 h43) h47) h46
  have h49 := C h48 h32
  have h50 := C (C h48 (T (T (T h49 h41) h39) h38)) h9
  have h51 := T h50 h36
  have h52 := C h32 h51
  have h53 := S h47
  have h54 := C (C h9 h45) h32
  have h55 := S h18
  have h56 := T (C h19 h55) h55
  have h57 := C (C h56 h32) h32
  have h58 := C (T (T h37 h57) h54) h40
  have h59 := T (T (T h58 h53) h30) h23
  have h60 := C h59 h32
  have h61 := C (C h59 (T (T (T h37 h57) h54) h60)) h9
  have h62 := T h35 h61
  have h63 := C h9 h62
  have h64 := R v2
  have h65 := C h64 (T (T (T h50 h36) h30) h23)
  have h66 := C h29 h65
  have h67 := C (T (T (T h66 h43) h47) h46) h32
  have h68 := C (T (T (T h67 h41) h39) h38) (T h45 h63)
  have h69 := h v11 v2 v0
  have h70 := C (T h7 (C (T h69 h68) h9)) (T (T (T h52 h33) h21) h16)
  have h71 := C (T h70 h13) h9
  have h72 := C h32 h62
  have h73 := C h32 h44
  have h74 := C (C h56 h17) h17
  have h75 := S h69
  have h76 := C h9 h51
  have h77 := C h64 (T (T (T h22 h43) h35) h61)
  have h78 := C h42 h77
  have h79 := C (T (T (T h58 h53) h30) h78) h32
  have h80 := C (T (T (T h37 h57) h54) h79) (T h76 h40)
  have h81 := C (T (C (T h80 h75) h9) h8) (T (T (T h15 h74) h73) h72)
  have h82 := h v34 v0 v0
  have h83 := S h82
  have h84 := C h32 (T (T (T (T (T (T h49 h41) h39) h38) h15) h74) h73)
  have h85 := C h32 (T (T (T (T (T (T (T h52 h33) h21) h16) h37) h57) h54) h60)
  have h86 := C h32 (T (T (T (T (T (T (T h49 h41) h39) h38) h15) h74) h73) h72)
  have h87 := C h32 (T (T h86 h70) h13)
  have h88 := C (T (T (T (T (T (T (T (T (T (T (T h87 h52) h33) h21) h16) h37) h57) h54) h79) (C (T (T (T (T (T h66 h43) h35) h61) h69) h68) h32)) (C (T (T (T h80 h75) h12) h81) h32)) (C (T h85 h84) h32)) h32
  have h89 := C h32 (T (T (T (T (T (T h33 h21) h16) h37) h57) h54) h60)
  have h90 := C h32 (T (C h32 (T (T h15 h74) h73)) h89)
  have h91 := C h90 h32
  have h92 := T (T (T (T h91 h88) h83) h35) h61
  have h93 := C h64 h92
  have h94 := C h64 h93
  have h95 := C (T (T (T (T (T (T h94 h66) h43) h35) h61) h12) h81) h9
  have h96 := C h32 (T h84 (C h32 (T (T h33 h21) h16)))
  have h97 := C h96 h32
  have h98 := C h32 (T (T h12 h81) h85)
  have h99 := C (T (T (T (T (T (T (T (T (T (T (T (C (T h89 h86) h32) (C (T (T (T h70 h13) h69) h68) h32)) (C (T (T (T (T (T h80 h75) h50) h36) h30) h78) h32)) h67) h41) h39) h38) h15) h74) h73) h72) h98) h32
  have h100 := T (T (T (T h50 h36) h82) h99) h97
  have h101 := C h64 h100
  have h102 := C h64 h101
  let v103 := M v0 (M v0 x)
  let v104 := M v103 v0
  have h105 := h v104 v2 x
  have h106 := S h105
  have h107 := C (T (T (T (T (T (T h70 h13) h50) h36) h30) h78) h102) h9
  have h108 := C (T h12 h81) h9
  have h109 := C (T (T h7 h108) h107) (T (T (T (T (T (C h32 (T (T (T (T (T (T (T h91 h88) h83) h35) h61) h12) h81) h85)) h87) h52) h33) h21) h16)
  have h110 := T (T (T (T (T (T (T h109 h106) h91) h88) h83) h30) h78) h102
  have h111 := C h110 h9
  have h112 := C (T (T h95 h71) h8) (T (T (T (T (T h15 h74) h73) h72) h98) (C h32 (T (T (T (T (T (T (T h86 h70) h13) h50) h36) h82) h99) h97)))
  have h113 := h v104 v0 v0
  have h114 := S h113
  have h115 := C h9 h92
  have h116 := T (T (T (T (T (T (T h94 h66) h43) h82) h99) h97) h105) h112
  have h117 := h v10 v0 v0
  have h118 := C (T (T (T (T (T (T h37 h57) h54) h60) h117) (C (T (T (T (T h88 h83) h30) h78) h102) h32)) (C h116 h32)) (T (T h115 h76) h40)
  have h119 := C (T (T (T h118 h114) h105) h112) h9
  have h120 := C h9 h100
  have h121 := C (T (T (T (T (T (T (C h110 h32) (C (T (T (T (T h94 h66) h43) h82) h99) h32)) (S h117)) h49) h41) h39) h38) (T (T h45 h63) h120)
  let v122 := M (M x (M x y)) y
  have h123 := h y v122 v0
  have h124 := h y x y
  have h125 := R v122
  have h126 := T (T (T (T h87 h52) h33) h21) h16
  have h127 := C h126 (T (T (T (T h22 h43) h82) h99) h97)
  have h128 := C h90 h17
  have h129 := R v1
  have h130 := C h129 (T (T (C h129 (T (T (T (T h128 h127) h115) h76) h40)) (C (C (T h124 (C h125 h124)) h32) h32)) (S h123))
  have h131 := C h130 (T h77 h101)
  have h132 := h v104 x v3
  have h133 := S h132
  have h134 := h (M v103 z) v1 v3
  have h135 := C h96 h17
  have h136 := T (T (T (T h15 h74) h73) h72) h98
  have h137 := C h136 (T (T (T (T h91 h88) h83) h30) h23)
  have h138 := C (T (T (T (T (T (T h45 h63) h120) h137) h135) h134) (C (T (T (T (T (T (T (T (T h131 h94) h66) h43) h82) h99) h97) h113) h121) h4)) h4
  have h139 := S h124
  have h140 := C h129 (T (T h123 (C (C (T (C h125 h139) h139) h32) h32)) (C h129 (T (T (T (T h45 h63) h120) h137) h135)))
  have h141 := C h140 (T (T (C h64 (T h138 h133)) h93) h65)
  have h142 := C (T (T (T (T (T (T (T (T (T h141 h131) h94) h66) h43) h82) h99) h97) h113) h121) h9
  have h143 := C h140 (T h93 h65)
  have h144 := C (T (T (T (T (T (T (C (T (T (T (T (T (T (T (T h118 h114) h91) h88) h83) h30) h78) h102) h143) h4) (S h134)) h128) h127) h115) h76) h40) h4
  have h145 := C h130 (T (T h77 h101) (C h64 (T h132 h144)))
  have h146 := h v5 v2 v0
  have h147 := T (T (T (T (T (T h138 h133) h91) h88) h83) h30) h23
  have h148 := h x v0 v0
  have h149 := T (T (T (T (T (T (T (T (T (T (T (C (T h148 (C (T (T (T (T (T (T (T h91 h88) h83) h30) h78) h102) h143) h145) h32)) (T (T (T (T (C h136 h147) h127) h115) h76) h40)) (S h146)) h138) h133) h91) h88) h83) h30) h78) h102) h143) h145
  have h150 := C h149 h9
  have h151 := T (T (T (T (T (T h22 h43) h82) h99) h97) h132) h144
  have h152 := S h148
  have h153 := C (T (T (T (T (T (T (T h141 h131) h94) h66) h43) h82) h99) h97) h32
  have h154 := C (T h153 h152) (T (T (T (T h45 h63) h120) h137) (C h126 h151))
  have h155 := h v5 x x
  have h156 := h v10 v0 z
  have h157 := T (T (T (T (T (C (T (T (T h45 h63) h120) h137) h147) (S h156)) h49) h41) h39) h38
  have h158 := T (T (T (C (T (T (T (T (T (T h7 h108) h107) (C h116 h9)) (C (T (T (T h109 h106) h113) h121) h9)) (C (T (T (T (T (T (T (T (T (T h118 h114) h91) h88) h83) h30) h78) h102) h143) h145) h9)) (C (T (T (T (T (T (T (T (T (T (T (T h141 h131) h94) h66) h43) h82) h99) h97) h132) h144) h146) h154) h9)) h157) (S h155)) h146) h154
  have h159 := C (T (T (T h127 h115) h76) h40) h151
  have h160 := C (T (T (T (T (T (T h150 h142) h119) h111) h95) h71) h8) (T (T (T (T (T h37 h57) h54) h60) h156) h159)
  T (T (T (T (T (T (T (T h37 h57) h54) h60) h156) h159) (h v6 z v3)) (C (C (T (C (T (T (T (T (T (T (T (T h22 h43) h82) h99) h97) h132) h144) (h v5 v0 v0)) (C (T (T (T (T (T (T (T (T (T (T (C h158 h32) (C h149 h32)) h153) h152) h37) h57) h54) h60) h156) h159) (C h32 (T h155 h160))) h32)) (T (T (T (T (T (T (T (T (C (T (T (T (T (T (T (T (T h22 h43) h82) h99) h97) h132) h144) h155) h160) h157) (C h158 h9)) h150) h142) h119) h111) h95) h71) h8)) (S (h v6 v0 v0))) h4) h4)) (S (h v3 v0 v3))

