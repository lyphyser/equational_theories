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
theorem Equation3385_implies_Equation3370 (G: Type _) [Magma G] (h: Equation3385 G) : Equation3370 G := fun x y z =>
  let v0 := M x y
  let v1 := M z x
  let v2 := M z v1
  have h3 := h y v2 v0
  have h4 := S h3
  let v5 := M y v2
  have h6 := R v5
  have h7 := h v2 v0 v1
  have h8 := h z x y
  have h9 := R v0
  have h10 := h y z v0
  have h11 := R v2
  have h12 := h y z v1
  have h13 := h v1 y v2
  have h14 := R v1
  have h15 := R y
  have h16 := C h15 (T (C h14 (T (T h13 (C h11 (S h12))) (C h11 (T h10 (C h9 (S h8)))))) (S h7))
  have h17 := h v1 v1 y
  have h18 := h v1 v1 z
  have h19 := S h18
  have h20 := h v1 z x
  have h21 := S h20
  have h22 := C h14 h21
  have h23 := h x v1 v1
  have h24 := R z
  have h25 := C h24 (T h23 h22)
  have h26 := T h25 h19
  have h27 := S h23
  have h28 := C h14 h20
  have h29 := C h24 (T h28 h27)
  have h30 := S h17
  have h31 := C h15 (T h7 (C h14 (T (T (C h11 (T (C h9 h8) (S h10))) (C h11 h12)) (S h13))))
  have h32 := h v2 x y
  have h33 := h v2 x v0
  have h34 := h x v0 v2
  have h35 := h z v1 z
  have h36 := S h35
  let v37 := M v1 z
  let v38 := M z v37
  have h39 := h z v38 x
  have h40 := S h39
  have h41 := R x
  have h42 := h z v37 v5
  have h43 := S h42
  have h44 := h v1 z z
  have h45 := h z z x
  have h46 := S h45
  have h47 := C h14 h46
  have h48 := h x z v1
  have h49 := C h6 (C h24 (C (T (C h24 (T h48 h47)) (S h44)) h6))
  have h50 := h z (M z (M x z)) v5
  have h51 := h z x z
  have h52 := T (T (T h51 h50) h49) h43
  have h53 := h z (M v1 x) v5
  have h54 := h v1 x z
  have h55 := S h54
  have h56 := h x z x
  have h57 := h x x v1
  have h58 := C h24 (T h57 (C h14 (S h56)))
  have h59 := T h58 h55
  have h60 := C h24 (T (C h14 h56) (S h57))
  have h61 := h v1 x v1
  have h62 := h x v1 x
  have h63 := S h62
  have h64 := h z x x
  have h65 := h z x v1
  have h66 := S h65
  have h67 := C h14 (T h18 h29)
  have h68 := h v2 x v5
  have h69 := S h68
  have h70 := h x y v2
  have h71 := C h6 h70
  have h72 := T (T (T (T h71 h69) h32) h31) h30
  have h73 := C h14 h72
  have h74 := S h70
  have h75 := C h6 h74
  have h76 := T h68 h75
  have h77 := C h14 h76
  have h78 := C h41 (T (T (T (T (T h77 h73) h67) h66) h64) (C h41 h59))
  have h79 := h v1 v2 x
  have h80 := S h51
  have h81 := S h50
  have h82 := S h48
  have h83 := C h14 h45
  have h84 := C h6 (C h24 (C (T h44 (C h24 (T h83 h82))) h6))
  have h85 := T (T (T h42 h84) h81) h80
  have h86 := C h85 h11
  have h87 := h z v38 v2
  have h88 := C h52 h11
  have h89 := S h79
  have h90 := T h71 h69
  have h91 := C h14 h90
  have h92 := S h32
  have h93 := T (T (T (T h17 h16) h92) h68) h75
  have h94 := C h14 h93
  have h95 := C h14 h26
  have h96 := T h54 h60
  have h97 := C h41 (T (T (T (T (T (C h41 h96) (S h64)) h65) h95) h94) h91)
  have h98 := C h52 (T (T (T (C h11 h93) (C h11 (T (T (T (T (T (T h71 h69) h32) h31) h30) h18) (C h24 (T (T (T (T (T h28 h27) h62) h97) h89) h88))))) (S h87)) h36)
  have h99 := h v2 v1 v1
  have h100 := h v1 v2 v1
  have h101 := h z (M x v1) v5
  have h102 := C h41 (T (T (T (T (T h18 h29) h101) (C h6 (C h24 (T (C (T (T (T (T (T (T (T h62 h97) h89) h100) (C h14 (C h14 (T (T (T (T (T h99 h98) h86) h79) h78) h63)))) (S h61)) h54) h60) h6) (C h59 h6))))) (S h53)) (C h24 (C h52 h41)))
  have h103 := C h41 h72
  have h104 := C h9 (T (T (T h103 h102) h40) h36)
  have h105 := h x v5 v0
  have h106 := h x v5 v5
  have h107 := h v2 x z
  have h108 := h x v2 v1
  have h109 := h v2 z x
  have h110 := h v2 z v2
  have h111 := S h110
  have h112 := C h85 h24
  have h113 := C h24 (T (T (T (T h112 h20) h102) h40) h36)
  have h114 := C h52 h24
  have h115 := C h24 h114
  have h116 := T (T (T (T (T h51 h50) h49) h43) h115) h113
  have h117 := C h11 h116
  have h118 := S h99
  have h119 := C h85 (T (T (T h35 h87) (C h11 (T (T (T (T (T (T (C h24 (T (T (T (T (T h86 h79) h78) h63) h23) h22)) h19) h17) h16) h92) h68) h75))) (C h11 h72))
  have h120 := h x v1 z
  have h121 := h x v2 x
  have h122 := C h11 (T (T (T (T (T (T (T (T (C h24 (T h121 (C h41 (T (T (C h41 h76) h103) h21)))) (S h120)) h62) h97) h89) h88) h119) h118) h117)
  have h123 := h z x v2
  have h124 := T (T h123 h122) h111
  have h125 := C h41 h93
  have h126 := C h24 h112
  have h127 := C h41 (T (T (T (T (T (C h24 (C h85 h41)) h53) (C h6 (C h24 (T (C h96 h6) (C (T (T (T (T (T (T (T h58 h55) h61) (C h14 (C h14 (T (T (T (T (T h62 h97) h89) h88) h119) h118)))) (S h100)) h79) h78) h63) h6))))) (S h101)) h25) h19)
  have h128 := C h24 (T (T (T (T h35 h39) h127) h21) h114)
  have h129 := T (T (T (T (T h128 h126) h42) h84) h81) h80
  have h130 := C h11 h129
  have h131 := T (T h110 (C h11 (T (T (T (T (T (T (T (T h130 h99) h98) h86) h79) h78) h63) h120) (C h24 (T (C h41 (T (T h20 h125) (C h41 h90))) (S h121)))))) (S h123)
  have h132 := h v1 v1 v1
  have h133 := C h14 (T (T (T (T (T (T (T (T h25 h19) h132) (C h14 (T (T (T (T (T (T (T h67 h66) h51) h50) h49) h43) h115) h113))) (C h124 h129)) (C h131 h124)) (C h14 h109)) (S h108)) h46)
  have h134 := S h132
  have h135 := C h14 (T (T (T (T (T (T (T h128 h126) h42) h84) h81) h80) h65) h95)
  have h136 := C h131 h116
  have h137 := C h124 h131
  have h138 := C h14 (S h109)
  have h139 := C h14 (T (T (T (T (T (T (T (T h45 h108) h138) h137) h136) h135) h134) h18) h29)
  have h140 := h x x z
  have h141 := h x x y
  have h142 := h y x v0
  have h143 := h x (M y x) v5
  have h144 := h x y x
  have h145 := S h105
  have h146 := C h9 (T (T (T h35 h39) h127) h125)
  have h147 := h v2 v0 v2
  have h148 := h v2 v2 v0
  have h149 := T (T h3 (C h9 (T (T (T (T h92 h107) (C h24 (T (T (T (T (T (T (C h11 (T (T (T (T (T (T (T (T (T h48 h47) h139) h66) h51) h50) h49) h43) h115) h113)) h130) h99) h98) h86) h79) (C h41 (T (T (T (T (T h77 h73) h67) h133) h83) h82))))) (S h140)) h141))) (S h142)
  let v150 := M y v0
  T (T (T (T (h x y v0) (h v0 (M x v150) v5)) (C h6 (C h9 (T (T (T (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (h x v150 v5) (C h6 (C h41 (C (T (T (C h15 (T (T (T (T (h x y z) (h z (M x (M y z)) v5)) (C h6 (C h24 (C (T (C h41 (T (T (T h12 (C h52 h6)) (C (T (T (T (T (T (T h42 h84) h81) h80) h123) h122) h111) h6)) (C h131 h149))) (S (h v1 y x))) h6)))) (S (h z (M v1 y) v5))) (C h24 (C h52 h15)))) (S (h z v38 y))) h36) h6)))) (S (h x v2 v5))) h108) h138) h137) h136) h135) h134) h17) h16) h92) h33) (C h9 (C h11 (T (T h34 (C h11 (T (T (T (C h41 (T (T (T (T h146 h145) h106) (C h6 (C h41 (C h149 h6)))) (S h143))) (S h144)) h70) (C h11 (T h105 h104))))) (S h147))))) (S h148)) h6) (C (T (T (T (T (T (T (T h148 (C h9 (C h11 (T (T h147 (C h11 (T (T (T (C h11 (T h146 h145)) h74) h144) (C h41 (T (T (T (T h143 (C h6 (C h41 (C (T (T h142 (C h9 (T (T (T (T (S h141) h140) (C h24 (T (T (T (T (T (T (C h41 (T (T (T (T (T h48 h47) h139) h95) h94) h91)) h89) h88) h119) h118) h117) (C h11 (T (T (T (T (T (T (T (T (T h128 h126) h42) h84) h81) h80) h65) h133) h83) h82))))) (S h107)) h32))) h4) h6)))) (S h106)) h105) h104))))) (S h34))))) (S h33)) h32) h31) h30) h18) h29) h6)) (C h26 h6)) (C (T h17 h16) h6))))) (S (h v0 (M y (M v2 v0)) v5))) h4

