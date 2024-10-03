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
theorem Equation522_implies_Equation2992 (G: Type _) [Magma G] (h: Equation522 G) : Equation2992 G := fun x y z =>
  let v0 := M z y
  let v1 := M y v0
  let v2 := M v1 x
  let v3 := M v2 z
  have h4 := h v3 v3 v2
  have h5 := S h4
  have h6 := h v2 v3 z
  have h7 := S h6
  have h8 := R v3
  have h9 := h z v3 v3
  have h10 := R v2
  have h11 := C h10 (T h9 (C h8 h7))
  have h12 := C h8 (C h8 h11)
  have h13 := R v1
  have h14 := h v1 v3 y
  have h15 := S h14
  have h16 := h y v1 v0
  have h17 := S h16
  have h18 := C h13 h17
  have h19 := h v0 v1 v1
  have h20 := R y
  have h21 := C h20 (T h19 h18)
  have h22 := C h8 h21
  have h23 := C h8 h22
  have h24 := h z v3 y
  have h25 := T (T h24 h23) h15
  have h26 := C h25 (T h12 h5)
  have h27 := S h9
  have h28 := C h10 (T (C h8 h6) h27)
  have h29 := C h8 (C h8 h28)
  have h30 := h v3 z v2
  have h31 := S h30
  have h32 := R z
  have h33 := C h32 (C h32 h11)
  have h34 := C h32 (T (T (T h33 h31) h4) h29)
  have h35 := h v2 z z
  have h36 := R (M z v3)
  have h37 := S h24
  have h38 := S h19
  have h39 := C h13 h16
  have h40 := C h20 (T h39 h38)
  have h41 := C h8 h40
  have h42 := C h8 h41
  have h43 := T (T h14 h42) h37
  have h44 := C h43 (T (T (C h43 h36) h33) h31)
  have h45 := h v2 v1 z
  have h46 := S h35
  have h47 := C h32 (C h32 h28)
  have h48 := C h32 (T (T (T h12 h5) h30) h47)
  have h49 := C h43 (T h4 h29)
  have h50 := C h8 (T (T (T (T h49 h48) h46) h45) h44)
  have h51 := h z v2 v0
  have h52 := S h51
  have h53 := h v0 z v1
  have h54 := S h53
  let v55 := M v0 v1
  have h56 := R (M v1 v55)
  have h57 := h y v0 v0
  have h58 := S h57
  have h59 := h z v0 y
  have h60 := h z v1 y
  have h61 := S h60
  have h62 := R v0
  have h63 := C h62 (T h61 h59)
  have h64 := C h62 (T (T (T h14 h42) h37) h60)
  have h65 := C h43 (T (T (T (T h64 h63) h58) h16) (C h43 h56))
  have h66 := R v55
  have h67 := C h25 h66
  have h68 := C h62 (T (T (T h61 h24) h23) h15)
  have h69 := S h59
  have h70 := C h62 (T h69 h60)
  have h71 := h y y v0
  have h72 := S h71
  have h73 := C h20 (C h20 (T (T h57 h70) h68))
  have h74 := C h43 (T (T (T (T h73 h72) h57) h70) h68)
  have h75 := R (M y (M y y))
  have h76 := C h20 (C h20 (T (T h64 h63) h58))
  have h77 := h y v1 y
  have h78 := S h77
  have h79 := C h25 (T (T (T (T h64 h63) h58) h71) h76)
  have h80 := C h43 h66
  have h81 := C h25 (T (T (T (T (C h25 h56) h17) h57) h70) h68)
  have h82 := h v0 y v1
  have h83 := h v1 v0 v0
  have h84 := S h83
  have h85 := h v0 v0 z
  have h86 := S h85
  have h87 := C h62 (C h62 (C h32 (T (T h57 h70) (C h62 h61))))
  have h88 := C h25 (T h87 h86)
  have h89 := C h62 (C h62 (C h32 (T (T (C h62 h60) h63) h58)))
  have h90 := C h32 (T (T (T (T h67 h65) h54) h85) h89)
  have h91 := h y z v0
  have h92 := C h62 (T (T (T (T h73 h72) h91) h90) h88)
  have h93 := h y v0 y
  have h94 := C h62 (T (T (T h73 h72) h93) (C h62 h92))
  have h95 := S h91
  have h96 := C h32 (T (T (T (T h87 h86) h53) h81) h80)
  have h97 := C h43 (T h85 h89)
  have h98 := C h62 (T (T (T (T h97 h96) h95) h71) h76)
  have h99 := C h62 (T (T h91 h90) h88)
  have h100 := C h13 (T (T (T (T (T (C h20 (T (T (T (T (T h99 h98) h94) h84) h21) (C h20 (T (T (T h39 h38) h53) h81)))) (S h82)) h53) h81) h80) h79)
  have h101 := R (M y (M v0 y))
  have h102 := C h25 h101
  have h103 := C h62 (T (T h97 h96) h95)
  have h104 := C h62 (T (T (T (C h62 h98) (S h93)) h71) h76)
  have h105 := T (T (T (T (T (T h61 h24) h23) h15) h83) h104) h92
  have h106 := C h32 (T (T (C h20 h60) (C h20 h105)) (C h20 h103))
  have h107 := h y v1 z
  have h108 := h y v0 z
  have h109 := T (T (T (T (T (T h98 h94) h84) h14) h42) h37) h60
  have h110 := C h32 (T (T (C h20 h99) (C h20 h109)) (C h20 h61))
  have h111 := C h43 h101
  have h112 := C h13 (T (T (T (T (T h74 h67) h65) h54) h82) (C h20 (T (T (T (T (T (C h20 (T (T (T h65 h54) h19) h18)) h40) h83) h104) h92) h103)))
  have h113 := h v1 v1 v1
  have h114 := S h113
  have h115 := C h25 (C h13 h60)
  have h116 := C h43 (C h13 h61)
  have h117 := h z z y
  have h118 := S h117
  have h119 := R (M z v1)
  have h120 := C h43 h119
  have h121 := T (T (T (T (T (T h120 h118) h24) h23) h15) h113) h116
  have h122 := C h62 (T (T (T (T (C h62 h121) (C h62 (T (T (T (T (T (T h115 h114) h14) h42) h37) h59) (C h62 (T (T (T (T (T (T h64 h63) h58) h77) h112) h111) h110))))) (S h108)) h107) (C h43 (T (T (T (T (T (C h43 (T (T (T (T (T h106 h102) h100) h78) h71) h76)) (C h25 h75)) h74) h67) h65) h54)))
  have h123 := h z v0 v1
  have h124 := T (T (T h120 h118) h123) h122
  have h125 := C h25 h119
  have h126 := T (T (T (T (T (T h115 h114) h14) h42) h37) h117) h125
  have h127 := T (T (T (T h98 h94) h84) h113) h116
  have h128 := T (T h83 h104) h92
  have h129 := h v1 v2 v1
  have h130 := h v3 v2 v2
  have h131 := h v3 z v3
  have h132 := C h10 (T (T (T (T (T (T (T (C h32 (T h35 h34)) (S h131)) h130) (C h10 (T (T (C h10 h28) (C h10 (C h10 h60))) (S h129)))) (C h10 h128)) (C h10 h127)) (C h10 h126)) (C h10 h124))
  have h133 := C h10 (C h43 h10)
  have h134 := T (T (T (T h133 h132) h52) h9) (C h8 (T (T (T h7 h35) h34) h26))
  have h135 := C h10 (C h25 h10)
  have h136 := T (T (T (T h115 h114) h83) h104) h92
  have h137 := S h123
  have h138 := C h62 (T (T (T (T (C h25 (T (T (T (T (T h53 h81) h80) h79) (C h43 h75)) (C h25 (T (T (T (T (T h73 h72) h77) h112) h111) h110)))) (S h107)) h108) (C h62 (T (T (T (T (T (T (C h62 (T (T (T (T (T (T h106 h102) h100) h78) h57) h70) h68)) h69) h24) h23) h15) h113) h116))) (C h62 h126))
  have h139 := T (T (T h138 h137) h117) h125
  have h140 := C h10 (T (T (T (T (T (T (T (C h10 h139) (C h10 h121)) (C h10 h136)) (C h10 (T (T h98 h94) h84))) (C h10 (T (T h129 (C h10 (C h10 h61))) (C h10 h11)))) (S h130)) h131) (C h32 (T h48 h46)))
  have h141 := T (T (T h138 h137) h51) h140
  have h142 := C h8 (T (T (T h49 h48) h46) h6)
  have h143 := S h45
  have h144 := C h25 (T (T h30 h47) (C h25 h36))
  have h145 := C h8 (T (T (T (T h144 h143) h35) h34) h26)
  have h146 := h v2 v2 z
  have h147 := C h10 (C h10 (T h144 h143))
  have h148 := S (h v2 x v2)
  have h149 := R x
  T (T (T (h x v3 v1) (C h8 (T (T (C h8 (T (T (C h43 (T (T (T (T (T (T (T (T (T (T (T (C h149 h128) (C h149 h127)) (C h149 h126)) (C h149 h124)) (C h149 h141)) (C h149 h135)) (C h149 h134)) (C h149 h50)) (C h149 (T (T (T (T h145 h142) h27) (h z x x)) (C h149 (T (T (T (C h149 (C h149 (T (T (C h25 h149) h146) h147))) h148) h146) h147))))) h148) h146) h147)) (C h25 (R (M v2 (M v2 v2))))) (C h13 (T (T (T (T (T (T (T (T (T (T (T (T (C h10 (C h10 (T h45 h44))) (S h146)) h6) (C h8 h145)) (C h8 (T (T (T (T h142 h27) h51) h140) h135))) (C h8 h133)) (C h8 (T (T (T h132 h52) h123) h122))) (C h8 h139)) (C h8 h121)) (C h8 h136)) (C h8 h109)) (C h8 (T (T (T (T h61 h24) h23) h15) h21))) h41)))) (C h8 (C h43 (T (T h22 (C h8 (T (T (T (T h40 h14) h42) h37) h60))) (C h8 h61))))) (C h8 (T (C h25 (T (T (T (T (T (T (T (T (T (T (T (T (T (C h8 h60) (C h8 h105)) (C h8 h127)) (C h8 h126)) (C h8 h124)) (C h8 h141)) (C h8 h135)) (C h8 h134)) (C h8 h50)) h7) h35) h34) h26) (C h13 h11))) (S (h v3 v1 v2))))))) h12) h5

