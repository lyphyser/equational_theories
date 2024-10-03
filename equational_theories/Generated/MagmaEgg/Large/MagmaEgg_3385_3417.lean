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
theorem Equation3385_implies_Equation3417 (G: Type _) [Magma G] (h: Equation3385 G) : Equation3417 G := fun x y z =>
  let v0 := M y x
  let v1 := M z v0
  have h2 := h z v1 z
  have h3 := S h2
  let v4 := M v1 z
  have h5 := h z (M z v4) v0
  have h6 := S h5
  have h7 := R v0
  let v8 := M z v1
  have h9 := h z v4 v8
  have h10 := S h9
  have h11 := R v8
  have h12 := h v1 z z
  have h13 := S h12
  have h14 := h z z v0
  have h15 := S h14
  have h16 := R v1
  have h17 := C h16 h15
  have h18 := h v0 z v1
  have h19 := h v0 z y
  have h20 := S h19
  have h21 := h z y x
  have h22 := S h21
  have h23 := h x z v0
  have h24 := R y
  have h25 := C h24 (T h23 (C h7 h22))
  have h26 := R z
  have h27 := C h26 (T (T (T h25 h20) h18) h17)
  have h28 := h z (M y (M x z)) v8
  have h29 := S h28
  have h30 := C h24 (T (C h7 h21) (S h23))
  have h31 := C h11 (C h26 (C (T h19 h30) h11))
  let v32 := M v0 z
  have h33 := h z v32 v8
  have h34 := T (T (T (T h33 h31) h29) h27) h13
  have h35 := C h11 (C h26 (C h34 h11))
  let v36 := M z v32
  have h37 := h z v36 v8
  have h38 := h z v0 z
  have h39 := T (T (T h38 h37) h35) h10
  have h40 := C h39 h7
  have h41 := h v1 v0 v0
  have h42 := h y x z
  have h43 := S h42
  have h44 := T (T (T h33 h31) h29) h43
  have h45 := C h44 h7
  have h46 := S h33
  have h47 := C h11 (C h26 (C (T h25 h20) h11))
  have h48 := S h18
  have h49 := C h16 h14
  have h50 := C h26 (T (T (T h49 h48) h19) h30)
  have h51 := T (T (T (T h12 h50) h28) h47) h46
  have h52 := C h51 h7
  have h53 := h v1 z v0
  have h54 := S h53
  have h55 := h v1 v1 v8
  have h56 := S h55
  have h57 := h v1 z v1
  have h58 := C h11 (T (T (T h42 h27) h13) h57)
  have h59 := T h58 h56
  have h60 := C h7 h59
  have h61 := C (T (T h42 h27) h13) (T (T (T (T h60 h54) h12) h50) h43)
  have h62 := h v0 v8 v0
  have h63 := T (T (T (T h14 h62) h61) h52) h45
  have h64 := C h16 h63
  have h65 := C h26 (T (T (C h7 (T (T h18 h17) h64)) (S h41)) h40)
  have h66 := h v0 v0 z
  have h67 := S h57
  have h68 := C h11 (T (T (T h67 h12) h50) h43)
  have h69 := T h55 h68
  have h70 := C h7 h69
  have h71 := h v1 v8 v8
  have h72 := C h11 (T (T (C h7 (T (T (T (T (T h62 h61) h52) h45) h66) h65)) h6) h3)
  have h73 := h v0 v0 v8
  have h74 := T h73 h72
  have h75 := C h16 h74
  have h76 := h v1 v0 v8
  have h77 := T (T h76 (C h11 (T (T h17 h64) h75))) (S h71)
  have h78 := C h7 (T (T (T (C h16 h77) h67) h53) h70)
  have h79 := h v1 v1 v0
  have h80 := C h7 (T (T (T (T (T (T (T (T h58 h56) h79) h78) h61) h52) h45) h66) h65)
  have h81 := S h79
  have h82 := S h62
  have h83 := C (T (T h12 h50) h43) (T (T (T (T h42 h27) h13) h53) h70)
  have h84 := C h34 h7
  have h85 := T (T (T h42 h28) h47) h46
  have h86 := C h85 h7
  have h87 := T (T (T (T h86 h84) h83) h82) h15
  have h88 := C h16 h87
  have h89 := S h73
  have h90 := S h66
  have h91 := S h38
  have h92 := S h37
  have h93 := C h11 (C h26 (C h51 h11))
  have h94 := T (T (T h9 h93) h92) h91
  have h95 := C h26 (T (T (C h94 h7) h41) (C h7 (T (T h88 h49) h48)))
  have h96 := C h11 (T (T h2 h5) (C h7 (T (T (T (T (T h95 h90) h86) h84) h83) h82)))
  have h97 := T h96 h89
  have h98 := C h16 h97
  have h99 := T (T h71 (C h11 (T (T h98 h88) h49))) (S h76)
  have h100 := C h7 (T (T (T h60 h54) h57) (C h16 h99))
  have h101 := C h7 (T (T (T (T (T (T (T (T h95 h90) h86) h84) h83) h100) h81) h55) h68)
  have h102 := T (T (T (T (T (T (T h2 h5) h101) h60) h54) h12) h50) h43
  have h103 := h x v0 v1
  have h104 := h v0 v1 v0
  have h105 := h v1 v0 z
  have h106 := C h16 (T (T (T (T (T (T (T (T h58 h56) h79) h78) h61) h52) h45) h73) h72)
  have h107 := C h16 h69
  have h108 := h v1 v1 v1
  have h109 := h z v4 v0
  have h110 := R x
  have h111 := h x v8 v1
  have h112 := T (T h111 (C h16 (C h110 (T (C h102 (T (T (T (T (T h38 h37) h35) h10) h109) (C h7 (T (T (C h26 h52) (C h26 (T (T (T (T (T h84 h83) h100) h81) h108) (C h16 (T (T (T (T (T h107 h106) h98) h88) h49) h48))))) (S h105))))) (S h104))))) (S h103)
  have h113 := h x v8 v8
  have h114 := C h110 h74
  have h115 := h v0 y x
  have h116 := h v0 y y
  have h117 := S h116
  let v118 := M x y
  have h119 := h y y v118
  have h120 := S h119
  have h121 := h y x y
  have h122 := R v118
  have h123 := C h122 h121
  have h124 := C h122 h102
  have h125 := T (T (T (T (T (T (T h42 h27) h13) h53) h70) h80) h6) h3
  have h126 := C h122 h125
  have h127 := S h121
  have h128 := C h122 h127
  have h129 := h y y x
  have h130 := h x (M y v0) v8
  have h131 := h y v0 v8
  have h132 := S h131
  have h133 := C h11 (T (T (C h24 h97) (C h24 h87)) (C h24 h14))
  have h134 := h y v8 v8
  have h135 := h x (M y v8) v8
  have h136 := C h102 (T (T (T (T (T (T h135 (C h11 (C h110 (C (T (T h134 h133) h132) h11)))) (S h130)) (S h129)) h119) h128) h126)
  have h137 := h x y v8
  have h138 := C h24 (T (T h137 h136) (C h7 (T (T h124 h123) h120)))
  have h139 := C h24 (T (T (C h7 (T (T h119 h128) h126)) (C h125 (T (T (T (T (T (T h124 h123) h120) h129) h130) (C h11 (C h110 (C (T (T h131 (C h11 (T (T (C h24 h15) (C h24 h63)) (C h24 h74)))) (S h134)) h11)))) (S h135)))) (S h137))
  have h140 := T (T (T (T (C (T (T (T (T h2 h5) h101) h60) h54) h24) (C h51 h24)) (C h44 h24)) h116) h139
  have h141 := S h115
  have h142 := C h110 h97
  have h143 := T (T (T (T h53 h70) h80) h6) h3
  have h144 := C h34 h26
  have h145 := C h85 h26
  have h146 := h z v4 z
  have h147 := T (T (T (T (T (C h26 (T (T (T (T (T (T h2 h5) h101) h60) h54) h12) (C h26 (T (T (T h49 h48) h145) h144)))) (S h146)) h9) h93) h92) h91
  have h148 := C h26 (T (T (T (T (T (T (C h26 (T (T (T (C h51 h26) (C h44 h26)) h18) h17)) h13) h53) h70) h80) h6) h3)
  have h149 := C h26 (C h85 h110)
  have h150 := C h26 (T (C h16 h23) (S (h v0 x v1)))
  have h151 := h v1 x z
  have h152 := h x z v1
  have h153 := h x v1 v8
  have h154 := h v1 y x
  have h155 := h v1 y v8
  have h156 := h y z v1
  have h157 := h y z y
  have h158 := S h157
  have h159 := h x v1 v1
  have h160 := h v1 v8 y
  have h161 := C h24 (T h160 (C h24 (T (T (T (C h16 h140) (C h16 (T (T (T (T h138 h117) h115) h114) (C h110 (T (T (T (T (T (T h96 h89) h86) h84) h83) h100) h81))))) (S h159)) h22)))
  have h162 := h y v1 v8
  have h163 := C h24 h147
  have h164 := h x x v8
  have h165 := h x y x
  T (T (T (T (T (T (T (T (T (T (T h137 h136) (C h7 (T (T (T (T (T (T (T (T (T (T (T (T (T (T h124 h123) h120) (h y y v8)) (C h102 (T (T (T (T (T (T (T (T (T (T (T (C h24 (T (T (T (T (T (T (T h134 h133) h132) (h y v0 v118)) (C h122 (T (T (T (T (T (S (h v0 x y)) (h v0 x z)) (C h26 (T (T (T (C h125 h152) (S (h v1 x v8))) (h v1 x x)) (C h110 (T (T (T (T (T (T (T (T (T (T (C h16 (T h164 (C h11 (T (C h110 h112) (S h165))))) (C h16 (T (T (T (T (T (C h11 (T h165 (C h110 (T (T h103 (C h16 (C h110 (T h104 (C h125 (T (T (T (T (T (C h7 (T (T h105 (C h26 (T (T (T (T (T (C h16 (T (T (T (T (T h18 h17) h64) h75) (C h16 (T (T (T (T (T (T (T (T h96 h89) h86) h84) h83) h100) h81) h55) h68))) (C h16 h59))) (S h108)) h79) h78) h61) h52))) (C h26 h84))) (S h109)) h9) h93) h92) h91)))))) (S h111))))) (S h164)) (h x x v1)) (C h16 (T (T (T (T (C h110 h22) (C h110 (T (T (T (T (T (T (T (T h21 h153) (C h11 (T (T (T (T (T (C h110 h99) (S h154)) h155) (C h11 (T (T (S h156) h157) (C h24 (T (C h24 (T (T (T h21 h159) (C h16 (T (T (T (T (C h110 (T (T (T (T (T (T h79 h78) h61) h52) h45) h73) h72)) h142) h141) h116) h139))) (C h16 (T (T (T (T h138 h117) (C h85 h24)) (C h34 h24)) (C h143 h24))))) (S h160)))))) (S h162)) (C h24 (T (T (T (T (T h38 h37) h35) h10) h146) h148))))) (C h102 (T (T (T (T (T h163 h162) (C h11 (T (T (T (T (T (T h161 h158) (h y z v8)) (C h11 (T (T (T (T (T h163 h162) (C h11 (T (T h161 h158) h156))) (S h155)) h154) (C h110 h77)))) (S h153)) (h x v1 x)) (C h110 (T (T (T (T (T (T (C h110 (T (T h151 h150) h149)) (S (h z v36 x))) h37) h35) h10) h146) h148))))) (S (h x z v8))) h152) (C h16 h112)))) (S (h v1 x v0))) h151) h150) h149) (C h26 (C h34 h110))))) (S (h z v4 x))) h146) h148))) (C h39 h147)) (C h94 h16)))) h107) h106) h98) h88) h49) h48) h145) h144) (C h143 h26)))))) (S (h x v8 z))) h113) (C h102 (T (T (T h142 h141) h116) h139))))) (S (h v0 y v118))) h116) h139)) h127) h42) h27) h13) h53) h70) h80) h6) h3) (h z v1 v0)) (C h7 (T (T (C h26 h40) h95) h90))))) (S (h v0 v0 v0))) h86) h84) h83) h82) (h v0 v8 y)) (C h24 (T (T (C h7 h140) (C h125 (T (T (T h138 h117) h115) h114))) (S h113)))) (h y (M x v8) v8)) (C h102 (C h24 (C h112 h102)))) (S (h y (M x v0) v0))))) (S (h y x v0))) h42) h27) h13) h53) h70) h80) h6) h3

