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
theorem Equation2917_implies_Equation4013 (G: Type _) [Magma G] (h: Equation2917 G) : Equation4013 G := fun x y z =>
  let v0 := M y z
  let v1 := M z v0
  let v2 := M v1 x
  have h3 := h v1 v2 z
  have h4 := S h3
  have h5 := R z
  let v6 := M v1 v2
  let v7 := M v2 v6
  let v8 := M v7 z
  have h9 := h v8 y z
  have h10 := R y
  have h11 := h v8 z v2
  have h12 := R v2
  have h13 := C h5 h3
  have h14 := R v1
  let v15 := M x y
  have h16 := h z v15 y
  have h17 := S h16
  let v18 := M (M v15 (M z v15)) y
  have h19 := h v18 y y
  have h20 := C h10 h16
  have h21 := h y y v0
  have h22 := R v0
  have h23 := C h22 (S h21)
  have h24 := C (T (C (T h23 (C h20 h10)) h10) (S h19)) h10
  let v25 := M (M y (M y y)) v0
  have h26 := h v25 v0 y
  have h27 := h v25 v0 x
  have h28 := S h27
  have h29 := R x
  have h30 := C h22 h21
  have h31 := h y z v0
  have h32 := C (C (T (C h22 (S h31)) h30) h29) h29
  have h33 := h (M v1 v0) v0 x
  have h34 := h v0 z v1
  let v35 := M z (M v0 z)
  have h36 := h (M v35 v1) v1 v0
  have h37 := h v35 y x
  have h38 := S h37
  have h39 := h (M v35 y) y x
  have h40 := h v0 z y
  have h41 := h v0 v2 y
  have h42 := C h10 (S h41)
  let v43 := M v2 (M v0 v2)
  have h44 := h (M v43 y) y x
  have h45 := C (C (C h10 (T (T h44 (C (C (T h42 (C h10 h40)) h29) h29)) (S h39))) h29) h29
  have h46 := S h44
  have h47 := C h10 h41
  have h48 := h v0 v0 y
  let v49 := M v0 (M v0 v0)
  have h50 := h (M v49 y) y x
  have h51 := h v49 y x
  have h52 := h y v1 z
  have h53 := S h52
  have h54 := h (M (M v1 (M y v1)) z) z x
  have h55 := C (C h5 h52) h29
  have h56 := h y z z
  have h57 := h (M v1 z) z x
  have h58 := h z z v1
  have h59 := C (T (C (T (T (T (C h14 (S h58)) h57) (C (T (C (C h5 (S h56)) h29) h55) h29)) (S h54)) h5) h53) h5
  let v60 := M (M z (M z z)) v1
  have h61 := h v60 v1 z
  have h62 := C (T (T (T (T (T (T (T (T (C (T (T (T (T (C h22 (C (T h61 h59) h22)) h51) (C (C (C h10 (T (T h50 (C (C (T (C h10 (S h48)) h47) h29) h29)) h46)) h29) h29)) h45) h38) h14) h36) (C (C (T (T (T (T (T (T (C h14 (S h34)) h33) h32) h28) h26) h24) h17) h22) h22)) h33) h32) h28) h26) h24) h17) h14
  have h63 := h v60 v0 v1
  have h64 := S h61
  have h65 := S h57
  have h66 := C (T (C (C h5 h53) h29) (C (C h5 h56) h29)) h29
  have h67 := C (T h52 (C (T (T (T h54 h66) h65) (C h14 h58)) h5)) h5
  have h68 := C (T (T (T (T h67 h64) h63) h62) h13) h12
  have h69 := C h10 h17
  have h70 := h v18 y v2
  have h71 := h v18 y x
  have h72 := h z v0 y
  have h73 := S h72
  have h74 := h (M (M v0 v1) y) y x
  have h75 := h y z x
  have h76 := S h75
  have h77 := h v0 z z
  have h78 := h (M v35 z) z x
  have h79 := h v43 y x
  have h80 := S h63
  have h81 := C (C (C h10 (T (T h39 (C (C (T (C h10 (S h40)) h47) h29) h29)) h46)) h29) h29
  have h82 := S h33
  have h83 := C (C (T h23 (C h22 h31)) h29) h29
  have h84 := S h26
  have h85 := C (T h19 (C (T (C h69 h10) h30) h10)) h10
  have h86 := C (T (T (T (T (T (T (T (T h16 h85) h84) h27) h83) h82) (C (C (T (T (T (T (T (T h16 h85) h84) h27) h83) h82) (C h14 h34)) h22) h22)) (S h36)) (C (T (T (T (T h37 h81) (C (C (C h10 (T (T h44 (C (C (T h42 (C h10 h48)) h29) h29)) (S h50))) h29) h29)) (S h51)) (C h22 (C (T h67 h64) h22))) h14)) h14
  have h87 := C h5 h4
  have h88 := C (T (T (T (T h87 h86) h80) h61) h59) h12
  let v89 := M z v1
  have h90 := h v89 v2 z
  have h91 := C (T (T (T (T (T h67 h64) h63) h62) h90) (C (T (T (T (C (T (T (T (C h12 (T (C h13 h12) h88)) h79) h45) h38) h5) h78) (C (C (C h5 (S h77)) h29) h29)) h76) (T h72 (C (T (T (T (T (T h74 (C (T (C (C h10 h73) h29) (C h20 h29)) h29)) (S h71)) h70) (C (T (C h69 h12) h68) h12)) (S h11)) h10)))) h5
  have h92 := h x v1 v2
  have h93 := S h92
  have h94 := T (C h12 h93) h76
  have h95 := C (C h94 h5) h5
  let v96 := M (M v1 (M x v1)) v2
  have h97 := h v96 v2 z
  have h98 := S h97
  have h99 := T h75 (C h12 h92)
  have h100 := C (C h99 h5) h5
  have h101 := h z v1 v0
  have h102 := T (T (C h22 (S h101)) h100) h98
  have h103 := C (T (T (C h102 h5) (C (T (T h97 h95) h91) h5)) (S h9)) h5
  have h104 := T (T h97 h95) (C h22 h101)
  have h105 := C h104 h5
  have h106 := C (T (T (C (T (T (T (T (T (C (T (T (T h75 (C (C (C h5 h77) h29) h29)) (S h78)) (C (T (T (T h37 h81) (S h79)) (C h12 (T h68 (C h87 h12)))) h5)) (T (C (T (T (T (T (T h11 (C (T h88 (C h20 h12)) h12)) (S h70)) h71) (C (T (C h69 h29) (C (C h10 h72) h29)) h29)) (S h74)) h10) h73)) (S h90)) h86) h80) h61) h59) h5) h100) h98) h5
  have h107 := h v96 v2 v2
  have h108 := S h107
  have h109 := h v2 x y
  have h110 := C h29 h75
  have h111 := C h10 (T (C (C h110 h10) h10) (S h109))
  have h112 := C (T h111 (C h99 h12)) h12
  have h113 := C h29 h76
  have h114 := C h113 h10
  have h115 := C h10 (T h109 (C h114 h10))
  have h116 := h v1 v2 x
  have h117 := S h116
  have h118 := h (M v7 x) x x
  have h119 := h v1 x x
  let v120 := M x v2
  have h121 := h (M v120 x) x x
  have h122 := h v2 x x
  have h123 := h (M v15 x) x x
  have h124 := h v15 v2 v15
  have h125 := S h124
  have h126 := R v15
  have h127 := h (M (M v2 (M v15 v2)) v15) v15 v15
  have h128 := h v2 x v15
  have h129 := h x v2 v1
  have h130 := C h14 (S h129)
  let v131 := M (M v2 v120) v1
  have h132 := h v131 v1 v15
  have h133 := h v131 v1 x
  have h134 := C h14 h129
  have h135 := h x y y
  let v136 := M y v15
  have h137 := h (M v136 y) y x
  have h138 := T (C h10 (T h137 (C (T (T (T (C (T (T (T (T (T (C h10 (S h135)) (C (T h75 (C h134 h29)) h29)) (S h133)) h132) (C (T (T (C h130 h126) (C (T h128 (C (T (C h113 h126) (C h126 h124)) h126)) h126)) (S h127)) h126)) h125) h29) h123) (C (T (T (T (C (C h29 (T (C (C h110 h29) h29) (S h122))) h29) h121) (C (T (C (C h29 (S h119)) h29) (C (C h29 h116) h29)) h29)) (S h118)) h29)) h117) h29))) h115
  have h139 := h v136 y v2
  have h140 := h y v0 v15
  have h141 := S h140
  let v142 := M (M v0 (M y v0)) v15
  have h143 := h v142 v15 x
  have h144 := C h126 h140
  have h145 := h y z v15
  have h146 := h (M v1 v15) v15 x
  have h147 := h v15 v1 v1
  let v148 := M (M v1 (M v15 v1)) v1
  let v149 := M (M v1 v89) v0
  have h150 := h v149 v0 z
  have h151 := h v149 v0 v2
  have h152 := S h121
  have h153 := C (T (C (C h29 h117) h29) (C (C h29 h119) h29)) h29
  have h154 := h v1 v1 v2
  have h155 := h y v2 z
  have h156 := T (T (T h155 (C (T (T (T (T (T (T (h (M (M v2 (M y v2)) z) z x) (C (T (C (C h5 (S h155)) h29) h55) h29)) h66) h65) (C (T (T (T (T (T (T (T (T (T (T (T h3 (C (T (T h9 h106) h105) h5)) (S h150)) h151) (C (T (C h102 h12) h93) h12)) (h v120 v2 v2)) (C (T (C (T (C h12 (T (T (T (T (T (T (T (T (T (T (T (T (h (M v120 v2) v2 x) (C (C (T (C h12 (S (h v1 x v2))) (C h12 h154)) h29) h29)) (C (C (T (C h12 (S h154)) (C h12 (h v1 v2 v2))) h29) h29)) (S (h (M v7 v2) v2 x))) (C (T (T (T (T (T (T (T (h v7 x x) (C (C (C h29 (T (T h118 h153) h152)) h29) h29)) (S (h v120 x x))) (C (T h92 (C h104 h12)) h12)) (S h151)) h150) h103) h4) h12)) (h v6 v2 x)) (C (T (C (T (T (C h12 (S (h y z v2))) (C (T h109 (C (T h114 h144) h10)) h10)) (S (h v142 v15 y))) h29) (C (T (T (T h143 (C (C (T (C h126 h141) (C h126 h145)) h29) h29)) (S h146)) (C h14 h147)) h29)) h29)) (S (h v148 v1 x))) (h v148 v1 v15)) (C (T (C (T (T (T (C h14 (S h147)) h146) (C (C (T (C h126 (S h145)) h144) h29) h29)) (S h143)) h126) h141) h126)) h139) (C (T (T (C h138 h12) h112) h108) h12)) h93)) h76) h12) h115) h12)) h112) h108) h97) h95) h91) h5)) h106) h105) h5)) h103) h4
  let v157 := M z (M v2 z)
  have h158 := h (M v15 y) y x
  T (C (T (T (T (T (T (T h92 (C (T (T h107 (C (T (C h94 h12) h115) h12)) (C (T h111 (C h10 (T (C (T (T (T h116 (C (T (T (T h118 h153) h152) (C (C h29 (T h122 (C (C h113 h29) h29))) h29)) h29)) (S h123)) (C (T (T (T (T (T h124 (C (T (T h127 (C (T (C (T (C h126 h125) (C h110 h126)) h126) (S h128)) h126)) (C h134 h126)) h126)) (S h132)) h133) (C (T (C h130 h29) h76) h29)) (C h10 h135)) h29)) h29) (S h137)))) h12)) h12)) (S h139)) (h v136 y x)) (C (C h138 h29) h29)) (S h158)) (C (T (T (T (h v15 y x) (C (C (C h10 (T (T h158 (C (C (T h111 (C h10 (h v2 z y))) h29) h29)) (S (h (M v157 y) y x)))) h29) h29)) (S (h v157 y x))) (R v157)) h156)) h156) (S (h v2 z v1))

