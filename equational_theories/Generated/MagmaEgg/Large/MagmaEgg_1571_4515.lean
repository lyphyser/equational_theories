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
theorem Equation1571_implies_Equation4515 (G: Type _) [Magma G] (h: Equation1571 G) : Equation4515 G := fun x y z =>
  let v0 := M x z
  let v1 := M v0 y
  let v2 := M v1 y
  have h3 := h v1 v1 (M v0 v2)
  have h4 := S h3
  have h5 := h v1 v0 y
  have h6 := R v1
  have h7 := h y x z
  have h8 := S h7
  have h9 := R v0
  have h10 := C h9 h8
  let v11 := M y z
  have h12 := h y v11 v11
  have h13 := S h12
  have h14 := h y y z
  let v15 := M v11 v11
  have h16 := R v15
  have h17 := C h16 h14
  have h18 := T (T h17 h13) h7
  have h19 := C h6 (T (C h9 h18) h10)
  have h20 := h v15 v0 y
  have h21 := C h5 (T (T h20 h19) (C h6 h5))
  have h22 := h v15 v15 v0
  have h23 := S h22
  let v24 := M x v0
  have h25 := h v0 v0 v24
  have h26 := S h25
  have h27 := h x x z
  have h28 := C h27 (C h9 h27)
  have h29 := T h28 h26
  let v30 := M v0 v11
  have h31 := h v15 v30 y
  have h32 := S h31
  have h33 := C h16 (S h14)
  have h34 := T (T h8 h12) h33
  have h35 := R v30
  have h36 := h x v0 v11
  have h37 := C (T h36 (C h35 h8)) (T h36 (C h35 h34))
  have h38 := T h37 h32
  have h39 := C h38 h29
  have h40 := h v0 x x
  have h41 := S h27
  have h42 := C h41 (C h9 h41)
  have h43 := T h25 h42
  have h44 := S h36
  have h45 := C (T (C h35 h7) h44) (T (C h35 h18) h44)
  have h46 := T h31 h45
  have h47 := C h46 h43
  have h48 := T h40 h39
  have h49 := C h48 (T h47 (C h38 (T (T (T h28 h26) h40) h39)))
  have h50 := C h29 h48
  have h51 := T (T h50 h49) h23
  have h52 := C h6 h51
  have h53 := S h40
  have h54 := T h47 h53
  have h55 := C h43 h54
  have h56 := C h54 (T (C h46 (T (T (T h47 h53) h25) h42)) h39)
  have h57 := h v15 v1 y
  have h58 := S h57
  let v59 := M x v11
  let v60 := M v0 (M y v59)
  have h61 := h y y v60
  have h62 := R v60
  have h63 := h y v0 v59
  have h64 := T h63 (C h8 h62)
  have h65 := R y
  let v66 := M y y
  have h67 := h v66 x v0
  have h68 := h v0 v0 v59
  have h69 := S h68
  have h70 := C h9 h7
  have h71 := C h7 h70
  have h72 := R v66
  have h73 := h v0 y y
  have h74 := R x
  have h75 := h v0 v1 v1
  have h76 := h v0 v0 y
  let v77 := M v1 v1
  have h78 := R v77
  have h79 := R v24
  have h80 := h v77 x v0
  let v81 := M x (M v0 x)
  have h82 := h v81 v59 v0
  have h83 := S h82
  have h84 := T (T h22 h56) h55
  have h85 := R v59
  have h86 := h x v59 v59
  have h87 := S h86
  have h88 := h x x v11
  let v89 := M v59 v59
  have h90 := R v89
  have h91 := C h90 h88
  have h92 := T h91 h87
  have h93 := C h92 (T (C h90 (T (T h91 h87) h88)) h87)
  have h94 := h v89 v89 x
  have h95 := h v59 x v11
  have h96 := S h95
  have h97 := h v59 v59 (M x (M v59 v11))
  let v98 := M v59 v0
  have h99 := R v98
  have h100 := C h99 (T (T h97 (C h96 (T (T (T (T (C h85 h96) h94) h93) h37) h32))) (C h85 h84))
  have h101 := C h43 (T (T (T h100 h83) h28) h26)
  have h102 := h v98 v0 v59
  have h103 := h v98 v1 v59
  have h104 := S h103
  have h105 := S h94
  have h106 := S h88
  have h107 := C h90 h106
  have h108 := T h86 h107
  have h109 := C h108 (T h86 (C h90 (T (T h106 h86) h107)))
  have h110 := C h99 (T (T (C h85 h51) (C h95 (T (T (T (T h31 h45) h109) h105) (C h85 h95)))) (S h97))
  have h111 := h v1 v0 v59
  let v112 := M v1 v59
  let v113 := M v0 v112
  have h114 := R v113
  have h115 := T (C h7 h114) (S h111)
  have h116 := C h115 (T (T (C h65 h115) h71) h69)
  have h117 := h y y v113
  have h118 := R v112
  have h119 := C h118 (T (T (T h117 h116) (C h6 h48)) (C h6 (T (T (T (T (T h47 h53) h25) h42) h82) h110)))
  have h120 := R v2
  have h121 := C h120 (T (C h6 (T (T (T (T (T h119 h104) h102) (C h8 (T (T (T h101 h50) h49) h23))) (C h64 (T (T (T (T (T h20 h19) h80) (C h79 (T (C h74 (T (C h78 h76) (S h75))) (C h74 (T h73 (C h72 (T h71 h69))))))) (S h67)) (C h65 h64)))) (S h61))) (C h6 (T h12 h33)))
  have h122 := h v112 v1 y
  have h123 := C h6 (T (T (T (T (T h122 h121) h58) h22) h56) h55)
  have h124 := S h122
  have h125 := S h117
  have h126 := T h111 (C h8 h114)
  have h127 := C h8 h10
  have h128 := C h126 (T (T h68 h127) (C h65 h126))
  have h129 := C h6 h54
  have h130 := C h6 (T (T (T (T (T h100 h83) h28) h26) h40) h39)
  have h131 := C h118 (T (T (T h130 h129) h128) h125)
  have h132 := S h102
  have h133 := C h29 (T (T (T h25 h42) h82) h110)
  have h134 := C h7 (T (T (T h22 h56) h55) h133)
  have h135 := S h20
  have h136 := C h6 (T h70 (C h9 h34))
  have h137 := S h76
  have h138 := T (C h7 h62) (S h63)
  have h139 := C h138 (T (T (T (T (T (C h65 h138) h67) (C h79 (T (C h74 (T (C h72 (T h68 h127)) (S h73))) (C h74 (T h75 (C h78 h137)))))) (S h80)) h136) h135)
  have h140 := C h120 (T (C h6 (T h17 h13)) (C h6 (T (T (T (T (T h61 h139) h134) h132) h103) h131)))
  have h141 := T (T (T h123 h52) h21) h4
  have h142 := C h141 h6
  have h143 := C h6 (T (T (T (T (T h142 h136) h135) h57) h140) h124)
  have h144 := C h6 (T (T (T (T (T h50 h49) h23) h57) h140) h124)
  have h145 := C h6 h84
  have h146 := S h5
  have h147 := C h146 (T (T (C h6 h146) h136) h135)
  have h148 := T (T (T h3 h147) h145) h144
  have h149 := C h148 h6
  have h150 := C (T (T h122 h121) h58) h6
  have h151 := C h9 h150
  have h152 := C (T (T (T (T h136 h135) h57) h140) h124) (T (T (T (T h143 h123) h52) h21) h4)
  let v153 := M v1 v112
  have h154 := h v153 v1 v1
  have h155 := T (T (T (T (T h3 h147) h145) h144) h154) h152
  have h156 := C h29 h155
  have h157 := C h43 h6
  let v158 := M v0 v1
  have h159 := h v158 v1 v0
  have h160 := S h159
  have h161 := h v0 v0 (M x (M v0 z))
  have h162 := S h161
  have h163 := h v0 x z
  let v164 := M v0 v0
  have h165 := h v164 x x
  have h166 := S h165
  have h167 := R v164
  have h168 := h x v0 v0
  have h169 := R (M x x)
  have h170 := C h169 (T (C h74 h92) (C h74 (T h168 (C h167 h41))))
  have h171 := h v89 x x
  have h172 := C h163 (T (T (T (T (T (T (T h31 h45) h109) h105) h171) h170) h166) (C h9 h163))
  have h173 := C h9 h51
  have h174 := R v158
  have h175 := h v153 v0 v1
  have h176 := S h154
  have h177 := C (T (T (T (T h122 h121) h58) h20) h19) (T (T (T (T h3 h147) h145) h144) (C h6 (T (T (T (T (T h122 h121) h58) h20) h19) h149)))
  have h178 := C (T (T h57 h140) h124) h6
  have h179 := C (T (T h8 h117) h116) (T (T (T (T (T (T (T (T (T h101 h50) h49) h23) h20) h19) h149) (C h141 h155)) (C h6 h150)) (C h6 (T (T (T (T h178 h177) h176) h175) (C h174 (T (T (T (C h9 (T (T (T (T (T h142 h136) h135) h22) h56) h55)) h173) h172) h162)))))
  have h180 := h v81 v0 v0
  have h181 := C h9 h84
  have h182 := S h171
  have h183 := C h169 (T (C h74 (T (C h167 h27) (S h168))) (C h74 h108))
  have h184 := S h163
  have h185 := C h184 (T (T (T (T (T (T (T (C h9 h184) h165) h183) h182) h94) h93) h37) h32)
  have h186 := C h29 h6
  have h187 := S (h v59 x z)
  let v188 := M v59 v1
  have h189 := S (h v1 x v11)
  T (T (T (T (T (T (T (h v59 v59 (M x (M v1 v11))) (C h189 (C h85 h189))) (C h6 (T (T (T (T (T (h v188 v1 v0) (C (T (T (T (T (T (T h128 h125) h61) h139) h134) h179) h160) (T (T (T (T (T (T (T (T (T (T (T (T (T (C h6 (T (T (T (T (T (T (T (T (T (C (R v188) (T (T (h v0 v0 (M x (M v59 z))) (C h187 (T (C h9 h187) h8))) (C h85 (T (T (T (T (T (T (T (T h61 h139) h134) h179) h160) h157) h156) h151) (C (T (T (T h76 (C h6 h157)) (C h6 (T (T (T (T (T h186 h159) (C (T (T h128 h125) h7) (T (T (T (T (T (T (T (T (T (C h6 (T (T (T (T (C h174 (T (T (T h161 h185) h181) (C h9 (T (T (T (T (T h50 h49) h23) h20) h19) h149)))) (S h175)) h154) h152) h150)) (C h6 h178)) (C h148 (T (T (T (T (T h177 h176) h123) h52) h21) h4))) h142) h136) h135) h22) h56) h55) h133))) h132) h103) h131))) (C h6 (T h119 h104))) (T (T (T (T (T (T h178 h177) h176) h123) h52) h21) h4)))))) (S (h (M v1 v98) v59 v1))) (C h6 (T h103 h131))) (C h6 (T (T (T (T (T h119 h104) h102) h179) h160) h157))) (C h6 h186)) h137) h25) h42) h180) (C (T (T (T (T (T (T (T (T (T h165 h183) h182) h94) h93) h37) h32) h57) h140) h124) (T (T h173 h172) h162)))) (C h6 (T (T (T (C (T (T (T (T (T (T (T (T (T h122 h121) h58) h31) h45) h109) h105) h171) h170) h166) (T (T h161 h185) h181)) (S h180)) h82) h110))) h130) h129) h128) h125) h61) h139) h134) h179) h160) h157) h156) h151))) (S (h v15 v0 v1))) h20) h19) h149))) h143) h123) h52) h21) h4

