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
theorem Equation3385_implies_Equation3895 (G: Type _) [Magma G] (h: Equation3385 G) : Equation3895 G := fun x y z =>
  let v0 := M y z
  let v1 := M y v0
  have h2 := h v1 z z
  have h3 := S h2
  let v4 := M v1 z
  have h5 := R z
  have h6 := h y v0 y
  have h7 := S h6
  let v8 := M v0 y
  let v9 := M y v8
  have h10 := h y v9 z
  have h11 := S h10
  have h12 := h y v8 v4
  have h13 := S h12
  have h14 := R v4
  have h15 := h v0 y y
  have h16 := h y y z
  have h17 := S h16
  have h18 := R v0
  have h19 := C h18 h17
  have h20 := h z y v0
  have h21 := R y
  have h22 := C h14 (C h21 (C (T (C h21 (T h20 h19)) (S h15)) h14))
  have h23 := h y (M y (M z y)) v4
  have h24 := h y z y
  have h25 := T (T (T h24 h23) h22) h13
  have h26 := C h25 h5
  have h27 := h v0 z v1
  have h28 := R v1
  have h29 := C h21 (T (T (C h28 h20) (S h27)) h26)
  have h30 := h v1 z y
  have h31 := C h5 (T h30 h29)
  have h32 := T (T h31 h11) h7
  have h33 := C h32 h5
  have h34 := h z z y
  have h35 := S h34
  have h36 := S h20
  have h37 := C h18 h16
  have h38 := h z v1 v4
  have h39 := S h38
  have h40 := C h32 h14
  have h41 := S h30
  have h42 := S h24
  have h43 := S h23
  have h44 := C h14 (C h21 (C (T h15 (C h21 (T h37 h36))) h14))
  have h45 := T (T (T h12 h44) h43) h42
  have h46 := C h45 h5
  have h47 := C h21 (T (T h46 h27) (C h28 h36))
  have h48 := C h5 (T h47 h41)
  have h49 := T (T h6 h10) h48
  have h50 := C h49 h33
  let v51 := M z v4
  have h52 := h v1 v51 z
  have h53 := C h14 (T h52 (C h5 (T h50 h40)))
  have h54 := h v1 z v4
  have h55 := C h45 (T (T (T h54 h53) h39) h17)
  have h56 := C h25 h14
  have h57 := T (T (T h56 h55) h37) h36
  have h58 := h v0 v1 z
  have h59 := C h45 h28
  have h60 := C h21 (T (T h59 h58) (C h5 h57))
  have h61 := C h28 (T h60 h35)
  have h62 := h y v9 v1
  have h63 := T (T h6 h62) h61
  have h64 := C h63 h33
  have h65 := C h5 h64
  have h66 := h v1 v51 v0
  have h67 := S h66
  have h68 := S h62
  have h69 := C h25 h28
  have h70 := C h45 h14
  have h71 := S h54
  have h72 := S h52
  have h73 := C h49 h5
  have h74 := C h32 h73
  have h75 := C h49 h14
  have h76 := C h14 (T (C h5 (T h75 h74)) h72)
  have h77 := C h25 (T (T (T h16 h38) h76) h71)
  have h78 := T (T (T h20 h19) h77) h70
  have h79 := C h21 (T (T (C h5 h78) (S h58)) h69)
  have h80 := C h28 (T h34 h79)
  have h81 := T (T (T h80 h68) h10) h48
  have h82 := C h45 h21
  have h83 := C h25 h21
  have h84 := h v0 y v1
  have h85 := S h84
  have h86 := C h81 h5
  have h87 := C h5 (T (T (T h86 h33) h30) h29)
  have h88 := T (T (T h31 h11) h62) h61
  have h89 := C h88 h5
  have h90 := C h5 (T (T (T (T (T h16 h38) h76) h71) h73) h89)
  have h91 := C h21 (T (T (T h90 h87) h11) h7)
  have h92 := h z y y
  have h93 := h z y v4
  have h94 := S h93
  have h95 := T (T h38 h76) h71
  have h96 := C h21 (T (T (T h33 h54) h53) h39)
  have h97 := C h5 (T h96 (C h21 h95))
  have h98 := h y v51 z
  have h99 := C h14 (T h98 h97)
  have h100 := h y z v4
  have h101 := h y z v0
  have h102 := h z v0 v0
  have h103 := h v0 y z
  have h104 := h v0 v0 y
  have h105 := C h18 (T (T (T (T (T (T (C h18 (T h104 (C h21 (T (C h18 h103) (S h102))))) (S h101)) h100) h99) h94) h92) h91)
  have h106 := h v0 v0 v0
  have h107 := h v0 v0 z
  have h108 := S h107
  have h109 := h v0 z y
  have h110 := S h92
  have h111 := C h5 (T (T (T (T (T h86 h33) h54) h53) h39) h17)
  have h112 := C h5 (T (T (T h47 h41) h73) h89)
  have h113 := C h21 (T (T (T h6 h10) h112) h111)
  have h114 := h y v9 v0
  have h115 := C h5 (T (T (T h80 h68) h114) (C h18 (T (C h21 (T (T (T (T (C h45 h18) h106) h105) (C h18 (T (T (T (T (T h113 h110) h20) h19) h77) h70))) (C h18 h57))) (S h109))))
  have h116 := C h28 (T (T (T (T (T (T (T h38 h76) h71) h2) h115) h108) h106) h105)
  let v117 := M z v1
  have h118 := h v1 v117 v1
  have h119 := S h118
  have h120 := h y v0 v1
  have h121 := S h120
  have h122 := h z z v1
  have h123 := S h122
  have h124 := C h5 h16
  have h125 := T (T h80 h68) h7
  have h126 := C h125 (T (T (T (T h6 h10) h112) h111) h124)
  have h127 := C h88 h28
  have h128 := C h28 (T (T (T (T (T h127 h126) h123) h34) h79) (C h21 h59))
  have h129 := C h81 h28
  have h130 := C h5 h17
  have h131 := C h63 (T (T (T (T h130 h90) h87) h11) h7)
  have h132 := h z z v4
  have h133 := S h132
  have h134 := h z v1 z
  have h135 := C h95 (T (T (T h54 h53) h39) h134)
  have h136 := T (T (T (T h135 h133) h122) h131) h129
  have h137 := T (T h54 h53) h39
  have h138 := C h137 (T (T (C h28 h136) h128) h121)
  have h139 := h v1 v117 v4
  have h140 := h v1 z v1
  have h141 := C h125 (T h140 (C h28 (T h139 h138)))
  have h142 := C h125 h73
  have h143 := S h139
  have h144 := C h137 (T (T (T (S h134) h38) h76) h71)
  have h145 := T (T (T (T h127 h126) h123) h132) h144
  have h146 := C h28 (T (T (T (T (T (C h21 h69) h60) h35) h122) h131) h129)
  have h147 := C h95 (T (T h120 h146) (C h28 h145))
  have h148 := C h63 (T (C h28 (T h147 h143)) (S h140))
  have h149 := C h63 (T (T (T (T (T (T (C h21 (T (T (T (T (T h147 h143) h118) h148) h142) h50)) (C h21 (T (T (T (T (T (T h74 h64) h141) h119) h116) h85) h83))) (C h21 h82)) h12) h44) h43) h42)
  have h150 := h y v117 v1
  have h151 := h y z v1
  have h152 := S h100
  have h153 := S h98
  have h154 := C h21 (T (T (T h38 h76) h71) h73)
  have h155 := C h14 (T (C h5 (T (C h21 h137) h154)) h153)
  have h156 := C h18 (T (T (T (T (T (T h113 h110) h93) h155) h152) h151) (C h28 (T (T h150 h149) (C h81 h18))))
  have h157 := S h114
  have h158 := S h106
  have h159 := S h103
  have h160 := C h18 (T (T (T (T (T (T h113 h110) h93) h155) h152) h101) (C h18 (T (C h21 (T h102 (C h18 h159))) (S h104))))
  have h161 := C h21 (T (T (T (T (C h18 h78) (C h18 (T (T (T (T (T h56 h55) h37) h36) h92) h91))) h160) h158) (C h25 h18))
  have h162 := h y z z
  have h163 := S h162
  have h164 := C h21 h136
  have h165 := h v1 v51 v1
  have h166 := C h5 h142
  have h167 := C h5 (T (T (T (C h18 (T h109 h161)) h157) h62) h61)
  have h168 := C h28 (T (T (T (T (T (T (T h160 h158) h107) h167) h3) h54) h53) h39)
  have h169 := C h5 (T (T (T h84 h168) h118) h148)
  have h170 := C h21 (T (T (T (T (T (T (T h169 h166) h72) h165) (C h28 (T (T (T (T (T (T h128 h121) h6) h10) h112) h111) h124))) h123) h132) h144)
  have h171 := C h5 (T (T (T h141 h119) h116) h85)
  have h172 := C h21 (T (T (T (T (T (T (T (T (T (T h33 h2) h115) h108) h106) h105) h156) h67) h52) h65) h171)
  have h173 := S h150
  have h174 := C h21 (T (T (T (T (T h74 h64) h141) h119) h139) h138)
  have h175 := C h21 (T (T (T (T (T (T h82 h84) h168) h118) h148) h142) h50)
  have h176 := C h21 h83
  have h177 := C h125 (T (T (T (T (T (T h24 h23) h22) h13) h176) h175) h174)
  have h178 := C h5 (T (T (T (T (T (T h177 h173) h154) h172) h170) h164) (C h21 (T (T h127 h126) h123)))
  have h179 := C h5 (T (T h96 h150) h149)
  have h180 := h y v51 v1
  have h181 := S h180
  have h182 := h z v0 y
  have h183 := C h28 (T (T h182 h170) h164)
  have h184 := T (T (T (T (T (T (T (T (T h183 h181) h98) h179) h178) h163) h24) h23) h22) h13
  have h185 := S h182
  have h186 := C h21 (T (T (T (T (T (T (T h135 h133) h122) (C h28 (T (T (T (T (T (T h130 h90) h87) h11) h7) h120) h146))) (S h165)) h52) h65) h171)
  have h187 := C h21 h145
  have h188 := C h28 (T (T h187 h186) h185)
  have h189 := C h5 (T (T h177 h173) h154)
  have h190 := C h5 (T (T (T (T (T (T (C h21 (T (T h122 h131) h129)) h187) h186) (C h21 (T (T (T (T (T (T (T (T (T (T h169 h166) h72) h66) (C h18 (T (T (T (T (T (T (C h28 (T (T (C h88 h18) h177) h173)) (S h151)) h100) h99) h94) h92) h91))) h160) h158) h107) h167) h3) h73))) h96) h150) h149)
  have h191 := T (T (T (T (T (T (T (T (T h12 h44) h43) h42) h162) h190) h189) h153) h180) h188
  have h192 := C h28 (T (T (T (T (T (T (T (T (T (T (C h95 (T (T (T (T (T h100 h99) h94) h20) (C (T (T (T (T (T h162 h190) h189) h153) h180) h188) h95)) (C (T h183 h181) h14))) (C h14 (T (T (T (T (T (T (T (T (T (C (T h180 h188) h14) (C (T (T (T (T (T h183 h181) h98) h179) h178) h163) h137)) h36) h93) h155) h152) h162) h190) h189) h97))) h155) h152) h24) h23) h22) h13) h176) h175) h174)
  have h193 := h v1 v117 v0
  have h194 := R x
  have h195 := C h194 (T (T (T (T (T (T (T (T (T h75 h74) h64) h141) h119) h193) (C h18 (T (T (T (T (T (T (T (T (T (T h192 h173) h154) h172) h185) h102) (C h18 (T (T h159 h83) (C h191 h21)))) (C h18 (T (T (T (T (T (C h184 h21) h82) h84) h168) h193) (C h18 (T (T (T (T h192 h173) h154) h172) h185))))) (S (h v0 z v0))) h26) (C h191 h5)))) (C h18 (T (T (T (C h184 h5) h46) h109) h161))) h157) h7)
  T (T (T (h x x v4) (C h14 (T (T (T (T (T (T (T (T (T (T (T (T (h x (M x v4) v4) (C h14 (C h194 (C (T (h x v4 v1) (C h28 (T (T (T (T (C h194 (T (T (T (T (T (T (T (C h137 h28) h147) h143) h118) h148) h142) h50) h40)) h195) (h x v1 v4)) (C h14 (T h195 (h x v1 z)))) (S (h z x v4))))) h14)))) (S (h x (M v1 (M z x)) v4))) (S (h v1 z x))) h2) h115) h108) h106) h105) h156) h67) h52) h65))) (S (h z (M v1 (M z z)) v4))) h3

