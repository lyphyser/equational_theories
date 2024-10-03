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
theorem Equation2519_implies_Equation2170 (G: Type _) [Magma G] (h: Equation2519 G) : Equation2170 G := fun x y z =>
  let v0 := M z y
  let v1 := M y z
  let v2 := M v1 x
  let v3 := M v2 v0
  have h4 := h v3 v2 (M x v3)
  have h5 := S h4
  have h6 := R v3
  have h7 := h x z v2
  have h8 := S h7
  have h9 := R v2
  have h10 := h y x z
  have h11 := R z
  have h12 := C h11 h10
  have h13 := T (C h12 h9) h8
  have h14 := C h13 h6
  let v15 := M v0 v2
  have h16 := h (M v3 (M v15 v3)) x x
  have h17 := S h16
  have h18 := R x
  have h19 := C h11 (S h10)
  have h20 := T h7 (C h19 h9)
  have h21 := C h20 h6
  have h22 := h x v3 x
  have h23 := S h22
  let v24 := M x x
  let v25 := M v3 (M v24 v3)
  have h26 := h v25 v3 x
  have h27 := C (C h18 (T h22 (C (T h26 (C (C h6 (T (C h23 h6) h21)) h18)) h18))) h18
  have h28 := h v25 v2 x
  have h29 := C h13 h9
  have h30 := C (C h18 (T (C (T (C (C h9 (T h29 (C h22 h9))) h18) (S h28)) h18) h23)) h18
  let v31 := M v2 (M v15 v2)
  have h32 := h v31 x x
  have h33 := h v0 v2 v2
  have h34 := h x v3 v1
  have h35 := R v1
  have h36 := h v1 v0 x
  have h37 := h v0 x v3
  have h38 := T (C (C h6 (T h37 (C (C h18 (S h36)) h6))) h35) (S h34)
  have h39 := C h35 h38
  have h40 := h v3 v1 v0
  have h41 := C (T h40 (C h39 (T h33 (C (T (T (T (T h32 h30) h27) h17) (C h6 h14)) h9)))) h14
  have h42 := h v31 v1 v1
  have h43 := S h42
  have h44 := C h20 h9
  have h45 := h x y v1
  have h46 := S h45
  have h47 := C h9 (T (C h46 h9) h44)
  let v48 := M x v1
  have h49 := h (M y (M v48 y)) v2 v1
  have h50 := h z v2 y
  have h51 := R y
  have h52 := C h9 h20
  have h53 := C h51 (T (C h52 h51) (S h50))
  have h54 := h v2 y x
  have h55 := C (T h54 (C h53 (T h45 (C (T h49 (C h47 h35)) h35)))) h35
  have h56 := h v2 v0 v0
  have h57 := S h56
  have h58 := R v0
  have h59 := h (M v3 v0) x v1
  have h60 := T h34 (C (C h6 (T (C (C h18 h36) h6) (S h37))) h35)
  have h61 := C h13 h18
  have h62 := h (M x (M v15 x)) x x
  have h63 := S h62
  have h64 := C h20 h18
  have h65 := h v25 x x
  have h66 := C (C h18 (T h22 (C (T h65 (C (C h18 (T (C h23 h18) h64)) h18)) h18))) h18
  have h67 := C h9 (T h29 (C h45 h9))
  have h68 := S h32
  have h69 := C (C h18 (T h22 (C (T h28 (C (C h9 (T (C h23 h9) h44)) h18)) h18))) h18
  have h70 := C (C h18 (T (C (T (C (C h18 (T h61 (C h22 h18))) h18) (S h65)) h18) h23)) h18
  have h71 := h x v2 v1
  have h72 := S h71
  have h73 := C (T (T (T (T (T (C h18 (T (C h72 h18) h64)) h62) h70) h69) h68) h67) h35
  let v74 := M v48 v2
  have h75 := h (M v2 v74) x v1
  have h76 := R v74
  have h77 := S h54
  have h78 := C h9 h13
  have h79 := C h51 (T h50 (C h78 h51))
  have h80 := C (T (C h79 h72) h77) h76
  have h81 := h v2 v1 v74
  have h82 := C (T h7 (C h19 (T (T (T (T (T h81 h80) h75) h73) (C (T (T (T (T (T h47 h32) h30) h66) h63) (C h18 (T h61 (C h60 h18)))) h35)) (S h59)))) h58
  have h83 := h v2 v2 v0
  have h84 := S h83
  have h85 := h (M v2 (M v3 v2)) x v0
  have h86 := C (T (C h12 (T (C (T (C (C h18 (T h52 (C h83 h13))) h58) (S h85)) h58) h84)) h8) h58
  let v87 := M x (M v2 x)
  have h88 := h v87 v0 v0
  have h89 := h v87 x x
  have h90 := S h89
  have h91 := h v1 x x
  have h92 := C (C h18 (T h54 (C (T h53 h91) h18))) h18
  have h93 := h v1 v3 x
  have h94 := C (C h18 (T (C (T (S h93) h79) h18) h77)) h18
  let v95 := M v2 v3
  have h96 := h (M v3 v95) x x
  have h97 := h v87 v2 x
  have h98 := S h97
  have h99 := C (C h9 (C h91 h9)) h18
  let v100 := M v1 v2
  have h101 := h (M v2 v100) x z
  have h102 := S h101
  have h103 := h y v2 z
  have h104 := h y v3 v2
  have h105 := C (S h104) h18
  have h106 := C h104 h18
  have h107 := h y v3 z
  have h108 := C (T (C h18 (T (C (S h107) h18) h106)) (C h18 (T h105 (C h103 h18)))) h11
  let v109 := M v1 v3
  let v110 := M v3 v109
  have h111 := h v110 x z
  have h112 := h v110 x x
  have h113 := S h112
  have h114 := S h91
  have h115 := h v87 v3 x
  have h116 := C (C h18 (T h91 (C (T h115 (C (C h6 (C h114 h6)) h18)) h18))) h18
  have h117 := C (C h18 (T (C (T h92 h90) h18) h114)) h18
  have h118 := h (M x v2) x x
  have h119 := h v1 y x
  have h120 := C (T (T (T (T (T (T (T (C h18 (T (C (T (S h119) h79) h18) h77)) h118) h117) h116) h113) h111) h108) h102) h18
  have h121 := h (M y (M v2 y)) x x
  have h122 := h v2 v3 v3
  have h123 := S h122
  have h124 := C h51 (C h123 h51)
  have h125 := C (T (T (T (T (T (T (T (T h124 h121) h120) h99) h98) h88) h86) h82) h57) h6
  let v126 := M v3 (M v95 v3)
  have h127 := h v126 y v3
  have h128 := h v126 v0 v3
  have h129 := S h128
  have h130 := C (C h58 (T h40 (C (T h39 h122) h58))) h6
  have h131 := S h40
  have h132 := C h35 h60
  have h133 := C (C h58 (T (C (T h123 h132) h58) h131)) h6
  have h134 := h v126 x v3
  have h135 := h v87 v1 v1
  have h136 := S h135
  have h137 := h v2 z v1
  have h138 := S h137
  have h139 := h (M z (M (M v2 v1) z)) x v1
  have h140 := C (C h35 (T h137 (C (T h139 (C (C h18 (T (C h138 h20) h78)) h35)) h35))) h35
  have h141 := C (T (T (T (T (T (T (T (T (T (C h6 (T (T (T (C (T (T h140 h136) (C h18 (T h52 (C h122 h13)))) h6) (S h134)) h128) h133)) (C h6 (T (T (T h130 h129) h127) h125))) h96) h94) h92) h90) h88) h86) h82) h57) h35
  have h142 := h v100 v3 v1
  have h143 := C (C h35 (T (C (T (C (C h18 (T h52 (C h137 h13))) h35) (S h139)) h35) h138)) h35
  have h144 := T h135 h143
  have h145 := h v87 z z
  have h146 := h v2 x z
  have h147 := S h146
  let v148 := M v2 z
  have h149 := h (M x (M v148 x)) x z
  have h150 := C (T (C (C h11 (T h146 (C (T h149 (C (C h18 (T (C h147 h20) h78)) h11)) h11))) h11) (S h145)) h9
  have h151 := T h145 (C (C h11 (T (C (T (C (C h18 (T h52 (C h146 h13))) h11) (S h149)) h11) h147)) h11)
  have h152 := h (M v87 v2) v3 v2
  have h153 := h v2 x v2
  let v154 := M v2 v2
  have h155 := h (M x (M v154 x)) x v2
  have h156 := S h81
  have h157 := C (T h54 (C h53 h71)) h76
  have h158 := S h75
  have h159 := C (T (T (T (T (T h47 h32) h30) h66) h63) (C h18 (T h61 (C h71 h18)))) h35
  have h160 := h v24 v2 x
  have h161 := h v3 v3 v1
  have h162 := C (T (T (T (T (T (C h18 (T (T (T (C (S h161) h18) (C (T h40 (C h39 (T h33 (C (T h32 h30) h9)))) h18)) (S h160)) h64)) h62) h70) h69) h68) h67) h35
  have h163 := h (M v3 (M (M v3 v1) v3)) x v1
  have h164 := h x v1 v1
  have h165 := h v100 x v1
  have h166 := C h51 (C h122 h51)
  have h167 := S h121
  have h168 := S h118
  have h169 := C (C h18 (T (C (T h114 h79) h18) h77)) h18
  have h170 := C (C h18 (T h91 (C (T h89 h169) h18))) h18
  have h171 := C (C h18 (T (C (T (C (C h6 (C h91 h6)) h18) (S h115)) h18) h114)) h18
  have h172 := S h111
  have h173 := C (T (C h18 (T (C (S h103) h18) h106)) (C h18 (T h105 (C h107 h18)))) h11
  have h174 := C (T (T (T (T (T (T (T h101 h173) h172) h112) h171) h170) h168) (C h18 (T h54 (C (T h53 h119) h18)))) h18
  have h175 := C (C h9 (C h114 h9)) h18
  have h176 := S h88
  have h177 := C (T h7 (C h19 (T h83 (C (T h85 (C (C h18 (T (C h84 h20) h78)) h58)) h58)))) h58
  have h178 := C (T (C h12 (T (T (T (T (T h59 (C (T (T (T (T (T (C h18 (T (C h38 h18) h64)) h62) h70) h69) h68) h67) h35)) h159) h158) h157) h156)) h8) h58
  have h179 := C (T (T (T (T (T (T (T (T h56 h178) h177) h176) h97) h175) h174) h167) h166) h6
  have h180 := S h96
  have h181 := C (C h18 (T h54 (C (T h53 h93) h18))) h18
  have h182 := C (C h18 (T (C (T (C (C h6 (T h14 (C h22 h6))) h18) (S h26)) h18) h23)) h18
  have h183 := S h33
  have h184 := C (T (C h132 (T (C (T (T (T (T (C h6 h21) h16) h182) h69) h68) h9) h183)) h131) h21
  have h185 := h v109 v3 v1
  have h186 := C h6 (C (T h185 (C (T (T (C h6 (T (C (T (C (C h35 (T (T (T (T (T (T (T (T (T (T (T h4 h184) h16) h182) h69) h68) h42) (C (T (C h79 (T (C (T (C h67 h35) (S h49)) h35) h46)) h77) h35)) (C (T (T (T (T (T (T (T (T (T h56 h178) h177) h176) h89) h169) h181) h180) (C h6 (T (T (T h179 (S h127)) h128) h133))) (C h6 (T (T (T h130 h129) h134) (C (T (T (C h18 (T (C h123 h20) h78)) h135) h143) h6)))) h35)) (S h142)) h165) (C (C h18 (T (C (T h140 h136) h18) h114)) h35))) h35) (S h164)) h6) h21)) h41) h5) h35)) h6)
  have h187 := h (M v3 (M v109 v3)) x v3
  have h188 := S h187
  have h189 := h v1 v3 v3
  have h190 := C (T (T (T (T (T (T (T h101 h173) h172) h112) h171) h170) h168) (C h18 (T h54 (C (T h53 h189) h18)))) h6
  have h191 := h v1 v0 v3
  have h192 := C (T (T (T (T (T (T (T (C h18 (T (C (T (S h191) h79) h18) h77)) h118) h117) h116) h113) h111) h108) h102) h6
  let v193 := M v0 (M v109 v0)
  have h194 := h v193 x v3
  have h195 := C (T (T (T (T (T (T (T (T (T (T h194 h192) h190) h188) h186) h163) h162) h159) h158) h157) h156) h9
  have h196 := h v193 x v2
  have h197 := S h194
  have h198 := C (T (T (T (T (T (T (T h101 h173) h172) h112) h171) h170) h168) (C h18 (T h54 (C (T h53 h191) h18)))) h6
  have h199 := C (T (T (T (T (T (T (T (C h18 (T (C (T (S h189) h79) h18) h77)) h118) h117) h116) h113) h111) h108) h102) h6
  have h200 := C h6 (C (T (C (T (T h4 h184) (C h6 (T h14 (C (T h164 (C (C h35 (T (T (T (T (T (T (T (T (T (T (T (C (C h18 (T h91 (C h144 h18))) h35) (S h165)) h142) h141) h55) h43) h32) h30) h27) h17) h41) h5)) h35)) h6)))) h35) (S h185)) h6)
  have h201 := S h163
  have h202 := C (T (T (T (T (T h47 h32) h30) h66) h63) (C h18 (T (T (T h61 h160) (C (T (C h132 (T (C (T h69 h68) h9) h183)) h131) h18)) (C h161 h18)))) h35
  have h203 := C (T (T (T (T (T (T (T (T (T (T h81 h80) h75) h73) h202) h201) h200) h187) h199) h198) h197) h9
  have h204 := h (M v2 v154) x x
  have h205 := h v1 v2 x
  let v206 := M z v2
  T (T (T (T (T (T (T (T (T (T (T (T (h x z v1) (C (T (T (T (T (T (T (T (T (T (T (C h11 (T (T (T (C (C h18 (T h91 (C h151 h18))) h11) (S (h v206 x z))) (h v206 v2 z)) (C (T (T (T (T (T (T (T (T (C h9 (T (T (T h150 h152) (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (C h6 (T (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (C (T (T (C (C h18 (T h52 (C h153 h13))) h9) (S h155)) (C h18 (C h203 h18))) h9) (S h196)) h194) h192) h190) h188) h186) h163) h162) h159) h158) h157) h156) h56) h178) h177) h176) h97) h175) h174) h167) h166) h6) h125)) h96) h94) h92) h90) h88) h86) h82) h57) h81) h80) h75) h73) h202) h201) h200) h187) h199) h198) h197) h9)) h195)) h204) (C (C h18 (T (C (T (S h205) h79) h18) h77)) h18)) h92) h90) h88) h86) h82) h57) h11))) (h (M z v148) x x)) (C (T (T (T (T (T (T (T (C h18 (T (C (T (S (h v1 z x)) h79) h18) h77)) h118) h117) h116) h113) h111) h108) h102) h18)) h99) h98) h89) h169) (C (C h18 (T h54 (C (T h53 h205) h18))) h18)) (S h204)) (C h9 (T (T (T h203 (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h194 h192) h190) h188) h186) h163) h162) h159) h158) h157) h156) h56) h178) h177) h176) h89) h169) h181) h180) (C h6 (T h179 (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h124 h121) h120) h99) h98) h88) h86) h82) h57) h81) h80) h75) h73) h202) h201) h200) h187) h199) h198) h197) h196) (C (T (T (C h18 (C h195 h18)) h155) (C (C h18 (T (C (S h153) h20) h78)) h9)) h9)) h6)))) h9)) (S h152)) (C h151 h9)))) (C h9 (T h150 (C h144 h9)))) h35)) (S (h v100 v2 v1))) h142) h141) h55) h43) h32) h30) h27) h17) h41) h5

