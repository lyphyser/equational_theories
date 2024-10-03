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
theorem Equation2925_implies_Equation14 (G: Type _) [Magma G] (h: Equation2925 G) : Equation14 G := fun x y =>
  let v0 := M x y
  have h1 := R v0
  let v2 := M y v0
  have h3 := h y v0 v2
  have h4 := S h3
  have h5 := R v2
  let v6 := M y v2
  let v7 := M (M v0 v6) v0
  have h8 := h v7 v2 x
  have h9 := S h8
  have h10 := R x
  have h11 := h v7 x v2
  have h12 := S h11
  have h13 := h y v2 v2
  have h14 := S h13
  have h15 := C (C h10 h14) h10
  have h16 := C (T h15 (C (C h10 h3) h10)) h5
  let v17 := M v2 v6
  let v18 := M v17 v2
  have h19 := h v18 x v2
  have h20 := h v18 v2 v2
  have h21 := S h20
  let v22 := M v2 y
  have h23 := h v22 x x
  have h24 := S h23
  have h25 := R y
  have h26 := h v0 x x
  have h27 := S h26
  let v28 := M v0 x
  let v29 := M (M x v28) x
  have h30 := h v29 y x
  have h31 := h v29 v2 x
  have h32 := S h31
  have h33 := C (C (C h5 h26) h5) h10
  have h34 := C (C (C h10 (T (T (T h33 h32) h30) (C (C (C h25 h27) h25) h10))) h10) h10
  let v35 := M (M v2 v0) v2
  have h36 := h v35 x x
  have h37 := C (T (T (T h36 h34) h24) (C h5 h13)) h5
  let v38 := M v35 v2
  have h39 := h v38 y v2
  have h40 := S h36
  have h41 := C (C (C h5 h27) h5) h10
  have h42 := C (C (C h10 (T (T (T (C (C (C h25 h26) h25) h10) (S h30)) h31) h41)) h10) h10
  have h43 := C (T (T (T (C h5 h14) h23) h42) h40) h5
  have h44 := h v17 y v2
  have h45 := h v6 v2 x
  have h46 := S h45
  have h47 := h v6 v2 y
  have h48 := S h47
  have h49 := h (M v6 y) x v0
  have h50 := h y y v0
  have h51 := h x y x
  have h52 := C h1 (S h51)
  have h53 := C h1 h51
  have h54 := h y x v0
  have h55 := C (T (C (C h10 (S h54)) h10) h53) h1
  let v56 := M (M x v2) x
  have h57 := h v56 x v0
  have h58 := h v56 y y
  have h59 := h v2 y y
  have h60 := C (C (C h10 (S h59)) h10) h25
  let v61 := M y v22
  have h62 := h (M v61 y) x y
  have h63 := h v61 y y
  have h64 := h v61 x y
  have h65 := S h62
  have h66 := C (C (C h10 h59) h10) h25
  have h67 := S h57
  have h68 := C (T h52 (C (C h10 h54) h10)) h1
  have h69 := h x v2 y
  have h70 := S h69
  have h71 := C (T (T (C (T (C h1 h70) h53) h1) h68) h67) h25
  have h72 := h v35 v0 y
  have h73 := R v35
  have h74 := h y v2 x
  have h75 := S h74
  have h76 := C (C (T (C h73 h75) h70) h73) h10
  let v77 := M y x
  let v78 := M v2 v77
  let v79 := M v78 v2
  have h80 := h v79 v35 x
  have h81 := C (T (C (C h5 (T (T (T (T (C (T (T h80 h76) (C (C h10 (T (T (T h72 h71) h66) h65)) h10)) h25) (S h64)) h63) (C (C (C h25 (T h62 h60)) h25) h25)) (S h58))) h5) (C (C h5 (T (T (T h57 h55) (C (T h52 (C (C h10 h50) h10)) h1)) (S h49))) h5)) h25
  have h82 := h v79 v2 y
  have h83 := T (T h82 h81) h48
  have h84 := C h83 h10
  have h85 := T h74 h84
  have h86 := C (C (T (T (T h36 h34) h24) (C h5 h85)) h5) h10
  have h87 := C (T (T (T (T (C h5 (T h86 h46)) h44) (C (C (C h25 (T h20 (C h43 h5))) h25) h5)) (S h39)) h37) h5
  have h88 := h v38 v2 x
  have h89 := h v29 x x
  have h90 := C (C (C h10 (T (T (T (C (C (C h10 h26) h10) h10) (S h89)) h31) h41)) h10) h10
  let v91 := M x v0
  have h92 := h (M v91 x) x x
  have h93 := h v0 x v2
  let v94 := M x (M v0 v2)
  have h95 := h (M v94 x) x v2
  have h96 := C (T (C (C h5 (T h95 (C (T (T (T (C (C h10 (S h93)) h10) h92) h90) h40) h5))) h5) (C (C h5 (T h88 (C (T (T (T (T h87 h21) h19) h16) h12) h10))) h5)) h10
  have h97 := h v94 v2 x
  have h98 := C (T (T h97 h96) h9) h5
  have h99 := S h97
  have h100 := S h92
  have h101 := C (C (C h10 (T (T (T h33 h32) h89) (C (C (C h10 h27) h10) h10))) h10) h10
  have h102 := S h82
  have h103 := S h80
  have h104 := C (C (T h69 (C h73 h74)) h73) h10
  have h105 := S h72
  have h106 := C (T (T h57 h55) (C (T h52 (C h1 h69)) h1)) h25
  have h107 := C (T (C (C h5 (T (T (T h49 (C (T (C (C h10 (S h50)) h10) h53) h1)) h68) h67)) h5) (C (C h5 (T (T (T (T h58 (C (C (C h25 (T h66 h65)) h25) h25)) (S h63)) h64) (C (T (T (C (C h10 (T (T (T h62 h60) h106) h105)) h10) h104) h103) h25))) h5)) h25
  have h108 := T (T h47 h107) h102
  have h109 := C h108 h10
  have h110 := T h109 h75
  have h111 := C (T (T (T (C h5 h110) h23) h42) h40) h5
  have h112 := C h111 h10
  have h113 := S h44
  have h114 := C (C (C h25 (T (C h37 h5) h21)) h25) h5
  have h115 := C (T (T (T (T h43 h39) h114) h113) (C h5 (T h45 h112))) h5
  have h116 := S h19
  have h117 := C (C h10 h13) h10
  have h118 := C (T (C (C h10 h4) h10) h117) h5
  have h119 := C (T (C (C h5 (T (C (T (T (T (T h11 h118) h116) h20) h115) h10) (S h88))) h5) (C (C h5 (T (C (T (T (T h36 h101) h100) (C (C h10 h93) h10)) h5) (S h95))) h5)) h10
  have h120 := C (T (T (T (T (T (T (T (T (C (C h5 (T (T (T (T h82 h81) h48) h45) h112)) h5) h87) h21) h19) h16) h12) h8) h119) h99) h5
  have h121 := h v78 v2 v2
  have h122 := T (T (T h121 h120) h98) h4
  have h123 := h v78 x x
  have h124 := S h123
  have h125 := C (T (T h8 h119) h99) h5
  have h126 := T (T (T h3 h125) (C (T (T (T (T (T (T (T (T h97 h96) h9) h11) h118) h116) h20) h115) (C (C h5 (T (T (T (T h86 h46) h47) h107) h102)) h5)) h5)) (S h121)
  have h127 := C h126 h10
  have h128 := h (M (M x v77) x) x x
  have h129 := h y x x
  have h130 := C (C h10 h75) h10
  have h131 := h v79 x x
  have h132 := C (C h10 (T (T h92 h90) h40)) h10
  have h133 := C (T (T (T (T (T (T h132 h104) h103) h131) (C (T h130 (C (C h10 h129) h10)) h10)) (S h128)) (C (C h10 h127) h10)) h10
  have h134 := h v91 x x
  have h135 := h v91 v2 x
  have h136 := S h135
  have h137 := h v2 x y
  have h138 := C (C (C h10 (S h137)) h10) h25
  let v139 := M x v22
  have h140 := h (M v139 x) x y
  have h141 := h v139 x x
  have h142 := S h140
  have h143 := C (C (C h10 h137) h10) h25
  have h144 := C (C h10 (T (T h36 h101) h100)) h10
  have h145 := S h131
  have h146 := C (C h10 h74) h10
  have h147 := C h122 h10
  have h148 := C (T (T (T (T (T (T (C (C h10 h147) h10) h128) (C (T (C (C h10 (S h129)) h10) h146) h10)) h145) h80) h76) h144) h10
  have h149 := C h5 (T (T (C (T (T (T h123 h148) (C (T h132 (C (C h10 (T (T (T h72 h71) h143) h142)) h10)) h10)) (S h141)) h10) h140) h138)
  have h150 := C h5 h127
  have h151 := C (T h150 h149) h5
  have h152 := h v6 v2 v0
  have h153 := S h152
  have h154 := C h5 h147
  have h155 := C h5 (T (T h143 h142) (C (T (T (T h141 (C (T (C (C h10 (T (T (T h140 h138) h106) h105)) h10) h144) h10)) h133) h124) h10))
  have h156 := C (T h155 h154) h5
  have h157 := h v29 v0 x
  let v158 := M v0 v0
  have h159 := h (M v158 v0) x x
  have h160 := h v158 v2 v0
  have h161 := h (M (M v2 v158) v2) x v0
  have h162 := h v0 v2 v0
  have h163 := h v0 x v0
  have h164 := S h163
  have h165 := h (M (M x v158) x) v2 v0
  have h166 := C (T (T (T h165 (C (T (T (T (T (C (C h5 h164) h5) h36) h101) h100) (C (C h10 h162) h10)) h1)) (S h161)) (C (C h5 (T h160 (C (T (T (T (T (C (C h5 (T (T (T (T h159 (C (C (C h10 (T (T (T (C (C (C h1 h26) h1) h10) (S h157)) h31) h41)) h10) h10)) h40) h72) h71)) h5) h156) h82) h81) h48) h1))) h5)) h1
  have h167 := C h10 h110
  have h168 := T (T (T h98 h4) h74) h84
  have h169 := C h10 h168
  have h170 := C (T (T (T (T (T (T (T (T (T h169 h167) h163) h166) h153) h47) h107) h102) h151) (C (C h5 (T (T (T (T h106 h105) h36) h101) h100)) h5)) h10
  have h171 := T (T (T h109 h75) h3) h125
  have h172 := C h10 h171
  have h173 := C h172 h10
  have h174 := C h10 h85
  have h175 := C h174 h10
  have h176 := C (T (T (T (C (C h5 (T (C (T (T (T (T h47 h107) h102) h151) (C (C h5 (T (T (T (T h106 h105) h36) (C (C (C h10 (T (T (T h33 h32) h157) (C (C (C h1 h27) h1) h10))) h10) h10)) (S h159))) h5)) h1) (S h160))) h5) h161) (C (T (T (T (T (C (C h10 (S h162)) h10) h92) h90) h40) (C (C h5 h163) h5)) h1)) (S h165)) h1
  have h177 := h y y x
  have h178 := C (T (C (C h10 (S h177)) h10) h146) h10
  let v179 := M y v77
  have h180 := h (M v179 y) x x
  have h181 := C h25 h147
  have h182 := C h25 h127
  have h183 := h v179 x y
  have h184 := S h183
  have h185 := T h98 h4
  have h186 := S h180
  have h187 := C (T h130 (C (C h10 h177) h10)) h10
  have h188 := h (M (M x v6) x) x v2
  have h189 := h y x v2
  have h190 := h v94 y v2
  have h191 := T h3 h125
  have h192 := C h122 h191
  have h193 := h v28 x y
  have h194 := h y y y
  let v195 := M y (M y y)
  have h196 := h (M v195 y) x y
  have h197 := h v195 x y
  have h198 := h v78 y y
  have h199 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h163 h166) h153) h47) h107) h102) h151) (C (T (T (T h155 h154) h198) (C (T (C (T (T (T (T (T (T (T (T (T (T (C h25 (T (T h192 (C h25 h168)) (C h25 h110))) h197) (C (C (C h10 (T h196 (C (C (C h10 (S h194)) h10) h25))) h10) h25)) (S h193)) h175) h173) h170) h136) h134) h133) h124) h25) h192) h25)) h5)) (S h190)) h97) h96) h9) h11) h118) (C (T h15 (C (C h10 h189) h10)) h5)) (S h188)) (C (C h10 h108) h10)) (C (C h10 (T (T h131 h187) h186)) h10)) h185
  have h200 := C h1 h171
  have h201 := C h1 h85
  have h202 := h (M v0 y) v2 y
  have h203 := C h1 h110
  have h204 := C h1 h168
  have h205 := C h126 h185
  have h206 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (C (C h10 (T (T h180 h178) h145)) h10) (C (C h10 h83) h10)) h188) (C (T (C (C h10 (S h189)) h10) h117) h5)) h16) h12) h8) h119) h99) h190) (C (T (T (T (C (T h205 (C (T (T (T (T (T (T (T (T (T (T h123 h148) (S h134)) h135) (C (T (T (T (T (T (T (T (T (T (C (C h5 (T (T (T (T h92 h90) h40) h72) h71)) h5) h156) h82) h81) h48) h152) h176) h164) h174) h172) h10)) (C h169 h10)) (C h167 h10)) h193) (C (C (C h10 (T (C (C (C h10 h194) h10) h25) (S h196))) h10) h25)) (S h197)) (C h25 (T (T (C h25 h85) (C h25 h171)) h205))) h25)) h25) (S h198)) h150) h149) h5)) h156) h82) h81) h48) h152) h176) h164) h191
  T (T (T (T (T (T (T (T (T h69 (C (C (C h5 (T (T (T (T (T (T (T (T (T (T h163 h166) h153) h47) h107) h102) h131) h187) h186) (C h182 h25)) (C (T (T (T (T h181 h183) h206) h204) h203) h25))) h5) h25)) (S h202)) h201) h200) h199) h184) (h v179 v2 v0)) (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (C (C h5 (T (T (T (T (T (T (C (T h183 h206) h1) (C (T (T (T (T h204 h203) h202) (C (C (C h5 (T (T (T (T (T (T (T (T (T (T (C (T (T (T (T h201 h200) h199) h184) h182) h25) (C h181 h25)) h180) h178) h145) h82) h81) h48) h152) h176) h164)) h5) h25)) h70) h1)) h134) h133) h124) h121) h120)) h5) (C (C h5 h168) h5)) h111) h39) h114) h113) (h v17 x v2)) (C (C (C h10 (T h19 (C h15 h5))) h10) h5)) (S (h v28 x v2))) h175) h173) h170) h136) h134) h133) h124) h1)) (C h122 h1)

