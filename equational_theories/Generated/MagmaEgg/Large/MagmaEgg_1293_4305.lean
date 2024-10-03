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
theorem Equation1293_implies_Equation4305 (G: Type _) [Magma G] (h: Equation1293 G) : Equation4305 G := fun x y z =>
  let v0 := M y z
  have h1 := R v0
  let v2 := M (M (M y y) x) x
  let v3 := M (M v0 y) y
  have h4 := h z v3 v2
  have h5 := S h4
  have h6 := R v2
  have h7 := h y z y
  have h8 := h y y x
  have h9 := R v3
  have h10 := C h9 (T h8 (C (T h8 (C h7 h6)) h6))
  let v11 := M (M (M v0 v0) x) x
  have h12 := h y z v11
  have h13 := S h12
  have h14 := R v11
  have h15 := h v0 v0 x
  have h16 := R z
  have h17 := C h16 (T h15 (C h15 h14))
  have h18 := T h17 h13
  have h19 := C h9 h18
  have h20 := T (T h19 h10) h5
  have h21 := C h20 h1
  have h22 := S h15
  have h23 := C h16 (T (C h22 h14) h22)
  have h24 := T h12 h23
  have h25 := C h9 h24
  have h26 := S h8
  have h27 := S h7
  have h28 := C h9 (T (C (T (C h27 h6) h26) h6) h26)
  let v29 := M x y
  let v30 := M x v29
  have h31 := h z v30 z
  have h32 := S h31
  let v33 := M (M (M z z) x) x
  let v34 := M z v0
  let v35 := M v34 z
  let v36 := M v35 z
  have h37 := h v0 v36 v33
  have h38 := S h37
  have h39 := R v33
  have h40 := h z v0 z
  have h41 := h z z x
  have h42 := R v36
  have h43 := C h42 (T h41 (C (T h41 (C h40 h39)) h39))
  have h44 := C (C (T h43 h38) h18) h18
  let v45 := M v36 z
  have h46 := R (M v45 v34)
  have h47 := C h46 h24
  have h48 := C (T h47 h44) h24
  have h49 := C h46 h18
  have h50 := R v30
  have h51 := C h20 h50
  have h52 := R v29
  let v53 := M (M (M v29 v29) x) x
  have h54 := h x y v53
  have h55 := S h54
  have h56 := R v53
  have h57 := h v29 v29 x
  have h58 := R y
  have h59 := C h58 (T h57 (C h57 h56))
  have h60 := C h16 h44
  have h61 := h v36 z v34
  have h62 := C (T (T h61 h60) h27) h52
  have h63 := T (T h62 h59) h55
  have h64 := C h63 h52
  have h65 := T (T h4 h28) h25
  have h66 := C h65 h64
  have h67 := h v35 z v29
  have h68 := C (T (T h67 h66) h51) h16
  have h69 := S h61
  have h70 := S h41
  have h71 := C h42 (T (C (T (C (S h40) h39) h70) h39) h70)
  have h72 := C (C (T h37 h71) h24) h24
  have h73 := C h16 h72
  have h74 := C (T (T (T (T (T h17 h13) h7) h73) h69) h68) (T (T (T (T (C h49 h18) h48) h19) h10) h5)
  have h75 := h v45 v34 v34
  have h76 := T (T (T h37 h71) h75) h74
  have h77 := C h50 h76
  have h78 := C (T (T (T (T h77 h32) h4) h28) h25) h1
  let v79 := M v30 v0
  have h80 := h v79 v0 v29
  have h81 := S h80
  have h82 := S h75
  have h83 := C (T h72 h49) h18
  have h84 := S h67
  have h85 := C (T (T h7 h73) h69) h52
  have h86 := S h57
  have h87 := C h58 (T (C h86 h56) h86)
  have h88 := T (T h54 h87) h85
  have h89 := C h88 h52
  have h90 := C h20 h89
  have h91 := C h65 h50
  have h92 := C (T (T h91 h90) h84) h16
  have h93 := C (T (T (T (T (T h92 h61) h60) h27) h12) h23) (T (T (T (T h4 h28) h25) h83) (C h47 h24))
  have h94 := T (T (T h93 h82) h43) h38
  have h95 := C h50 h94
  have h96 := C (T (T (T (T h19 h10) h5) h31) h95) h1
  have h97 := C h65 h1
  let v98 := M z v30
  have h99 := h v98 z v29
  have h100 := C h68 h52
  have h101 := C h100 h52
  have h102 := C (T (T (T (T (C (T h77 h32) (T h89 h101)) (S h99)) h91) h90) h84) h16
  have h103 := T (T (T (T (T (T (T h102 h61) h60) h27) h12) h23) h97) h96
  have h104 := C h103 h52
  have h105 := C h104 h52
  have h106 := C h92 h52
  have h107 := C h106 h52
  have h108 := C (T (T (T (T h67 h66) h51) h99) (C (T h31 h95) (T h107 h64))) h16
  have h109 := C (T h92 h108) h52
  have h110 := C h109 h52
  let v111 := M v98 z
  let v112 := M v111 z
  have h113 := h v112 y y
  have h114 := S h113
  have h115 := R (M v112 y)
  have h116 := R v112
  have h117 := R (M v112 v34)
  have h118 := R v34
  have h119 := C (T (T (T h102 h61) h60) h27) (T (T (T (T (T (T (T h4 h28) h25) h83) (C (T h47 (C (C (T h75 h74) h118) h118)) h24)) (C (C h117 h18) h18)) (C (C (C h116 h18) h24) h24)) (C (C h115 h18) h18))
  have h120 := T (T (T (T (T (T (T h78 h21) h17) h13) h7) h73) h69) h108
  have h121 := C h120 h16
  have h122 := C (T (T (T (T (T (T h121 h119) h114) h93) h82) h43) h38) (T (T (T h89 h101) h110) h105)
  have h123 := C h103 h16
  have h124 := C (T (T (T h7 h73) h69) h108) (T (T (T (T (T (T (T (C (C h115 h24) h24) (C (C (C h116 h24) h18) h18)) (C (C h117 h24) h24)) (C (T (C (C (T h93 h82) h118) h118) h49) h18)) h48) h19) h10) h5)
  have h125 := C (T (T h113 h124) h123) h50
  have h126 := C (T (T h125 h122) h81) h1
  have h127 := C h76 h50
  have h128 := C h127 h1
  let v129 := M v0 v30
  let v130 := M v129 v0
  have h131 := h v130 v29 v34
  have h132 := S h131
  have h133 := R (M v130 v29)
  have h134 := C h133 h24
  have h135 := C h133 h18
  have h136 := C h94 h50
  have h137 := C h136 h1
  have h138 := C (T (T h121 h119) h114) h50
  have h139 := C (T h102 h68) h52
  have h140 := C h139 h52
  have h141 := C h120 h52
  have h142 := C h141 h52
  have h143 := C (T (T (T (T (T (T h37 h71) h75) h74) h113) h124) h123) (T (T (T h142 h140) h107) h64)
  have h144 := C (T (T h80 h143) h138) h1
  have h145 := h (M v79 v30) z v29
  have h146 := C (T (T (T (C h127 h50) (C h125 h50)) (C (T (T (T h122 h81) h77) h32) (T (T h89 h101) h110))) (S h145)) h16
  have h147 := T (T (T (T (T (T (T (T (T (T h146 h102) h61) h60) h27) h12) h23) h97) h96) h144) h137
  have h148 := C h147 h52
  have h149 := C (T (T (T h145 (C (T (T (T h31 h95) h80) h143) (T (T h140 h107) h64))) (C h138 h50)) (C h136 h50)) h16
  have h150 := T (T (T (T (T (T (T (T h78 h21) h17) h13) h7) h73) h69) h108) h149
  have h151 := C h150 h52
  have h152 := C (T h109 h104) h24
  have h153 := R (M v111 v29)
  have h154 := C h153 h18
  have h155 := C h100 h24
  have h156 := R (M v36 v29)
  have h157 := C h156 h18
  have h158 := C h88 h24
  have h159 := h x v29 v0
  have h160 := C h52 (T (T h159 (C (T (T (T (T (T (T h158 h157) h155) h154) h152) (C (T h151 h148) h118)) h135) (T (T (T h78 h21) h17) h13))) (C h134 h24))
  let v161 := M v29 x
  let v162 := M v161 v29
  have h163 := R (M v162 y)
  have h164 := C h163 h18
  have h165 := S h159
  have h166 := C h63 h18
  have h167 := C h156 h24
  have h168 := C h106 h18
  have h169 := C h153 h24
  have h170 := C (T h141 h139) h18
  have h171 := T (T (T (T (T (T (T (T h146 h102) h61) h60) h27) h12) h23) h97) h96
  have h172 := C h171 h52
  have h173 := T (T (T (T (T (T (T (T (T (T h128 h126) h78) h21) h17) h13) h7) h73) h69) h108) h149
  have h174 := C h173 h52
  have h175 := T h131 (C h52 (T (T (C h135 h18) (C (T (T (T (T (T (T h134 (C (T h174 h172) h118)) h170) h169) h168) h167) h166) (T (T (T h12 h23) h97) h96))) h165))
  have h176 := C h175 h52
  have h177 := R (M (M v79 v0) v29)
  have h178 := C h177 h24
  have h179 := T h160 h132
  have h180 := C h179 h52
  have h181 := C (T (T h180 h174) h172) h18
  have h182 := T (T (T (T (T (T h181 h178) h170) h169) h168) h167) h166
  have h183 := C h182 (T h97 h96)
  have h184 := R (M v162 v34)
  have h185 := C h184 h24
  have h186 := C (T (T (T (T (T (T (T (T (T (T (T h185 h183) h165) h54) h87) h85) h100) h109) h104) h151) h148) h176) h58
  have h187 := C h184 h18
  have h188 := C h187 h18
  have h189 := C (T (T h151 h148) h176) h24
  have h190 := C h177 h18
  have h191 := T (T (T (T (T (T h158 h157) h155) h154) h152) h190) h189
  have h192 := C h191 (T h78 h21)
  have h193 := C (T (T (T (T (T (T (T (T (T (T h180 h174) h172) h141) h139) h106) h62) h59) h55) h159) h192) h118
  have h194 := T (T h193 h188) h186
  have h195 := C h194 h24
  have h196 := C (T (T (T (T (T (T (T (T (T (T h183 h165) h54) h87) h85) h100) h109) h104) h151) h148) h176) h118
  have h197 := C h185 h24
  have h198 := C (T (T (T (T (T (T (T (T (T (T (T h180 h174) h172) h141) h139) h106) h62) h59) h55) h159) h192) h187) h58
  have h199 := h v162 v29 v0
  have h200 := S h199
  have h201 := C h171 h16
  have h202 := C h176 h52
  have h203 := C h148 h52
  have h204 := C h151 h52
  have h205 := T (T (T (T (T (T h89 h101) h110) h105) h204) h203) h202
  have h206 := h v129 v30 z
  have h207 := h v129 v0 v29
  have h208 := S h207
  have h209 := C (T (T (T (T (T (T (T (T (T (C h179 h16) (C h173 h16)) h201) h121) h119) h114) h93) h82) h43) h38) (T (T (T (T (T h89 h101) h110) h105) h204) h203)
  have h210 := C h172 h52
  have h211 := C h174 h52
  have h212 := C h150 h16
  have h213 := C (T (T (T (T (T (T (T (T (T h37 h71) h75) h74) h113) h124) h123) h212) (C h147 h16)) (C h175 h16)) (T (T (T (T (T h211 h210) h142) h140) h107) h64)
  have h214 := h v29 x v29
  let v215 := M (M (M v30 v30) x) x
  have h216 := h x v29 v215
  have h217 := S h216
  have h218 := R v215
  have h219 := h v30 v30 x
  have h220 := C h52 (T h219 (C h219 h218))
  have h221 := C h182 h50
  have h222 := T (T h198 h197) h196
  have h223 := C h222 h50
  have h224 := C h194 h50
  have h225 := C h191 h50
  have h226 := S h219
  have h227 := C h52 (T (C h226 h218) h226)
  have h228 := C (T (T (C (T (T (T (T (T (T (T (T (T (T (T (T h180 h174) h172) h141) h139) h106) h62) h59) h55) h216) h227) h225) h224) h50) (C (T (T (T h223 h221) h220) h217) h205)) (S h214)) (T (T (T (T (T h97 h96) h144) h137) (C (T h207 h213) h1)) (C (T (T (T h209 h208) h206) (C h205 (T (T (T (T (T (T (T h201 h121) h119) h114) h93) h82) h43) h38))) h1))
  have h229 := C (T (T (T (T (T (T (T (T (T (T (T (T h223 h221) h220) h217) h54) h87) h85) h100) h109) h104) h151) h148) h176) h50
  have h230 := T (T (T (T (T (T (C h180 h52) h211) h210) h142) h140) h107) h64
  have h231 := C (T (T (T h216 h227) h225) h224) h230
  have h232 := C h222 h18
  have h233 := C h163 h24
  have h234 := R (M v162 v30)
  have h235 := C h234 h18
  have h236 := C (T (T h214 h231) h229) (T (T (T (T (T (C (T (T (T (C h230 (T (T (T (T (T (T (T h37 h71) h75) h74) h113) h124) h123) h212)) (S h206)) h207) h213) h1) (C (T h209 h208) h1)) h128) h126) h78) h21)
  T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h89 h101) h110) h105) h204) h203) h202) (h (M v162 v29) v29 v34)) (C (T (T (T (T (T (T (T (T (T h158 h157) h155) h154) h152) h190) h189) h193) h188) h186) (T (T (T (T (T (T (T (T (T (T (T (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (C (T (T (T (T (C h230 (T (T (T (T (T (T (T (T (T (T (T (T h158 h157) h155) h154) h152) h190) h189) h193) h188) h186) (C (T (T (T (T (T (T (T (T (T (T (T (T h180 h174) h172) h141) h139) h106) h62) h59) h55) h159) h192) h187) h195) h24)) (C h164 h18)) (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h233 h232) h185) h183) h165) h54) h87) h85) h100) h109) h104) h151) h148) h176) h199) h236) h235) h58))) (S (h v162 v30 y))) h199) h236) h235) h18) (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (C h234 h24) h228) h200) h180) h174) h172) h141) h139) h106) h62) h59) h55) h159) h192) h187) h195) h164) h58)) (C h233 h24)) (C (T (T (T (T (T (T (T (T (T (T (T (T h232 h185) h183) h165) h54) h87) h85) h100) h109) h104) h151) h148) h176) h18)) h198) h197) h196) h181) h178) h170) h169) h168) h167) h166) h214) h231) h229) h118) h228) h200) h180) h174) h172) h141) h139) h106) h62) h59) h55))) (C (T (T (T (T (T (T (T (T (T h198 h197) h196) h181) h178) h170) h169) h168) h167) h166) (T (T (T (T h159 h192) h187) h195) h164))) (S (h v161 v29 y))) h160) h132) h128) h126) h78) h21

