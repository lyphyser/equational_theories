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
theorem Equation952_implies_Equation3286 (G: Type _) [Magma G] (h: Equation952 G) : Equation3286 G := fun x y z =>
  let v0 := M z z
  let v1 := M y v0
  let v2 := M y v1
  have h3 := h v2 v0 v0
  have h4 := S h3
  have h5 := h v0 v0 y
  have h6 := S h5
  let v7 := M v1 v1
  have h8 := h v7 v2 v0
  let v9 := M v0 v2
  have h10 := R v9
  have h11 := h v0 v0 x
  have h12 := S h11
  have h13 := R v2
  let v14 := M x v0
  let v15 := M v14 v14
  have h16 := h v15 v2 v0
  have h17 := h v15 x v0
  have h18 := R (M v0 x)
  have h19 := h v0 v0 v0
  have h20 := R x
  let v21 := M v0 v0
  have h22 := h (M v21 v21) x v0
  have h23 := R v21
  have h24 := h v21 v0 z
  have h25 := R v0
  have h26 := h z z x
  have h27 := S h26
  have h28 := h z z z
  let v29 := M x z
  let v30 := M v29 v29
  have h31 := h v30 z z
  have h32 := h v30 x z
  have h33 := R (M z x)
  have h34 := S h28
  have h35 := h v21 x z
  have h36 := C h25 (T (T (T (T (T (T (C (T (T (C h11 h23) (C h12 (T (T (T (T h35 (C h20 (C (T h34 h26) h33))) (S h32)) h31) (C h28 (C h27 h25))))) (S h24)) h23) h22) (C h20 (C (T (S h19) h11) h18))) (S h17)) h16) (C h13 (C (T h12 h5) h10))) (S h8))
  have h37 := h v21 v0 v0
  have h38 := T (T h37 h36) h6
  have h39 := h v0 y x
  have h40 := S h39
  have h41 := h (M v14 (M x y)) x y
  let v42 := M y x
  have h43 := R v42
  have h44 := h v0 y y
  have h45 := S h44
  let v46 := M y y
  let v47 := M v1 v46
  have h48 := h v47 x y
  have h49 := h v47 v0 y
  have h50 := R v1
  have h51 := h y v0 v0
  have h52 := S h51
  let v53 := M v0 y
  have h54 := h (M v53 v21) x v0
  have h55 := S h54
  have h56 := h y v0 v2
  have h57 := S h56
  have h58 := C h20 (C (T h57 h51) h18)
  let v59 := M v2 v0
  let v60 := M v2 y
  let v61 := M v60 v59
  have h62 := h v61 x v0
  have h63 := h v61 z v0
  have h64 := S h63
  have h65 := h z v0 v0
  have h66 := S h65
  have h67 := C h25 (T (C h66 h23) h34)
  let v68 := M v0 z
  let v69 := M v68 v21
  have h70 := h v69 v0 v0
  have h71 := h v69 x v0
  have h72 := S h71
  have h73 := h z v0 y
  have h74 := C h20 (C (T (S h73) h65) h18)
  let v75 := M y z
  have h76 := h (M v75 v1) x v0
  have h77 := h v1 z v2
  have h78 := S h77
  let v79 := M v2 v1
  have h80 := h (M v79 (M v2 z)) x z
  have h81 := h v1 z y
  have h82 := h (M v2 v75) x z
  have h83 := h z v2 y
  have h84 := S h83
  have h85 := R v75
  have h86 := C h85 (T (C h84 (T (T h82 (C h20 (C (T (S h81) h77) h33))) (S h80))) h78)
  let v87 := M v75 (M y v2)
  have h88 := h v87 v75 v2
  have h89 := h v87 x v2
  have h90 := S h89
  have h91 := R (M v2 x)
  have h92 := h z v2 x
  have h93 := S h92
  have h94 := C h20 (C (T h93 h83) h91)
  have h95 := h (M v29 (M x v2)) x v2
  have h96 := T (T (T (T (T (T (T (T (T h95 h94) h90) h88) h86) h76) h74) h72) h70) h67
  have h97 := S h95
  have h98 := C h20 (C (T h84 h92) h91)
  have h99 := S h88
  have h100 := C h85 (T h77 (C h83 (T (T h80 (C h20 (C (T h78 h81) h33))) (S h82))))
  have h101 := S h76
  have h102 := C h20 (C (T h66 h73) h18)
  have h103 := S h70
  have h104 := C h25 (T h28 (C h65 h23))
  have h105 := h v68 v2 v2
  have h106 := S h105
  let v107 := M v2 v2
  have h108 := h v107 x v1
  have h109 := R (M v1 x)
  have h110 := h v1 v1 y
  let v111 := M x x
  have h112 := h v1 v1 v111
  have h113 := S h112
  let v114 := M v111 v1
  let v115 := M v114 v114
  have h116 := h v115 x v1
  have h117 := h v115 v2 v1
  let v118 := M v1 v2
  have h119 := R v118
  have h120 := h v0 v1 y
  have h121 := R v68
  have h122 := h v2 v0 v2
  have h123 := S h122
  have h124 := C (T (T h92 (C h122 h96)) (C h123 h121)) (T (T (T (T (C h13 (T h120 (C h112 h119))) (S h117)) h116) (C h20 (C (T h113 h110) h109))) (S h108))
  have h125 := h v2 z v111
  have h126 := S h125
  have h127 := R z
  have h128 := C h127 (C h126 h25)
  let v129 := M (M v111 v2) (M v111 z)
  have h130 := h v129 z z
  have h131 := h v129 v2 z
  let v132 := M z v2
  have h133 := h v132 x v0
  have h134 := h (M v0 v132) x v2
  have h135 := h z v2 z
  have h136 := h v87 v0 v2
  have h137 := R v59
  have h138 := h v129 x v0
  have h139 := S h130
  have h140 := C h127 (C h125 h25)
  have h141 := S h116
  have h142 := S h110
  have h143 := T (T (T (T (T (T (T (T (T h104 h103) h71) h102) h101) h100) h99) h89) h98) h97
  have h144 := C (T (T (C h122 h121) (C h123 h143)) h93) (T (T (T (T h108 (C h20 (C (T h142 h112) h109))) h141) h117) (C h13 (T (C h113 h119) (S h120))))
  have h145 := h y v2 v0
  have h146 := S h145
  have h147 := C h127 (T (C h146 (T (T (T (T (T (T (T (T (T (T (T (C h13 (T (T (T (T (T h92 (C h13 (T (T (T (T (T (T (T (T (T (T (T h95 h94) h90) h88) h86) h76) h74) h72) h70) h67) h105) (C h125 (T (T (T (T (T h144 h140) h139) h138) (C h20 (C (T (T (T (T (C h25 (T (T h130 h128) (C h83 h137))) (S h136)) h89) (C h20 (C (T h84 h135) h91))) (S h134)) h18))) (S h133)))))) (S h131)) h130) h128) h124)) h106) h104) h103) h71) h102) h101) h100) h99) h89) h98) h97)) (C h56 h96))
  let v148 := M v53 v9
  have h149 := h v148 z v2
  have h150 := h v148 x v2
  have h151 := S h150
  have h152 := h y v2 v2
  have h153 := C h20 (C (T (S h152) h145) h91)
  let v154 := M v60 v107
  have h155 := h v154 x v2
  have h156 := T (C h25 (T (T (T (T (T (T (T (T h155 h153) h151) h149) h147) h64) h62) h58) h55)) h52
  have h157 := C h156 h38
  have h158 := h v154 v0 v0
  have h159 := S h155
  have h160 := C h20 (C (T h146 h152) h91)
  have h161 := S h149
  have h162 := C h127 (T (C h57 h143) (C h145 (T (T (T (T (T (T (T (T (T (T (T h95 h94) h90) h88) h86) h76) h74) h72) h70) h67) h105) (C h13 (T (T (T (T (T h144 h140) h139) h131) (C h13 (T (T (T (T (T (T (T (T (T (T (T (C h126 (T (T (T (T (T h133 (C h20 (C (T (T (T (T h134 (C h20 (C (T (S h135) h83) h91))) h90) h136) (C h25 (T (T (C h84 h137) h140) h139))) h18))) (S h138)) h130) h128) h124)) h106) h104) h103) h71) h102) h101) h100) h99) h89) h98) h97))) h93)))))
  have h163 := S h62
  have h164 := C h20 (C (T h52 h56) h18)
  have h165 := R y
  have h166 := h v46 x v1
  have h167 := h v47 v1 y
  have h168 := h v9 x v1
  have h169 := T (T (T (T h168 (C h20 (C (T (C h50 (C h44 h13)) (S h167)) h109))) (S h166)) (C h165 (T (T (T (T (T (T h51 (C h11 (T (T (T (T (T (T (T (T (T (T h54 h164) h163) h63) h162) h161) h150) h160) h159) h158) (C h25 h157)))) (C h12 (C h44 h50))) (S h49)) h48) (C h20 (C (T h45 h39) h43))) (S h41)))) h40
  have h170 := C h169 h38
  have h171 := S h37
  have h172 := C h25 (T (T (T (T (T (T h8 (C h13 (C (T h6 h11) h10))) (S h16)) h17) (C h20 (C (T h12 h19) h18))) (S h22)) (C (T (T h24 (C h11 (T (T (T (T (C h34 (C h26 h25)) (S h31)) h32) (C h20 (C (T h27 h28) h33))) (S h35)))) (C h12 h23)) h23))
  have h173 := T (T h5 h172) h171
  have h174 := T h51 (C h25 (T (T (T (T (T (T (T (T h54 h164) h163) h63) h162) h161) h150) h160) h159))
  have h175 := C h174 h173
  have h176 := T (T (T (T h39 (C h165 (T (T (T (T (T (T h41 (C h20 (C (T h40 h44) h43))) (S h48)) h49) (C h11 (C h45 h50))) (C h12 (T (T (T (T (T (T (T (T (T (T (C h25 h175) (S h158)) h155) h153) h151) h149) h147) h64) h62) h58) h55))) h52))) h166) (C h20 (C (T h167 (C h50 (C h45 h13))) h109))) (S h168)
  have h177 := C h176 h170
  have h178 := h v2 v1 v0
  have h179 := S h178
  have h180 := h (M v9 (M v0 v1)) x v1
  have h181 := h v2 v1 v2
  have h182 := S h181
  let v183 := M v107 v79
  have h184 := h v183 x v1
  have h185 := h v183 v59 v1
  have h186 := h v1 v2 v1
  have h187 := S h186
  have h188 := C h176 h173
  have h189 := C h169 h188
  let v190 := M v7 v118
  have h191 := h v190 v0 v2
  have h192 := h v190 v2 v2
  have h193 := R v107
  have h194 := h (M v59 v79) v1 v1
  have h195 := R v7
  have h196 := h v0 v1 v2
  have h197 := C h25 (T (T (T (C h113 (T (T (T (T (T (T (C h50 (T h5 (C h196 h195))) (S h194)) (C h137 (T (T (T (C h13 (T h110 (C h186 h193))) (S h192)) h191) (C (T (T (T (T (T (T h5 h172) h171) h188) h189) h4) h181) (C h187 h137))))) (S h185)) h184) (C h20 (T (C h182 h109) (C h178 h109)))) (S h180))) h179) h3) h177)
  have h198 := C h112 (T (T (T (T (T (T h180 (C h20 (T (C h179 h109) (C h181 h109)))) (S h184)) h185) (C h137 (T (T (T (C (T (T (T (T (T (T h182 h3) h177) h170) h37) h36) h6) (C h186 h137)) (S h191)) h192) (C h13 (T (C h187 h193) h142))))) h194) (C h50 (T (C (S h196) h195) h6)))
  have h199 := h v115 v0 v1
  have h200 := h v1 v1 v2
  have h201 := C h20 (C (T (S h200) h112) h109)
  have h202 := h (M v79 v79) x v1
  have h203 := h v1 v0 y
  have h204 := R v79
  have h205 := C h204 (C h123 (S h203))
  let v206 := M v107 v59
  have h207 := h v206 v79 v0
  have h208 := h v206 x v0
  have h209 := S h208
  have h210 := C h20 (C (T h4 h122) h18)
  let v211 := M v9 v21
  have h212 := h v211 x v0
  have h213 := h v211 x y
  have h214 := S h212
  have h215 := C h20 (C (T h123 h3) h18)
  have h216 := S h207
  have h217 := C h204 (C h122 h203)
  have h218 := S h202
  have h219 := C h20 (C (T h113 h200) h109)
  have h220 := S h199
  have h221 := C h25 (T (T (T h189 h4) h178) h198)
  have h222 := h (M v1 v42) x x
  have h223 := R v111
  have h224 := h v0 x y
  let v225 := M x v111
  have h226 := h x x x
  have h227 := S h226
  let v228 := M v111 v111
  have h229 := h v228 x x
  have h230 := h v111 v0 x
  have h231 := h v111 v0 v1
  T (T (T h231 (C h25 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (h (M (M v1 v111) (M v1 v0)) x v0) (C h20 (C (T (S h231) h230) h18))) (C h20 (T (T (T (T (C (S h230) (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h5 h172) h171) h188) h189) h221) h220) h116) h219) h218) h217) h216) h208) h215) h214) h213) (C h20 (T (T (C (T (C h174 (T (T (T (T (T (T (T (T (T (T (T h212 h210) h209) h207) h205) h202) h201) h141) h199) h197) h177) h170)) h157) h43) h222) (C h20 (C (S h224) h223))))) (T (T (h x v111 x) (C h223 (C (T (T (T (T (h v111 v111 v111) (C h223 (C (T (h v228 v111 x) (C h223 (T (C h227 (C h226 h223)) (S h229)))) (R v228)))) (S (h v228 v111 v111))) h229) (C h20 (C h227 h223))) (R v225)))) (S (h v225 v111 x))))) (S (h (M x (M v0 v111)) v111 x))) (C h20 (C h224 h223))) (S h222)) (C (T h175 (C h156 (T (T (T (T (T (T (T (T (T (T (T h188 h189) h221) h220) h116) h219) h218) h217) h216) h208) h215) h214))) h43)))) (S h213)) h212) h210) h209) h207) h205) h202) h201) h141) h199) h197) h4) h178) h198))) h197) h4

