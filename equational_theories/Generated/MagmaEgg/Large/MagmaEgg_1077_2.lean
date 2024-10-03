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
theorem Equation1077_implies_Equation2 (G: Type _) [Magma G] (h: Equation1077 G) : Equation2 G := fun x y =>
  let v0 := M y (M y y)
  let v1 := M v0 x
  let v2 := M v0 y
  let v3 := M v2 (M v2 y)
  let v4 := M v3 x
  have h5 := h y v4 v1
  have h6 := S h5
  have h7 := R v1
  have h8 := h v2 y x
  have h9 := R y
  have h10 := h y y y
  have h11 := h y y x
  have h12 := R v4
  have h13 := C h12 (T h11 (C (T h10 (C h9 h8)) h7))
  have h14 := R x
  have h15 := h v3 y y
  let v16 := M x y
  let v17 := M x v16
  let v18 := M v17 x
  let v19 := M v3 y
  have h20 := h y v19 v18
  have h21 := S h20
  have h22 := R v18
  have h23 := h v2 y y
  have h24 := T h10 (C h9 h23)
  have h25 := h x y x
  have h26 := R v19
  have h27 := C h26 (T h25 (C h24 h22))
  have h28 := h v19 x x
  have h29 := S h28
  have h30 := S h10
  have h31 := S h23
  have h32 := T (C h9 h31) h30
  have h33 := C h26 (T (C h32 h22) (S h25))
  have h34 := C h26 (T h20 h33)
  have h35 := S h11
  have h36 := C h26 (T (C h32 h7) h35)
  have h37 := h y v19 v1
  have h38 := T h13 h6
  have h39 := C h12 h38
  have h40 := C h12 (T (C (T (C h9 (S h8)) h30) h7) h35)
  have h41 := T h5 h40
  have h42 := h v4 y y
  have h43 := S h42
  have h44 := C h12 h41
  have h45 := S h37
  have h46 := C h26 (T h11 (C h24 h7))
  have h47 := C h26 (T h27 h21)
  have h48 := T (T h37 h36) h34
  have h49 := C h9 (T (C h48 h9) (C (T (T (T (T (T h47 h46) h45) h5) h40) h44) h9))
  have h50 := C (T h49 h43) h41
  have h51 := T (T (T h50 h39) h13) h6
  have h52 := R v0
  have h53 := C h52 h51
  let v54 := M v0 v2
  have h55 := h v54 y y
  have h56 := S h55
  have h57 := R (M v54 y)
  have h58 := T (T h47 h46) h45
  have h59 := C h9 (T (C (T (T (T (T (T h39 h13) h6) h37) h36) h34) h9) (C h58 h9))
  have h60 := C (T h42 h59) h38
  have h61 := T (T (T h5 h40) h44) h60
  have h62 := C h52 h61
  have h63 := C (T (T (T (T h5 h40) h44) h60) h62) h57
  have h64 := h v0 y y
  have h65 := C (T h64 h63) h51
  have h66 := C h9 (T (T (C (T (T h39 h13) h6) (T (T (T (T (T h5 h40) h44) h60) h62) h65)) h56) h65)
  have h67 := S h64
  have h68 := C (T (T (T (T h53 h50) h39) h13) h6) h57
  have h69 := C (T (T (T (T (T (T (T (T (T (T (T (T h68 h67) h49) h66) h56) h53) h50) h39) h13) h6) h37) h36) h34) h14
  have h70 := C (T h68 h67) h61
  have h71 := C h9 (T (T h70 h55) (C (T (T h5 h40) h44) (T (T (T (T (T h70 h53) h50) h39) h13) h6)))
  have h72 := h v54 y x
  have h73 := S h72
  have h74 := C (T (T (T (T (T (T (T (T (T (T (T (T h47 h46) h45) h5) h40) h44) h60) h62) h55) h71) h59) h64) h63) h14
  have h75 := C h48 h14
  have h76 := C h9 (T h75 h74)
  let v77 := M y (M y x)
  have h78 := h v77 y y
  have h79 := S h78
  let v80 := M v77 (M v77 y)
  have h81 := R (M v80 y)
  have h82 := C (T (T (T (T (T (T h76 h73) h55) h71) h59) h64) h63) h9
  have h83 := T (T (T (T (T (T h82 h70) h53) h50) h39) h13) h6
  have h84 := R v77
  have h85 := C h84 h83
  have h86 := T (T (T (T (T (T (T h85 h82) h70) h53) h50) h39) h13) h6
  have h87 := C h86 h81
  have h88 := C (T (T (T (T (T (T (T (T h87 h79) h76) h73) h55) h71) h59) h64) h63) h14
  have h89 := C h58 h14
  have h90 := C h9 (T h69 h89)
  have h91 := C (T (T (T (T (T (T h68 h67) h49) h66) h56) h72) h90) h9
  have h92 := T (T (T (T (T (T h5 h40) h44) h60) h62) h65) h91
  have h93 := C h84 h92
  have h94 := T (T (T (T (T (T (T h5 h40) h44) h60) h62) h65) h91) h93
  have h95 := C h94 h81
  have h96 := h v80 y y
  have h97 := S h96
  have h98 := h v77 y x
  have h99 := S h98
  have h100 := R (M v80 x)
  have h101 := C h86 h100
  have h102 := C (T (T (T (T (T (T (T (T h101 h99) h76) h73) h53) h50) h39) h13) h6) (T (T (T (T (T (T (T (T h5 h40) h44) h60) h62) h65) h91) h93) (C (T h78 h95) h83))
  have h103 := C h94 h100
  have h104 := h v80 x y
  have h105 := S h104
  have h106 := C (T (T (T (T (T (T (T (T h5 h40) h44) h60) h62) h72) h90) h98) h103) (T (T (T (T (T (T (T (T (C (T h87 h79) h92) h85) h82) h70) h53) h50) h39) h13) h6)
  have h107 := C h14 (T (T (T (T (T (T (T (T (T h5 h40) h44) h60) h62) h65) h91) h93) h96) h106)
  have h108 := C (T (T (T (T (T (T (T (T h107 h105) h85) h82) h70) h72) h90) h98) h103) h9
  have h109 := C h14 (T (T (T (T (T (T (T (T (T h102 h97) h85) h82) h70) h53) h50) h39) h13) h6)
  have h110 := C (T (T (T (T h108 h102) h97) h104) h109) h9
  have h111 := T (T (T (T (T (T (T (T (T (T (T h110 h108) h102) h97) h85) h82) h70) h53) h50) h39) h13) h6
  let v112 := M v16 y
  have h113 := R v112
  have h114 := C h113 h111
  have h115 := C (T (T (T (T (T (T (T (T (T (T (T h114 h110) h108) h102) h97) h85) h82) h70) h72) h90) h78) h95) h14
  have h116 := C (T (T (T (T (T (T (T (T h101 h99) h76) h73) h65) h91) h93) h104) h109) h9
  have h117 := C (T (T (T (T h107 h105) h96) h106) h116) h9
  have h118 := T (T (T (T (T (T (T (T (T (T (T h5 h40) h44) h60) h62) h65) h91) h93) h96) h106) h116) h117
  have h119 := C h113 h118
  have h120 := T h117 h119
  have h121 := C h120 h14
  have h122 := h v112 y x
  have h123 := S h122
  have h124 := C (T (T (T (T (T (T (T (T (T (T h108 h102) h97) h85) h82) h70) h53) h50) h39) h13) h6) h121
  have h125 := C (T h124 h123) h14
  have h126 := C h14 (T (T (T (T h125 h121) h115) h88) h69)
  have h127 := h v112 x x
  have h128 := h v112 y y
  have h129 := S h128
  have h130 := C (T (T (T (T (T (T (T (T (T (T (T (T h124 h123) h108) h102) h97) h85) h82) h70) h53) h50) h39) h13) h6) (T (T (T (T (T (T (T (T (T (T (T (T (T h5 h40) h44) h60) h62) h65) h91) h93) h96) h106) h116) h117) h119) (C h120 h111))
  have h131 := T h114 h110
  have h132 := C h131 h14
  have h133 := C (T (T (T (T (T (T (T (T (T (T h5 h40) h44) h60) h62) h65) h91) h93) h96) h106) h116) h132
  have h134 := S h127
  have h135 := C (T h122 h133) h14
  have h136 := C (T (T (T (T (T (T (T (T (T (T (T h87 h79) h76) h73) h65) h91) h93) h96) h106) h116) h117) h119) h14
  have h137 := C (T (T (T (T (T (T (T (T h68 h67) h49) h66) h56) h72) h90) h78) h95) h14
  have h138 := C h14 (T (T (T (T h74 h137) h136) h132) h135)
  have h139 := C (T (T (T (T h28 h138) h134) h122) h133) (T h46 h45)
  have h140 := C (T (T (T (T h124 h123) h127) h126) h29) (T h37 h36)
  have h141 := C (T (T (T (T (T (T (T (T (T (T (T (T h5 h40) h44) h60) h62) h65) h91) h93) h96) h106) h116) h122) h133) (T (T (T (T (T (T (T (T (T (T (T (T (T (C h131 h118) h114) h110) h108) h102) h97) h85) h82) h70) h53) h50) h39) h13) h6)
  have h142 := R v3
  have h143 := C h142 (T (T (T (T (T (T (T (T (T (T (T (T (T h5 h40) h44) h60) h62) h65) h91) h93) h96) h106) h116) h127) h126) h29)
  have h144 := T (T (T (T (T (T (T (T (T (T (T (T (T (T h5 h40) h44) h60) h62) h65) h91) h93) h96) h106) h116) h127) h126) h29) h143
  have h145 := C h144 (T (T (T (T (T (T (T (T (T h75 h74) h137) h136) h132) h135) (C (T (T (T (T h124 h123) h128) h141) h140) h14)) (C (T (T (T (T (T h139 h130) h129) h127) h126) h29) h14)) h27) h21)
  have h146 := C h142 (T (T (T (T (T (T (T (T (T (T (T (T (T h28 h138) h134) h108) h102) h97) h85) h82) h70) h53) h50) h39) h13) h6)
  have h147 := T (T (T (T (T (T (T (T (T (T (T (T (T (T h146 h28) h138) h134) h108) h102) h97) h85) h82) h70) h53) h50) h39) h13) h6
  have h148 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T h146 h28) h138) h134) h108) h102) h97) h85) h82) h70) h72) h90) h145) (C h147 (T (T (T (T (T (T (T h5 h40) h44) h60) h62) h72) h90) h145))) (S h15)) h14
  have h149 := h v16 y y
  have h150 := S h149
  let v151 := M v16 v112
  let v152 := M v151 y
  have h153 := R v152
  have h154 := C (T (T (T (T (T (T (T (T (T h107 h105) h85) h82) h70) h53) h50) h39) h13) h6) (T (T h127 h126) h29)
  have h155 := T (T (T (T (T h154 h31) h50) h39) h13) h6
  have h156 := C h155 h153
  have h157 := C (T (T (T (T (T (T (T (T (T (T h156 h150) h107) h105) h96) h106) h116) h127) h126) h29) h143) h14
  have h158 := T (T (T (T (T (T (T (T (T h5 h40) h44) h60) h62) h65) h91) h93) h104) h109
  have h159 := C h158 (T (T h28 h138) h134)
  have h160 := T (T (T (T (T h5 h40) h44) h60) h23) h159
  have h161 := C h160 h153
  have h162 := h v16 y x
  have h163 := S h162
  let v164 := M v151 x
  have h165 := R v164
  have h166 := C h155 h165
  have h167 := C (T (T (T h166 h163) h149) h161) h14
  have h168 := C h160 h165
  have h169 := h v151 y x
  have h170 := S h169
  have h171 := C (T (T (T (T (T (T (T (T (T (T h146 h28) h138) h134) h108) h102) h97) h104) h109) h149) h161) h14
  have h172 := C h147 (T (T (T (T (T (T (T (T (T h20 h33) (C (T (T (T (T (T h28 h138) h134) h128) h141) h140) h14)) (C (T (T (T (T h139 h130) h129) h122) h133) h14)) h125) h121) h115) h88) h69) h89)
  have h173 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T h15 (C h144 (T (T (T (T (T (T (T h172 h76) h73) h53) h50) h39) h13) h6))) h172) h76) h73) h65) h91) h93) h96) h106) h116) h127) h126) h29) h143) h14
  have h174 := C (T (T (T (T (T (T (T (T (T (T (T h166 h163) h107) h105) h85) h82) h70) h53) h50) h39) h13) h6) (T (T (T (T (T (T (T (T (T h5 h40) h44) h60) h62) h55) h71) h43) h173) h171)
  have h175 := C (T (T (T (T (T (T (T (T (T h154 h31) h62) h65) h91) h93) h104) h109) h162) h168) h9
  have h176 := C (T (T h175 h174) h170) h9
  have h177 := C h153 (T (T (T (T (T (T (T (T (T h176 h175) h174) h170) h154) h31) h50) h39) h13) h6)
  have h178 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T h177 h176) h175) h174) h170) h154) h31) h62) h65) h91) h93) h104) h109) h162) h168) h14
  have h179 := C (T (T (T (T (T (T (T (T (T h166 h163) h107) h105) h85) h82) h70) h53) h23) h159) h9
  have h180 := C (T (T (T (T (T (T (T (T (T (T (T h5 h40) h44) h60) h62) h65) h91) h93) h104) h109) h162) h168) (T (T (T (T (T (T (T (T (T h157 h148) h42) h66) h56) h53) h50) h39) h13) h6)
  have h181 := C (T (T h169 h180) h179) h9
  have h182 := C h153 (T (T (T (T (T (T (T (T (T h5 h40) h44) h60) h23) h159) h169) h180) h179) h181)
  have h183 := C (T h181 h182) h14
  have h184 := h v152 y x
  have h185 := S h184
  have h186 := T (T (T (T (T (T (T (T h175 h174) h170) h154) h31) h50) h39) h13) h6
  have h187 := C h186 h183
  have h188 := C (T h187 h185) h14
  have h189 := C (T h177 h176) h14
  have h190 := T (T (T (T (T (T (T (T h5 h40) h44) h60) h23) h159) h169) h180) h179
  have h191 := C h190 h189
  have h192 := C (T (T (T (T h169 h180) h179) h184) h191) h14
  have h193 := T (T (T (T (T (T (T (T (T (T (T (T (T (T h192 h188) h183) h178) h167) h157) h148) h42) h66) h56) h53) h50) h39) h13) h6
  have h194 := C h193 h190
  have h195 := C h165 (T (T (T (T (T (T (T (T (T (T (T h194 h150) h107) h105) h85) h82) h70) h53) h50) h39) h13) h6)
  have h196 := C (T (T (T (T (T (T (T (T (T (T h195 h194) h150) h107) h105) h85) h82) h70) h53) h23) h159) h14
  have h197 := C (T (T (T (T h187 h185) h175) h174) h170) h14
  have h198 := C (T h184 h191) h14
  have h199 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T h166 h163) h107) h105) h85) h82) h70) h53) h23) h159) h169) h180) h179) h181) h182) h14
  have h200 := C (T (T (T h156 h150) h162) h168) h14
  have h201 := T (T (T (T (T (T (T (T (T (T (T (T (T (T h5 h40) h44) h60) h62) h55) h71) h43) h173) h171) h200) h199) h189) h198) h197
  have h202 := C h201 h186
  have h203 := C h165 (T (T (T (T (T (T (T (T (T (T (T h5 h40) h44) h60) h62) h65) h91) h93) h104) h109) h149) h202)
  have h204 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h192 h188) h183) h178) h167) h157) h148) h42) h66) h56) h65) h91) h93) h104) h109) h149) h202) h203) h14
  have h205 := h v164 y x
  have h206 := S h205
  have h207 := C h193 h204
  have h208 := C (T h207 h206) h14
  have h209 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h195 h194) h150) h107) h105) h85) h82) h70) h55) h71) h43) h173) h171) h200) h199) h189) h198) h197) h14
  have h210 := C h201 h209
  have h211 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h107 h105) h85) h82) h70) h55) h71) h43) h173) h171) h200) h199) h189) h198) h197) h205) h210) h14
  let v212 := M v16 x
  have h213 := h v212 y x
  have h214 := S h213
  have h215 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h207 h206) h192) h188) h183) h178) h167) h157) h148) h42) h66) h56) h65) h91) h93) h104) h109) h14
  have h216 := C (T h205 h210) h14
  have h217 := C (T (T (T (T (T (T (T (T (T (T h154 h31) h62) h65) h91) h93) h104) h109) h149) h202) h203) h14
  have h218 := T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h5 h40) h44) h60) h62) h55) h71) h43) h173) h171) h200) h199) h189) h198) h197) h217) h209) h216) h215
  have h219 := C h218 h193
  have h220 := R v212
  have h221 := C h220 (T (T (T (T (T (T (T (T (T (T (T h5 h40) h44) h60) h62) h65) h91) h93) h104) h109) h162) h219)
  have h222 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h211 h208) h204) h196) h192) h188) h183) h178) h167) h157) h148) h42) h66) h56) h65) h91) h93) h104) h109) h162) h219) h221) h14
  have h223 := T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h211 h208) h204) h196) h192) h188) h183) h178) h167) h157) h148) h42) h66) h56) h53) h50) h39) h13) h6
  have h224 := C h223 h222
  have h225 := C h223 h201
  have h226 := C h220 (T (T (T (T (T (T (T (T (T (T (T h225 h163) h107) h105) h85) h82) h70) h53) h50) h39) h13) h6)
  have h227 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h226 h225) h163) h107) h105) h85) h82) h70) h55) h71) h43) h173) h171) h200) h199) h189) h198) h197) h217) h209) h216) h215) h14
  have h228 := C (T (T h162 h219) h221) h14
  have h229 := T h224 h214
  have h230 := C h229 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h5 h40) h44) h60) h62) h55) h71) h43) h173) h171) h200) h199) h189) h198) h197) h217) h209) h216) h215) h228) h227)
  have h231 := C h218 h227
  have h232 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h107 h105) h85) h82) h70) h55) h71) h43) h173) h171) h200) h199) h189) h198) h197) h217) h209) h216) h215) h213) h231) h223
  have h233 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T h232 h230) h224) h214) h211) h208) h204) h196) h192) h188) h183) h178) h167) h157) h148) h9
  let v234 := M v16 v212
  let v235 := M v234 y
  have h236 := h v235 y x
  have h237 := S h236
  have h238 := C (T (T h226 h225) h163) h14
  have h239 := C h229 h14
  have h240 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h232 h230) h224) h214) h211) h208) h204) h196) h192) h188) h183) h178) h167) h157) h148) h42) h66) h56) h65) h91) h93) h104) h109) h218
  have h241 := T (T h233 h13) h6
  have h242 := R v234
  have h243 := C h242 h241
  have h244 := C (T (T (T h243 h240) h232) h230) h14
  have h245 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h224 h214) h211) h208) h204) h196) h192) h188) h183) h178) h167) h157) h148) h42) h66) h56) h65) h91) h93) h104) h109) h218
  have h246 := T h213 h231
  have h247 := C h246 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h222 h238) h211) h208) h204) h196) h192) h188) h183) h178) h167) h157) h148) h42) h66) h56) h53) h50) h39) h13) h6)
  have h248 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h107 h105) h85) h82) h70) h55) h71) h43) h173) h171) h200) h199) h189) h198) h197) h217) h209) h216) h215) h213) h231) h247) h245) h223
  have h249 := T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h5 h40) h44) h60) h62) h55) h71) h43) h173) h171) h200) h199) h189) h198) h197) h217) h209) h216) h215) h213) h231) h247) h245) h248
  have h250 := C h249 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h244 h239) h222) h238) h211) h208) h204) h196) h192) h188) h183) h178) h167) h157) h148) h42) h66) h56) h53) h50) h39) h13) h6)
  have h251 := h v234 y x
  have h252 := R v235
  have h253 := C h252 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h5 h40) h44) h60) h62) h55) h71) h43) h173) h171) h200) h199) h189) h198) h197) h217) h209) h216) h215) h213) h231) h247) h245) h251) h250)
  have h254 := C (T (T (T h240 h251) h250) h253) h14
  have h255 := C h241 h254
  have h256 := T h255 h237
  have h257 := C h256 h14
  have h258 := S h251
  have h259 := C h242 h249
  have h260 := C (T (T (T h247 h245) h248) h259) h14
  have h261 := C h246 h14
  have h262 := C h241 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h5 h40) h44) h60) h62) h55) h71) h43) h173) h171) h200) h199) h189) h198) h197) h217) h209) h216) h215) h228) h227) h261) h260)
  have h263 := C h252 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h262 h258) h232) h230) h224) h214) h211) h208) h204) h196) h192) h188) h183) h178) h167) h157) h148) h42) h66) h56) h53) h50) h39) h13) h6)
  have h264 := C (T (T (T h263 h262) h258) h248) h14
  have h265 := C h249 h264
  have h266 := T (T h248 h236) h265
  have h267 := C h266 h14
  let v268 := M v234 x
  have h269 := h v268 y x
  have h270 := S h269
  have h271 := T (T h255 h237) h240
  have h272 := C h271 h14
  have h273 := T h236 h265
  have h274 := C h273 h14
  have h275 := C (T (T (T (T h243 h240) h251) h250) h253) h14
  have h276 := C h256 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h5 h40) h44) h60) h62) h55) h71) h43) h173) h171) h200) h199) h189) h198) h197) h217) h209) h216) h215) h228) h227) h261) h260) h275) h264)
  have h277 := C (T (T (T (T h263 h262) h258) h248) h259) h14
  have h278 := T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h267 h257) h254) h277) h244) h239) h222) h238) h211) h208) h204) h196) h192) h188) h183) h178) h167) h157) h148) h42) h66) h56) h53) h50) h39) h13) h6
  have h279 := C h266 h278
  have h280 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h279 h276) h255) h237) h240) h232) h230) h224) h214) h228) h227) h261) h260) h275) h264) h274) h272) h9
  have h281 := T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h5 h40) h44) h60) h62) h55) h71) h43) h173) h171) h200) h199) h189) h198) h197) h217) h209) h216) h215) h228) h227) h261) h260) h275) h264) h274) h272
  have h282 := C h271 h281
  have h283 := C h273 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h254 h277) h244) h239) h222) h238) h211) h208) h204) h196) h192) h188) h183) h178) h167) h157) h148) h42) h66) h56) h53) h50) h39) h13) h6)
  have h284 := T (T (T (T h248 h236) h265) h283) h282
  have h285 := C h284 h278
  have h286 := R v268
  have h287 := C h286 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h5 h40) h44) h60) h62) h55) h71) h43) h173) h171) h200) h199) h189) h198) h197) h217) h209) h216) h215) h213) h231) h247) h245) h248) h236) h265) h283) h282) h285) h280)
  have h288 := C h278 (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h267 h257) h254) h277) h244) h239) h222) h238) h213) h231) h247) h245) h248) h236) h265) h283) h282) h285) h280) h287) h14)
  have h289 := C (T (T (T (T h279 h276) h255) h237) h240) h281
  have h290 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h267 h257) h254) h277) h244) h239) h222) h238) h213) h231) h247) h245) h248) h236) h265) h283) h282) h9
  have h291 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (C h286 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h290 h289) h279) h276) h255) h237) h240) h232) h230) h224) h214) h211) h208) h204) h196) h192) h188) h183) h178) h167) h157) h148) h42) h66) h56) h53) h50) h39) h13) h6)) h290) h289) h279) h276) h255) h237) h240) h232) h230) h224) h214) h228) h227) h261) h260) h275) h264) h274) h272) h14
  have h292 := S (h v16 x x)
  have h293 := C h14 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h107 h105) h85) h82) h70) h55) h71) h43) h173) h171) h200) h199) h189) h198) h197) h217) h209) h216) h215) h228) h227) h261) h260) h275) h264) h274) h272)
  have h294 := h x y y
  let v295 := M v17 y
  have h296 := R v295
  have h297 := C (T (C (T (T (T (T (T (T (T (T (T (T (T h293 h292) h107) h105) h85) h82) h70) h53) h50) h39) h13) h6) h296) (S h294)) h158
  let v298 := M v17 v295
  T (T (T (T (T (T (T h294 (C (T (h y x y) (C h14 (T (T h93 h104) h109))) h296)) (h v298 y y)) (C h9 (T (T (T (T (T (T (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (C (R v298) (T (T (T (T (T (T (T (T (T (T (T (T h297 h293) h292) h107) h105) h85) h82) h70) h53) h50) h39) h13) h6)) h297) h293) h292) h107) h105) h85) h82) h70) h55) h71) h43) h173) h171) h200) h199) h189) h198) h197) h217) h209) h216) h215) h228) h227) h261) h260) h275) h264) h274) h272) h269) (C h281 h291)) h9) (C (T h288 h270) (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h5 h40) h44) h60) h62) h55) h71) h43) h173) h171) h200) h199) h189) h198) h197) h217) h209) h216) h215) h228) h227) h261) h260) h275) h264) h274) h272) (C h284 h14)) (C (T (T h285 h280) h287) h14)) h291))) h288) h270) h267) h257) h254))) h237) h233) h13) h6

