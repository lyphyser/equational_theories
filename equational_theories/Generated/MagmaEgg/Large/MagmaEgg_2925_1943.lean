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
theorem Equation2925_implies_Equation1943 (G: Type _) [Magma G] (h: Equation2925 G) : Equation1943 G := fun x y z =>
  let v0 := M x z
  have h1 := R v0
  let v2 := M y z
  have h3 := R v2
  have h4 := h y x v2
  have h5 := S h4
  let v6 := M y v2
  let v7 := M v6 v0
  have h8 := h (M (M x v6) x) v7 y
  have h9 := R y
  have h10 := R v7
  have h11 := R x
  have h12 := h v6 y y
  let v13 := M v6 y
  have h14 := h (M (M y v13) y) x y
  have h15 := R v13
  have h16 := h y y z
  have h17 := h z z y
  have h18 := S h17
  let v19 := M z y
  let v20 := M (M z v19) z
  have h21 := h v20 v13 y
  have h22 := h v20 x y
  have h23 := S h22
  have h24 := C (C h11 h17) h11
  have h25 := h z v0 y
  have h26 := S h25
  have h27 := C (T (C (C h11 h26) h11) h24) h9
  have h28 := h (M (M v0 v19) v0) x y
  have h29 := T (T (T (T (T (T h28 h27) h23) h21) (C (C (T (C h15 h18) (S h16)) h15) h9)) h14) (C (C (C h11 (S h12)) h11) h9)
  have h30 := S h28
  have h31 := C (C h11 h18) h11
  have h32 := C (T h31 (C (C h11 h25) h11)) h9
  have h33 := h z v2 y
  have h34 := C (T (C (C h11 (S h33)) h11) h24) h9
  have h35 := h (M (M v2 v19) v2) x y
  have h36 := S h35
  have h37 := C (T h31 (C (C h11 h33) h11)) h9
  have h38 := h z y y
  have h39 := C (T (C (C h11 (S h38)) h11) h24) h9
  let v40 := M y v19
  have h41 := h (M v40 y) x y
  have h42 := h v40 v7 y
  have h43 := C (T (T h42 (C (T (T (C (C h10 (T (T (T h41 h39) h37) h36)) h10) (C (C h10 (T (T (T h35 h34) h32) h30)) h10)) (C (C h10 h29) h10)) h9)) (S h8)) h3
  have h44 := S h42
  have h45 := S h41
  have h46 := C (T h31 (C (C h11 h38) h11)) h9
  have h47 := h v20 y y
  have h48 := C (C (C h10 (T (T (T (T (C (C (C h9 h17) h9) h9) (S h47)) h22) h46) h45)) h10) h9
  have h49 := h (M v2 y) v7 y
  have h50 := T (T (T (T (T (T (C (C (C h11 h12) h11) h9) (S h14)) (C (C (T h16 (C h15 h17)) h15) h9)) (S h21)) h22) h32) h30
  have h51 := C h50 h9
  have h52 := C h9 (T h51 h26)
  have h53 := C h52 h9
  have h54 := T h43 h5
  have h55 := C h29 h9
  have h56 := C h9 (T h25 h55)
  have h57 := C h56 h54
  have h58 := C (T (T (T (T h57 h53) h49) h48) h44) h3
  have h59 := C (T (T h58 h43) h5) h3
  have h60 := h v40 v2 v2
  have h61 := C (T (T h8 (C (T (T (C (C h10 h50) h10) (C (C h10 (T (T (T h28 h27) h37) h36)) h10)) (C (C h10 (T (T (T h35 h34) h46) h45)) h10)) h9)) h44) h3
  have h62 := T h4 h61
  have h63 := C h52 h62
  have h64 := C h56 h9
  have h65 := h y v2 v7
  have h66 := S h65
  have h67 := C h3 h66
  have h68 := C (T (T h67 h64) h63) h3
  let v69 := M y v7
  let v70 := M (M v2 v69) v2
  have h71 := h (M (M v2 (M v70 v7)) v2) y v6
  have h72 := S h71
  have h73 := R v6
  have h74 := C h3 h65
  have h75 := h y v2 v6
  have h76 := S h75
  let v77 := M (M v2 (M y v6)) v2
  have h78 := h v77 v2 v6
  have h79 := h v77 v6 v6
  have h80 := h v2 z v6
  have h81 := S h80
  have h82 := C (C h9 h81) h9
  let v83 := M (M z (M v2 v6)) z
  have h84 := h v83 y v6
  have h85 := C (T h82 (C (C h9 (T (T (T (T h80 (C (T h84 (C (T h82 (C h73 h75)) h73)) h73)) (S h79)) h78) (C (C (T (C h3 h76) h74) h3) h73))) h9)) h73
  have h86 := h v83 x v7
  have h87 := S h86
  have h88 := S h84
  have h89 := C (C h9 h80) h9
  have h90 := C (T (C (T (C h73 h66) h89) h73) h88) h10
  have h91 := h v70 v6 v7
  have h92 := h v70 v7 v7
  have h93 := S h92
  have h94 := C h10 h65
  have h95 := C (T (C h10 h54) h94) h10
  have h96 := S h49
  have h97 := C (C (C h10 (T (T (T (T h41 h39) h23) h47) (C (C (C h9 h18) h9) h9))) h10) h9
  have h98 := S h60
  have h99 := C (T (T (T (T h42 h97) h96) h64) h63) h3
  have h100 := C (T (T h4 h61) h99) h3
  have h101 := C (T (T (T (T (T (T h100 h98) h42) h97) h96) h64) h63) h3
  have h102 := h (M v6 v2) v7 v7
  have h103 := S h102
  have h104 := C (T (T (T (T (T (T h57 h53) h49) h48) h44) h60) h59) h3
  have h105 := C (T (T (T h4 h61) h99) h104) h10
  let v106 := M v7 v69
  have h107 := h v106 x v7
  have h108 := h (M v106 v7) x v7
  have h109 := h y v7 v7
  have h110 := C h11 h66
  have h111 := h v70 x v7
  have h112 := S h91
  have h113 := C (T h84 (C (T h82 (C h73 h65)) h73)) h10
  have h114 := C (T (C (C h9 (T (T (T (T (C (C (T h67 (C h3 h75)) h3) h73) (S h78)) h79) (C (T (C (T (C h73 h76) h89) h73) h88) h73)) h81)) h9) h89) h73
  have h115 := C (T (T h57 h53) h74) h3
  have h116 := C (T h105 (C (T (T (T (T (T (T (T (T h101 h115) h71) h114) h88) h86) (C (C (C h11 (T (T (T (T h113 h112) h111) (C (C (T h110 (C h11 h109)) h11) h10)) (S h108))) h11) h10)) (S h107)) (C h10 h105)) h10)) h10
  have h117 := C (C h10 (T (T (T h116 h103) h101) h58)) h10
  have h118 := C (T h117 h95) h10
  have h119 := h v69 v7 v7
  have h120 := C (T (T (T h101 h58) h43) h5) h10
  have h121 := C (C h11 (T (T (T (T (T h120 h119) h118) h93) h91) h90)) h11
  have h122 := C (C h11 h105) h11
  have h123 := h (M (M x v69) x) x v7
  have h124 := S h123
  have h125 := h y x v7
  have h126 := C (C (T h110 (C h11 h125)) h11) h10
  have h127 := C h11 h65
  have h128 := h y y v7
  have h129 := C (C (T (C h11 (S h128)) h127) h11) h10
  let v130 := M y v69
  have h131 := h (M v130 y) x v7
  have h132 := C h9 h120
  have h133 := C h132 h9
  have h134 := C h9 h105
  have h135 := S h119
  have h136 := S h111
  have h137 := C (T (C (T (T (T (T (T (T (T (T (C h10 h120) h107) (C (C (C h11 (T (T (T (T h108 (C (C (T (C h11 (S h109)) h127) h11) h10)) h136) h91) h90)) h11) h10)) h87) h84) h85) h72) h68) h104) h10) h120) h10
  have h138 := C (C h10 (T (T (T h99 h104) h102) h137)) h10
  have h139 := C h10 h66
  have h140 := C (T h139 (C h10 h62)) h10
  have h141 := C (T h140 h138) h10
  have h142 := h v130 x y
  have h143 := S h142
  have h144 := S h131
  have h145 := C (C (T h110 (C h11 h128)) h11) h10
  have h146 := C (T (T (T (T (T (T (T (T h119 h118) h93) h111) h126) h124) h122) h121) (C (C h11 (T (T (T (T h113 h112) h111) h145) h144)) h11)) h9
  have h147 := h (M v69 y) x x
  have h148 := h v7 v2 x
  have h149 := S h148
  let v150 := M (M v2 (M v7 x)) v2
  have h151 := h v150 y x
  have h152 := h v150 v2 x
  have h153 := S h152
  have h154 := C (C (C h3 h148) h3) h11
  let v155 := M (M v2 v7) v2
  have h156 := h v155 x x
  have h157 := h v7 v0 y
  have h158 := C (C h3 (S h157)) h3
  have h159 := C (C h3 h157) h3
  have h160 := S h156
  have h161 := C (C (C h3 h149) h3) h11
  have h162 := h v150 x x
  let v163 := M x v7
  have h164 := h (M v163 x) x x
  have h165 := h v7 v2 y
  have h166 := S h165
  have h167 := h (M (M v2 (M v7 y)) v2) x y
  have h168 := T (T (T (T (T (T (T (T (T h167 (C (T (T (T (T (C (C h11 h166) h11) h164) (C (C (C h11 (T (T (T (C (C (C h11 h148) h11) h11) (S h162)) h152) h161)) h11) h11)) h160) h159) h9)) (C (T (T (T (T (T (T h158 h156) (C (C (C h11 (T (T (T h154 h153) h151) (C (C (C h9 h149) h9) h11))) h11) h11)) (S h147)) h146) h143) h134) h9)) h133) h131) h129) h136) h92) h141) h135
  have h169 := C h9 h168
  have h170 := C (C (C h11 (T (T (T (C (C (C h9 h148) h9) h11) (S h151)) h152) h161)) h11) h11
  have h171 := C (C (T (C h11 (S h125)) h127) h11) h10
  have h172 := C (C h11 h120) h11
  have h173 := C (C h11 (T (T (T (T (T h113 h112) h92) h141) h135) h105)) h11
  have h174 := C (T (T (T (T (T (T (T (T (C (C h11 (T (T (T (T h131 h129) h136) h91) h90)) h11) h173) h172) h123) h171) h136) h92) h141) h135) h9
  have h175 := C h134 h9
  have h176 := T (T (T (T (T (T (T (T (T h119 h118) h93) h111) h145) h144) h175) (C (T (T (T (T (T (T h132 h142) h174) h147) h170) h160) h159) h9)) (C (T (T (T (T h158 h156) (C (C (C h11 (T (T (T h154 h153) h162) (C (C (C h11 h149) h11) h11))) h11) h11)) (S h164)) (C (C h11 h165) h11)) h9)) (S h167)
  have h177 := C h9 h176
  have h178 := C h168 h9
  have h179 := C (T (T (T (T (T (T (T (T (C (T (T (T (T h165 h178) h146) h143) h177) (T (T (T (T (T h116 h103) h101) h58) h43) h5)) (C (T h169 h134) h9)) h133) h131) h129) h126) h124) h122) h121) h10
  have h180 := C h94 h10
  have h181 := C h139 h10
  have h182 := C (T (T (T (T (T (T (T (T h173 h172) h123) h171) h145) h144) h175) (C (T h132 h177) h9)) (C (T (T (T (T h169 h142) h174) (C h176 h9)) h166) (T (T (T (T (T h4 h61) h99) h104) h102) h137))) h10
  have h183 := h y z x
  have h184 := S h183
  let v185 := M y x
  let v186 := M (M z v185) z
  have h187 := h v186 v7 x
  have h188 := S h187
  have h189 := C (T (T (T (T (T (T (T (T (T (T (T h4 h61) h99) h115) h71) h114) h88) h86) h182) h117) h95) (C (T h139 (C h10 h183)) h10)) h11
  have h190 := C (T h189 h188) h11
  have h191 := C (T (T (T (T (T (T (T (T (T (T (T (C (T (C h10 h184) h94) h10) h140) h138) h179) h87) h84) h85) h72) h68) h58) h43) h5) h11
  have h192 := C (T h187 h191) h11
  have h193 := h z z v0
  have h194 := S h193
  let v195 := M (M z (M z v0)) z
  have h196 := h v195 v7 v7
  have h197 := h v195 x v0
  have h198 := h x x v7
  have h199 := S h198
  have h200 := C h1 h199
  have h201 := C h1 h198
  have h202 := h x z v7
  have h203 := S h202
  let v204 := M (M z v163) z
  have h205 := h v204 v0 v7
  have h206 := h v204 x v7
  let v207 := M (M x v163) x
  have h208 := h v207 x v7
  have h209 := h v207 y v7
  have h210 := h v186 x x
  have h211 := S h210
  have h212 := C (T h110 (C h11 h183)) h11
  have h213 := h y v7 x
  have h214 := h (M (M v7 v185) v7) x x
  have h215 := h v186 v2 x
  have h216 := S h215
  have h217 := C (C (T h67 (C h3 h183)) h3) h11
  have h218 := C (C (T (C h3 h184) h74) h3) h11
  have h219 := h y y x
  let v220 := M y v185
  have h221 := h (M v220 y) x x
  have h222 := h v220 v7 y
  have h223 := h v220 v7 v7
  have h224 := C (T (T (T (T (T (T (T (T (T (C (T (C h9 (T (T (T (C (T (T h223 (C (C (C h10 (T (T (T (T (T (T (C (T h222 (C (T (T (T (T (T (T (T (C (C h10 (T (T (T (T h221 (C (T (C (T (C h11 (S h219)) h127) h11) h212) h11)) h211) h215) h218)) h10) (C (C h10 (T (T (T h217 h216) h187) h191)) h10)) h214) (C (T (C (T (C h11 (S h213)) h127) h11) h212) h11)) h211) h187) h191) (C h9 h198)) h9)) h10) (S h209)) h208) (C (C (T (C h11 h199) (C h11 h202)) h11) h10)) (S h206)) h205) (C (T (T (C (T (C h1 h203) h201) h1) (C (T h200 (C (C h11 h193) h11)) h1)) (S h197)) h10))) h10) h10)) (S h196)) h1) h194) h25) h55)) h52) (T h183 h192)) (C h3 (T (T (T (T (T (T (T (T (T (T (T (T (T h190 h184) h4) h61) h99) h115) h71) h114) h88) h86) h182) h117) h95) h181))) (C h3 (T (T (T (T (T (T (T (T (T h180 h140) h138) h179) h87) h84) h85) h72) h68) h58))) h57) h53) h49) h48) h44) h60) h59) h1
  have h225 := h v220 y v0
  have h226 := S h223
  have h227 := C (T (C h11 h184) h127) h11
  have h228 := C (T (C (T (T (T (T (T (T (T (C h9 h199) h189) h188) h210) (C (T h227 (C (T h110 (C h11 h213)) h11)) h11)) (S h214)) (C (C h10 (T (T (T h189 h188) h215) h218)) h10)) (C (C h10 (T (T (T (T h217 h216) h210) (C (T h227 (C (T h110 (C h11 h219)) h11)) h11)) (S h221))) h10)) h9) (S h222)) h10
  have h229 := S h208
  have h230 := C (C (T (C h11 h203) (C h11 h198)) h11) h10
  let v231 := M v7 v7
  let v232 := M v7 v231
  have h233 := h v7 z v7
  let v234 := M (M z v231) z
  T (T (T (T h202 (C (T (T (T (T (T h206 h230) h229) h209) h228) (C (T (T (T (T (T (T (T (T (T (T h225 h224) h165) h178) h147) h170) h160) (h v155 x v7)) (C (C (C h11 (T (T (T (T (C (C (C h3 h233) h3) h10) (S (h v234 v2 v7))) (h v234 x v7)) (C (T (C (C h11 (S h233)) h11) (C (C h11 (h v7 v7 v7)) h11)) h10)) (S (h (M v232 v7) x v7)))) h11) h10)) (S (h v232 x v7))) (C h10 (C (T (C (T (T (T (T (T (T (T (T (T h100 h98) h42) h97) h96) h64) h63) (C h3 (T (T (T (T (T (T (T (T (T h99 h115) h71) h114) h88) h86) h182) h117) h95) h181))) (C h3 (T (T (T (T (T (T (T (T (T (T (T (T (T h180 h140) h138) h179) h87) h84) h85) h72) h68) h58) h43) h5) h183) h192))) (C (T h56 (C h9 (T (T (T h51 h26) h193) (C (T (T h196 (C (C (C h10 (T (T (T (T (T (T (C (T (T h197 (C (T (C (C h11 h194) h11) h201) h1)) (C (T h200 (C h1 h202)) h1)) h10) (S h205)) h206) h230) h229) h209) h228)) h10) h10)) h226) h1)))) (T h190 h184))) h1) (S h225)) h10))) h10)) h10)) h226) h225) h224

