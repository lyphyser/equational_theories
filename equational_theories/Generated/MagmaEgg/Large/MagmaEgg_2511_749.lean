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
theorem Equation2511_implies_Equation749 (G: Type _) [Magma G] (h: Equation2511 G) : Equation749 G := fun x y z =>
  let v0 := M x z
  let v1 := M v0 y
  let v2 := M z v1
  have h3 := R v2
  let v4 := M y v2
  have h5 := h y v4 v0
  have h6 := S h5
  have h7 := R v0
  let v8 := M y v4
  let v9 := M v4 (M v8 v0)
  have h10 := h v9 x v2
  have h11 := S h10
  have h12 := R x
  have h13 := h v9 v0 x
  have h14 := S h13
  have h15 := C h5 h12
  have h16 := h y v2 v0
  have h17 := C (C h7 (T (C (S h16) h12) h15)) h12
  have h18 := h (M v2 (M v4 v0)) v0 x
  have h19 := h v2 v0 v0
  have h20 := S h19
  let v21 := M v2 v0
  have h22 := h (M v0 (M v21 v0)) v0 y
  have h23 := R y
  have h24 := h x z y
  have h25 := C (C h23 (T (C (T (C (C h7 (T h24 (C h19 h23))) h23) (S h22)) h7) h20)) h7
  have h26 := h (M v0 x) y v0
  have h27 := h v0 z v2
  have h28 := S h27
  let v29 := M v0 z
  have h30 := h (M z (M v29 v2)) v2 x
  have h31 := C (T h30 (C (T (T (T (C h3 (T (T (C h28 h12) h26) h25)) h18) h17) h14) h12)) h3
  have h32 := C (C h12 (T h27 h31)) h3
  have h33 := T (C (T h32 h11) h7) h6
  have h34 := C h33 h3
  have h35 := S h26
  have h36 := S h24
  have h37 := C (C h23 (T h19 (C (T h22 (C (C h7 (T (C h20 h23) h36)) h23)) h7))) h7
  have h38 := S h18
  have h39 := C h6 h12
  have h40 := C (C h7 (T h39 (C h16 h12))) h12
  have h41 := C (T (C (T (T (T h13 h40) h38) (C h3 (T (T h37 h35) (C h27 h12)))) h12) (S h30)) h3
  have h42 := T h41 h28
  have h43 := C (C h12 h42) h3
  have h44 := h y v0 v0
  have h45 := h (M v0 (M (M y v0) v0)) v0 x
  have h46 := R z
  have h47 := C h36 h46
  have h48 := C h24 h46
  have h49 := h v0 z v0
  have h50 := S h49
  have h51 := h (M z (M v29 v0)) v0 y
  have h52 := h (M v0 v1) y v0
  have h53 := R v1
  have h54 := h v0 y v2
  have h55 := S h54
  let v56 := M v1 v2
  have h57 := h (M y v56) v1 y
  have h58 := S h57
  have h59 := h v56 v1 v1
  have h60 := S h59
  have h61 := h z z v1
  have h62 := S h61
  have h63 := C (C h53 (C h62 h53)) h53
  let v64 := M z (M (M z z) v1)
  have h65 := h v64 v1 v1
  have h66 := h v64 v1 x
  have h67 := S h66
  have h68 := h z y v1
  have h69 := S h68
  have h70 := C (C h53 (T (C h69 h12) (C h61 h12))) h12
  let v71 := M z y
  have h72 := h (M y (M v71 v1)) v1 x
  have h73 := C (T (T (T (T h72 h70) h67) h65) h63) h53
  have h74 := h z y z
  have h75 := S h74
  let v76 := M y (M v71 z)
  have h77 := h v76 v2 v1
  have h78 := S h77
  have h79 := h v76 z x
  have h80 := S h79
  have h81 := h z v1 z
  have h82 := C (C h46 (T (C (S h81) h12) (C h74 h12))) h12
  have h83 := h (M v1 (M v2 z)) z x
  have h84 := h v2 v2 x
  have h85 := S h84
  let v86 := M v2 v2
  have h87 := h v86 v1 v2
  have h88 := h z v1 v2
  have h89 := S h88
  have h90 := h (M v1 v86) v2 v1
  have h91 := C (C h3 (C (T (C (C h53 (T h88 (C (T h90 (C (C h3 (C h89 h53)) h53)) h3))) h3) (S h87)) h12)) h12
  have h92 := h (M v1 z) v2 x
  have h93 := h v76 z v1
  have h94 := h (M z v2) v1 z
  have h95 := S h72
  have h96 := C (C h53 (T (C h62 h12) (C h68 h12))) h12
  have h97 := S h65
  have h98 := C (C h53 (C h61 h53)) h53
  have h99 := C (T (T (T (T h98 h97) h66) h96) h95) h53
  have h100 := T h99 h69
  have h101 := C h53 (T (T (C h100 h3) h94) (C (T (T (T (C h53 (T (C (T (C (C h46 (C h74 h53)) h53) (S h93)) h46) h75)) h92) h91) h85) h46))
  have h102 := C (T (T (T h101 h83) h82) h80) h3
  let v103 := M v56 v1
  have h104 := h v103 v1 v2
  have h105 := C (T (T (T (T (T (T h72 h70) h67) h65) h63) h104) h102) h53
  have h106 := C (C h3 (T h68 h105)) h53
  have h107 := C (T h106 h78) h46
  have h108 := T (T (T h107 h75) h68) h73
  have h109 := S h104
  have h110 := T h68 h73
  have h111 := S h92
  have h112 := C (C h3 (C (T h87 (C (C h53 (T (C (T (C (C h3 (C h88 h53)) h53) (S h90)) h3) h89)) h3)) h12)) h12
  have h113 := C h53 (T (T (C (T (T (T h84 h112) h111) (C h53 (T h74 (C (T h93 (C (C h46 (C h75 h53)) h53)) h46)))) h46) (S h94)) (C h110 h3))
  have h114 := S h83
  have h115 := C (C h46 (T (C h75 h12) (C h81 h12))) h12
  have h116 := C (T (T (T h79 h115) h114) h113) h3
  have h117 := C (T (T (T (T (T (T h116 h109) h98) h97) h66) h96) h95) h53
  have h118 := C (C h3 (T h117 h69)) h53
  have h119 := C (T h77 h118) h46
  have h120 := C (T (T (T (T h84 h112) h111) (C h53 (T h74 h119))) (C h53 h108)) h53
  have h121 := h v2 v0 y
  have h122 := S h121
  have h123 := h (M v0 (M v21 y)) y v1
  have h124 := C h100 h53
  have h125 := C h108 h53
  have h126 := C (T (T (T (T (T h106 h78) h79) h115) h114) h113) h3
  have h127 := C (T h126 h102) h53
  have h128 := C (T (T (T (T (T h101 h83) h82) h80) h77) h118) h3
  have h129 := h v103 v1 v1
  have h130 := C h110 h53
  have h131 := C h53 h130
  have h132 := C (T (T (T (C (T (T h120 h60) h131) h53) (S h129)) h104) h128) h53
  have h133 := T (T (T (T (T h132 h127) h117) h69) h74) h119
  have h134 := C h133 h53
  have h135 := T (T (T h99 h69) h74) h119
  have h136 := C (T (T (T (T (C h53 h135) (C h53 (T h107 h75))) h92) h91) h85) h53
  have h137 := C h53 h124
  have h138 := C (T (T (T h126 h109) h129) (C (T (T h137 h59) h136) h53)) h53
  have h139 := C (T h116 h128) h53
  have h140 := T (T (T (T (T h107 h75) h68) h105) h139) h138
  have h141 := C h140 h53
  have h142 := C h135 h53
  have h143 := C (T (T h131 (C h53 (T h142 h141))) (C h53 (T (T (T (T h134 h125) h124) h121) (C (T h123 (C (C h23 (T (T (C h122 h53) h120) h60)) h53)) h23)))) h23
  have h144 := C (T h143 h58) h3
  have h145 := T h144 h55
  have h146 := C (T (T (C h53 (T (T (T (T (C (T (C (C h23 (T (T h59 h136) (C h121 h53))) h53) (S h123)) h23) h122) h130) h142) h141)) (C h53 (T h134 h125))) h137) h23
  have h147 := C (T h57 h146) h3
  let v148 := M v2 v1
  have h149 := h (M v148 v1) v1 x
  have h150 := h (M z x) y v2
  have h151 := h v2 v0 z
  have h152 := S h151
  let v153 := M v0 (M v21 z)
  have h154 := h v153 z y
  have h155 := h v153 z x
  have h156 := h v2 y z
  have h157 := h (M y (M (M v2 y) z)) z x
  have h158 := C (T h10 h43) h7
  have h159 := T h5 h158
  have h160 := h v56 y v2
  have h161 := h (M v56 y) v2 x
  have h162 := T h54 h147
  have h163 := C h3 (T (T h37 h35) (C h162 h12))
  have h164 := C (T (T (T (T (T h32 h11) h13) h40) h38) h163) h12
  have h165 := C h3 (T (T (C h145 h12) h26) h25)
  have h166 := C (T (T (T (T (T h165 h18) h17) h14) h10) h43) h12
  have h167 := h (M v1 v0) x v1
  have h168 := h v1 x v0
  have h169 := S h168
  have h170 := C (T (T (T (T (T (C h7 (T (T (T (T (T (T (C h169 h7) h167) (C (T (T (C h12 (T (T (T (T (C (T (C (C h53 (T (T (T (T (T (T (T h27 h31) (C (T (C (T (T (T h13 h40) h38) h163) h12) h166) h3)) (C (T (T (T (T h164 (S h161)) h143) h58) (C h23 (T (T h160 (C (T (T (T (T (C h159 h145) (C h33 h48)) h157) (C (C h46 (T (C (S h156) h12) (C h151 h12))) h12)) (S h155)) h3)) (C (T h154 (C (C h46 (T (C h152 h23) h36)) h23)) h3)))) h3)) (S h150)) (C h110 h12)) (C h135 h12)) (C h140 h12))) h12) (S h149)) h53) h132) h127) h117) h69)) h27) h31) h53)) (C (T (T (T h41 h28) h54) h147) h53)) (C h145 h53)) h52) (C (T (C h23 (T (T (C (T (C (C h7 (C h49 h23)) h23) (S h51)) h7) h50) h48)) (C h23 h47)) h7))) h45) (C (C h7 (T (C (S h44) h12) h15)) h12)) h14) h10) h43) h7
  let v171 := M x (M (M v1 x) v0)
  have h172 := h v171 v0 v0
  have h173 := h v171 v0 y
  have h174 := S h173
  have h175 := h v1 v1 v0
  have h176 := S h175
  have h177 := C (C h7 (T (C h176 h23) (C h168 h23))) h23
  let v178 := M v1 (M (M v1 v1) v0)
  have h179 := h v178 v0 y
  have h180 := h v178 z v4
  have h181 := S h180
  have h182 := R v4
  have h183 := S h179
  have h184 := C (C h7 (T (C h169 h23) (C h175 h23))) h23
  have h185 := S h172
  have h186 := T (T (T h144 h55) h27) h31
  have h187 := C (T (T (T (T (T h32 h11) h13) (C (C h7 (T h39 (C h44 h12))) h12)) (S h45)) (C h7 (T (T (T (T (T (T (C (T (C h23 h48) (C h23 (T (T h47 h49) (C (T h51 (C (C h7 (C h50 h23)) h23)) h7)))) h7) (S h52)) (C h162 h53)) (C h186 h53)) (C (T (T h41 h28) (C h12 (T (T (T (T h68 h105) h139) h138) (C (T h149 (C (C h53 (T (T (T (T (T (T (T (C h133 h12) (C h108 h12)) (C h100 h12)) h150) (C (T (T (T (T (C h23 (T (T (C (T (C (C h46 (T h24 (C h151 h23))) h23) (S h154)) h3) (C (T (T (T (T h155 (C (C h46 (T (C h152 h12) (C h156 h12))) h12)) (S h157)) (C h159 h47)) (C h33 h162)) h3)) (S h160))) h57) h146) h161) h166) h3)) (C (T h164 (C (T (T (T h165 h18) h17) h14) h12)) h3)) h41) h28)) h12)) h53)))) h53)) (S h167)) (C h168 h7)))) h7
  have h188 := C h46 (C (T (C h159 h46) (C (T (T (T (T h187 h185) h173) h184) h183) h46)) h182)
  have h189 := h (M z (M (M y z) v4)) v4 x
  have h190 := S h189
  have h191 := h y z v4
  have h192 := h y v1 v4
  have h193 := S h192
  have h194 := C h193 h12
  have h195 := C (C h182 (T h194 (C h191 h12))) h12
  let v196 := M v1 (M (M y v1) v4)
  have h197 := h v196 v4 x
  have h198 := h v196 v4 v2
  have h199 := S h198
  have h200 := C (C h182 (C h192 h3)) h3
  have h201 := C (T (T (T (T (T h200 h199) h197) h195) h190) h188) h182
  have h202 := C (T (T (T (T (T (T h201 h181) h179) h177) h174) h172) h170) h3
  have h203 := C (C h182 (C h193 h3)) h3
  have h204 := S h197
  have h205 := C h192 h12
  have h206 := C (C h182 (T (C (S h191) h12) h205)) h12
  have h207 := C h46 (C (T (C (T (T (T (T h179 h177) h174) h172) h170) h46) (C h33 h46)) h182)
  have h208 := C (T (T (T (T (T h207 h189) h206) h204) h198) h203) h182
  let v209 := M (M v4 v4) v2
  have h210 := h v209 v4 v2
  have h211 := h v2 v1 v4
  have h212 := S h211
  have h213 := h (M v1 (M v148 v4)) v4 y
  have h214 := h (M v4 x) y v4
  have h215 := C (T (T (T (T (T (T (T (C (T (T h214 (C (C h23 (T (C (T (C (C h182 (T h24 (C h211 h23))) h23) (S h213)) h182) h212)) h182)) (C h182 (T (C h159 h3) (C (T (T (T (T (T (T h187 h185) h173) h184) h183) h180) h208) h3)))) h3) (S h210)) h200) h199) h197) h195) h190) h188) h182
  have h216 := T h215 h208
  have h217 := C (T (T (T (T (T (T (T h207 h189) h206) h204) h198) h203) h210) (C (T (T (C h182 (T h202 h34)) (C (C h23 (T h211 (C (T h213 (C (C h182 (T (C h212 h23) h36)) h23)) h182))) h182)) (S h214)) h3)) h182
  have h218 := h v178 x v4
  have h219 := T h201 h181
  have h220 := T (T (T (C h159 h12) (C (T (T (T (T (T (T h187 h185) h173) h184) h183) h180) h217) h12)) (C h216 h12)) (C h219 h12)
  let v221 := M y x
  have h222 := h (M x (M v221 v4)) v4 x
  have h223 := h y x v4
  have h224 := h v209 v4 v0
  have h225 := T h180 h208
  have h226 := C (T (T (T (T (T (T (T (C h12 (C (T (T (T (C h225 h12) (C (T h201 h217) h12)) (C (T (T (T (T (T (T h215 h181) h179) h177) h174) h172) h170) h12)) (C h33 h12)) h182)) h222) (C (C h182 (T (C (S h223) h12) h205)) h12)) h204) h198) h203) h224) (C (C h182 (T (C h219 h7) h176)) h7)) h182
  have h227 := h y v4 v1
  have h228 := S h227
  let v229 := M v4 v1
  have h230 := h x v0 v2
  let v231 := M v0 (M (M x v0) v2)
  have h232 := h x x v2
  T (T (T (T (T h232 (C (T (T (T (T (T (T (T (h (M x (M (M x x) v2)) v2 x) (C (C h3 (T (C (S h232) h12) (C h230 h12))) h12)) (S (h v231 v2 x))) (h v231 v2 v1)) (C (T (T (T (T (T (C h3 (T (T (T (T (C (S h230) h53) (C (T h24 (C h3 (T h227 (C (T (h (M v4 (M v8 v1)) v1 v2) (C (C h53 (C h228 h3)) h3)) h53)))) h53)) (S (h (M v1 v4) v2 v1))) (C (T (T (C h162 h23) (C h186 h23)) (C h42 (T (T (T (T (T (T (T (T h5 h158) h187) h185) h173) h184) h183) h218) h226))) h182)) (S (h v229 v0 v4)))) (h (M v2 v229) v1 x)) (C (C h53 (T (C (S (h y v2 v1)) h12) (C h227 h12))) h12)) (C (C h53 (T (C h228 h12) (C (h y x v1) h12))) h12)) (S (h (M x (M v221 v1)) v1 x))) (C h12 (C h220 h53))) h53)) (S (h v178 x v1))) h218) h226) h3)) (C (T (T (T (C (T (T (T (T (T (T (T (C (C h182 (T h175 (C h225 h7))) h7) (S h224)) h200) h199) h197) (C (C h182 (T h194 (C h223 h12))) h12)) (S h222)) (C h12 (C h220 h182))) h182) (S h218)) h180) h217) h3)) (C h216 h3)) h202) h34

