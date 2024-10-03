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
theorem Equation1131_implies_Equation1117 (G: Type _) [Magma G] (h: Equation1131 G) : Equation1117 G := fun x y z =>
  let v0 := M x z
  let v1 := M y v0
  let v2 := M v1 z
  let v3 := M y v2
  have h4 := h v3 v1 v3
  let v5 := M v3 v3
  have h6 := R v1
  have h7 := R v3
  have h8 := h v5 v3 y
  have h9 := S h8
  have h10 := R y
  have h11 := h v2 v3 v3
  have h12 := S h11
  have h13 := C h10 (C (C h10 h12) h7)
  let v14 := M (M v3 (M v3 v2)) v3
  have h15 := h v14 y v3
  have h16 := h v14 x v3
  have h17 := S h16
  have h18 := R x
  have h19 := C h18 h11
  have h20 := h v2 v3 v2
  have h21 := C h18 (C (T (C h18 (S h20)) h19) h7)
  let v22 := M v2 v2
  have h23 := h (M (M v3 v22) v2) x v3
  have h24 := R v2
  have h25 := h v22 v2 v1
  have h26 := h z v2 v0
  have h27 := S h26
  have h28 := h (M (M v2 (M v0 z)) v0) x v2
  have h29 := S h28
  have h30 := h x y v1
  have h31 := S h30
  have h32 := h z y x
  have h33 := C h32 h6
  have h34 := T (C h10 h33) h31
  have h35 := R z
  have h36 := S h32
  have h37 := C h36 h6
  have h38 := T h30 (C h10 h37)
  have h39 := C h38 h35
  have h40 := C h18 (C (T h39 (C h34 h26)) h24)
  have h41 := h (M x (M v0 v2)) v1 v2
  have h42 := C h34 h35
  have h43 := C h18 (C (T (C h38 h27) h42) h24)
  have h44 := C (C h7 (T (C h24 (T h33 (C (T (T h36 h26) (C h24 (T (T (T h28 h43) h41) (C h6 (C (C h6 (T (C h24 (T h40 h29)) h27)) h24))))) h6))) (S h25))) h24
  have h45 := C h7 (T (T (T (T (T h44 h23) h21) h17) h15) h13)
  have h46 := C (C h7 (T h25 (C h24 (T (C (T (T (C h24 (T (T (T (C h6 (C (C h6 (T h26 (C h24 (T h28 h43)))) h24)) (S h41)) h40) h29)) h27) h32) h6) h37)))) h24
  have h47 := S h23
  have h48 := C h18 h12
  have h49 := C h18 (C (T h48 (C h18 h20)) h7)
  have h50 := S h15
  have h51 := C h10 (C (C h10 h11) h7)
  have h52 := h (M y v5) y v3
  let v53 := M z v1
  have h54 := h v53 v3 v2
  have h55 := C (T (C h7 (T (T (T (T (T (T (T (C h10 (C (T h30 (C h10 (T (T h37 h54) h45))) h7)) (S h52)) h51) h50) h16) h49) h47) h46)) h45) h10
  have h56 := C h7 h55
  let v57 := M x v3
  have h58 := h v57 v3 y
  have h59 := S h54
  have h60 := C h7 (T (T (T (T (T h51 h50) h16) h49) h47) h46)
  have h61 := C (T h60 (C h7 (T (T (T (T (T (T (T h44 h23) h21) h17) h15) h13) h52) (C h10 (C (T (C h10 (T (T h60 h59) h33)) h31) h7))))) h10
  have h62 := C h7 h61
  have h63 := T (T h8 h62) (S h58)
  have h64 := C h24 h63
  have h65 := C h7 h64
  have h66 := C h65 h24
  have h67 := h (M v53 y) x z
  have h68 := h v0 z y
  have h69 := h v0 z v3
  have h70 := S h69
  let v71 := M (M z (M v3 v0)) v3
  have h72 := h v71 x z
  have h73 := h v71 y z
  have h74 := h v1 y z
  have h75 := h v3 v3 v2
  have h76 := S h75
  have h77 := h (M (M v3 (M v2 v3)) v2) x v3
  have h78 := h v3 v3 v3
  have h79 := C h18 (S h78)
  have h80 := C h18 h78
  have h81 := h v3 v3 x
  have h82 := h (M (M v3 v57) x) x v3
  have h83 := h v5 x y
  have h84 := h v2 v3 y
  have h85 := h (M v5 y) x v3
  have h86 := T (T h58 h56) h9
  have h87 := h (M v57 y) x x
  have h88 := h v2 x y
  have h89 := h v2 x v3
  have h90 := C h18 (S h89)
  have h91 := C h18 h89
  have h92 := h v2 x v1
  have h93 := S h92
  have h94 := h (M (M x (M v1 v2)) v1) x x
  have h95 := T h92 (C h18 (T (T (T (T (T (T (T (T (T h94 (C h18 (C (T (C h18 h93) h91) h18))) (C h18 (C (T h90 (C h18 h88)) h18))) (S h87)) (C h86 h10)) h85) (C h18 (C (T (C h18 (S h84)) h19) h7))) h17) h15) h13))
  have h96 := C h95 h10
  have h97 := C h7 (T (T (T (T (C (T (C h7 (T (C h18 h96) (S h83))) (C h7 h63)) h18) h82) (C h18 (C (T (C h18 (S h81)) h80) h7))) (C h18 (C (T h79 (C h18 h75)) h7))) (S h77))
  let v98 := M v2 y
  have h99 := h v98 v3 x
  have h100 := h y v3 v3
  have h101 := S h100
  have h102 := C h24 (T (T (C (T (T (T (C h24 h101) h99) h97) h76) (T (T (T (T (T (T (C h10 (C (T h74 (C h10 (T h42 h69))) h35)) (S h73)) h72) (C h18 (C (T (C h18 h70) (C h18 h68)) h35))) (S h67)) (C (T h54 h45) h10)) h61)) h56) h9)
  let v103 := M v3 y
  let v104 := M (M v3 v103) v3
  have h105 := h v104 v2 v3
  have h106 := h v104 x v3
  have h107 := S h106
  have h108 := C h18 h100
  have h109 := h y v3 v2
  have h110 := S h109
  have h111 := C h18 (C (T (C h18 h110) h108) h7)
  let v112 := M (M v3 v98) v2
  have h113 := h v112 x v3
  have h114 := T (T (T (T h113 h111) h107) h105) h102
  have h115 := C h7 h114
  have h116 := T h109 h115
  have h117 := C h116 h24
  have h118 := T (C h18 (T (T (T (T (T (T (T (T (T h51 h50) h16) (C h18 (C (T h48 (C h18 h84)) h7))) (S h85)) (C h63 h10)) h87) (C h18 (C (T (C h18 (S h88)) h91) h18))) (C h18 (C (T h90 (C h18 h92)) h18))) (S h94))) h93
  have h119 := C h118 h10
  have h120 := S h113
  have h121 := C h18 h101
  have h122 := C h18 (C (T h121 (C h18 h109)) h7)
  have h123 := S h105
  have h124 := S h74
  have h125 := S h99
  have h126 := C h7 (T (T (T (T h77 (C h18 (C (T (C h18 h76) h80) h7))) (C h18 (C (T h79 (C h18 h81)) h7))) (S h82)) (C (T (C h7 h86) (C h7 (T h83 (C h18 h119)))) h18))
  have h127 := C h24 (T (T h8 h62) (C (T (T (T h75 h126) h125) (C h24 h100)) (T (T (T (T (T (T h55 (C (T h60 h59) h10)) h67) (C h18 (C (T (C h18 (S h68)) (C h18 h69)) h35))) (S h72)) h73) (C h10 (C (T (C h10 (T h70 h39)) h124) h35)))))
  have h128 := T (T (T (T h127 h123) h106) h122) h120
  have h129 := C h7 h128
  have h130 := T h129 h110
  have h131 := C h95 h130
  have h132 := C h24 h86
  have h133 := C h7 h132
  have h134 := C h24 h133
  have h135 := h y x z
  have h136 := S h135
  have h137 := h (M (M x (M z y)) z) x x
  have h138 := h y x v1
  have h139 := C h18 (S h138)
  have h140 := C h18 h138
  have h141 := h y x v0
  let v142 := M v0 y
  let v143 := M x v142
  have h144 := h (M v143 v0) x x
  have h145 := R v0
  have h146 := h v143 v1 v2
  have h147 := S h146
  have h148 := h z y v1
  have h149 := C h18 (C (T (C h38 (S h148)) h42) h10)
  have h150 := h (M v3 v1) x y
  have h151 := h y v1 v3
  have h152 := S h151
  have h153 := C (T (T (T (C h24 h152) h99) h97) h76) h6
  have h154 := C h24 (T (T h153 h150) h149)
  have h155 := h (M (M v1 v103) v3) v2 v1
  have h156 := C h6 (T h155 h154)
  have h157 := C h6 (T (T h117 h66) (C (T (T (T (T h133 h129) h110) h151) h156) h24))
  have h158 := h (M v1 v3) v3 y
  have h159 := S h158
  have h160 := h v0 v3 v0
  have h161 := S h160
  have h162 := h (M (M v3 (M v0 v0)) v0) y v3
  have h163 := C h7 (C (T h160 (C h7 (T h162 (C h10 (C (T (C h10 (T h161 h39)) h124) h7))))) h10)
  have h164 := h (M (M v3 v142) v0) x v3
  have h165 := h y v3 v0
  have h166 := C h18 (T (T (T (T (T (T (T (T (T (T h132 h127) h123) h106) (C h18 (C (T h121 (C h18 h165)) h7))) (S h164)) (C (T (T (T h163 h159) h157) h147) h145)) h144) (C h18 (C (T (C h18 (S h141)) h140) h18))) (C h18 (C (T h139 (C h18 h135)) h18))) (S h137))
  have h167 := C h18 h64
  have h168 := C h18 h114
  have h169 := C h24 (T (T (T (T (T (T h168 h167) h166) h136) h109) h115) h65)
  have h170 := C h18 h128
  have h171 := C h18 h132
  have h172 := C h7 (C (T (C h7 (T (C h10 (C (T h74 (C h10 (T h42 h160))) h7)) (S h162))) h161) h10)
  have h173 := C h130 h24
  have h174 := C h133 h24
  have h175 := C (T (T (T h75 h126) h125) (C h24 h151)) h6
  have h176 := S h150
  have h177 := C h18 (C (T h39 (C h34 h148)) h10)
  have h178 := C h24 (T (T h177 h176) h175)
  have h179 := C (T (T (T (T (C h6 (T h178 (S h155))) h152) h109) h115) h65) h24
  have h180 := C h6 (T (T h179 h174) h173)
  have h181 := C h18 (T (T (T (T (T (T (T (T (T (T h137 (C h18 (C (T (C h18 h136) h140) h18))) (C h18 (C (T h139 (C h18 h141)) h18))) (S h144)) (C (T (T (T h146 h180) h158) h172) h145)) h164) (C h18 (C (T (C h18 (S h165)) h108) h7))) h107) h105) h102) h64)
  have h182 := h v112 v2 x
  have h183 := C h24 (T (T (T (T (T (T h133 h129) h110) h135) h181) h171) h170)
  have h184 := C h24 h65
  have h185 := C h118 h116
  have h186 := C h7 (T (T (T (T (T (T (T (C h24 (C (T (T (T (T (T (T h75 h126) h125) h96) h185) h184) h183) h18)) (S h182)) h113) h111) h107) h105) h102) h64)
  let v187 := M v3 x
  have h188 := h x v1 v3
  let v189 := M (M v1 v187) v3
  have h190 := h x v1 x
  T (T h190 (C h6 (T (T (T (T (T (h (M (M v1 (M x x)) x) x v1) (C h18 (C (T (C h18 (S h190)) (C h18 h188)) h6))) (S (h v189 x v1))) (h v189 v3 v1)) (C h7 (C (T (T (T (T (T (T (T (T (C h7 (S h188)) (h v187 v3 v2)) (C (T (T (T (T (T (T (T h75 h126) h125) h96) h185) h184) h183) (C h24 (T (T (T (T (T (T (T h168 h167) h166) h136) h109) h115) h65) (C h7 (T (T (T (T (T (T (T h132 h127) h123) h106) h122) h120) h182) (C h24 (C (T (T (T (T (T (T h169 h134) h131) h119) h99) h97) h76) h18))))))) (T (T (T (T (C (T (T (T (T (T (T h186 h133) h129) h110) h151) h156) (C h6 (T h178 (C h24 (T (T (T (T (T (T h153 h150) h149) h146) h180) h158) h172))))) h24) (C (C h6 (T (C h24 (T (T (T (T (T (T h163 h159) h157) h147) h177) h176) h175)) h154)) h24)) h179) h174) h173))) (C (T (T (T (T (T (T (T (C h24 (T (T (T (T (T (T (T h186 h133) h129) h110) h135) h181) h171) h170)) h169) h134) h131) h119) h99) h97) h76) (T h117 h66))) (S (h v57 v3 v2))) h58) h56) h9) (C h7 h4)) h6))) (S (h (M (M v1 v5) v3) v3 v1))))) (S h4)

