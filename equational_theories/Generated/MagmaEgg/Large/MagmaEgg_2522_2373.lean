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
theorem Equation2522_implies_Equation2373 (G: Type _) [Magma G] (h: Equation2522 G) : Equation2373 G := fun x y z =>
  have h0 := R y
  let v1 := M x z
  have h2 := R v1
  let v3 := M z v1
  let v4 := M y v3
  let v5 := M v4 y
  have h6 := h z v1 v5
  have h7 := C (S h6) h2
  have h8 := C (C h0 h7) h0
  let v9 := M v1 (M (M z v5) v5)
  have h10 := h v9 y v1
  have h11 := h v9 x v1
  have h12 := S h11
  have h13 := R x
  have h14 := C h6 h2
  have h15 := C h13 h14
  have h16 := h z v1 v3
  have h17 := S h16
  have h18 := C (T (C h13 (C h17 h2)) h15) h13
  let v19 := M (M z v3) v3
  have h20 := h (M v1 v19) x v1
  have h21 := h v3 v4 v4
  have h22 := S h21
  have h23 := R v4
  let v24 := M v3 v4
  have h25 := h (M v4 (M v24 v4)) x v4
  have h26 := h v24 v4 v3
  have h27 := R v3
  have h28 := h y v3 x
  have h29 := S h28
  have h30 := C h29 h27
  let v31 := M (M y x) x
  let v32 := M v3 v31
  have h33 := h v32 v3 v3
  have h34 := h v5 v4 y
  have h35 := S h34
  have h36 := h (M v4 (M (M v5 y) y)) x v4
  have h37 := C (T (T h36 (C (C h13 (T (T (T (C h35 h23) (C (C h23 (T h28 (C (T h33 (C (C h27 h30) h27)) h27))) h23)) (S h26)) (C h21 h23))) h13)) (S h25)) h23
  have h38 := T (T h34 h37) h22
  have h39 := S h20
  have h40 := C h13 h7
  have h41 := C (T h40 (C h13 (C h16 h2))) h13
  have h42 := S h10
  have h43 := C (C h0 h14) h0
  have h44 := C h28 h27
  have h45 := C (T (T h25 (C (C h13 (T (T (T (C h22 h23) h26) (C (C h23 (T (C (T (C (C h27 h44) h27) (S h33)) h27) h29)) h23)) (C h34 h23))) h13)) (S h36)) h23
  have h46 := T (T (T (T (T (T (T h21 h45) h35) h43) h42) h11) h41) h39
  have h47 := C h46 h2
  have h48 := T h47 h17
  have h49 := C h48 h38
  have h50 := T (T h21 h45) h35
  let v51 := M v3 v1
  have h52 := R v51
  have h53 := C h52 h50
  have h54 := T (T (T (T (T (T (T h20 h18) h12) h10) h8) h34) h37) h22
  have h55 := C h54 h2
  have h56 := h z x v1
  have h57 := S h56
  have h58 := h v3 v1 v3
  have h59 := C (C h13 (C (S h58) h2)) h13
  have h60 := h (M v1 (M (M v3 v3) v3)) x v1
  have h61 := C h48 h2
  have h62 := C (C h61 h38) h38
  have h63 := C h2 h62
  let v64 := M v51 v1
  have h65 := R v64
  have h66 := C (C h65 h50) h50
  have h67 := C h2 h66
  have h68 := h v64 v1 x
  have h69 := S h68
  have h70 := T h16 h55
  have h71 := C h70 h2
  have h72 := T (T (T (T (T (T (T (T h20 h18) h12) h10) h8) h34) h37) h22) h71
  have h73 := h (M v1 (M (M v3 x) x)) x v1
  have h74 := h v3 v1 x
  have h75 := h (M x v51) x x
  have h76 := h z x x
  have h77 := S h76
  let v78 := M (M z x) x
  have h79 := h (M x v78) x x
  have h80 := h v51 v1 x
  have h81 := S h80
  have h82 := h (M v1 v78) x v1
  have h83 := h z v1 x
  have h84 := C (T (T (T (T (T (T (T (T (T h61 h21) h45) h35) h43) h42) h11) (C (T h40 (C h13 (C h83 h2))) h13)) (S h82)) (C h2 (C (C h70 h13) h13))) h2
  have h85 := C (T (T (T (T (T (T (T h84 h81) h47) h17) h76) (C (T (T (T h79 (C (C h13 (T (C h77 h13) (C h56 h13))) h13)) (S h75)) (C h13 (C h74 h2))) h13)) (S h73)) (C h2 (T (C (C h46 h13) h13) (C (C h72 h13) h13)))) h2
  have h86 := T (T (T h34 h37) h22) h71
  have h87 := C (C h86 (T (T h85 h69) h61)) h38
  have h88 := h v64 v5 v1
  have h89 := C h2 (T (T h71 h88) h87)
  have h90 := C (T (T (T (T (T (T (T h89 h67) h63) h60) h59) h57) h16) h55) h38
  have h91 := R v5
  let v92 := M v1 v3
  have h93 := h v92 v5 v1
  have h94 := S h93
  have h95 := S h88
  have h96 := C (T (T (T (T (T (T (T (T (T (C h2 (C (C h48 h13) h13)) h82) (C (T (C h13 (C (S h83) h2)) h15) h13)) h12) h10) h8) h34) h37) h22) h71) h2
  have h97 := T (T (T (T (T (T (T (T h61 h21) h45) h35) h43) h42) h11) h41) h39
  have h98 := C (T (T (T (T (T (T (T (C h2 (T (C (C h97 h13) h13) (C (C h54 h13) h13))) h73) (C (T (T (T (C h13 (C (S h74) h2)) h75) (C (C h13 (T (C h57 h13) (C h76 h13))) h13)) (S h79)) h13)) h77) h16) h55) h80) h96) h2
  have h99 := T (T (T h61 h21) h45) h35
  have h100 := C h99 (T (T h71 h68) h98)
  have h101 := C h100 h50
  have h102 := C h2 (T (T h101 h95) h61)
  have h103 := C h65 h38
  have h104 := C h2 (C h103 h38)
  have h105 := C h71 h50
  have h106 := C h2 (C h105 h50)
  have h107 := S h60
  have h108 := C (C h13 (C h58 h2)) h13
  have h109 := C (T (T (T (T (T (T (T (T (T h84 h81) h47) h17) h56) h108) h107) h106) h104) h102) h2
  have h110 := h z v1 v4
  have h111 := h (M v1 (M (M z v4) v4)) x v1
  have h112 := h v32 x v3
  have h113 := h y v3 v3
  let v114 := M v4 v3
  have h115 := h (M v3 v114) x v3
  have h116 := R v114
  have h117 := C (T (T (T (C h38 h116) h115) (C (T (C h13 (C (S h113) h27)) (C h13 h44)) h13)) (S h112)) h27
  have h118 := C (T h117 h29) h27
  have h119 := C (T (T (T h112 (C (T (C h13 h30) (C h13 (C h113 h27))) h13)) (S h115)) (C h50 h116)) h27
  have h120 := h y v5 v3
  have h121 := S h120
  have h122 := h (M v5 v114) x v5
  have h123 := h y v5 v4
  have h124 := S h123
  have h125 := C h124 h91
  have h126 := C h123 h91
  have h127 := h y v5 z
  have h128 := S h127
  have h129 := C (C h13 (T (C h128 h91) h126)) h13
  have h130 := h (M v5 (M (M y z) z)) x v5
  have h131 := C (T (T (T h130 h129) (C (C h13 (T h125 (C h120 h91))) h13)) (S h122)) h50
  have h132 := C (T (T (T h131 h121) h28) h119) h27
  have h133 := S h130
  have h134 := C (C h13 (T h125 (C h127 h91))) h13
  have h135 := C (T (T (T h122 (C (C h13 (T (C h121 h91) h126)) h13)) h134) h133) h38
  have h136 := h (M v5 (M (M y v4) v4)) x v5
  have h137 := C (T (T h136 h134) h133) h50
  have h138 := C (T (T (T h137 h128) h120) h135) h27
  have h139 := S h136
  have h140 := C (T (T h130 h129) h139) h38
  have h141 := h y v5 x
  have h142 := h (M v5 v31) x v5
  have h143 := C (T (T (T (C (T (T h142 (C (C h13 (T (C (S h141) h91) h126)) h13)) h139) h50) h124) h127) h140) h27
  have h144 := R z
  have h145 := C (T (T (T h137 h128) h123) (C (T (T h136 (C (C h13 (T h125 (C h141 h91))) h13)) (S h142)) h38)) h27
  have h146 := C (T (T (T h131 h121) h127) h140) h27
  have h147 := C (T (T (T h117 h29) h120) h135) h27
  have h148 := C (T h28 h119) h27
  have h149 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (C h2 (C (T (T (C (T (T (T (T (T h89 h67) h63) h60) h59) h57) (T (T (T h148 h147) h146) h145)) (C h144 h143)) (C h70 (T (T h138 h132) h118))) h23)) (C h2 (C (C h48 h23) h23))) h111) (C (T (C h13 (C (S h110) h2)) h15) h13)) h12) h10) h8) h34) h37) h22) h71) h68) h98) h109) h2
  have h150 := h v92 v1 v4
  have h151 := C h99 (T (T (T (T (T (T (T h56 h108) h107) h106) h104) h102) h150) h149)
  have h152 := C h72 h144
  have h153 := C h46 h144
  have h154 := C (T (T h153 h152) h151) h50
  have h155 := C (T h154 h94) h50
  have h156 := C h54 h144
  have h157 := C h97 h144
  have h158 := S h150
  have h159 := C (T (T (T (T (T (T (T (T (T h89 h67) h63) h60) h59) h57) h16) h55) h80) h96) h2
  have h160 := C (T (T (T (T (T (T (T (T (T (T (T (T (T h159 h85) h69) h61) h21) h45) h35) h43) h42) h11) (C (T h40 (C h13 (C h110 h2))) h13)) (S h111)) (C h2 (C (C h70 h23) h23))) (C h2 (C (T (T (C h48 (T (T h148 h147) h146)) (C h144 h145)) (C (T (T (T (T (T h56 h108) h107) h106) h104) h102) (T (T (T h143 h138) h132) h118))) h23))) h2
  have h161 := C h86 (T (T (T (T (T (T (T h160 h158) h89) h67) h63) h60) h59) h57)
  have h162 := C (T (T h161 h157) h156) h38
  have h163 := h x z x
  have h164 := S h163
  have h165 := h (M z (M (M x x) x)) x z
  have h166 := h x z z
  have h167 := C (S h166) h144
  let v168 := M v1 z
  let v169 := M z v168
  have h170 := h v169 x z
  have h171 := h v169 z z
  have h172 := C h166 h144
  have h173 := h (M v3 z) y v3
  have h174 := S h173
  have h175 := C (T h93 h162) h38
  have h176 := C (T (T (T (T (T (T (T h47 h17) h56) h108) h107) h106) h104) h102) h50
  have h177 := C h52 h38
  have h178 := C h70 h50
  have h179 := h z v3 v3
  have h180 := C (C h0 (T (T (T (T (C (S h179) h27) h178) h177) h176) h175)) h0
  let v181 := M v3 v19
  have h182 := h v181 y v3
  have h183 := C (T (T (T (T (T (T h34 h37) h22) h71) h68) h98) h109) (C (T (T (T (C (T (T (T (T h182 h180) h174) h153) h152) h144) (C h157 h144)) (C (T (T (T (T (T h156 (C (C h144 h172) h144)) (S h171)) h170) (C (T (C h13 h167) (C h13 (C h163 h144))) h13)) (S h165)) h144)) h164) h144)
  have h184 := R (M (M v181 z) z)
  have h185 := C h50 h184
  have h186 := h v181 v3 z
  have h187 := S h182
  have h188 := C (C h0 (T (T (T (T h155 h90) h53) h49) (C h179 h27))) h0
  have h189 := C (C h144 h167) h144
  have h190 := S h170
  have h191 := C (T (C h13 (C h164 h144)) (C h13 h172)) h13
  T (T (T (T (T (T (T (T (T (T (T h163 (C (T (T (T (T (T (T (T (T (T h165 h191) h190) h171) h189) h173) h188) h187) h186) (C (T (T (T (T (T (T (T (T (T h185 h183) h160) h158) h89) h67) h63) h60) h59) h57) (T (T (T (T (T h71 h88) h87) h66) h62) (C (T (T (T (T (T h105 h103) h100) (C h91 (T (T (T h85 h69) h88) h87))) (C h38 (R (M (M v64 v3) v3)))) (C (T (T (T (T (T (T (T (T (T (T (T h21 h45) h35) h43) h42) h11) h41) h39) (C h2 (C h178 h50))) (C h2 (C h177 h38))) (C h2 (C h176 h50))) (C h2 (T (T (T (T (T (T (T (C (T (T (T (T (T (T (T (T h175 (C (T (T (T (T (T h154 h94) h150) h149) (C (T (T (T (T (T (T h159 h85) h69) h61) h21) h45) h35) (C (T (T (T h163 (C (T (T (T (T (T h165 h191) h190) h171) h189) h153) h144)) (C h152 h144)) (C (T (T (T (T h157 h156) h173) h188) h187) h144)) h144))) (C h38 h184)) h27)) (S h186)) h182) h180) h174) h153) h152) h151) h91) h94) h89) h67) h63) h60) h59) h57))) (T (T (T (T (T h101 h95) h61) h21) h45) h35))) h50)))) h144)) (S (h v168 z v5))) (C h2 (T (T (T (T (T (T (T h56 h108) h107) h106) h104) h102) h93) (C (T (T (T (T (T (T (T (T h161 h157) h156) h173) h188) h187) h186) (C (T (T (T (T (T h185 h183) h160) h158) h93) h162) h27)) h155) h91)))) (C h2 (C h90 h38))) (C h2 (C h53 h50))) (C h2 (C h49 h38))) h20) h18) h12) h10) h8

