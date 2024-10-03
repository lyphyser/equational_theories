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
theorem Equation2522_implies_Equation1304 (G: Type _) [Magma G] (h: Equation2522 G) : Equation1304 G := fun x y z =>
  let v0 := M x z
  let v1 := M v0 z
  let v2 := M v1 y
  let v3 := M y v2
  have h4 := h v3 x v3
  have h5 := S h4
  have h6 := R x
  have h7 := R v3
  have h8 := R v2
  have h9 := h y v2 v3
  have h10 := S h9
  have h11 := C h10 h8
  let v12 := M v2 (M (M y v3) v3)
  have h13 := h v12 v3 v2
  have h14 := h v12 v2 v2
  have h15 := S h14
  have h16 := C h9 h8
  have h17 := C h8 h16
  let v18 := M v2 v3
  have h19 := h v18 v2 v2
  have h20 := C h8 h11
  have h21 := T h9 (C (T h14 (C h20 h8)) h8)
  have h22 := C (C h6 (T (T (T (C (T (T (C (C h8 h21) h8) (S h19)) h17) h8) h15) h13) (C (C h7 h11) h7))) h6
  have h23 := h (M v2 y) x v2
  have h24 := R y
  have h25 := h v2 y v1
  have h26 := S h25
  have h27 := h (M y (M (M v2 v1) v1)) x y
  have h28 := S h23
  have h29 := T (C (T (C h17 h8) h15) h8) h10
  have h30 := C (C h6 (T (T (T (C (C h7 h16) h7) (S h13)) h14) (C (T (T h20 h19) (C (C h8 h29) h8)) h8))) h6
  have h31 := h y v2 v1
  have h32 := C (C h6 (C (S h31) h8)) h6
  let v33 := M (M y v1) v1
  have h34 := h (M v2 v33) x v2
  have h35 := C (T (T (T h34 h32) (C (C h6 (T (T (T h4 h30) h28) (C h25 h24))) h6)) (S h27)) h24
  have h36 := C (T h35 h26) h24
  have h37 := S h34
  have h38 := C (C h6 (C h31 h8)) h6
  have h39 := h v12 x v2
  have h40 := h v18 v3 v2
  have h41 := h v1 y v0
  have h42 := C (S h41) h24
  have h43 := C (C h24 h42) h24
  let v44 := M y (M (M v1 v0) v0)
  have h45 := h v44 y y
  have h46 := S h45
  have h47 := C h41 h24
  have h48 := C (C h24 h47) h24
  have h49 := h y x x
  have h50 := S h49
  have h51 := h (M x (M (M y x) x)) x x
  have h52 := h x v1 z
  have h53 := S h52
  have h54 := h y x v2
  have h55 := h (M x (M v3 v2)) x x
  have h56 := h v3 v2 v1
  have h57 := C (T (T (T (C h6 (C (S h56) h8)) h55) (C (C h6 (T (C (S h54) h52) (C h49 h53))) h6)) (S h51)) h6
  let v58 := M v3 v1
  let v59 := M v58 v1
  let v60 := M v2 v59
  have h61 := h v60 x v2
  have h62 := h v60 x y
  have h63 := S h62
  have h64 := S h61
  have h65 := C (T (T (T h51 (C (C h6 (T (C h50 h52) (C h54 h53))) h6)) (S h55)) (C h6 (C h56 h8))) h6
  have h66 := T (T h49 h65) h64
  have h67 := h v18 y v2
  have h68 := h v2 v3 z
  have h69 := C (S h68) h7
  have h70 := C (C h6 (T (T (T h69 h67) (C (C h24 h29) h24)) (C (C h66 h24) h24))) h6
  have h71 := C h68 h7
  have h72 := h v2 v3 x
  have h73 := C (C h6 (T (C (S h72) h7) h71)) h6
  let v74 := M v3 (M (M v2 x) x)
  have h75 := h v74 x v3
  have h76 := h v74 x x
  have h77 := S h75
  have h78 := C (C h6 (T h69 (C h72 h7))) h6
  have h79 := T (T h61 h57) h50
  have h80 := C (C h6 (T (T (T (C (C h79 h24) h24) (C (C h24 h21) h24)) (S h67)) h71)) h6
  have h81 := h v60 x v1
  have h82 := S h81
  have h83 := R v1
  have h84 := h v1 x v1
  have h85 := S h84
  have h86 := C (C h6 h52) h6
  have h87 := T h86 h85
  have h88 := T h84 (C (C h6 h53) h6)
  have h89 := h (M x v33) x x
  have h90 := h y x v1
  let v91 := M v1 v1
  have h92 := h (M y (M v91 v1)) x y
  have h93 := S h92
  have h94 := h v1 y v1
  have h95 := C h6 h42
  have h96 := C (T h95 (C h6 (C h94 h24))) h6
  have h97 := h v44 x y
  have h98 := h v3 y v0
  have h99 := h (M y (M (M v3 v0) v0)) x y
  have h100 := C (T (T (T h99 (C (C h6 (T (T (T (T (T (T (C (S h98) h24) h48) h46) h97) h96) h93) (C h90 h53))) h6)) (S h89)) (C h6 (C (T (C h24 h88) (C h66 h87)) h83))) h6
  have h101 := S h97
  have h102 := C h6 h47
  have h103 := C (T (C h6 (C (S h94) h24)) h102) h6
  have h104 := C (T (T (T (C h6 (C (T (C h79 h88) (C h24 h87)) h83)) h89) (C (C h6 (T (T (T (T (T (T (C (S h90) h52) h92) h103) h101) h45) h43) (C h98 h24))) h6)) (S h99)) h6
  have h105 := h (M x v2) x x
  have h106 := h x v2 v3
  have h107 := C (S h106) h8
  let v108 := M (M x v3) v3
  let v109 := M v2 v108
  have h110 := h v109 v3 v2
  have h111 := h v109 x v2
  have h112 := C h106 h8
  have h113 := h x v2 v1
  have h114 := S h113
  let v115 := M x v1
  let v116 := M v115 v1
  have h117 := h (M v2 v116) x v2
  have h118 := C (C (T (T (T (T (T (T h113 (C (T (T (T (T (T (T (T h117 (C (C h6 (T (C h114 h8) h112)) h6)) (S h111)) h110) (C (T (T (C h7 (T (T (T (T (T (T (T (T (T (T h107 h105) (C (C h6 (T (C (T (C h102 h6) h101) h6) (C (T (T (T (T h97 h96) h93) (C (T (T (T (T h49 h65) h64) h81) h104) h53)) (C (T (T (T (T (T h100 h82) h62) h80) h78) h77) h6)) h6))) h6)) (S h76)) h75) h73) h70) h63) h61) h57) h50)) h48) h46) h7)) (C (T (T h45 h43) (C h7 h21)) h7)) (S h40)) h17) h8)) h15) h39) (C (C h6 h11) h6)) h38) h37) h24) h24
  let v119 := M (M x y) y
  have h120 := h v3 v1 v1
  have h121 := S h120
  have h122 := h (M v1 v59) v3 v1
  have h123 := h v58 x v3
  have h124 := h x v3 z
  have h125 := h x v3 v1
  have h126 := C (S h125) h7
  let v127 := M v3 v116
  have h128 := h v127 x v3
  have h129 := h v127 v3 v3
  have h130 := C h125 h7
  have h131 := h (M x v119) x x
  have h132 := h x x y
  have h133 := h x x z
  have h134 := h v115 x x
  have h135 := h x v1 v3
  have h136 := C (S h135) h88
  let v137 := M v1 v108
  have h138 := h v137 v3 v1
  have h139 := h v137 x v1
  have h140 := C h135 h87
  have h141 := h v91 x v1
  have h142 := h v1 v1 z
  have h143 := S h142
  have h144 := h (M v1 (M (M v1 z) z)) v3 v1
  have h145 := C (T (T h144 (C (C h7 (T (T (T (T (T (T (T (T (T (T (T (T (C h143 h88) (C h83 h87)) h141) (C (C h6 (T (C h53 h88) h140)) h6)) (S h139)) h138) (C (C h7 (T (T (T (T (T (T (T h136 (C h6 h87)) h134) (C (C h6 (T (C (S h133) h6) (C h132 h6))) h6)) (S h131)) (C h6 h118)) (C h6 (T (T (T h36 h23) h22) h5))) h130)) h7)) (S h129)) h128) (C (C h6 (T h126 (C h124 h7))) h6)) (S h123)) (C h7 h88)) (C h120 h87))) h7)) (S h122)) h83
  have h146 := T (T h142 h145) h121
  have h147 := C (C (T (T (T (T (T (T h34 h32) (C (C h6 h16) h6)) (S h39)) h14) (C (T (T (T (T (T (T (T h20 h40) (C (T (T (C h7 h29) h48) h46) h7)) (C (T (T h45 h43) (C h7 (T (T (T (T (T (T (T (T (T (T h49 h65) h64) h62) h80) h78) h77) h76) (C (C h6 (T (C (T (T (T (T (C (T (T (T (T (T h75 h73) h70) h63) h81) h104) h6) (C (T (T (T (T h100 h82) h61) h57) h50) h52)) h92) h103) h101) h6) (C (T h97 (C h95 h6)) h6))) h6)) (S h105)) h112))) h7)) (S h110)) h111) (C (C h6 (T h107 (C h113 h8))) h6)) (S h117)) h8)) h114) h24) h24
  have h148 := C (T h25 (C (T (T (T h27 (C (C h6 (T (T (T (C h26 h24) h23) h22) h5)) h6)) h38) h37) h24)) h24
  have h149 := T (T (T (T (T (T (T h142 h145) h121) h4) h30) h28) h148) h147
  have h150 := C h83 h88
  have h151 := S h141
  have h152 := C (C h6 (T h136 (C h52 h87))) h6
  have h153 := T (T h120 (C (T (T h122 (C (C h7 (T (T (T (T (T (T (T (T (T (T (T (T (C h121 h88) (C h7 h87)) h123) (C (C h6 (T (C (S h124) h7) h130)) h6)) (S h128)) h129) (C (C h7 (T (T (T (T (T (T (T h126 (C h6 (T (T (T h4 h30) h28) h148))) (C h6 h147)) h131) (C (C h6 (T (C (S h132) h6) (C h133 h6))) h6)) (S h134)) (C h6 h88)) h140)) h7)) (S h138)) h139) h152) h151) h150) (C h142 h87))) h7)) (S h144)) h83)) h143
  have h154 := h x v1 v1
  T (T (T (T (T (T (T (T (T h154 (C (T (T (T (T (T (h (M v1 v116) x v1) (C (C h6 (T (C (S h154) h88) h140)) h6)) h152) h151) h150) (C h149 (T (T (T (T h86 h85) h142) h145) h121))) h146)) (C (C (R v119) h153) h153)) (C (C (T (T (T (T h118 h36) h23) h22) h5) (T (T (T (T (T (T (T h142 h145) h121) h4) h30) h28) h148) (C (T (T h35 h26) (C h149 h24)) h24))) h146)) (S (h v119 v3 y))) h118) h36) h23) h22) h5

