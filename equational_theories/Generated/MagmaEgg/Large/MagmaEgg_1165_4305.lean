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
theorem Equation1165_implies_Equation4305 (G: Type _) [Magma G] (h: Equation1165 G) : Equation4305 G := fun x y z =>
  let v0 := M y z
  have h1 := h v0 z x
  have h2 := R x
  let v3 := M z v0
  have h4 := h v3 z x
  have h5 := R z
  let v6 := M z v3
  have h7 := h (M (M x v6) x) z x
  have h8 := h v6 z x
  have h9 := R v3
  have h10 := h z v3 y
  have h11 := R y
  have h12 := h z y z
  have h13 := h y z v3
  let v14 := M x y
  let v15 := M x v14
  have h16 := h x y v15
  have h17 := S h16
  have h18 := R v15
  have h19 := h y x x
  have h20 := S h19
  have h21 := h x v15 x
  have h22 := T h21 (C h18 (C h20 h2))
  have h23 := C h22 h18
  have h24 := C h11 h23
  have h25 := T h24 h17
  have h26 := T (C h18 (C h19 h2)) (S h21)
  have h27 := C h26 h18
  have h28 := C h11 h27
  have h29 := T h16 h28
  have h30 := C h29 h11
  have h31 := C h5 (T (T (T (C (C h2 (T (C h5 (C (T h30 (C h25 (T h13 (C h5 (C (T (C h9 (C h12 h11)) (S h10)) h9))))) h2)) (S h8))) h2) h7) (C h5 (C (C h2 (S h4)) h2))) (S h1))
  let v32 := M v14 x
  have h33 := h v32 z x
  have h34 := h v32 x v0
  have h35 := S h34
  have h36 := R v0
  have h37 := C h25 h11
  have h38 := C h2 (C (T (C h29 h20) h37) h2)
  let v39 := M v15 x
  have h40 := h v39 x x
  have h41 := h v39 v0 v0
  have h42 := h v15 x y
  have h43 := S h42
  have h44 := h v14 v0 v0
  have h45 := S h44
  have h46 := C h36 (C (T (C h2 (T h45 h30)) h43) h2)
  let v47 := M v0 v14
  let v48 := M (M v0 v47) v0
  have h49 := h v48 v0 x
  have h50 := C h36 (T (C h36 (C (T h44 (C h36 (T h49 h46))) h36)) (S h41))
  have h51 := C (T h50 (C h36 (T h40 h38))) h36
  have h52 := S h49
  have h53 := C h36 (C (T h42 (C h2 (T h37 h44))) h2)
  have h54 := C h36 (T h41 (C h36 (C (T (C h36 (T h53 h52)) h45) h36)))
  have h55 := h v48 v0 v15
  have h56 := h (M (M v15 v14) v15) x x
  have h57 := h y x v15
  have h58 := S h33
  have h59 := C h5 (T (T (T h1 (C h5 (C (C h2 h4) h2))) (S h7)) (C (C h2 (T h8 (C h5 (C (T (C h29 (T (C h5 (C (T h10 (C h9 (C (S h12) h11))) h9)) (S h13))) h37) h2)))) h2))
  let v60 := M y x
  let v61 := M v14 v60
  have h62 := h v14 v61 y
  have h63 := S h62
  have h64 := h x y v14
  have h65 := R v61
  have h66 := C h65 (T h30 (C (T (T h24 h17) h64) h11))
  have h67 := h (M v61 v14) y x
  have h68 := S h67
  have h69 := h x y x
  have h70 := C h2 (S h69)
  have h71 := C h11 (C (T h70 (C h2 h64)) h2)
  have h72 := C h2 h69
  have h73 := C h11 (C (T (C h2 h25) h72) h2)
  let v74 := M x v15
  have h75 := h v74 y x
  have h76 := h x y y
  have h77 := C h11 (C (T (C h2 (S h76)) h72) h2)
  let v78 := M (M y v60) y
  have h79 := h v78 y x
  have h80 := C h2 (T (T (T (T (T (T h79 h77) h71) h68) h66) h63) h30)
  have h81 := T h80 h43
  have h82 := C h22 h81
  have h83 := h v78 x x
  have h84 := S h79
  have h85 := C h11 (C (T h70 (C h2 h76)) h2)
  have h86 := S h64
  have h87 := C h11 (C (T (C h2 h86) h72) h2)
  have h88 := C h65 (T (C (T (T h86 h16) h28) h11) h37)
  have h89 := C (T (T (T (T (C h36 (T (T (T (T (T (T (T (T (T (T h62 h88) h67) h87) h85) h84) h83) (C h2 (T (T (C (T (T (T (T (T (T (T h82 h27) h75) h73) h71) h68) h66) h63) h2) h33) h31))) (C h2 (T (T h59 h58) (C (T h30 (C h25 h57)) h2)))) (S h56)) (C (C h18 h44) h18))) (S h55)) h49) h46) h54) h36
  have h90 := h (M v47 v0) x x
  have h91 := S h90
  have h92 := h y x v0
  have h93 := C h2 (C (T h30 (C h25 h92)) h2)
  have h94 := S h40
  have h95 := C h2 (C (T h30 (C h25 h19)) h2)
  have h96 := C h2 (T (T (T (T (T (T h37 h62) h88) h67) h87) h85) h84)
  have h97 := T h42 h96
  have h98 := T (T (T (T h59 h58) h34) (C h2 (T (T (T (T (T (C (T (C h36 (T h95 h94)) h54) h36) (C (T (T (T (T h50 h53) h52) h55) (C h36 (T (T (T (T (T (T (T (T (T (T (C (C h18 h45) h18) h56) (C h2 (T (T (C (T (C h29 (S h57)) h37) h2) h33) h31))) (C h2 (T (T h59 h58) (C (T (T (T (T (T (T (T h62 h88) h67) h87) (C h11 (C (T h70 (C h2 h29)) h2))) (S h75)) h23) (C h26 h97)) h2)))) (S h83)) h79) h77) h71) h68) h66) h63))) h36)) h90) (C h2 (C (T (C h29 (S h92)) h37) h2))) h95) h94))) h20
  have h99 := h v15 y x
  have h100 := S h99
  let v101 := M y v15
  have h102 := h (M (M x v101) x) y x
  have h103 := h (M v74 x) x x
  have h104 := S h103
  have h105 := h v14 x x
  have h106 := C h2 (C (T h42 (C h2 (T h37 h105))) h2)
  have h107 := C h2 (C (T (C h2 (T (S h105) h30)) h43) h2)
  have h108 := h v15 y y
  have h109 := h (M (M y v101) y) y x
  have h110 := R (M x v78)
  let v111 := M v3 v15
  have h112 := h (M (M v3 v111) v3) v3 x
  have h113 := h v15 v3 v3
  have h114 := h v14 x v0
  have h115 := C h2 (C (T (C h2 (T (S h114) h30)) h43) h2)
  let v116 := M v0 v15
  have h117 := h (M v116 v0) x x
  have h118 := h v15 v3 v15
  have h119 := h (M (M v15 v111) v15) v3 v0
  have h120 := C h11 (T (T (T (T (T (T (T (T h119 (C h9 (T (T (T (C (C h36 (S h118)) h36) h117) h115) h20))) (C h9 (T (T (T h19 h106) h104) (C (T h23 (C h26 h113)) h2)))) (S h112)) (C (C h98 (T (T (C h9 h97) (C h98 h110)) (C h11 h81))) h98)) h109) (C h11 (T (T (T (C (T (C h22 (S h108)) h27) h2) h103) h107) h20))) (C h11 (T (T (T h19 h106) h104) (C (T h23 (C h26 h99)) h2)))) (S h102))
  have h121 := T (T (T h120 h100) h42) h96
  have h122 := S h117
  have h123 := C h2 (C (T h42 (C h2 (T h37 h114))) h2)
  have h124 := T (T (T (T h19 (C h2 (T (T (T (T (T h40 h38) h93) h91) h89) h51))) h35) h33) h31
  have h125 := C h11 (T (T (T (T (T (T (T (T h102 (C h11 (T (T (T (C (T (C h22 h100) h27) h2) h103) h107) h20))) (C h11 (T (T (T h19 h106) h104) (C (T h23 (C h26 h108)) h2)))) (S h109)) (C (C h124 (T (T (C h11 h97) (C h124 h110)) (C h9 h81))) h124)) h112) (C h9 (T (T (T (C (T (C h22 (S h113)) h27) h2) h103) h107) h20))) (C h9 (T (T (T h19 h123) h122) (C (C h36 h118) h36)))) (S h119))
  have h126 := h v15 y v3
  have h127 := S h126
  have h128 := h (M (M v3 v101) v3) y v0
  have h129 := C h98 (T (C h11 (T (T (T h19 h123) h122) (C (C h36 h126) h36))) (S h128))
  have h130 := h (M v3 (M y y)) v0 v3
  have h131 := C h124 (T h128 (C h11 (T (T (T (C (C h36 h127) h36) h117) h115) h20)))
  have h132 := h (M (M y v116) y) v0 x
  have h133 := h v15 v0 y
  have h134 := h z v0 v3
  have h135 := S h134
  let v136 := M v0 z
  let v137 := M (M v3 v136) v3
  have h138 := h v137 v0 y
  have h139 := h v137 v0 x
  have h140 := h z z v3
  have h141 := C h2 (S h140)
  have h142 := C h2 h140
  have h143 := h z v0 v15
  let v144 := M (M v15 v136) v15
  have h145 := h v144 v0 x
  have h146 := h v144 v14 x
  have h147 := h v136 v14 v15
  have h148 := h v0 z v0
  have h149 := h (M (M v0 v3) v0) v14 v14
  have h150 := R v14
  have h151 := h v3 v14 y
  have h152 := S h151
  have h153 := h (M (M y (M v14 v3)) y) v14 v0
  let v154 := M v3 v14
  have h155 := h v154 v14 z
  have h156 := T h155 (C h150 (C (T (C h5 (T (C h150 (C (T h151 (C h150 (T h153 (C h150 (C (C h36 h152) h36))))) h150)) (S h149))) (S h148)) h5))
  have h157 := T (C h150 (C (C h18 h156) h18)) (S h147)
  let v158 := M (M v15 v154) v15
  have h159 := h v158 v14 v15
  have h160 := h v158 v14 x
  have h161 := T (C h150 (C (T h148 (C h5 (T h149 (C h150 (C (T (C h150 (T (C h150 (C (C h36 h151) h36)) (S h153))) h152) h150))))) h5)) (S h155)
  have h162 := T h147 (C h150 (C (C h18 h161) h18))
  have h163 := C (C h2 h162) h2
  have h164 := h v136 v14 z
  have h165 := h (M (M z v154) z) v3 x
  have h166 := h v14 v3 z
  have h167 := C h150 (T (C (C h2 (T (C h150 (T (T (C h9 (C (T h42 (C h2 (T h37 h166))) h2)) (S h165)) (C (C h5 h156) h5))) (S h164))) h2) h163)
  have h168 := h (M v3 v39) v14 x
  have h169 := S h168
  have h170 := C (C h2 h157) h2
  have h171 := C h150 (T h170 (C (C h2 (T h164 (C h150 (T (T (C (C h5 h161) h5) h165) (C h9 (C (T (C h2 (T (S h166) h30)) h43) h2)))))) h2))
  let v172 := M (M x v136) x
  have h173 := h v172 v14 x
  T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h126 h131) h130) (C h36 (T (T (C (C h98 (T (T (C h36 (T (T (T h129 h127) h99) h125)) (C h36 h121)) (C h36 h81))) h98) h132) (C h36 (T (T (T (C (T (C h22 (S h133)) h27) h2) h103) h107) h20))))) (C h36 (C (C h11 h134) h11))) (S h138)) h139) (C h36 (T (C (T (C h2 h135) h142) h2) (C (T h141 (C h2 h143)) h2)))) (S h145)) h146) (C h150 (T (C (C h2 (T (T (T (T (C h150 (C (C h18 h162) h18)) (S h159)) h160) h171) h169)) h2) (C (C h2 (T (T h168 h167) (C h150 h170))) h2)))) (S h173)) (h v172 x v3)) (C h2 (T (T (T (T (T (T (C (C h98 (T (T (T (T (T (T (T (T (T (C h2 (T (T (T (T (T (T (T (T (T (T (T (T (T h173 (C h150 (T (C (C h2 (T (T (C h150 h163) h171) h169)) h2) (C (C h2 (T (T (T (T h168 h167) (S h160)) h159) (C h150 (C (C h18 h157) h18)))) h2)))) (S h146)) h145) (C h36 (T (C (T (C h2 (S h143)) h142) h2) (C (T h141 (C h2 h134)) h2)))) (S h139)) h138) (C h36 (C (C h11 h135) h11))) (C h36 (T (T (C h36 (T (T (T h19 h106) h104) (C (T h23 (C h26 h133)) h2))) (S h132)) (C (C h124 (T (T (C h36 h97) (C h36 (T (T (T h80 h43) h99) h125))) (C h36 (T (T (T h120 h100) h126) h131)))) h124)))) (S h130)) h129) h127) h99) h125)) (C h2 h121)) h82) h27) h75) h73) h71) h68) h66) h63)) h98) (h (M (M y v14) y) x x)) (C h2 (C (T (C h29 (S (h y x y))) h37) h2))) h93) h91) h89) h51))) h35) h33) h31

