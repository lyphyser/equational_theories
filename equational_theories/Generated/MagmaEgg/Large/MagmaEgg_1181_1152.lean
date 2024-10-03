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
theorem Equation1181_implies_Equation1152 (G: Type _) [Magma G] (h: Equation1181 G) : Equation1152 G := fun x y z =>
  let v0 := M x y
  let v1 := M z v0
  let v2 := M v1 z
  let v3 := M y v2
  have h4 := h v3 v2 v1
  have h5 := S h4
  let v6 := M (M v1 (M v1 v3)) v2
  have h7 := h v6 v3 v0
  have h8 := S h7
  have h9 := R v3
  have h10 := h v6 v3 v2
  have h11 := R v2
  have h12 := h v3 v2 x
  have h13 := S h12
  have h14 := h (M (M x (M x v3)) v2) x v2
  have h15 := S h14
  have h16 := R x
  have h17 := h y x v0
  have h18 := S h17
  let v19 := M (M v0 (M v0 y)) x
  have h20 := h v19 x x
  have h21 := S h20
  have h22 := C h16 h17
  have h23 := C h22 h16
  have h24 := T (C h16 (T (C h16 h23) h21)) h18
  have h25 := C h11 (C h24 h11)
  let v26 := M v0 x
  have h27 := h v26 v2 x
  have h28 := h x v0 v2
  have h29 := S h28
  have h30 := R v0
  have h31 := C h16 (C (T (T (T (C h30 h29) h27) h25) (C h11 h12)) h16)
  let v32 := M (M v2 (M v2 x)) v0
  have h33 := h v32 x v0
  have h34 := T (T h33 h31) h15
  have h35 := T (C h11 h34) h13
  have h36 := C h11 h35
  have h37 := h v32 v3 v2
  have h38 := S h33
  have h39 := S h27
  have h40 := C h16 h18
  have h41 := C h40 h16
  have h42 := T h17 (C h16 (T h20 (C h16 h41)))
  have h43 := C h11 (C h42 h11)
  have h44 := C h16 (C (T (T (T (C h11 h13) h43) h39) (C h30 h28)) h16)
  have h45 := C h30 (T (T (T (T (T h14 h44) h38) h37) (C h9 (C (T h36 (C h11 h4)) h9))) (S h10))
  have h46 := C h30 h34
  have h47 := h v26 y x
  have h48 := R y
  let v49 := M y (M y y)
  have h50 := h (M v49 v3) x v3
  have h51 := h y v3 y
  have h52 := h (M v3 y) x y
  have h53 := h v2 y v0
  have h54 := S h53
  have h55 := C h48 h54
  let v56 := M (M v0 (M v0 v2)) y
  have h57 := h v56 y y
  have h58 := h z v1 v3
  have h59 := S h58
  have h60 := R v1
  have h61 := C h60 h59
  let v62 := M (M v3 (M v3 z)) v1
  have h63 := h v62 x v1
  have h64 := h v62 v2 v1
  have h65 := S h64
  have h66 := C h60 h58
  have h67 := C h11 (C h66 h11)
  have h68 := h v2 x v2
  have h69 := C h9 (T (T (T h68 (C h16 (C (T (T (T (T (T h67 h65) h63) (C h16 (T (C h61 h16) (C (T h53 (C h48 (T h57 (C h48 (C h55 h48))))) h16)))) (S h52)) (C h9 h51)) h16))) (S h50)) (C (T (T (T (C h48 (C h42 h48)) (S h47)) (C h30 (T h28 h46))) (C h30 h45)) h9))
  have h70 := C h11 (T (T (C h55 h11) h69) h8)
  have h71 := h v56 v2 y
  have h72 := C h48 h53
  have h73 := h v0 z v3
  have h74 := S h73
  have h75 := h (M (M v3 (M v3 v0)) z) x z
  have h76 := R z
  have h77 := h v0 z v0
  have h78 := C h76 (S h77)
  let v79 := M (M v0 (M v0 v0)) z
  have h80 := h v79 x z
  have h81 := h v79 z z
  have h82 := C h76 h77
  have h83 := C h76 (T (T (T (T (C h76 (C h82 h76)) (S h81)) h80) (C h16 (T (C h78 h16) (C (C h76 h73) h16)))) (S h75))
  let v84 := M z (M z v2)
  have h85 := h v84 v3 z
  have h86 := S h85
  have h87 := C h76 (T (T (T (T h75 (C h16 (T (C (C h76 h74) h16) (C h82 h16)))) (S h80)) h81) (C h76 (C h78 h76)))
  have h88 := T h73 h87
  have h89 := C h76 (C h76 h88)
  have h90 := h (M z v1) x v1
  have h91 := S h90
  have h92 := h v62 v1 v1
  have h93 := S h92
  have h94 := C h66 h60
  have h95 := T (C h60 (T (C h60 h94) h93)) h59
  let v96 := M v2 v1
  have h97 := h v96 v1 v1
  have h98 := C h61 h60
  have h99 := C h16 (C (T (T (T h67 h65) h92) (C h60 (T (T h98 h97) (C h60 (C h95 h60))))) h16)
  have h100 := h v96 v0 v1
  have h101 := T h58 (C h60 (T h92 (C h60 h98)))
  have h102 := h v84 x x
  let v103 := M x v0
  have h104 := h (M (M x v103) x) x x
  have h105 := h v0 x x
  have h106 := h (M v103 x) x x
  have h107 := h y x x
  have h108 := h y x y
  have h109 := S h108
  have h110 := h (M v49 x) x x
  have h111 := h v19 v3 x
  have h112 := T (T h14 h44) h38
  have h113 := T h12 (C h11 h112)
  have h114 := C h11 h113
  have h115 := h v26 v3 x
  let v116 := M y v3
  have h117 := h v116 v3 v3
  have h118 := h v116 v1 x
  have h119 := C h9 (C (T (T (T (T (C h60 (T (C h60 (T (T h118 (C h60 (T (T (T (C (T (T (T (C h16 (T (T (T (T (T (C h16 (T (T (T (T (T h117 (C h9 (T (C (T (T (T (T (C h9 (T (C h9 (C h42 h9)) (S h115))) (C h9 (T (T (T h27 h25) h114) (C (T (T (T h68 h99) h91) h89) h35)))) h86) h83) h74) h9) (C h22 h9)))) (S h111)) h20) (C h16 (T h41 (C (C h16 h108) h16)))) (S h110))) h109) h17) (C h16 (T (T (T h20 (C h16 (T h41 (C (C h16 h107) h16)))) (S h106)) (C (C h16 h105) h16)))) (S h104)) (C (C h16 (C h16 h88)) h16))) (S h102)) h83) h74) h60) (C h30 (C h101 h30))) (S h100)) h94))) h93)) h59)) h68) h99) h91) h89) h9)
  have h120 := h v116 v3 v1
  have h121 := h v56 x y
  have h122 := h v2 y v3
  have h123 := S h122
  let v124 := M v3 v2
  have h125 := h (M (M v3 v124) y) x y
  have h126 := C h48 (T (T (T (T (T (T h125 (C h16 (C (C h48 h123) h16))) (C h16 (C h72 h16))) (S h121)) h71) h70) h5)
  have h127 := T h83 h74
  have h128 := S h68
  have h129 := C h11 (C h61 h11)
  have h130 := C h16 (C (T (T (T (T (T (C h9 (S h51)) h52) (C h16 (T (C (T (C h48 (T (C h48 (C h72 h48)) (S h57))) h54) h16) (C h66 h16)))) (S h63)) h64) h129) h16)
  have h131 := C h48 (C h24 h48)
  have h132 := C h30 (T (C h30 h112) h29)
  have h133 := C h30 (C h30 (T (T (T (T (T h10 (C h9 (C (T (C h11 h5) h114) h9))) (S h37)) h33) h31) h15))
  have h134 := C h9 (T (T (T (C (T (T (T h133 h132) h47) h131) h9) h50) h130) h128)
  have h135 := C h16 (C (T (T (T (C h60 (T (T (C h60 (C h101 h60)) (S h97)) h94)) h93) h64) h129) h16)
  have h136 := C h76 (C h76 h127)
  T (T (T (T (T (T (T (T (T h28 h46) h45) (C h30 (T h7 h134))) (C (T (T (T (T (T (T h73 h87) h85) (C h9 (C (T (T (T (T h136 h90) h135) h128) (C h60 (T h58 (C h60 (T (T h92 (C h60 (T (T (T h98 h100) (C h30 (C h95 h30))) (C (T (T (T h73 h87) h102) (C h16 (T (T (T (T (T (C (C h16 (C h16 h127)) h16) h104) (C h16 (T (T (T (C (C h16 (S h105)) h16) h106) (C h16 (T (C (C h16 (S h107)) h16) h23))) h21))) h18) h108) (C h16 (T (T (T (T (T h110 (C h16 (T (C (C h16 h109) h16) h23))) h21) h111) (C h9 (T (C h40 h9) (C (T (T (T (T h73 h87) h85) (C h9 (T (T (T (C (T (T (T h136 h90) h135) h128) h113) h36) h43) h39))) (C h9 (T h115 (C h9 (C h24 h9))))) h9)))) (S h117)))))) h60)))) (S h118)))))) h9))) (S h120)) (C h48 (T (T (T (T (T (T h4 (C h11 (T (T h7 h134) (C h72 h11)))) (S h71)) h121) (C h16 (C h55 h16))) (C h16 (C (C h48 h122) h16))) (S h125)))) h123) (T (T (h v124 v3 v0) (C h9 (T (T (T (T (T (T (T (T (C (T (T (T (T (C h30 (C h30 (T h69 h8))) h133) h132) h47) h131) h9) h50) h130) h128) h122) h126) h120) h119) h86))) (C h9 h127)))) (C (T (T (T (T (T (T h122 h126) h120) h119) h86) h83) h74) (C h72 h30))) (S (h v56 v0 y))) h71) h70) h5

