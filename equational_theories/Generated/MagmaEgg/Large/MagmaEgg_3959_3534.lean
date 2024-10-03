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
theorem Equation3959_implies_Equation3534 (G: Type _) [Magma G] (h: Equation3959 G) : Equation3534 G := fun x y z =>
  let v0 := M x y
  let v1 := M z y
  let v2 := M v1 z
  have h3 := h x v2 v0
  let v4 := M x v2
  let v5 := M x v0
  let v6 := M v2 v5
  let v7 := M v6 v4
  have h8 := R v1
  have h9 := R y
  have h10 := h x y v1
  have h11 := S h10
  let v12 := M x v1
  have h13 := h (M y v12) v1 v1
  have h14 := h x y v4
  have h15 := S h14
  have h16 := R v4
  let v17 := M x v4
  have h18 := h y v17 v1
  let v19 := M y v1
  have h20 := h (M v17 v19) v1 v4
  have h21 := h v17 v19 x
  have h22 := R x
  have h23 := h x v2 x
  have h24 := S h23
  let v25 := M x x
  have h26 := h (M v2 v25) x x
  have h27 := R v19
  have h28 := h z y v4
  have h29 := S h28
  let v30 := M y (M z v4)
  have h31 := h v30 v4 v4
  have h32 := h (M v4 (M v30 v4)) y v4
  have h33 := h z v4 y
  have h34 := S h33
  have h35 := h v4 v1 x
  have h36 := h v1 z x
  have h37 := S h36
  let v38 := M z (M v1 x)
  have h39 := h v38 x x
  have h40 := R v2
  have h41 := h z y v2
  have h42 := S h41
  have h43 := h v1 z v2
  have h44 := S h43
  let v45 := M z v2
  let v46 := M y v45
  have h47 := R v46
  let v48 := M v1 v2
  let v49 := M z v48
  have h50 := h v49 v46 v2
  have h51 := h z v48 y
  have h52 := h v1 z v1
  have h53 := S h52
  let v54 := M v1 v1
  have h55 := h (M z v54) v1 v1
  have h56 := h z v54 y
  have h57 := S h56
  have h58 := h z y v1
  have h59 := S h58
  have h60 := h (M y (M z v1)) v1 v1
  have h61 := C (T (T h58 h60) (C (C h8 h59) h8)) h9
  let v62 := M v1 y
  have h63 := h z v62 y
  have h64 := T (T (T h63 (C (T (C (T h61 h57) h8) h53) h9)) (C (T (T h52 h55) (C (C h8 h53) h8)) h9)) (S h51)
  have h65 := h (M z v62) v46 y
  have h66 := h v1 z y
  have h67 := C (T (T (C (C h8 h58) h8) (S h60)) h59) h9
  have h68 := h z y v0
  have h69 := S h68
  let v70 := M z v0
  let v71 := M y v70
  have h72 := h x v71 y
  have h73 := h y v70 x
  have h74 := S h73
  have h75 := h (M v70 (M y x)) x x
  have h76 := h z v0 y
  have h77 := S h76
  have h78 := R v0
  have h79 := C (C h78 h69) h9
  have h80 := h (M v0 (M v71 v0)) y y
  have h81 := C (C h78 h68) h9
  have h82 := h z v0 x
  have h83 := h z x y
  have h84 := h z y y
  have h85 := h v19 x y
  have h86 := h v19 v0 x
  have h87 := h x y x
  have h88 := S h87
  have h89 := h (M y v25) x x
  have h90 := h v5 v19 x
  have h91 := h v5 v19 v1
  have h92 := R (M v5 v1)
  have h93 := h y v1 y
  let v94 := M y y
  have h95 := h (M v1 v94) y v4
  have h96 := h v1 v94 z
  have h97 := R z
  have h98 := h v1 z z
  have h99 := R v94
  have h100 := h v45 v94 z
  have h101 := h (M v45 v94) y v4
  have h102 := h y v45 y
  have h103 := h y v45 v1
  have h104 := S h103
  have h105 := h (M v45 v19) v1 v1
  have h106 := h v1 v46 z
  let v107 := M v2 v1
  have h108 := h v5 v107 v1
  have h109 := h (M v5 v107) v1 v4
  have h110 := h v2 v5 v1
  have h111 := h v1 z v4
  have h112 := S h111
  let v113 := M v1 v4
  have h114 := h (M z v113) x v4
  have h115 := h z v113 y
  have h116 := S h115
  have h117 := h x v2 v1
  have h118 := S h117
  have h119 := C (C h8 h118) h8
  have h120 := h (M v2 v12) v1 v1
  have h121 := S h66
  have h122 := T (T (T h51 (C (T (T (C (C h8 h52) h8) (S h55)) h53) h9)) (C (T h52 (C (T h56 h67) h8)) h9)) (S h63)
  have h123 := h v49 x y
  have h124 := h v49 x v2
  have h125 := h v38 v4 x
  let v126 := M v38 v4
  have h127 := C (C h22 h44) h111
  have h128 := S h123
  have h129 := C (T (T (T (C (C h8 h117) h8) (S h120)) h118) (C h22 (T h66 (C h64 h9)))) h9
  have h130 := h x v2 v4
  have h131 := h z v113 v0
  T (T (T (T (T (T (T h14 (h (M y v17) v4 v4)) (C (C h16 h15) h16)) (h (M v4 v0) v4 v1)) (C (C h16 (C (T (T (h v4 v0 y) (C (T (C h78 (T (T (C (T (T h117 h120) h119) h9) h116) h131)) (C (T h14 (C (T (T (T (T h18 h20) (C (C h8 (C (T (T (T (T (T (T h21 (C (T (T (T (T (C h27 (T (T (C (C h22 h23) h22) (S h26)) h24)) (C (C h9 (T h28 h31)) h16)) (S h32)) (C (C h16 h29) h9)) h34) h22)) (C (T (T (T (T (T (T (T (T h33 (C (T (T (T (T (T h35 (C (T (T (T (T (T (T (T (C h8 (T (T (C (C h22 h36) h22) (S h39)) h37)) (C (T h41 (C h47 h43)) h40)) (S h50)) (C h122 h47)) h65) (C (T (C h47 h121) h42) h9)) h61) h57) h22)) (C (T (T (T (T h56 h67) (C h68 h9)) (S h72)) (C h22 h73)) h22)) (S h75)) h74) (C h9 (T h76 h81))) h9)) (S h80)) h79) h77) h82) (C (C h78 (T (T h83 (C (C h22 h84) h9)) (S h85))) h22)) (S h86)) (C h27 (T (T h87 h89) (C (C h22 h88) h22)))) h22)) (S h90)) h91) (C (C (T (T (T (T (T (T (T h93 h95) (C (C h9 (C (T (T h96 (C (C h99 h98) h97)) (S h100)) h16)) h16)) (S h101)) (S h102)) h103) h105) (C (T (T (C h8 h104) h106) (C h42 h97)) h8)) h92) h8)) (S h108)) h16)) h16)) (S h109)) (S h110)) h16)) (T (T (T (T (T (T (T (T (T (T (S h131) h115) h129) h128) h124) h127) (C (T (T h130 (h (M v2 v17) v4 v4)) (C (T (T (T (T (C h16 (S h130)) (C (C h22 h111) h16)) (S h114)) (C (T (T (T (T (T h115 h129) h128) h124) h127) (C h16 (T h112 h36))) h22)) (S h125)) h16)) h112)) (S (h x v126 v2))) (h x v126 y)) (C (T (T (T (T (T (T (C (T (T (T (T h125 (C (T (T (T (T (T (C h16 (T h37 h111)) (C (C h22 h43) h112)) (S h124)) h123) (C (T (T (T (C h22 (T (C h122 h9) h121)) h117) h120) h119) h9)) h116) h22)) h114) (C (C h22 h112) h16)) (C h16 h3)) h78) (S (h v6 v4 v0))) (C (T (T (T (T h110 h109) (C (C h8 (C (T (T (T (T (T (T h108 (C (C (T (T (T (T (T (T (T (C (T (T (C h41 h97) (S h106)) (C h8 h103)) h8) (S h105)) h104) h102) h101) (C (C h9 (C (T (T h100 (C (C h99 (S h98)) h97)) (S h96)) h16)) h16)) (S h95)) (S h93)) h92) h8)) (S h91)) h90) (C (T (T (T (T (T (T (T (T (C h27 (T (T (C (C h22 h87) h22) (S h89)) h88)) h86) (C (C h78 (T (T h85 (C (C h22 (S h84)) h9)) (S h83))) h22)) (S h82)) h76) h81) h80) (C (T (T (T (T (T (C h9 (T h79 h77)) h73) h75) (C (T (T (T (T (C h22 h74) h72) (C h69 h9)) h61) h57) h22)) (C (T (T (T (T (T (T (T h56 h67) (C (T h41 (C h47 h66)) h9)) (S h65)) (C h64 h47)) h50) (C (T (C h47 h44) h42) h40)) (C h8 (T (T h36 h39) (C (C h22 h37) h22)))) h22)) (S h35)) h9)) h34) h22)) (C (T (T (T (T h33 (C (C h16 h28) h9)) h32) (C (C h9 (T (S h31) h29)) h16)) (C h27 (T (T h23 h26) (C (C h22 h24) h22)))) h22)) (S h21)) h16)) h16)) (S h20)) (S h18)) h16)) h15) h10) h13) (C (C h8 h11) h8)) h9)) (C (T (T (C (C h8 h10) h8) (S h13)) h11) h9)))) h9)) (S (h v0 v7 y))) h8)) h8)) (S (h (M v0 v7) v4 v1))) (S (h v6 v0 v4))) (S h3)

