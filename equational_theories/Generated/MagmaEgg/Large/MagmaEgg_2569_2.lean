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
theorem Equation2569_implies_Equation2 (G: Type _) [Magma G] (h: Equation2569 G) : Equation2 G := fun x y =>
  let v0 := M (M y y) y
  let v1 := M y v0
  let v2 := M (M y v1) v1
  let v3 := M y v2
  let v4 := M x (M (M y x) x)
  have h5 := R y
  have h6 := R v2
  let v7 := M x v0
  let v8 := M x (M (M y v7) v7)
  have h9 := h y v7 v8
  have h10 := S h9
  have h11 := R v8
  have h12 := h v7 x y
  have h13 := h y x y
  have h14 := R v7
  have h15 := C (T h13 (C h14 (T h13 (C h12 h5)))) h11
  have h16 := T h15 h10
  have h17 := C h16 h11
  have h18 := h v8 y y
  have h19 := S h13
  have h20 := C (T (C h14 (T (C (S h12) h5) h19)) h19) h11
  have h21 := T h9 h20
  have h22 := C h21 h11
  have h23 := C (C h5 (T (T h9 h20) h22)) h5
  have h24 := C h21 (T h23 (S h18))
  have h25 := C (C h5 (T (T h17 h15) h10)) h5
  have h26 := C h5 (T (C (C h5 h24) (T (T (T h24 h17) h15) h10)) h25)
  have h27 := T (T (T (T h26 h24) h17) h15) h10
  have h28 := C h27 h6
  have h29 := R x
  have h30 := h v2 x y
  have h31 := S h30
  have h32 := C h16 (T h18 h25)
  have h33 := C h5 (T h23 (C (C h5 h32) (T (T (T h9 h20) h22) h32)))
  have h34 := T (T (T (T h9 h20) h22) h32) h33
  have h35 := C h34 h6
  have h36 := T (T (T (T (T h9 h20) h22) h32) h33) h35
  have h37 := C (C h29 h36) h5
  have h38 := C h34 (T h37 h31)
  have h39 := T (T (T (T (T h28 h26) h24) h17) h15) h10
  have h40 := C (C h29 h39) h5
  have h41 := h v2 y y
  have h42 := S h41
  let v43 := M (M x y) y
  have h44 := R v43
  have h45 := T (T (T (T (T (T h38 h28) h26) h24) h17) h15) h10
  have h46 := C h45 h44
  have h47 := h v43 y y
  let v48 := M (M y v43) v43
  have h49 := R (M y v48)
  have h50 := T (C h49 (T (T (T (T (T (T (T h46 h38) h28) h26) h24) h17) h15) h10)) (S h47)
  have h51 := C h27 (T h30 h40)
  have h52 := T (T (T (T (T (T h9 h20) h22) h32) h33) h35) h51
  have h53 := C h52 h50
  have h54 := h v48 y y
  have h55 := C (T (T h53 h54) (C (T (T (T (T (T (T (T (T h53 h46) h38) h28) h26) h24) h17) h15) h10) h36)) h5
  have h56 := h v48 x y
  have h57 := S h56
  have h58 := S h54
  have h59 := C h52 h44
  have h60 := T h47 (C h49 (T (T (T (T (T (T (T h9 h20) h22) h32) h33) h35) h51) h59))
  have h61 := C h45 h60
  have h62 := C (T (T (C (T (T (T (T (T (T (T (T h9 h20) h22) h32) h33) h35) h51) h59) h61) h39) h58) h61) h5
  have h63 := C (C h29 h60) (T (T (T (T (T (T (T (T (T (T (T (T h37 h31) h41) h62) h58) h46) h38) h28) h26) h24) h17) h15) h10)
  have h64 := C h5 (T (T (T (T (T (T h63 h57) h54) h55) h42) h30) h40)
  let v65 := M x v43
  let v66 := M v65 v43
  let v67 := M y v66
  have h68 := h v67 y y
  have h69 := h v67 x y
  have h70 := T (T (T (T (T (T (T h64 h38) h28) h26) h24) h17) h15) h10
  have h71 := R v67
  have h72 := C (C h29 h50) (T (T (T (T (T (T (T (T (T (T (T (T h9 h20) h22) h32) h33) h35) h51) h59) h54) h55) h42) h30) h40)
  have h73 := C h5 (T (T (T (T (T (T h37 h31) h41) h62) h58) h56) h72)
  have h74 := T (T (T (T (T (T (T h9 h20) h22) h32) h33) h35) h51) h73
  have h75 := R v66
  have h76 := C h70 h75
  have h77 := C (T (T (T (T (T (T (T (T (T (C h74 (T (T (T (T h76 h64) h59) h56) h72)) h76) h64) h38) h28) h26) h24) h17) h15) h10) h74
  have h78 := h v66 y y
  have h79 := T (T (T (T (T (T (T (T (T (T (T h9 h20) h22) h32) h33) h35) h51) h59) h56) h72) h78) h77
  have h80 := C h79 h71
  have h81 := T (T (T (T (T (T h64 h59) h56) h72) h78) h77) h80
  have h82 := S h78
  have h83 := C h74 h75
  have h84 := C (T (T (T (T (T (T (T (T (T h9 h20) h22) h32) h33) h35) h51) h73) h83) (C h70 (T (T (T (T h63 h57) h46) h73) h83))) h70
  have h85 := T (T (T (T (T (T (T (T (T (T (T h84 h82) h63) h57) h46) h38) h28) h26) h24) h17) h15) h10
  have h86 := C h85 h71
  have h87 := T (T (T (T (T (T h86 h84) h82) h63) h57) h46) h73
  have h88 := T (T (T (T (T (T (T (T (T h9 h20) h22) h32) h33) h35) h51) h73) h69) (C (C h29 h87) h74)
  let v89 := M (M x x) x
  let v90 := M y v89
  let v91 := M y (M (M x v90) v90)
  let v92 := M x v89
  have h93 := h x v92 v91
  have h94 := R v91
  have h95 := h v90 y x
  have h96 := h x y x
  have h97 := T h96 (C h95 h29)
  have h98 := R v92
  have h99 := h x x x
  T (T (T (T (T (T h93 (C (T (C h98 (T (C (S h95) h29) (S h96))) (S h99)) (T (T (T (h v91 y y) (C (T (T (T (T (T (T (T (T (T (C (T (T (T (T (T (T (T (T (T h9 h20) h22) h32) h33) h35) h51) h73) h68) (C (T (T (T (T (T (T (T (T (T (T (T (T (T (C h79 h87) h86) h84) h82) h63) h57) h46) h38) h28) h26) h24) h17) h15) h10) h88)) (T (T (C (T (C (T (h y x x) (C (R v65) h97)) h94) (S (h x v65 v91))) h94) (C (T h99 (C h98 h97)) h94)) (S h93))) (S (h v67 y x))) h64) h38) h28) h26) h24) h17) h15) h10) h88)) (C (T (T (T (T (T (T (T (T (T (T (T (T (T h9 h20) h22) h32) h33) h35) h51) h59) h56) h72) h78) h77) h80) (C h85 h81)) (T (T (T (T (T (T (T (T (T (C (C h29 h81) h70) (S h69)) h64) h38) h28) h26) h24) h17) h15) h10))) (S h68)))) (C h29 h64)) (C h29 h38)) (C h29 h28)) (C (T (h x x y) (C (R v4) (T (h y y y) (C (h v1 y y) h5)))) (R v3))) (S (h y v4 v3))

