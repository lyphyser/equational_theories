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
theorem Equation895_implies_Equation1571 (G: Type _) [Magma G] (h: Equation895 G) : Equation1571 G := fun x y z =>
  let v0 := M x z
  let v1 := M y v0
  let v2 := M y z
  let v3 := M v2 v1
  let v4 := M v1 x
  have h5 := h v3 v3 (M v4 (M v3 x))
  have h6 := S h5
  have h7 := h v1 v3 x
  have h8 := R v3
  have h9 := C h8 (C h7 h7)
  let v10 := M v1 v1
  let v11 := M z x
  have h12 := h z v2 x
  have h13 := R v2
  let v14 := M z z
  have h15 := R v14
  have h16 := R z
  have h17 := R v10
  have h18 := h y z v0
  have h19 := S h18
  let v20 := M v0 x
  have h21 := h v0 v0 (M v11 v20)
  have h22 := S h21
  have h23 := h z v0 x
  have h24 := R v0
  have h25 := C h24 (C h23 h23)
  have h26 := T h25 h22
  have h27 := C h16 h26
  have h28 := h x z z
  have h29 := T h28 h27
  have h30 := h v1 v3 v3
  have h31 := S h30
  have h32 := T h9 h6
  have h33 := S h7
  have h34 := C h8 (C h33 h33)
  have h35 := R v1
  have h36 := h v2 v1 v1
  have h37 := S h36
  have h38 := T h5 h34
  have h39 := C h35 h38
  have h40 := T h39 h37
  have h41 := C h40 h35
  have h42 := C h35 h32
  have h43 := T h36 h42
  have h44 := C h43 (T (C (T (T h41 h5) h34) h8) (C h32 h8))
  let v45 := M v1 v3
  have h46 := h v45 v2 v1
  have h47 := C h32 (T (T (T h36 h42) h46) h44)
  have h48 := C h38 h13
  have h49 := T (T h48 h47) h31
  have h50 := R x
  have h51 := h (M v3 v2) v1 v3
  have h52 := S h51
  have h53 := S h46
  have h54 := C h43 h35
  have h55 := C h40 (T (C h38 h8) (C (T (T h9 h6) h54) h8))
  have h56 := T h55 h53
  have h57 := C h32 h13
  have h58 := C h38 (T (T (T h55 h53) h39) h37)
  have h59 := T (T h30 h58) h57
  have h60 := h (M v45 (M v3 v3)) v1 v1
  have h61 := T h46 h44
  have h62 := C (T h47 h31) (T (T (C h43 h13) (C h61 h13)) (C (T h60 (C h59 (T (T (T (C (C h56 h35) h17) (C h41 h17)) h9) h6))) h43))
  have h63 := R (M v2 v2)
  have h64 := C h48 h63
  have h65 := T (T h64 h62) h52
  have h66 := C h57 h63
  have h67 := T h30 h58
  have h68 := C h67 (T (T (C (T (C h49 (T (T (T h5 h34) (C h54 h17)) (C (C h61 h35) h17))) (S h60)) h40) (C h56 h13)) (C h40 h13))
  have h69 := T (T (T (T (T h30 h58) h57) h51) h68) h66
  have h70 := h z v0 v0
  have h71 := C h26 h24
  have h72 := S h23
  have h73 := C h24 (C h72 h72)
  have h74 := S h28
  have h75 := T h21 h73
  have h76 := C h16 h75
  have h77 := T h76 h74
  have h78 := C h77 h16
  have h79 := C (T (T h78 h21) h73) h24
  have h80 := C h29 (T h79 h71)
  let v81 := M z v0
  have h82 := h v81 x z
  have h83 := C (T (C h26 (T (T (T h28 h27) h82) h80)) (S h70)) (T (T (C h69 h50) (C h65 h50)) (C h49 h29))
  have h84 := R v4
  have h85 := S h82
  have h86 := C h29 h16
  have h87 := C h77 (T (C h75 h24) (C (T (T h25 h22) h86) h24))
  have h88 := C (T h87 h85) h16
  let v89 := M v0 v14
  have h90 := h v89 v1 x
  have h91 := S h90
  have h92 := T (T (T (T (T h64 h62) h52) h48) h47) h31
  have h93 := T (T h51 h68) h66
  have h94 := C (T h70 (C h75 (T (T (T h87 h85) h76) h74))) (T (T (C h59 h77) (C h93 h50)) (C h92 h50))
  have h95 := C h49 (T h18 h94)
  have h96 := R y
  have h97 := C h65 h96
  have h98 := C h69 h96
  have h99 := T (T (T (T (T h98 h97) h95) h91) h25) h22
  have h100 := R (M v1 y)
  T (T (T (T (T (T (T (T h28 h27) h82) h80) (h (M v81 (M v0 v0)) z z)) (C h16 (T (T (T (C h88 h15) (C h78 h15)) (h v89 v1 v1)) (C h67 (T (T (C (C h26 h35) h17) (h (M (M v0 v1) v10) z z)) (C h16 (T (T (C (C (T (T (T (C (C h75 h35) h17) (C (C (T (T (T h90 (C h59 (T h83 h19))) (C h93 h96)) (C h92 h96)) h35) h17)) (C (T (T (T (T (C h99 (T (h v1 v1 y) (C (C (T (T h18 h94) (C (C h26 h50) h84)) h24) (T (T (T (T (T (C h98 h100) (C h97 h100)) (C (T (T (T (T (T h95 h91) h25) h22) h86) (C (T h82 h80) h16)) h99)) (C h88 h24)) h79) h71)))) (S (h (M v20 v4) v0 v0))) (C (C h75 h50) h84)) h83) h19) h17)) (S (h y y v0))) h16) h15) (C h13 (C h12 h12))) (S (h v2 v2 (M v11 (M v2 x))))))))))) (S (h (M v3 v10) z v2))) h9) h6

