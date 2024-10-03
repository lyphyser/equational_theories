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
theorem Equation2349_implies_Equation2399 (G: Type _) [Magma G] (h: Equation2349 G) : Equation2399 G := fun x y z =>
  have h0 := R y
  let v1 := M z x
  let v2 := M z v1
  let v3 := M y v2
  have h4 := h v3 x v3
  have h5 := S h4
  let v6 := M x (M x (M v3 v3))
  have h7 := R v6
  have h8 := C (T (C h7 h5) h5) h0
  have h9 := h v2 v6 y
  have h10 := h v1 v2 v2
  have h11 := S h9
  have h12 := C (T h4 (C h7 h4)) h0
  let v13 := M v3 y
  let v14 := M x (M x (M v13 v13))
  have h15 := h y v14 v3
  have h16 := S h15
  have h17 := R v3
  have h18 := h v13 x v13
  have h19 := R v14
  have h20 := C (T h18 (C h19 h18)) h17
  let v21 := M y (M y v13)
  let v22 := M x (M x (M y y))
  have h23 := h v3 v22 v21
  have h24 := S h23
  have h25 := R v21
  have h26 := h y y v3
  have h27 := R v22
  have h28 := h y x y
  have h29 := C (T h28 (C h27 (T h28 (C h27 h26)))) h25
  have h30 := T h9 h8
  have h31 := C h30 (T h29 h24)
  have h32 := T (T h31 h20) h16
  have h33 := C h17 h32
  have h34 := h (M y v21) v2 v2
  have h35 := S h34
  have h36 := R v2
  have h37 := S h28
  have h38 := C (T (C h27 (T (C h27 (S h26)) h37)) h37) h25
  have h39 := T h12 h11
  have h40 := C h39 (T h23 h38)
  have h41 := S h18
  have h42 := C (T (C h19 h41) h41) h17
  let v43 := M v2 (M v2 v3)
  let v44 := M x (M x (M v2 v2))
  have h45 := h y v44 v43
  have h46 := R v43
  have h47 := h v2 v2 y
  have h48 := R v44
  have h49 := h v2 x v2
  have h50 := R (M v2 (M v2 v43))
  have h51 := C (T (C h30 h50) (C h39 (C h36 (T (T (T (T (C (T h49 (C h48 (T h49 (C h48 h47)))) h46) (S h45)) h15) h42) h40)))) h36
  have h52 := h v43 v2 v2
  have h53 := C h39 (T (T h52 h51) h35)
  have h54 := C h17 h53
  have h55 := h v43 v1 y
  have h56 := S h52
  have h57 := S h49
  have h58 := C (T (C h30 (C h36 (T (T (T (T h31 h20) h16) h45) (C (T (C h48 (T (C h48 (S h47)) h57)) h57) h46)))) (C h39 h50)) h36
  have h59 := R v1
  let v60 := M y v3
  have h61 := R v60
  have h62 := h v1 x v1
  have h63 := S h62
  have h64 := h v1 y z
  let v65 := M x (M x (M v1 v1))
  have h66 := R v65
  have h67 := h z v65 v60
  have h68 := R z
  have h69 := h x v65 z
  have h70 := T (T h69 (C (T (C h66 h63) h63) h68)) (C h59 (T (T h67 (C (T (C h66 (T (C h66 (S h64)) h63)) h63) h61)) (C h59 (C h0 (T (T (T (T h23 h38) h34) h58) h56)))))
  have h71 := C h70 (T (T (T h53 h31) h20) h16)
  have h72 := C h30 (T (T h34 h58) h56)
  have h73 := R x
  have h74 := C h73 h72
  have h75 := T (T h15 h42) h40
  have h76 := C h73 h75
  have h77 := R v13
  have h78 := C h77 (T (T (T h76 h74) h71) (S h55))
  have h79 := C h17 h78
  have h80 := C h73 h32
  have h81 := C h73 h53
  have h82 := T (T (C h59 (T (T (C h59 (C h0 (T (T (T (T h52 h51) h35) h29) h24))) (C (T h62 (C h66 (T h62 (C h66 h64)))) h61)) (S h67))) (C (T h62 (C h66 h62)) h68)) (S h69)
  have h83 := C h82 (T (T (T h15 h42) h40) h72)
  have h84 := T (T (T (C h70 (T (T (T (T h78 h53) h31) h20) h16)) h83) h81) h80
  have h85 := R (M x (M v13 (M x y)))
  have h86 := C h77 (T (T (T h55 h83) h81) h80)
  have h87 := T (T (T h76 h74) h71) (C h82 (T (T (T (T h15 h42) h40) h72) h86))
  have h88 := C h17 (T (T (C h36 h87) (C h30 h85)) (C h77 h84))
  let v89 := M v2 (M v2 v1)
  have h90 := R v89
  have h91 := h x v2 z
  have h92 := h z z v89
  have h93 := C h17 (T (T (C h77 h87) (C h39 h85)) (C h36 h84))
  have h94 := C h17 h86
  have h95 := C h17 h72
  have h96 := C h17 h75
  let v97 := M z (M z v13)
  have h98 := T (C (C h68 (C h68 h91)) h90) (S h92)
  T (T (T (T (T (T (T (h x v13 z) (C (T (C h39 (R (M v13 v1))) (C h36 (T (C h77 (T h10 (C h98 (T (T (C h68 (T h10 (C h98 (T (T (T (T (T h9 h8) h96) h95) h94) h93)))) (C h68 (C h68 h88))) (C h68 (C h68 (T (T h79 h54) h33))))))) (C h39 (R (M z v97)))))) h68)) (S (h v97 v2 z))) (C h68 (C h68 (T (T h96 h95) h94)))) (C h68 (C h68 h93))) (C h68 (T (C (T h92 (C (C h68 (C h68 (S h91))) h90)) (T (T (T (T (T h88 h79) h54) h33) h12) h11)) (S h10)))) h9) h8

