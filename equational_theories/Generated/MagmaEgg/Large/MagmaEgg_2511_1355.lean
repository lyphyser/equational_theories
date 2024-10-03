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
theorem Equation2511_implies_Equation1355 (G: Type _) [Magma G] (h: Equation2511 G) : Equation1355 G := fun x y z =>
  let v0 := M z x
  let v1 := M v0 y
  let v2 := M v1 z
  let v3 := M y v2
  have h4 := h v3 z y
  have h5 := S h4
  have h6 := R y
  have h7 := h v0 y z
  have h8 := R z
  have h9 := C (C h8 (C h7 h6)) h6
  have h10 := h v1 v3 y
  have h11 := S h10
  have h12 := h y v2 z
  have h13 := R v2
  have h14 := T (C (C h13 h7) h8) (S h12)
  have h15 := R v1
  have h16 := h z v1 y
  have h17 := R v3
  have h18 := C (T h7 (C h17 (T h16 (C (C h15 (T h9 h5)) h6)))) h14
  have h19 := S h7
  have h20 := T h12 (C (C h13 h19) h8)
  have h21 := h v0 v0 z
  have h22 := S h21
  have h23 := C (C h8 (T (T (C h22 h20) h18) h11)) h6
  let v24 := M v0 (M (M v0 v0) z)
  have h25 := h v24 z y
  have h26 := h v24 z x
  have h27 := S h26
  have h28 := R x
  have h29 := h (M v0 x) y v0
  have h30 := S h29
  have h31 := R v0
  have h32 := h x v1 y
  have h33 := S h32
  have h34 := h z x y
  have h35 := C (T h18 h11) h34
  have h36 := h v2 v0 z
  have h37 := h v2 x v0
  have h38 := S h37
  have h39 := h (M x (M (M v2 x) v0)) v0 y
  have h40 := C (C h6 (T h37 (C (T h39 (C (C h31 (T (C (T (T h38 h36) h35) h6) h33)) h6)) h31))) h31
  have h41 := h v3 v3 z
  have h42 := C (S h41) h31
  have h43 := C h41 h31
  have h44 := S h36
  have h45 := C (C h8 (C h19 h6)) h6
  have h46 := C (T (C h17 (T (C (C h15 (T h4 h45)) h6) (S h16))) h19) h20
  have h47 := C (T h10 h46) (S h34)
  have h48 := C (C h6 (T (C (T (C (C h31 (T h32 (C (T (T h47 h44) h37) h6))) h6) (S h39)) h31) h38)) h31
  have h49 := h v0 v1 z
  have h50 := C (T (C h8 (T (T (T (C (S h49) h28) h29) h48) h43)) (C h8 (T (T (T h42 h40) h30) (C h21 h28)))) h28
  let v51 := M v1 (M (M v0 v1) z)
  have h52 := h v51 z x
  have h53 := h v51 x v2
  have h54 := S h53
  have h55 := S h52
  have h56 := C (T (C h8 (T (T (T (C h22 h28) h29) h48) h43)) (C h8 (T (T (T h42 h40) h30) (C h49 h28)))) h28
  have h57 := S h25
  have h58 := C (C h8 (T (T h10 h46) (C h21 h14))) h6
  have h59 := C (T (T (T (T (T (T h4 h45) h58) h57) h26) h56) h55) h28
  have h60 := C h59 h13
  have h61 := C h28 h60
  let v62 := M v3 x
  have h63 := h (M x (M v62 v2)) v2 x
  have h64 := S h63
  have h65 := h v3 x v2
  have h66 := h (M v2 v62) x v2
  have h67 := S h66
  have h68 := h y v2 x
  have h69 := C (C h28 (C h68 h13)) h13
  have h70 := C (T (T h69 h67) (C h13 (C h65 h28))) h28
  let v71 := M x v3
  let v72 := M v71 v2
  have h73 := h (M v72 x) v2 v3
  have h74 := C (C h28 (C (S h68) h13)) h13
  have h75 := C (T (T (C h13 (C (S h65) h28)) h66) h74) h28
  have h76 := C (T (T (T (T (T (T h52 h50) h27) h25) h23) h9) h5) h28
  have h77 := C h76 h13
  have h78 := C h28 h77
  have h79 := C (T (T h78 h63) h75) h13
  have h80 := T (T (T (T (T (T (T (T h4 h45) h58) h57) h26) h56) h55) h53) h79
  have h81 := C h80 h17
  have h82 := h v2 y v3
  have h83 := S h82
  have h84 := h (M y (M (M v2 y) v3)) v3 y
  have h85 := C (C h6 (T (C (T (C (C h17 (T h32 (C (T (T h47 h44) h82) h6))) h6) (S h84)) h17) h83)) h17
  have h86 := h v62 y v3
  have h87 := C (T (T h70 h64) h61) h13
  have h88 := C (T h87 h54) h28
  have h89 := C h13 (T (T (T (T h88 h76) h86) h85) h81)
  have h90 := C (T h53 h79) h28
  have h91 := C h13 (T h59 h90)
  have h92 := C (T (T (T h69 h67) h91) h89) h17
  have h93 := C (T (T (T (T h92 (S h73)) h70) h64) h61) h13
  have h94 := C h13 (T h88 h76)
  have h95 := S h86
  have h96 := C (C h6 (T h82 (C (T h84 (C (C h17 (T (C (T (T h83 h36) h35) h6) h33)) h6)) h17))) h17
  have h97 := T (T (T (T (T (T (T (T h87 h54) h52) h50) h27) h25) h23) h9) h5
  have h98 := C h97 h17
  have h99 := C h13 (T (T (T (T h98 h96) h95) h59) h90)
  have h100 := C (T (T (T h99 h94) h66) h74) h17
  have h101 := h v72 v3 v2
  have h102 := C (T (T (T (T (C h80 (T (T (T (T (T (T (T (T h93 h54) h52) h50) h27) h25) h23) h9) h5)) h98) h96) h95) h59) h13
  have h103 := h x v0 v2
  let v104 := M v0 (M (M x v0) v2)
  have h105 := h x v2 v2
  T (T (T (T (T (T (T (T (T (T (T h105 (C (T (T (T (T (h (M v2 (M (M x v2) v2)) v2 x) (C (C h13 (T (C (S h105) h28) (C h103 h28))) h28)) (S (h v104 v2 x))) (h v104 v2 v3)) (C (T (T (T (T (T (T (T (C h13 (T (T (T (T (T (T (C (S h103) h17) (h v71 v2 v3)) (C (C h13 (T h92 (C (T (T (T (T (T (T h99 h94) h66) h74) h101) h102) h77) h17))) h17)) (S (h v62 v2 v3))) h86) h85) h81)) h99) h94) h66) h74) h101) h102) h77) h17)) h13)) (C (T (C (T (T (T (T (T (T h60 (C (T (T (T (T h76 h86) h85) h81) (C h97 (T (T (T (T (T (T (T (T h4 h45) h58) h57) h26) h56) h55) h53) (C (T (T (T (T h78 h63) h75) h73) h100) h13)))) h13)) (S h101)) h69) h67) h91) h89) h17) h100) h13)) h93) h54) h52) h50) h27) h25) h23) h9) h5

