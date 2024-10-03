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
theorem Equation2917_implies_Equation1793 (G: Type _) [Magma G] (h: Equation2917 G) : Equation1793 G := fun x y z =>
  let v0 := M z y
  let v1 := M v0 x
  let v2 := M y z
  let v3 := M v2 v1
  have h4 := h v3 v3 v0
  have h5 := R v0
  let v6 := M (M v3 (M v3 v3)) v0
  have h7 := R v1
  have h8 := R v2
  have h9 := R v3
  have h10 := h y z z
  have h11 := R z
  have h12 := C h11 (S h10)
  let v13 := M (M z v2) z
  have h14 := h v13 z x
  have h15 := S h14
  have h16 := R x
  have h17 := C (C (C h11 h10) h16) h16
  let v18 := M v1 v3
  have h19 := h v1 v1 v2
  have h20 := S h19
  have h21 := h (M (M v1 (M v1 v1)) v2) v2 v2
  have h22 := h v2 z v3
  have h23 := C h9 (S h22)
  have h24 := C (T (T (C h23 h8) (C (C (C h8 h19) h8) h8)) (S h21)) h8
  let v25 := M z (M v2 z)
  let v26 := M v25 v3
  have h27 := h v26 v3 v2
  have h28 := h v26 v3 x
  have h29 := C h9 h22
  have h30 := h v2 v2 v3
  let v31 := M v2 (M v2 v2)
  have h32 := h (M v31 v3) v3 x
  have h33 := h v31 y v3
  have h34 := h (M v31 y) y x
  have h35 := h v2 v2 y
  have h36 := R y
  have h37 := h v2 x y
  have h38 := C h36 (S h37)
  let v39 := M x (M v2 x)
  have h40 := h (M v39 y) y x
  have h41 := h v39 y v3
  have h42 := h v39 y x
  have h43 := S h40
  have h44 := C h36 h37
  have h45 := h v2 z y
  have h46 := h (M v25 y) y x
  have h47 := h v25 y x
  have h48 := h v25 v3 x
  have h49 := S h27
  have h50 := C (T (T h21 (C (C (C h8 h20) h8) h8)) (C h29 h8)) h8
  have h51 := h v1 z v3
  have h52 := C h9 (S h51)
  have h53 := C h9 h51
  have h54 := h z v3 y
  have h55 := C h36 (S h54)
  have h56 := C (C h55 h7) h7
  let v57 := M (M v3 (M z v3)) y
  have h58 := h v57 y v1
  have h59 := h v57 y x
  have h60 := C h36 h54
  have h61 := h x y v2
  have h62 := C h8 (S h61)
  have h63 := C h8 h61
  have h64 := h x v3 v2
  have h65 := T (C h8 (S h64)) h63
  have h66 := C (T (T (T (T (T (C h65 h16) (C (T h62 (C h60 h16)) h16)) (S h59)) h58) h56) h53) h16
  let v67 := M (M v3 (M x v3)) v2
  have h68 := h v67 v2 x
  have h69 := h v67 v2 y
  have h70 := S h69
  have h71 := T h62 (C h8 h64)
  have h72 := C (C h71 h36) h36
  have h73 := h (M (M y (M x y)) v2) v2 y
  have h74 := S h73
  have h75 := C (C h65 h36) h36
  have h76 := S h68
  have h77 := S h58
  have h78 := C (C h60 h7) h7
  have h79 := C (T (T (T (T (T h52 h78) h77) h59) (C (T (C h55 h16) h63) h16)) (C h71 h16)) h16
  have h80 := h v1 v0 v3
  have h81 := T (C h9 (S h80)) h53
  let v82 := M (M v0 (M v1 v0)) v3
  have h83 := h v82 v3 x
  have h84 := h v82 v3 v2
  have h85 := T h52 (C h9 h80)
  have h86 := h v57 y v2
  have h87 := h v2 v2 v2
  have h88 := S h87
  have h89 := h (M v31 v2) v2 v2
  have h90 := h v3 v0 v2
  let v91 := M (M v0 (M v3 v0)) v2
  have h92 := h v3 z v2
  have h93 := h v1 v3 v1
  have h94 := h x v1 v0
  let v95 := M (M v1 (M x v1)) v0
  have h96 := h x x v0
  T (T h96 (C (T (T (T (T (T (T (T (h (M (M x (M x x)) v0) v0 x) (C (T (T (C (C h5 (S h96)) h16) h17) h15) h16)) (C (T (T h14 (C (C h12 h16) h16)) (C (C h5 h94) h16)) h16)) (S (h v95 v0 x))) (h v95 v0 v1)) (C (T (C (C h5 (S h94)) h7) (C h7 h93)) h7)) (C (T (C h7 (S h93)) (C (T (T (T (T (T (T h19 h50) h49) h28) (C (T (C h23 h16) (C (C h9 h30) h16)) h16)) (S h32)) (C (T (T (T (T (T (T (T (T (T (T (T (T h33 (C (C (C h36 (T (T h34 (C (C (T (C h36 (S h35)) h44) h16) h16)) h43)) h9) h9)) (S h41)) h42) (C (C (C h36 (T (T h40 (C (C (T h38 (C h36 h45)) h16) h16)) (S h46))) h16) h16)) (S h47)) h48) (C (T (T (T (T (T (C (T (C h9 (T (T h27 h24) h20)) h53) h16) h79) h76) h69) h75) h74) h16)) (C (T (T (T (T (T h73 h72) h70) h68) h66) (C h85 h16)) h16)) (S h83)) h84) (C (T (T (C h81 h8) (C (T (T (T (T h52 h78) h77) h86) (C (T (C h55 h8) (C h8 h87)) h8)) h8)) (S h89)) h8)) h88) (T h92 (C (T (T (T (T (T (T (h (M (M z (M v3 z)) v2) v2 x) (C (C (T (C h8 (S h92)) (C h8 h90)) h16) h16)) (S (h v91 v2 x))) (h v91 v2 v3)) (C (T (T (T (T (C (T (T (T (T (T (T (T (C h8 (S h90)) (C (T (T (T (T (T (T (T (T (T (T (T (T h87 (C (T (T h89 (C (T (T (T (T (C (T (C h8 h88) (C h60 h8)) h8) (S h86)) h58) h56) h53) h8)) (C h85 h8)) h8)) (S h84)) h83) (C (T (T (T (T (T (C h81 h16) h79) h76) h69) h75) h74) h16)) (C (T (T (T (T (T h73 h72) h70) h68) h66) (C (T h52 (C h9 (T (T h19 h50) h49))) h16)) h16)) (S h48)) h47) (C (C (C h36 (T (T h46 (C (C (T (C h36 (S h45)) h44) h16) h16)) h43)) h16) h16)) (S h42)) h41) (C (C (C h36 (T (T h40 (C (C (T h38 (C h36 h35)) h16) h16)) (S h34))) h9) h9)) (S h33)) h9)) h32) (C (T (C (C h9 (S h30)) h16) (C h29 h16)) h16)) (S h28)) h27) h24) h20) h9) (h v18 z x)) (C (C (C h11 (T (T (h (M v18 z) z x) (C (C (C h11 (S (h v2 v1 z))) h16) h16)) (S (h y z x)))) h16) h16)) h17) h15) h9)) (C (T (h v13 z v3) (C (T (C h12 h9) (C h5 h4)) h9)) h9)) (S (h v6 v0 v3))) h8)))) h7)) h7)) (S (h v6 v2 v1))) h5)) (S h4)

