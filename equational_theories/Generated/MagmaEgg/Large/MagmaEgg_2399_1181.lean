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
theorem Equation2399_implies_Equation1181 (G: Type _) [Magma G] (h: Equation2399 G) : Equation1181 G := fun x y z =>
  let v0 := M z x
  let v1 := M z v0
  let v2 := M v1 y
  let v3 := M y v2
  have h4 := R v3
  let v5 := M y (M y v3)
  have h6 := R v5
  have h7 := h y y x
  have h8 := S h7
  let v9 := M y (M x (M x y))
  have h10 := R v9
  have h11 := R v1
  let v12 := M v1 (M x (M x v1))
  have h13 := h v1 x v12
  have h14 := S h13
  have h15 := R x
  have h16 := h v1 v1 x
  have h17 := R v12
  have h18 := C (C h15 (T h16 (C h17 h16))) h15
  have h19 := h x x z
  have h20 := h x v0 z
  let v21 := M v0 (M x (M x v0))
  have h22 := h v0 z v21
  have h23 := S h22
  have h24 := R z
  have h25 := h v0 v0 x
  have h26 := R v21
  have h27 := C (C h24 (T h25 (C h26 h25))) h24
  let v28 := M z (M x (M x z))
  let v29 := M z v1
  have h30 := h z v29 v28
  have h31 := S h30
  have h32 := R v29
  have h33 := h z z x
  have h34 := R v28
  have h35 := h x z z
  have h36 := S h19
  have h37 := S h16
  have h38 := C (C h15 (T (C h17 h37) h37)) h15
  have h39 := C (T (T (T (T h13 h38) h36) h35) (C h32 (T h33 (C h34 h33)))) h32
  have h40 := T h39 h31
  have h41 := T (T h19 h18) h14
  have h42 := C h41 h40
  let v43 := M v1 v29
  have h44 := R v43
  have h45 := T (T h13 h38) h36
  have h46 := C h45 h44
  have h47 := S h33
  have h48 := C (T (T (T (T (C h32 (T (C h34 h47) h47)) (S h35)) h19) h18) h14) h32
  have h49 := T h30 h48
  have h50 := C h24 (T (T (T h46 h42) h27) h23)
  have h51 := C h50 h49
  have h52 := h v29 z v1
  have h53 := S h52
  have h54 := C h41 h44
  have h55 := C h45 h49
  have h56 := S h25
  have h57 := C (C h24 (T (C h26 h56) h56)) h24
  have h58 := C h24 (T (T (T h22 h57) h55) h54)
  have h59 := C h58 h40
  have h60 := C h11 (T h59 h53)
  have h61 := C h58 (T (T h60 h39) h31)
  have h62 := C h11 (T h52 h51)
  have h63 := h v43 x v1
  have h64 := S h63
  have h65 := R (M v1 (M v1 v43))
  have h66 := C h50 (T (T h30 h48) h62)
  have h67 := C (T (T (T (T (T (T h22 h57) h55) h54) h59) h66) (C h45 h65)) h45
  have h68 := C h11 (T (T h67 h64) h62)
  have h69 := C (T (T (T (T (T (T (C h41 h65) h61) h51) h46) h42) h27) h23) h41
  have h70 := C h11 (T (T h68 h61) h53)
  have h71 := T (T h70 h63) h69
  have h72 := C h11 h71
  let v73 := M v0 v1
  have h74 := R (M v1 (M v1 v73))
  have h75 := C h41 h74
  have h76 := C h11 (T (T h60 h63) h69)
  have h77 := C h11 (T (T h52 h66) h76)
  have h78 := T (T h67 h64) h77
  have h79 := C h15 h78
  have h80 := C h45 (T (T (T (C h41 (T (T h79 h75) h72)) h70) h63) h69)
  have h81 := R (M x (M x v73))
  have h82 := C h41 h81
  have h83 := C h15 h71
  have h84 := C h45 h74
  have h85 := C h11 h78
  have h86 := C h41 (C h41 h54)
  have h87 := R (M x (M x v43))
  have h88 := C h45 h87
  have h89 := C h11 (C h45 (T (T h22 h57) h55))
  have h90 := C h45 (C h45 (T (T (T (T (T (T h89 h88) h86) h76) h85) h84) h83))
  have h91 := C h11 (C h41 (T (T h42 h27) h23))
  have h92 := C h41 h87
  have h93 := C h45 (C h45 h46)
  have h94 := C h41 (C h41 (T (T (T (T (T (T h79 h75) h72) h68) h93) h92) h91))
  have h95 := C h45 h81
  have h96 := C h41 (T (T (T h67 h64) h77) (C h45 (T (T h85 h84) h83)))
  have h97 := R v2
  T (T (h x v3 z) (C (T (C h4 (T (T (T (T (T h13 h38) h36) h20) (C (T (T (T h67 h64) h39) h31) (T (T (T (T (T (T (T (T (T (T (T (T h22 h57) h55) h54) h59) h66) h76) h85) h84) h83) h96) h95) h94))) (C h24 (T (T (T (T (T (T (T (T (T h90 h82) h80) h79) h75) h72) h68) h93) h92) h91)))) (C h4 (T (T (h (M z (M v1 (M v1 v0))) v3 v2) (C (C h4 (C h97 (T (T (T (T (C h97 (T (T (T (T (T (C h24 (T (T (T (T (T (T (T (T (T h89 h88) h86) h76) h85) h84) h83) h96) h95) h94)) (C (T (T (T h30 h48) h63) h69) (T (T (T (T (T (T (T (T (T (T (T (T h90 h82) h80) h79) h75) h72) h68) h61) h51) h46) h42) h27) h23))) (S h20)) h19) h18) h14)) (C (C h11 (T h7 (C h10 h7))) h11)) (S (h y v1 v9))) (h y v5 v9)) (C (T (C h6 (T (C h10 h8) h8)) (S (h v2 y y))) h6)))) h4)) (S (h v5 v3 v2))))) h4)) (S (h v3 v3 y))

