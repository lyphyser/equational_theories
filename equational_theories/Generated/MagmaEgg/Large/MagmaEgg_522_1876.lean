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
theorem Equation522_implies_Equation1876 (G: Type _) [Magma G] (h: Equation522 G) : Equation1876 G := fun x y z =>
  let v0 := M z y
  let v1 := M y z
  let v2 := M x v1
  let v3 := M v2 v0
  have h4 := h y z z
  have h5 := S h4
  have h6 := h v1 v1 x
  have h7 := S h6
  have h8 := h x v1 v1
  have h9 := S h8
  have h10 := h v2 v2 x
  have h11 := S h10
  have h12 := h x v2 v1
  have h13 := R v2
  have h14 := h v1 v2 v2
  have h15 := R x
  have h16 := C h15 (T h14 (C h13 (S h12)))
  have h17 := C h13 (C h13 h16)
  have h18 := R v1
  have h19 := C h18 (C h18 (T h17 h11))
  have h20 := h v2 v1 v2
  have h21 := C h18 (T (T (T h17 h11) h20) h19)
  have h22 := C h18 (T h21 h9)
  have h23 := C h15 (T (C h13 h12) (S h14))
  have h24 := C h13 (C h13 h23)
  have h25 := S h20
  have h26 := C h18 (C h18 (T h10 h24))
  have h27 := C h18 (T (T (T h26 h25) h10) h24)
  have h28 := h x v2 v2
  have h29 := S h28
  have h30 := C h18 (T h8 h27)
  have h31 := C h15 (T h30 h25)
  have h32 := C h13 h31
  have h33 := C h13 h32
  have h34 := h v1 v2 x
  have h35 := C h18 (T (T (T (C h13 (T h34 h33)) h29) h8) h27)
  have h36 := C h15 (T h35 h22)
  have h37 := S h34
  have h38 := C h15 (T h20 h22)
  have h39 := C h13 h38
  have h40 := C h13 h39
  have h41 := C h18 (T (T (T h21 h9) h28) (C h13 (T h40 h37)))
  have h42 := h v2 x v1
  have h43 := C h15 (T h30 h41)
  have h44 := C h15 (T (T (T (C h15 h43) (S h42)) h20) h41)
  have h45 := h v1 x x
  have h46 := T (T h45 h44) h36
  have h47 := C h18 (C h18 h46)
  have h48 := R z
  have h49 := C h48 (T h47 h7)
  have h50 := C h48 h49
  have h51 := h v1 z v1
  have h52 := C h48 (T (T (T h47 h7) h51) h50)
  have h53 := C h48 (T h52 h5)
  have h54 := h v1 v2 v0
  have h55 := S h54
  have h56 := S h45
  have h57 := C h15 (T (T (T h35 h25) h42) (C h15 h36))
  have h58 := S h51
  have h59 := T (T h43 h57) h56
  have h60 := C h18 (C h18 h59)
  have h61 := C h48 (T h6 h60)
  have h62 := C h48 h61
  have h63 := C h48 (T (T (T h62 h58) h6) h60)
  have h64 := C h48 (T h4 h63)
  have h65 := T h64 h58
  have h66 := R v0
  have h67 := C h66 (C h65 (T (T (T (T h43 h57) h56) h51) h53))
  have h68 := h v1 v0 x
  have h69 := h v1 v0 v1
  have h70 := S h69
  have h71 := T (T (T (T h43 h57) h56) h6) h60
  have h72 := T h51 h53
  have h73 := C h72 (T (C h66 h46) (C h66 h71))
  have h74 := T (T (T h73 h70) h68) h67
  have h75 := T (T (T (T h47 h7) h45) h44) h36
  have h76 := C h65 (T (C h66 h75) (C h66 h59))
  have h77 := C h13 (T (T (T (T (T h40 h37) h45) h44) h36) h31)
  have h78 := h x v1 x
  have h79 := C h13 (T (T (T (T (T h38 h43) h57) h56) h34) h33)
  have h80 := h x x v2
  have h81 := h v2 v1 v1
  have h82 := C h13 (T (T (T (T (T (T (T (T (T (C h66 h16) (C h66 (T (T h23 h10) h24))) (C h65 (T (T (T (T h17 h11) h81) (C h18 (T (T (T (C h18 (T h35 h19)) h9) h28) h77))) (C h18 (T (T (T h79 h29) h80) (C h15 (C h15 (T h79 h29)))))))) (S h78)) h28) h77) h39) (C h13 h71)) (C h13 (T (T (T h47 h7) h69) h76))) (C h13 h74))
  have h83 := R v3
  have h84 := C h66 (T (T h17 h11) h16)
  have h85 := S h80
  have h86 := C h15 (C h15 (T h28 h77))
  have h87 := C h72 (T (T (T (T (C h18 (T (T (T h86 h85) h28) h77)) (C h18 (T (T (T h79 h29) h8) (C h18 (T h26 h41))))) (S h81)) h10) h24)
  have h88 := S h68
  have h89 := C h66 (C h72 (T (T (T (T h64 h58) h45) h44) h36))
  have h90 := T (T (T h89 h88) h69) h76
  have h91 := C h13 (T (T (T (T (T (T (T (T (T (C h13 h90) (C h13 (T (T (T h73 h70) h6) h60))) (C h13 h75)) h32) h79) h29) h78) h87) h84) (C h66 h23))
  have h92 := h v0 z v2
  have h93 := h y v0 z
  have h94 := h y v1 z
  have h95 := R (M v1 (M z v1))
  have h96 := C h66 (T (T (T (T (C h65 h95) (S h94)) h4) h63) h49)
  have h97 := h z v0 v1
  have h98 := S h97
  have h99 := C h66 (T (T (T (T h61 h52) h5) h94) (C h72 h95))
  have h100 := R y
  T (T (h x v3 x) (C h83 (C h83 (T (T (T (T (T h86 h85) h78) h87) h84) (C h66 (T (T (T (T (T h23 (h v2 v3 v1)) (C h83 (T (T (C h83 (T (T (T h35 h25) (h v2 v3 v0)) (C h83 (C h83 (C h65 h83))))) (S (h v1 v3 v3))) (C h100 (T (T h97 h96) (C h65 (T (T h61 h52) h5))))))) (C h83 (T (T (T (T (C h100 (T (T (C h72 (T (T h4 h63) h49)) h99) h98)) h51) h53) h92) (C h48 (T (T (T (T (T (C h48 (T (T (T h82 h55) h68) h67)) (C h48 h90)) (C h48 (T (T (T h73 h70) h51) h50))) h5) h93) (C h65 (T h99 h98))))))) (C h83 (T (T (T (T (T (C h48 (T (T (T (T (T (C h72 (T h97 h96)) (S h93)) h4) (C h48 (T (T (T h62 h58) h69) h76))) (C h48 h74)) (C h48 (T (T (T h89 h88) h54) h91)))) (S h92)) h64) h58) h54) h91))) (C h83 (T (T (T h82 h55) h51) h53)))))))) (S (h v3 v3 v0))

