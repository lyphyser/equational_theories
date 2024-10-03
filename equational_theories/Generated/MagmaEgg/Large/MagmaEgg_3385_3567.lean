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
theorem Equation3385_implies_Equation3567 (G: Type _) [Magma G] (h: Equation3385 G) : Equation3567 G := fun x y z =>
  let v0 := M z x
  let v1 := M v0 z
  have h2 := h y v1 z
  have h3 := S h2
  have h4 := h v1 z v0
  have h5 := h z v0 z
  have h6 := S h5
  have h7 := R v1
  have h8 := h z z v1
  have h9 := h z z x
  have h10 := R v0
  have h11 := h x z v0
  have h12 := R y
  have h13 := R z
  have h14 := C h13 (C h12 (T (T h11 (C h10 (T (T (S h9) h8) (C h7 h6)))) (S h4)))
  have h15 := h y x z
  have h16 := S (h y x v0)
  have h17 := h x v0 v0
  have h18 := h v0 z x
  have h19 := T (C h10 h18) (S h17)
  have h20 := C h12 h19
  have h21 := S h18
  have h22 := C h10 h21
  have h23 := h x v0 v1
  have h24 := S h23
  have h25 := R x
  have h26 := h x v0 z
  let v27 := M y v1
  have h28 := h z (M x v1) v27
  have h29 := R v27
  have h30 := h x v1 x
  have h31 := S h30
  have h32 := h v1 x v27
  have h33 := S h32
  have h34 := h x y v1
  have h35 := C h29 h34
  have h36 := h x y x
  have h37 := h x (M y x) v27
  have h38 := S h15
  have h39 := S h8
  have h40 := C h12 (T (T h4 (C h10 (T (T (C h7 h5) h39) h9))) (S h11))
  have h41 := C h13 h40
  have h42 := T (T h2 h41) h38
  have h43 := h x v27 v27
  have h44 := h x x v27
  have h45 := C h25 (C h25 (T (T (T h44 (C h29 (T (C h25 (T (T h43 (C h29 (C h25 (C h42 h29)))) (S h37))) (S h36)))) h35) h33))
  have h46 := h x x x
  have h47 := T (T h46 h45) h31
  have h48 := h z (M x x) v27
  have h49 := C h25 (T (T (T h48 (C h29 (C h13 (C h47 h29)))) (S h28)) (S h26))
  have h50 := h z x x
  have h51 := C h7 (T (T h50 h49) (C h25 (T h17 h22)))
  have h52 := h v1 v0 z
  have h53 := S h52
  have h54 := h v1 v1 v0
  have h55 := h z v1 v1
  have h56 := h z v1 v0
  have h57 := S h50
  have h58 := S h46
  have h59 := S h43
  have h60 := T (T h15 h14) h3
  have h61 := C h29 (C h25 (C h60 h29))
  have h62 := C h25 (T (T (T h32 (C h29 (S h34))) (C h29 (T h36 (C h25 (T (T h37 h61) h59))))) (S h44))
  have h63 := C h25 h62
  have h64 := C h25 (T (T (T h26 h28) (C h29 (C h13 (C (T (T h30 h63) h58) h29)))) (S h48))
  have h65 := h z x v0
  have h66 := T (C h10 (T (T (T (T h65 (C h10 (C h13 (T h23 (C h7 (T (T (C h25 h19) h64) h57)))))) (S h56)) h55) (C h7 h53))) (S h54)
  have h67 := C h13 h66
  have h68 := C h10 (T (T (T (T (C h7 h52) (S h55)) h56) (C h10 (C h13 (T h51 h24)))) (S h65))
  have h69 := T h54 h68
  have h70 := C h25 h69
  have h71 := C h7 (T h70 h21)
  have h72 := h x v1 v1
  have h73 := h x x v1
  have h74 := S h73
  have h75 := S h72
  have h76 := C h25 h66
  have h77 := C h7 (T h18 h76)
  have h78 := h v0 z v0
  have h79 := h z v0 v1
  have h80 := h v0 v0 z
  have h81 := h v1 v0 v0
  have h82 := h z v0 v0
  have h83 := C h7 (T (T (T (T (T (T h6 h82) (C h10 (T (T (T h67 h53) h81) (C h10 (T (C h7 h80) (S h79)))))) (S h78)) h18) h76) (C h25 (T h77 h75)))
  let v84 := M x y
  have h85 := C h25 (T h72 h71)
  have h86 := R v84
  have h87 := C h86 (T (T (T (T (T (C h25 (T h35 h33)) h62) (C h25 h47)) h85) h70) h21)
  have h88 := h x v27 v84
  have h89 := h x z x
  have h90 := S h89
  have h91 := h y v0 z
  have h92 := S h91
  have h93 := C h13 (T h92 (C h12 (T (T h50 h49) h90)))
  have h94 := C h42 (T (T h93 h14) h3)
  have h95 := h z z v27
  have h96 := T (T h18 h76) (C h25 (T (T (T (T (T (T (T (T (T h77 h75) h30) h63) h58) h73) (C h7 (T (T (T (T (T (T h85 h70) h21) h78) (C h10 (T (T (T (C h10 (T h79 (C h7 (S h80)))) (S h81)) h52) (C h13 h69)))) (S h82)) h5))) h39) h95) h94))
  have h97 := C h12 (T (T h89 h64) h57)
  have h98 := h y x y
  have h99 := S h98
  have h100 := C h12 (T (T (T (T (T (T (T (C h13 (T (h y y v84) (C h86 (T (T (T h99 h15) h14) h3)))) (C h13 (T (T (T (T (T (T (T (T (T (T (T (T (C h86 (T (T (T h2 h41) h38) h98)) (C h86 (T (T (T h99 h15) h14) (C h13 (T (T (T (T (T h40 h97) h91) (h z v27 v1)) (C h7 (C h13 (T (T (T (T (C h29 h96) h61) h59) h88) h87)))) (S (h z v84 v1))))))) (S (h z z v84))) h8) h83) h74) h46) h45) h31) h72) h71) h54) h68))) h67) h53) h51) h24) h17) h22)
  have h101 := h z y y
  have h102 := h z y v0
  have h103 := C h13 (T h97 h91)
  T (T (T (T (T (h x y v0) (C h10 (T (T (T (T (T (T (T (S (h y z x)) (h y z v84)) (C h86 (S (h z x y)))) (C h86 (T (T (T (T h50 h49) h90) (h x z z)) (C h13 (T (T (T (T (T (T (T (C h25 (T h95 h94)) (C h25 (T (T (T (T (T (T (T (T (T (C h60 (T (T h2 h41) h103)) (S h95)) h8) h83) h74) h46) h45) h31) h72) h71))) h70) h21) (h v0 z y)) (h y (M v0 (M z y)) v1)) (C h7 (C h12 (T (T (T (T (C (T (T (T (T (T (C h10 (T h102 (C h10 (T (T (T (C h13 h91) h93) h14) h3)))) (C h10 (T (T (T (T (C h10 (T (T (T h2 h41) h103) (C h13 h92))) (S h102)) h101) h100) h20))) h16) h15) h14) h3) h96) h61) h59) h88) h87)))) (S (h y v84 v1))))))) (S (h z y v84))) h101) h100) h20))) h16) h15) h14) h3

