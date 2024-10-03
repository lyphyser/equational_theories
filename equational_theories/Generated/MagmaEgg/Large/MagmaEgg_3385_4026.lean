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
theorem Equation3385_implies_Equation4026 (G: Type _) [Magma G] (h: Equation3385 G) : Equation4026 G := fun x y z =>
  let v0 := M z y
  let v1 := M z v0
  have h2 := h z v0 z
  have h3 := S h2
  let v4 := M v0 z
  let v5 := M z v4
  have h6 := h z v5 v1
  have h7 := S h6
  have h8 := R v1
  let v9 := M v1 x
  have h10 := h z v4 v9
  have h11 := R v9
  have h12 := h v0 z z
  have h13 := h z z y
  have h14 := S h13
  have h15 := R v0
  have h16 := h y z v0
  have h17 := R z
  have h18 := h z (M z (M y z)) v9
  have h19 := h z y z
  have h20 := T (T (T h19 h18) (C h11 (C h17 (C (T (C h17 (T h16 (C h15 h14))) (S h12)) h11)))) (S h10)
  have h21 := C h20 h8
  have h22 := h v0 v1 x
  have h23 := S h22
  have h24 := T (T (T h10 (C h11 (C h17 (C (T h12 (C h17 (T (C h15 h13) (S h16)))) h11)))) (S h18)) (S h19)
  have h25 := C h24 h11
  have h26 := h v1 x v9
  have h27 := S h26
  have h28 := h v1 (M x v9) x
  have h29 := R x
  have h30 := h v1 x z
  have h31 := S h30
  have h32 := h z (M v1 (M x z)) v9
  have h33 := S h32
  have h34 := h x z v0
  have h35 := S h34
  have h36 := h v0 x v1
  have h37 := C h11 (C h17 (C (T h36 (C h8 h35)) h11))
  have h38 := h z (M v0 x) v9
  have h39 := C h17 (C h24 h29)
  have h40 := C h29 (T (T (T (T h39 h38) h37) h33) h31)
  have h41 := h z v5 x
  have h42 := T (T h2 h41) h40
  have h43 := S h41
  have h44 := C h17 (C h20 h29)
  have h45 := S h38
  have h46 := C h11 (C h17 (C (T (C h8 h34) (S h36)) h11))
  have h47 := C h29 (T (T (T (T h30 h32) h46) h45) h44)
  have h48 := T (T h47 h43) h3
  have h49 := C h11 (T (C h29 (T (C h42 h11) (C h48 (C h42 h29)))) (S h28))
  have h50 := h x v1 v9
  have h51 := T (T h50 h49) h27
  have h52 := C h20 h51
  have h53 := C h29 (T (T h34 h52) h25)
  have h54 := C h17 (T (T h53 h23) h21)
  have h55 := h x x z
  have h56 := h x x v1
  have h57 := S h56
  have h58 := S h50
  have h59 := C h11 (T h28 (C h29 (T (C h42 (C h48 h29)) (C h48 h11))))
  have h60 := C h29 (T (T (T (T (T (T (T h39 h38) h37) h33) h31) h26) h59) h58)
  have h61 := C h48 (T (T h2 h41) h60)
  have h62 := C h8 (T (T (T h61 h57) h55) h54)
  have h63 := h x x v9
  have h64 := S h63
  have h65 := h x v1 x
  have h66 := C h51 (T (T (T h26 h59) h58) h65)
  have h67 := C h8 (T h66 h64)
  have h68 := T (T h26 h59) h58
  have h69 := C h68 (T (T (T (S h65) h50) h49) h27)
  have h70 := C h8 (T (T (T h61 h57) h63) h69)
  have h71 := C h29 (T (T (T (T (T (T (T h50 h49) h27) h30) h32) h46) h45) h44)
  have h72 := C h42 (T (T h71 h43) h3)
  have h73 := S h55
  have h74 := C h24 h68
  have h75 := C h20 h11
  have h76 := C h29 (T (T h75 h74) h35)
  have h77 := C h24 h8
  have h78 := C h17 (T (T h77 h22) h76)
  have h79 := C h8 (T (T (T h78 h73) h56) h72)
  have h80 := T (T (T (T h2 h6) h79) h70) h67
  have h81 := h v0 v1 v0
  have h82 := C h8 (T (T (T h66 h64) h56) h72)
  have h83 := C h8 (T h63 h69)
  have h84 := h z y v0
  have h85 := S h84
  have h86 := h z (M y v0) v9
  have h87 := h y v0 x
  have h88 := h v0 x v9
  have h89 := h x v0 v9
  have h90 := R y
  have h91 := h x z y
  have h92 := C h29 (T (T (T (T h75 h74) h35) h91) (C h90 (T (T h89 (C h11 (T (T h23 h21) (C h24 h42)))) (S h88))))
  have h93 := h z (M v0 v1) v9
  have h94 := C h42 h8
  have h95 := C h15 (T (T (T (T (T (T (T (T h94 h61) h57) h55) h54) (C h17 h77)) h93) (C h11 (C h17 (C (T (T h22 h92) (S h87)) h11)))) (S h86))
  have h96 := h v0 v1 v1
  have h97 := C h15 (T (T (T h96 (C h80 (T h95 h85))) (C (T (T (T (T (T h83 h82) h62) h7) h41) h40) h15)) (C h48 h15))
  have h98 := h v0 z v0
  have h99 := h v0 v0 z
  have h100 := S h99
  have h101 := S h96
  have h102 := C h48 h8
  have h103 := S h91
  have h104 := C h90 (T (T h88 (C h11 (T (T (C h20 h48) h77) h22))) (S h89))
  have h105 := T (T (T (T h83 h82) h62) h7) h3
  have h106 := C h105 (T h84 (C h15 (T (T (T (T (T (T (T (T h86 (C h11 (C h17 (C (T (T h87 (C h29 (T (T (T (T h104 h103) h34) h52) h25))) h23) h11)))) (S h93)) (C h17 h21)) h78) h73) h56) h72) h102)))
  have h107 := C (T (T (T (T (T h47 h43) h6) h79) h70) h67) h15
  have h108 := C h42 h15
  have h109 := C h17 (T (T (T h53 h23) h81) (C h15 (T (C h15 (T (T (T h108 h107) h106) h101)) (S h98))))
  T (T (T (h x y v1) (C h8 (T (T (C h29 h14) (C h29 (T (T (T (T (T (T (T (T h13 (h y v1 v1)) (C h80 (T (T (T (T (T (T (T (T (C h90 (T (T (T (T (T h94 h61) h57) h55) h109) h100)) (S (h v0 z y))) h98) h97) (C h15 (T (T (T (T (T (T h108 h107) h106) h101) h22) h92) (C h29 (T (T (T (T (T (T (T h104 h103) h34) h52) h25) (h v0 v9 v9)) (C h68 (T (T (C h15 (T (T (T (T (T (C h68 h11) h66) h64) h56) h72) h102)) h95) h85))) (C h51 h15)))))) (S (h x v9 v0))) h47) h43) h3))) (C h105 (T (T h2 h6) h79))) (C h8 (T (T (T h62 h7) h41) h60))) h57) h55) h109) h100))) (C h29 (T (T (T (T (T h99 (C h17 (T (T (T (C h15 (T h98 h97)) (S h81)) h22) h76))) h73) h56) (C h8 (T (T (T h71 h43) h6) h79))) (C h80 (T (T h62 h7) h3))))))) (S (h x (M v1 (M x x)) v1))) (S (h v1 x x))

