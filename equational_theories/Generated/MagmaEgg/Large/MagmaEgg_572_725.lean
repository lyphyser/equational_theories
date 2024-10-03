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
theorem Equation572_implies_Equation725 (G: Type _) [Magma G] (h: Equation572 G) : Equation725 G := fun x y z =>
  let v0 := M z x
  let v1 := M v0 z
  let v2 := M y v1
  let v3 := M y v2
  have h4 := h v3 z v3
  have h5 := S h4
  have h6 := h z v1 z
  have h7 := S h6
  have h8 := h v0 z z
  have h9 := R v1
  have h10 := C h9 h8
  have h11 := T h10 h7
  have h12 := R v3
  have h13 := C h12 h11
  have h14 := S h8
  have h15 := C h9 h14
  have h16 := h z v0 v0
  have h17 := S h16
  have h18 := h v0 v1 v1
  have h19 := S h18
  have h20 := R v0
  have h21 := C h20 h11
  have h22 := C h20 h21
  have h23 := T h6 h15
  have h24 := C h20 h23
  have h25 := h v1 v0 v0
  have h26 := S h25
  have h27 := C h20 h24
  have h28 := C h20 h27
  have h29 := C h20 (T (T h28 h26) h24)
  have h30 := C h9 (T h29 h22)
  have h31 := h v0 v1 v0
  have h32 := C h9 (T (T h14 h31) h30)
  have h33 := C h9 (T h6 h32)
  have h34 := C h9 (T (T (T h33 h19) h31) h30)
  have h35 := C h9 h34
  have h36 := R z
  have h37 := C h36 (T h35 h19)
  have h38 := h v1 z v1
  have h39 := C h20 (T (T (T h28 h26) h38) h37)
  have h40 := C h20 h22
  have h41 := C h20 (T (T h21 h25) h40)
  have h42 := S h38
  have h43 := S h31
  have h44 := C h9 (T h27 h41)
  have h45 := C h9 (T (T h44 h43) h8)
  have h46 := C h9 (T h45 h7)
  have h47 := C h9 (T (T (T h44 h43) h18) h46)
  have h48 := C h9 h47
  have h49 := C h36 (T h18 h48)
  have h50 := C h20 (T (T (T h49 h42) h25) (C h20 (T h41 h39)))
  have h51 := C h12 (T (T (T (T (T (T h27 h41) h39) h50) h17) h6) h15)
  have h52 := C h12 h51
  have h53 := C h20 (T (T (T h49 h42) h25) h40)
  have h54 := C h20 (T (T (T (C h20 (T h53 h29)) h26) h38) h37)
  have h55 := h z v0 y
  have h56 := R y
  have h57 := C h56 (T h38 h37)
  have h58 := T (T (T (T (T (T (C h20 (C h56 h57)) (S h55)) h16) h54) h53) h29) h22
  have h59 := C h12 h58
  have h60 := C h12 h59
  have h61 := h v0 v3 v3
  have h62 := C h36 (T (T (T h35 h19) h61) (C h12 (T (T h60 h52) (C h12 h13))))
  have h63 := S h61
  have h64 := T h49 h42
  have h65 := C h56 (C h56 h64)
  have h66 := T (T (T (T (T (T h27 h41) h39) h50) h17) h55) (C h20 h65)
  have h67 := C h12 h66
  have h68 := C h12 h67
  have h69 := C h12 (T (T (T (T (T (T h10 h7) h16) h54) h53) h29) h22)
  have h70 := C h12 h69
  have h71 := C h12 h23
  have h72 := C h36 (T (T (T (C h12 (T (T (C h12 h71) h70) h68)) h63) h18) h48)
  have h73 := T (T h4 h72) h42
  have h74 := C h73 h58
  have h75 := T (T h38 h62) h5
  have h76 := C h75 h66
  have h77 := R v2
  have h78 := h v3 v2 v3
  have h79 := S h78
  let v80 := M v3 v2
  have h81 := R (M v3 v80)
  have h82 := C h75 h81
  have h83 := h y v1 v3
  have h84 := C h77 (T h83 h82)
  have h85 := C h77 (T (C h73 h81) (S h83))
  have h86 := h y v1 y
  have h87 := S h86
  have h88 := R (M y v3)
  have h89 := C h73 h88
  have h90 := h v1 y v1
  have h91 := C h73 h56
  have h92 := R (M v3 y)
  have h93 := C h12 (T h89 h87)
  have h94 := h y v3 v3
  have h95 := C h75 h88
  have h96 := C h12 (T h86 h95)
  have h97 := C h75 h56
  have h98 := h v3 z z
  have h99 := h v3 z v1
  have h100 := C h36 (T (T (T (T h38 h62) h5) h99) (C h36 (T (T (T (T (T (T (T (C h75 (C h75 (T (T h71 h69) h67))) h63) h31) h30) h76) h59) h51) h13)))
  have h101 := S h99
  have h102 := C h36 (T (T (T (T (T (T (T h71 h69) h67) h74) h44) h43) h61) (C h73 (C h73 (T (T h59 h51) h13))))
  have h103 := C h36 (C h36 (T (T (T (T h102 h101) h4) h72) h42))
  have h104 := R x
  T (T (T (T (T (h x z z) (C h36 (T (T (T (T (T (T (T (C h36 (T (T (T (T (T (C h36 (T (C h104 (T (T (T (T h16 h54) h53) h29) h22)) (C h104 (T (T (T (T (T (T h27 h41) h39) h50) h17) (h z x v3)) (C h104 (T (T (C h12 (C h12 (T h18 h46))) (C h12 (T (T (T (T (T (T (C h12 (T (T (T (T (T (T h33 h19) h31) h30) h76) h59) h51)) h70) h68) (C h73 (T (T (T (T h74 h44) h43) h18) h46))) h34) h45) h15))) h13)))))) (S (h v3 z x))) (h v3 v2 v2)) (C h77 (C h77 (T (T (T (C h77 (T (T (T (T (T (C h12 (T (T (T (h v2 y y) (C h56 (T (T (T (T (T (T (C h56 (T (T (C h56 (T (T (T (T h84 h79) h98) h103) (C h36 (T (T h100 (C h36 (T (T (T h102 h101) h98) h103))) (C h36 (T (T (T (C h36 h100) (S h98)) h78) h85)))))) (S (h v2 y z))) h57)) h65) h4) h72) h42) h90) (C h56 (T (C h75 (T (T (T (T (T (C h75 h97) (C h73 h92)) (C h75 h96)) (S h94)) h86) h95)) h93))))) (C h56 (C h56 h91))) (C h56 (T (T (T (T (T (C h56 h97) (C h56 (T h96 (C h73 (T (T (T (T (T h89 h87) h94) (C h73 h93)) (C h75 h92)) (C h73 h91)))))) (S h90)) h38) h62) h5)))) h89) h87) h83) h82) (C h73 (C h73 (R v80))))) (S (h v3 v2 v1))) h78) h85)))) (C h77 (C h77 (T (T (T (T h84 h79) h4) h72) h37)))) (C h77 (C h77 h64)))) (S (h v0 z v2))) h31) h30) h76) h59) h51) (C h12 (T (T (T (T (T (T h10 h32) h47) (C h75 (T (T (T (T h33 h19) h31) h30) h76))) h60) h52) (C h12 (T (T (T (T (T (T h69 h67) h74) h44) h43) h18) h46))))))) (S (h v1 z v3))) h38) h62) h5

