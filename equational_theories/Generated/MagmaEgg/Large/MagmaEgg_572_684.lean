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
theorem Equation572_implies_Equation684 (G: Type _) [Magma G] (h: Equation572 G) : Equation684 G := fun x y z =>
  let v0 := M y z
  let v1 := M v0 z
  let v2 := M x v1
  let v3 := M y v2
  have h4 := h y z v1
  have h5 := S h4
  have h6 := h v0 z z
  have h7 := S h6
  have h8 := R v1
  have h9 := C h8 h7
  have h10 := h z v1 z
  have h11 := h z v1 y
  have h12 := h v1 z z
  have h13 := S h12
  have h14 := S h10
  have h15 := C h8 h6
  have h16 := T h15 h14
  have h17 := R z
  have h18 := C h17 (C h8 h16)
  have h19 := C h17 (T h4 h18)
  have h20 := C h17 h19
  have h21 := C h17 (T h20 h13)
  have h22 := R y
  have h23 := h z y z
  have h24 := h v0 v1 v0
  have h25 := S h24
  have h26 := R v0
  have h27 := C h26 h16
  have h28 := C h26 h27
  have h29 := C h26 h28
  have h30 := h v1 v0 v0
  have h31 := C h26 (T (T h27 h30) h29)
  have h32 := T h10 h9
  have h33 := C h26 h32
  have h34 := C h26 h33
  have h35 := C h8 (T h34 h31)
  have h36 := h v0 v1 v1
  have h37 := C h17 (T h36 (C h8 (T (T (T (C h8 (T (T h35 h25) (C h22 (T h23 (C h22 h21))))) (S h11)) h10) h9)))
  have h38 := T h37 h5
  have h39 := R v3
  have h40 := S h30
  have h41 := C h26 h34
  have h42 := C h26 (T (T h41 h40) h33)
  have h43 := C h8 (T h42 h28)
  have h44 := C h17 (C h8 h32)
  have h45 := C h17 (T h44 h5)
  have h46 := C h17 h45
  have h47 := C h17 (T h12 h46)
  have h48 := C h17 (T (C h8 (T (T (T h15 h14) h11) (C h8 (T (T (C h22 (T (C h22 h47) (S h23))) h24) h43)))) (S h36))
  have h49 := h y z z
  have h50 := S h49
  have h51 := C h17 (T h44 h48)
  have h52 := C h17 h51
  have h53 := R x
  have h54 := h v1 v2 v1
  have h55 := S h54
  have h56 := h x v1 v1
  have h57 := R v2
  have h58 := C h57 h56
  have h59 := T h58 h55
  have h60 := C h57 (S h56)
  have h61 := C h17 (T h37 h18)
  have h62 := C h17 h61
  have h63 := T (T h12 h52) h50
  have h64 := T (T h49 h62) h13
  have h65 := h v2 x v0
  have h66 := S h65
  have h67 := T (T (T (T (T (T h37 h5) h49) h62) h13) h30) h29
  have h68 := C h26 h67
  have h69 := C h26 (T (C h26 (T h68 h42)) h29)
  have h70 := h z v0 v0
  have h71 := h z y v1
  have h72 := T (T (T (T (T (T h41 h40) h12) h52) h50) h4) h48
  have h73 := C h17 h72
  have h74 := h v0 z v0
  have h75 := R (M v0 v1)
  have h76 := C h64 h75
  have h77 := C h64 (T (T (T (T (T (T h76 h35) h25) h74) h73) h61) h45)
  have h78 := h v0 v1 y
  have h79 := S h74
  have h80 := C h17 h67
  have h81 := C h63 h75
  have h82 := h v0 y v0
  have h83 := S h82
  have h84 := C h26 h38
  have h85 := C h26 h72
  have h86 := C h26 (T h41 (C h26 (T h31 h85)))
  have h87 := C h26 (T h4 h48)
  have h88 := C h63 (T (T (T h87 h68) h86) (C h26 (C h26 h84)))
  have h89 := R (M v0 y)
  have h90 := C h64 h89
  have h91 := C h63 h89
  have h92 := C h64 (T (T (T (C h26 (C h26 h87)) h69) h85) h84)
  have h93 := h v0 y v1
  have h94 := S h93
  have h95 := C h64 (T h82 h92)
  have h96 := C h22 h95
  have h97 := C h63 (T h88 h83)
  have h98 := C h22 h97
  have h99 := C h63 (T (T (T h88 h83) h93) h98)
  have h100 := C h64 (T (T (T h96 h94) h82) h92)
  have h101 := h y v0 y
  have h102 := C h53 (T (T h101 (C h26 (T h100 h97))) (C h26 (T (T (T (T (T (T (T (T (T (T (T h95 h99) (C h22 (T (T (T (T h96 h94) h82) h92) h91))) (C h22 (T (T (T (T (T h90 h88) h83) h24) h43) h81))) h77) (C h63 (T (T (T (T (T h19 h51) h80) h79) h78) (C h8 h77)))) (S h71)) h70) h69) h42) h28) (C h26 (T h54 h60)))))
  have h103 := S h101
  have h104 := C h26 (T h95 h99)
  have h105 := C h63 (T (T (T (T (T (T h19 h51) h80) h79) h24) h43) h81)
  have h106 := C h26 (T (T (T (T (T (T (T (T (T (T (T (C h26 h59) h34) h31) h86) (S h70)) h71) (C h64 (T (T (T (T (T (C h8 h105) (S h78)) h74) h73) h61) h45))) h105) (C h22 (T (T (T (T (T h76 h35) h25) h82) h92) h91))) (C h22 (T (T (T (T h90 h88) h83) h93) h98))) h100) h97)
  have h107 := C h17 (T (T (T h41 h40) h12) h46)
  T (T (T (h x y x) (C h22 (T (T (T (C h53 (C h53 (T (T (T h102 h66) (h v2 x z)) (C h53 (T (T (T (T (T (C h17 (T (T (T (T (C h17 (T (T (T (T h58 h55) h12) h46) (C h17 (T (T (T (T h19 h51) h80) h107) h21)))) h7) h74) h107) h21)) (C h17 (T (T (T (T h47 (C h17 (T (T (T h20 h13) h30) h29))) h73) h61) h45))) h20) h13) h54) h60))))) (S (h v2 x x))) h65) (C h53 (T (T h106 h104) h103))))) (C h22 (T (T h102 (C h53 (T (T (T (T h106 h104) h103) (h y x v3)) (C h53 (T (C h39 (T (T (T (T (T (T (C h39 (C h22 (T (T (T (h x y v1) (C h22 (C h8 (C h63 (T h102 h66))))) (C h64 (R (M v1 v3)))) (C h63 (C h63 h39))))) (S (h y v3 y))) h49) h62) h13) h54) h60)) (C h39 h59)))))) (C h53 (C h53 (T (C h39 (T (T (T (T h12 h52) h50) h4) h48)) (C h39 h38))))))) (S (h v3 y x))

