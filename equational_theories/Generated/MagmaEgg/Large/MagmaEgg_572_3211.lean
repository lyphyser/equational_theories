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
theorem Equation572_implies_Equation3211 (G: Type _) [Magma G] (h: Equation572 G) : Equation3211 G := fun x y z =>
  let v0 := M y z
  let v1 := M v0 z
  let v2 := M v1 x
  let v3 := M v2 y
  have h4 := h v3 y v3
  have h5 := S h4
  have h6 := h y v0 v0
  have h7 := S h6
  have h8 := h z v0 v3
  have h9 := S h8
  have h10 := h v0 z v2
  have h11 := S h10
  have h12 := h v1 z z
  have h13 := S h12
  have h14 := h z v1 z
  have h15 := h v0 z z
  have h16 := R v1
  have h17 := R z
  have h18 := C h17 (C h16 (T (C h16 h15) (S h14)))
  have h19 := h y z v1
  have h20 := C h17 (T h19 h18)
  have h21 := C h17 h20
  have h22 := h y v3 y
  have h23 := S h22
  have h24 := h v2 y y
  have h25 := R v3
  have h26 := C h25 h24
  have h27 := T h26 h23
  have h28 := R v2
  have h29 := C h28 (T (T (C h17 (C h17 h27)) h21) h13)
  have h30 := h v3 v2 z
  have h31 := C h28 (T h30 h29)
  have h32 := C h17 h31
  have h33 := C h25 (C h17 (T h32 h11))
  have h34 := h v2 v3 z
  have h35 := C h25 (T h34 h33)
  have h36 := R v0
  have h37 := C h36 h35
  have h38 := S h24
  have h39 := C h25 h38
  have h40 := T h22 h39
  have h41 := C h36 h40
  have h42 := R y
  have h43 := C h42 (T (T h41 h37) h9)
  have h44 := C h42 h43
  have h45 := C h36 h27
  have h46 := S h34
  have h47 := S h30
  have h48 := S h19
  have h49 := C h17 (C h16 (T h14 (C h16 (S h15))))
  have h50 := C h17 (T h49 h48)
  have h51 := C h17 h50
  have h52 := C h28 (T (T h12 h51) (C h17 (C h17 h40)))
  have h53 := C h28 (T h52 h47)
  have h54 := C h17 h53
  have h55 := C h25 (C h17 (T h10 h54))
  have h56 := C h25 (T h55 h46)
  have h57 := C h36 h56
  have h58 := C h42 (T (T h8 h57) h45)
  have h59 := h v0 y y
  have h60 := S h59
  have h61 := C h42 h58
  have h62 := C h42 h61
  have h63 := C h42 (T (T h62 h60) h58)
  have h64 := C h36 (T h63 h44)
  have h65 := h y v0 y
  have h66 := C h36 (T (T (T (T h56 h26) h23) h65) h64)
  have h67 := C h36 (T h8 h66)
  have h68 := C h17 (T (T (T (T (T h21 h13) h67) h7) h19) h18)
  have h69 := S h65
  have h70 := C h42 h44
  have h71 := C h42 (T (T h43 h59) h70)
  have h72 := C h36 (T h61 h71)
  have h73 := C h36 (T (T (T (T h72 h69) h22) h39) h35)
  have h74 := C h36 (T h73 h9)
  have h75 := h z y z
  have h76 := C h17 (T (T (T (T (T h49 h48) h6) h74) h12) h51)
  have h77 := h z y y
  have h78 := C h36 (T (T (T (T (T (T (C h36 (T (T (T h67 h7) h65) h64)) h73) h9) h77) (C h42 (T (T (T (C h42 (T (T (T (T (C h42 (T h20 h76)) (S h75)) h8) h57) h45)) h43) h59) h70))) h63) h44)
  have h79 := h v0 z v0
  have h80 := C h17 (T (T (T (T h32 h11) h79) (C h17 (T (T (T (T (T (T h78 h72) h69) h6) h74) h12) h51))) h68)
  have h81 := C h25 (T (T (T (T (T (T (T h80 h13) h67) h7) h22) h39) h35) (C h25 (T h55 (C h25 (T (T (T h80 h13) h67) h7)))))
  have h82 := h v2 v1 v2
  have h83 := C h42 (T h34 h81)
  have h84 := C h28 (T (T (T h83 h5) h30) h29)
  have h85 := C h36 (T (T (T (T (T (T h61 h71) (C h42 (T (T (T h62 h60) h58) (C h42 (T (T (T (T h41 h37) h9) h75) (C h42 (T h68 h50))))))) (S h77)) h8) h66) (C h36 (T (T (T h72 h69) h6) h74)))
  have h86 := C h17 (T (T (T (T h76 (C h17 (T (T (T (T (T (T h21 h13) h67) h7) h65) h64) h85))) (S h79)) h10) h54)
  have h87 := C h25 (T (T (T (T (T (T (T (C h25 (T (C h25 (T (T (T h6 h74) h12) h86)) h33)) h56) h26) h23) h6) h74) h12) h86)
  have h88 := C h42 (T h87 h46)
  have h89 := C h28 (T (T (T h52 h47) h4) h88)
  have h90 := C h28 (T h31 h89)
  have h91 := C h28 (C h28 (C h28 h27))
  have h92 := h v3 v2 v2
  have h93 := T h6 h74
  have h94 := T h67 h7
  have h95 := C h94 (T (T (T (C h93 (T (T (T h92 h91) h90) (C h28 h84))) (S h82)) h34) h81)
  have h96 := R (M y v3)
  have h97 := C h93 h96
  have h98 := S h92
  have h99 := C h28 (C h28 (C h28 h40))
  have h100 := C h28 (T h84 h53)
  have h101 := C h94 (T (T (T (C h28 h89) h100) h99) h98)
  have h102 := C h94 (T (T h83 (C h93 (T (T (T h87 h46) h82) h101))) (C h94 h96))
  have h103 := R (M y v2)
  have h104 := C h93 h103
  have h105 := C h28 (T (T (T (T h100 h99) h98) h4) h88)
  have h106 := h y v2 v2
  have h107 := R x
  T (T (T (T (T (T (h x y v3) (C h42 (T (T (T (T (C h25 (T (T (T (T (T (C h25 (T (C h107 (T (T (T h106 h105) h84) h53)) (C h107 (T (T (T (T (T (T (T h31 h89) (C h28 (T (T (T (T h83 h5) h92) h91) h90))) (S h106)) h6) h74) (h v1 x y)) (C h107 (T (T (T (T h104 h102) h38) h82) h101)))))) (S (h y v3 x))) h65) h64) h85) (C h36 (T (C h36 (T (T (T (T h67 h7) h65) h64) h85)) (C h36 (T (T (T (T (T (T h78 h72) h69) h106) h105) h84) h53)))))) (S (h v2 v3 v0))) h24) (C h93 (T (T h97 h95) h88))) (C h94 h103)))) (C h93 h104)) (C h94 (T (T (T h102 h38) h82) h101))) h97) h95) h5

