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
theorem Equation572_implies_Equation2992 (G: Type _) [Magma G] (h: Equation572 G) : Equation2992 G := fun x y z =>
  let v0 := M z y
  let v1 := M y v0
  let v2 := M v1 x
  let v3 := M v2 z
  have h4 := h v3 v1 v3
  have h5 := S h4
  have h6 := h v1 v0 v0
  have h7 := S h6
  have h8 := h v0 v1 v0
  have h9 := S h8
  have h10 := h y v0 v0
  have h11 := R v1
  have h12 := C h11 h10
  have h13 := h y v0 y
  have h14 := S h13
  have h15 := h z y y
  have h16 := h z y v3
  have h17 := S h16
  have h18 := R v3
  have h19 := R y
  have h20 := C h19 (C h18 (C h18 (T h12 h9)))
  have h21 := h v1 y v3
  have h22 := R v0
  have h23 := C h11 (T (C h22 (T (T (T h21 h20) h17) h15)) h14)
  have h24 := R (M v0 v1)
  have h25 := S h21
  have h26 := C h11 (S h10)
  have h27 := C h19 (C h18 (C h18 (T h8 h26)))
  have h28 := T (T h16 h27) h25
  have h29 := C h28 h24
  have h30 := C h28 (T (T (T h29 h23) h12) h9)
  have h31 := T (T h21 h20) h17
  have h32 := C h31 h24
  have h33 := S h15
  have h34 := C h11 (T h13 (C h22 (T (T (T h33 h16) h27) h25)))
  have h35 := h v0 v1 z
  have h36 := S h35
  have h37 := C h31 (T (T (T h8 h26) h34) h32)
  have h38 := C h11 h37
  have h39 := C h31 (T (T (T (T (T h38 h36) h8) h26) h34) h32)
  have h40 := C h22 (T h39 h30)
  have h41 := h v1 v0 v1
  have h42 := h z v3 z
  have h43 := S h42
  have h44 := h v2 z z
  have h45 := C h18 h44
  have h46 := C h22 (T (T h45 h43) h15)
  have h47 := C h22 (T h46 (C h22 (T (T (T (T (T h33 h16) h27) h25) h41) h40)))
  have h48 := S h44
  have h49 := C h18 h48
  have h50 := C h22 (T (T h33 h42) h49)
  have h51 := C h22 (T h13 h50)
  have h52 := C h22 (T h46 h14)
  have h53 := S h41
  have h54 := C h11 h30
  have h55 := C h28 (T (T (T (T (T h29 h23) h12) h9) h35) h54)
  have h56 := C h22 (T h37 h55)
  have h57 := C h22 (T (C h22 (T (T (T (T (T h56 h53) h21) h20) h17) h15)) h50)
  have h58 := h v1 v0 z
  have h59 := S h58
  have h60 := h v0 v1 v1
  have h61 := h v0 y v0
  have h62 := R (M y v1)
  have h63 := h y v1 z
  have h64 := h y v0 v2
  have h65 := R v2
  have h66 := C h65 (T h47 h7)
  have h67 := h v3 v2 v0
  have h68 := C h65 (T h67 h66)
  have h69 := C h22 (T (T (T (C h22 h68) (S h64)) h63) (C h31 (T (T (T (C h28 (T (T (C h28 h62) (C h11 (T (T (T (C h19 (T h6 (C h22 (C h22 (T (T (T (T h56 h53) h6) h57) h52))))) (S h61)) h35) h54))) h39)) h36) h60) (C h31 (T (C h31 h32) h30)))))
  have h70 := C h18 (T (T (T (T h69 h59) h6) h57) h52)
  have h71 := h v2 v3 v0
  have h72 := C h18 (T (T (T (T (T (T (T h69 h59) h21) h20) h17) h42) (C h18 (T (T h48 h71) h70))) (C h18 (C h18 (T (T h51 h47) h7))))
  have h73 := h v2 v1 v2
  have h74 := S h73
  have h75 := C h11 (T h71 h72)
  have h76 := C h65 (T (T (T h75 h5) h67) h66)
  have h77 := C h65 h76
  have h78 := S h71
  have h79 := S h67
  have h80 := C h65 (T h6 h57)
  have h81 := C h65 (T h80 h79)
  have h82 := C h22 (T (T (T (C h28 (T (T (T (C h28 (T h37 (C h28 h29))) (S h60)) h35) (C h31 (T (T h55 (C h11 (T (T (T h38 h36) h61) (C h19 (T (C h22 (C h22 (T (T (T (T h51 h47) h7) h41) h40))) h7))))) (C h31 h62))))) (S h63)) h64) (C h22 h81))
  have h83 := C h18 (T (T (T (T h51 h47) h7) h58) h82)
  have h84 := C h18 (T (T h83 h78) h44)
  have h85 := T (T h6 h57) h52
  have h86 := C h18 (C h18 h85)
  have h87 := C h18 (T (T (T (T (T (T (T h86 h84) h43) h16) h27) h25) h58) h82)
  have h88 := C h11 (T h87 h78)
  have h89 := C h65 (T (T (T h80 h79) h4) h88)
  have h90 := C h65 (T h68 h89)
  have h91 := C h65 (C h65 (C h65 (T h45 h43)))
  have h92 := h v3 v2 v2
  have h93 := C h11 (T (T (T h92 h91) h90) h77)
  have h94 := C h28 (T (T (T h93 h74) h71) h72)
  have h95 := R (M v1 v3)
  have h96 := C h31 h95
  have h97 := S h92
  have h98 := C h65 (C h65 (C h65 (T h42 h49)))
  have h99 := C h65 (T h76 h81)
  have h100 := C h11 (T (T (T (C h65 h89) h99) h98) h97)
  have h101 := h v2 z v1
  have h102 := S h101
  have h103 := R z
  have h104 := C h103 (T (T h75 (C h31 (T (T (T h87 h78) h73) h100))) (C h28 h95))
  have h105 := R (M v1 v2)
  have h106 := C h31 h105
  have h107 := C h65 (T (T (T (T h99 h98) h97) h4) h88)
  have h108 := h v1 v2 v2
  have h109 := R x
  T (T (T (T (T (T (h x v1 v3) (C h11 (T (T (T (T (C h18 (T (T (T (C h18 (T (T (C h109 h85) (C h109 (T (T (T (T (T (T h51 h47) h7) h108) h107) h76) h81))) (C h109 (T (T (T (T (T h68 h89) (C h65 (T (T (T (T h75 h5) h92) h91) h90))) (S h108)) (h v1 x v1)) (C h109 (T (T (T (T h106 h104) h102) h73) h100)))))) (S (h v1 v3 x))) (h v1 v3 v1)) (C h18 (T (T (T (T (T (T (C h31 h96) (C h28 (T (T (T (T (T h94 h5) h92) h91) h90) h77))) h74) h71) h72) (C h18 (T h86 (C h18 (T (T (T h83 h78) h73) h100))))) (C h18 (T (T (T (T (T (T (T (T (T (C h18 (T (T (T h93 h74) h71) h70)) h84) h43) h16) h27) h25) h108) h107) h76) h81)))))) (S (h v2 v3 v3))) h101) (C h103 (T (T h96 h94) h88))) (C h28 h105)))) (C h31 h106)) (C h28 (T (T (T h104 h102) h73) h100))) h96) h94) h5

