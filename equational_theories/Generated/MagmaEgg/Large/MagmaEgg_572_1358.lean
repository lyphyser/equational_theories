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
theorem Equation572_implies_Equation1358 (G: Type _) [Magma G] (h: Equation572 G) : Equation1358 G := fun x y z =>
  let v0 := M z x
  let v1 := M v0 z
  let v2 := M v1 y
  let v3 := M y v2
  have h4 := h v3 y y
  have h5 := S h4
  have h6 := h y v3 y
  have h7 := S h6
  have h8 := h v1 y y
  have h9 := R y
  have h10 := R v3
  have h11 := C h10 (C h9 h8)
  have h12 := h z v1 z
  have h13 := S h12
  have h14 := h v0 z z
  have h15 := R v1
  have h16 := C h15 h14
  have h17 := T h16 h13
  have h18 := R v0
  have h19 := C h18 h17
  have h20 := S h14
  have h21 := C h15 h20
  have h22 := h z v0 v2
  have h23 := S h22
  have h24 := h v0 v1 v1
  have h25 := S h24
  have h26 := C h18 h19
  have h27 := T h12 h21
  have h28 := C h18 h27
  have h29 := h v1 v0 v0
  have h30 := S h29
  have h31 := C h18 h28
  have h32 := C h18 h31
  have h33 := C h18 (T (T h32 h30) h28)
  have h34 := T h33 h26
  have h35 := C h15 h34
  have h36 := h v0 v1 v0
  have h37 := C h15 (T (T h20 h36) h35)
  have h38 := C h15 (T h12 h37)
  have h39 := C h15 (T (T (T h38 h25) h36) h35)
  have h40 := R z
  have h41 := h v1 z v1
  have h42 := R v2
  have h43 := C h42 (T h41 (C h40 (T (C h15 h39) h25)))
  have h44 := S h8
  have h45 := C h42 h44
  have h46 := h y v2 y
  have h47 := C h42 (T (T h46 h45) h43)
  have h48 := C h18 h47
  have h49 := C h9 (T (C h18 (T (T (T h48 h23) h12) h21)) h19)
  have h50 := h v2 y v0
  have h51 := h v2 y v2
  have h52 := S h51
  have h53 := S h46
  have h54 := C h42 h8
  have h55 := S h36
  have h56 := C h18 h26
  have h57 := C h18 (T (T h19 h29) h56)
  have h58 := T h31 h57
  have h59 := C h15 h58
  have h60 := C h15 (T (T h59 h55) h14)
  have h61 := C h15 (T h60 h13)
  have h62 := C h15 (T (T (T h59 h55) h24) h61)
  have h63 := C h42 (T (C h40 (T h24 (C h15 h62))) (S h41))
  have h64 := C h42 (T (T h63 h54) h53)
  have h65 := C h10 (T h50 h49)
  have h66 := C h42 (T (T (T (T (T h65 h11) h7) h46) h45) h43)
  have h67 := C h42 (C h42 (T h66 h64))
  have h68 := h v3 v2 v2
  have h69 := C h9 (T h68 h67)
  have h70 := C h10 (T (T (T h69 h52) h50) h49)
  have h71 := C h10 (T (T h70 h11) h7)
  have h72 := S h68
  have h73 := S h50
  have h74 := C h18 h64
  have h75 := C h9 (T h28 (C h18 (T (T (T h16 h13) h22) h74)))
  have h76 := C h10 (T h75 h73)
  have h77 := C h10 (C h9 h44)
  have h78 := C h42 (T (T (T (T (T h63 h54) h53) h6) h77) h76)
  have h79 := C h42 (C h42 (T h47 h78))
  have h80 := C h9 (T h79 h72)
  have h81 := C h10 (T (T (T h75 h73) h51) h80)
  have h82 := h y v3 v3
  have h83 := C h10 (T (T h6 h77) h81)
  have h84 := h v3 y v3
  have h85 := C h9 (T h69 (C h9 (T (T (T h79 h72) h84) (C h9 (T (C h10 (T (T (T (T (C h10 h83) (S h82)) h6) h77) h81)) h71)))))
  have h86 := h v0 v1 v3
  have h87 := S h86
  have h88 := T (T h8 h85) h5
  have h89 := C h88 h34
  have h90 := C h88 (T (T (T h38 h25) h36) h89)
  have h91 := C h9 (T (C h9 (T (T (T (C h9 (T h83 (C h10 (T (T (T (T h70 h11) h7) h82) (C h10 h71))))) (S h84)) h68) h67)) h80)
  have h92 := T (T h4 h91) h44
  have h93 := C h92 (T (T (T h12 h37) h62) h90)
  have h94 := C h10 h17
  have h95 := C h10 h27
  have h96 := C h92 h58
  have h97 := C h92 (T (T (T h96 h55) h24) h61)
  have h98 := C h88 (T (T (T h97 h39) h60) h13)
  have h99 := C h10 (T (T (T (T h96 h55) h86) h98) h95)
  have h100 := R (M v3 z)
  have h101 := h v1 v2 v1
  have h102 := S h101
  have h103 := h y v3 v1
  have h104 := C h42 (T (T (T (T h65 h11) h7) h103) (C h92 (C h15 (C h15 (T h69 h52)))))
  have h105 := C h42 (T (T (T (T (C h88 (C h15 (C h15 (T h51 h80)))) (S h103)) h6) h77) h76)
  have h106 := R x
  T (T (T (T (T (h x z z) (C h40 (T (T (T (T (T (T (C h40 (T (T (T (T (T (T (T (T (C h40 (T (T (C h106 (T (T (T h22 (C h18 (T (T (T (T h78 h104) h102) h29) h56))) h33) h26)) (C h106 (T (T (T (T h31 h57) (C h18 (T (T (T (T h32 h30) h101) h105) h66))) h74) (C h18 (T (T (T (T (T (T h47 h78) h104) h102) h8) h85) h5))))) (C h106 (T (T (T (T (C h18 (T (T (T (T (T (T h4 h91) h44) h101) h105) h66) h64)) h48) h23) (h z x v3)) (C h106 (T (T (C h10 (C h10 (T h24 h61))) (C h10 (T (T (T (T (T (C h10 (T (T (T (T h38 h25) h86) h98) h95)) (C h10 (T (T (T (T h94 h93) h87) h36) h89))) h97) h39) h60) h21))) h94)))))) (S (h v3 z x))) h4) h91) h44) h101) h105) h66) h64)) (C h40 (T (T (T (T (T (T (T (T h47 h78) h104) h102) h8) h85) h5) (h v3 z z)) (C h40 (C h40 (T (T (T (T (C h40 (T (C h92 (T (T (T (T (T (T h12 h37) h62) h90) h99) (C h10 h94)) (C h92 h100))) (C h88 (C h88 h100)))) (S (h v3 z v3))) h4) h91) h44)))))) h20) h86) h98) h95) (C h10 (T (T (T (T (T h16 h37) h62) h90) h99) (C h10 (T (T (T (T h94 h93) h87) h24) h61))))))) (S (h v1 z v3))) h8) h85) h5

