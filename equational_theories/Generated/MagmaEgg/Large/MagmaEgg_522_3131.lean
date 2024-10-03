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
theorem Equation522_implies_Equation3131 (G: Type _) [Magma G] (h: Equation522 G) : Equation3131 G := fun x y z =>
  let v0 := M y x
  let v1 := M v0 z
  let v2 := M v1 z
  let v3 := M v2 y
  have h4 := h v2 v3 y
  have h5 := S h4
  have h6 := R v3
  have h7 := h y v3 v3
  have h8 := R v2
  have h9 := C h8 (T h7 (C h6 h5))
  have h10 := R v0
  have h11 := h v3 v2 v2
  have h12 := h v3 v2 y
  have h13 := S h7
  have h14 := h z v2 v2
  have h15 := S h14
  have h16 := h v1 v2 z
  have h17 := C h8 h16
  have h18 := R v1
  have h19 := C h18 (T h17 h15)
  have h20 := C h6 (T h19 h4)
  have h21 := C h6 (T h20 h13)
  have h22 := h v2 v3 v1
  have h23 := R y
  have h24 := C h23 (T h22 h21)
  have h25 := C h8 (T (C h8 (C h8 h24)) (S h12))
  have h26 := h y v2 v2
  have h27 := S h16
  have h28 := C h8 h27
  have h29 := C h18 (T h14 h28)
  have h30 := S h22
  have h31 := C h6 (T h5 h29)
  have h32 := S h26
  have h33 := C h6 (T h7 h31)
  have h34 := C h8 (C h23 (T h33 h30))
  have h35 := C h8 (T h12 (C h8 h34))
  have h36 := C h6 (T (T (T h35 h32) h7) h31)
  have h37 := C h6 (T (T h36 h30) h29)
  have h38 := C h6 (T (T (T h20 h13) h26) h25)
  have h39 := h v2 v2 v3
  have h40 := S h39
  have h41 := C h8 (C h8 (T h22 h38))
  have h42 := C h6 (T (T (T h41 h40) h22) h38)
  have h43 := C h8 (C h8 (T h36 h30))
  have h44 := h v2 z v2
  have h45 := S h44
  have h46 := T h39 h43
  have h47 := R z
  have h48 := C h47 (C h47 h46)
  have h49 := h v1 z z
  have h50 := C h47 (T h49 (C h47 (T (T (T h48 h45) h39) h43)))
  have h51 := C h6 (T (T (T h50 h45) h39) h43)
  have h52 := S h49
  have h53 := T h41 h40
  have h54 := C h47 (C h47 h53)
  have h55 := C h47 (T (C h47 (T (T (T h41 h40) h44) h54)) h52)
  have h56 := h v2 z z
  have h57 := S h56
  have h58 := h z v0 v2
  have h59 := S h58
  have h60 := R (M v2 (M z v2))
  have h61 := h v0 v3 z
  have h62 := S h61
  have h63 := C h6 (T (T (T h41 h40) h44) h55)
  have h64 := C h6 h63
  have h65 := h v2 v3 v2
  have h66 := T (T h65 h64) h62
  have h67 := S h65
  have h68 := C h6 h51
  have h69 := C h10 (T (T (T (C h47 (T (T (T (T h61 h68) h67) h44) h54)) h52) h16) (C h66 h60))
  have h70 := C h8 (T h69 h59)
  have h71 := T (T h61 h68) h67
  have h72 := C h10 (T (T (T (C h71 h60) h27) h49) (C h47 (T (T (T (T h48 h45) h65) h64) h62)))
  have h73 := h z v1 v0
  have h74 := S h73
  have h75 := C h18 (T (T (T h41 h40) h29) (C h18 (T (T (T h17 h15) h58) h72)))
  have h76 := C h18 h46
  have h77 := C h8 (T (T (T (T h76 h75) h74) h58) h72)
  have h78 := h v1 z v2
  have h79 := h v1 v2 v2
  have h80 := C h18 h53
  have h81 := C h18 (T (T (T (C h18 (T (T (T h69 h59) h14) h28)) h19) h39) h43)
  have h82 := C h8 (T (T (T (T h69 h59) h73) h81) h80)
  have h83 := R (M v0 (M z v0))
  have h84 := h z v0 v0
  have h85 := C h8 (T h58 h72)
  have h86 := C h47 (T (T (T (T (T h85 h82) (C h8 (T (T (T (T h76 h75) h74) h84) (C h71 (T (C h71 h83) h82))))) (S h79)) h78) (C h47 (C h47 (T h77 h70))))
  have h87 := C h6 (T (T (T h86 h57) h44) h55)
  have h88 := C h47 (T (T (T (T (T (C h47 (C h47 (T h85 h82))) (S h78)) h79) (C h8 (T (T (T (T (C h66 (T h77 (C h66 h83))) (S h84)) h73) h81) h80))) h77) h70)
  have h89 := h v2 y z
  have h90 := S h89
  have h91 := C h23 (T (T (T h33 h30) h56) h88)
  have h92 := h v3 y y
  have h93 := C h6 (T (T (T (C h23 (T h92 (C h23 (T (T (T (C h23 h91) h90) h56) h88)))) h90) h56) h88)
  have h94 := R (M v3 (M y v3))
  have h95 := S h92
  have h96 := C h23 (C h23 (T (T (T h86 h57) h22) h21))
  have h97 := C h23 (T (T (T h86 h57) h89) h96)
  have h98 := C h6 (T (T (T h86 h57) h89) (C h23 (T h97 h95)))
  have h99 := C h6 (T (T (T h50 h45) h56) h88)
  have h100 := C h6 (T (T (T h36 h30) h39) h43)
  have h101 := C h6 (T (T h19 h22) h38)
  have h102 := h y y v3
  have h103 := R (M y (M y y))
  have h104 := C h23 (C h23 (T (T (T (T (T (T h93 h87) h51) h42) h37) h20) h13))
  have h105 := S (h y v0 y)
  have h106 := C h66 h103
  have h107 := C h71 (T (T (T (T (T (T (T (T h93 h87) h51) h42) h37) h20) h13) h102) h104)
  have h108 := C h66 h94
  have h109 := C h8 (T (T (T (T (T (T (T (T (T (C h8 (C h8 (T (C h6 h4) h13))) h35) h32) h7) h31) h101) h100) h63) h99) h98)
  have h110 := C h66 (T (T (T (T (T (T (T (T h24 h91) h97) h95) h11) h109) h108) h107) h106)
  T (T (T (h x v0 v0) (C h10 (S (h y v0 x)))) (C h10 (T (T (h y v2 v0) (C h66 (T (T (T (T (T (C h66 (T (T (T (C h10 (T (T (T (T (T (T (C h23 (T (T (T (T (T h61 h68) h67) h89) h96) (C h23 (T (T (T (T h91 h97) h95) (h v3 v0 y)) (C h10 (T (T (T (T (T (C h71 (R (M y (M v3 y)))) h34) h110) h105) (h y v3 v2)) (C h6 (T (T (T (T (C h6 (T (T (T (T (T (T (T (T h110 h105) h7) h31) h101) h100) h63) h99) h98)) h5) h65) h64) h62)))))))) (S (h v3 y v0))) h11) h109) h108) h107) h106)) h105) h102) h104)) (C h71 h103)) (C h66 (T (T (T (T (T (T (T (T (C h23 (C h23 (T (T (T (T (T (T h7 h31) h101) h100) h63) h99) h98))) (S h102)) h7) h31) h101) h100) h63) h99) h98))) (C h71 h94)) (C h8 (T (T (T (T (T (T (T (T (T h93 h87) h51) h42) h37) h20) h13) h26) h25) (C h8 h9)))) (S h11)))) (C h10 h9)))) (S (h v3 v0 v2))

