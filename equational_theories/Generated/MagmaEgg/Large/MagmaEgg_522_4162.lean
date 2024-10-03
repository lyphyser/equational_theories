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
theorem Equation522_implies_Equation4162 (G: Type _) [Magma G] (h: Equation522 G) : Equation4162 G := fun x y z =>
  let v0 := M y x
  let v1 := M v0 z
  let v2 := M v1 z
  have h3 := h v2 v2 z
  have h4 := S h3
  have h5 := h z v2 v2
  have h6 := S h5
  have h7 := h v1 v2 z
  have h8 := h z v1 v1
  have h9 := S h8
  have h10 := h v0 v1 z
  have h11 := R v1
  have h12 := R v0
  have h13 := C h12 (T (C h11 h10) h9)
  have h14 := R v2
  have h15 := C h14 (T h13 h7)
  have h16 := C h14 (T h15 h6)
  have h17 := h v1 v2 v0
  have h18 := R z
  have h19 := C h18 (T h17 h16)
  have h20 := C h14 (C h14 h19)
  have h21 := h v0 v2 z
  have h22 := T (T h21 h20) h4
  have h23 := R y
  have h24 := S h21
  have h25 := S h17
  have h26 := S h10
  have h27 := C h12 (T h8 (C h11 h26))
  have h28 := S h7
  have h29 := C h14 (T h28 h27)
  have h30 := C h14 (T h5 h29)
  have h31 := C h18 (T h30 h25)
  have h32 := C h14 (C h14 h31)
  have h33 := T (T h3 h32) h24
  have h34 := C h23 (C h33 h23)
  have h35 := C h23 (C h22 h23)
  have h36 := h y v0 x
  have h37 := h x v0 v0
  have h38 := C h23 (T h37 (C h12 (S h36)))
  let v39 := M x y
  have h40 := h v0 z z
  have h41 := S h40
  have h42 := h v1 v1 v2
  have h43 := S h42
  have h44 := C h11 (T (T (T h26 h21) h20) h4)
  have h45 := C h14 (T (T (T h15 h6) h8) h44)
  have h46 := T h17 h45
  have h47 := C h11 (C h11 h46)
  have h48 := C h18 (T (T (T h47 h43) h17) h16)
  have h49 := h v1 z v1
  have h50 := C h18 (T (T (T h47 h43) h49) (C h18 (T h48 h31)))
  have h51 := C h11 (T (T (T h3 h32) h24) h10)
  have h52 := C h14 (T (T (T h51 h9) h5) h29)
  have h53 := T h52 h25
  have h54 := C h11 (C h11 h53)
  have h55 := C h18 (T (T (T h30 h25) h42) h54)
  have h56 := R x
  have h57 := S h49
  have h58 := C h18 (T (T (T (C h18 (T h19 h55)) h57) h42) h54)
  have h59 := C h11 h31
  have h60 := h v2 v1 v1
  have h61 := C h11 (T h5 (C h14 h28))
  have h62 := C h14 (T (T h52 h25) h27)
  have h63 := T (T (T h47 h43) h17) h45
  have h64 := C h14 h63
  have h65 := C h18 (T (T (T (T h3 h32) h24) h40) h58)
  have h66 := C h14 (T (T (T h65 h57) h42) h54)
  have h67 := C h18 (T (T (T (T h50 h41) h21) h20) h4)
  have h68 := C h14 (T (T (T h47 h43) h49) h67)
  have h69 := T (T (T h52 h25) h42) h54
  have h70 := C h14 h69
  have h71 := C h14 (T (T h13 h17) h45)
  have h72 := h z z v2
  have h73 := S h72
  have h74 := C h18 (C h18 (T (T (T (T h5 h29) h71) h70) h68))
  have h75 := T (T (T (T (T (T h74 h73) h5) h29) h71) h70) h68
  have h76 := C h11 (T (T (T (T (T (T (T (T (C h11 h75) (C h11 (T (T (T (T (T (T (T h66 h64) h62) h15) h6) h8) h44) (C h11 h61)))) (S h60)) h3) h32) h24) h40) h58) h48)
  have h77 := h z v1 z
  have h78 := h z v0 v1
  have h79 := R (M v1 (M z v1))
  have h80 := h z v0 v2
  have h81 := R (M z (M z z))
  have h82 := C h18 (C h18 (T (T (T (T h66 h64) h62) h15) h6))
  have h83 := h v1 v2 v1
  have h84 := h v1 v0 z
  have h85 := C h11 (T (T (T (T (T (T (C h12 h46) (C h12 h69)) (C h12 (T (T (T (T h47 h43) h84) (C h22 (T (T (T (T (C h12 (T (T (T (T (T h65 h57) h83) (C h14 (T (T (T (T (T h64 h62) h15) h6) h72) h82))) (C h33 h81)) (C h12 h75))) (S h80)) h77) h76) h59))) (C h33 h79)))) (S h78)) h77) h76) h59)
  have h86 := T (T (T (T (T (T h66 h64) h62) h15) h6) h72) h82
  have h87 := S h77
  have h88 := C h11 (T (C h14 h7) h6)
  have h89 := C h11 (T (T (T (T (T (T (T (T h55 h50) h41) h21) h20) h4) h60) (C h11 (T (T (T (T (T (T (T (C h11 h88) h51) h9) h5) h29) h71) h70) h68))) (C h11 h86))
  have h90 := C h11 h19
  have h91 := C h11 (T (T (T (T (T (T h90 h89) h87) h78) (C h12 (T (T (T (T (C h22 h79) (C h33 (T (T (T (T h90 h89) h87) h80) (C h12 (T (T (T (T (T (C h12 h86) (C h22 h81)) (C h14 (T (T (T (T (T h74 h73) h5) h29) h71) h70))) (S h83)) h49) h67))))) (S h84)) h42) h54))) (C h12 h63)) (C h12 h53))
  have h92 := h v0 v2 v1
  have h93 := S h92
  have h94 := R (M v1 (M v0 v1))
  have h95 := C h22 (T (C h12 (T h10 h91)) (C h22 h94))
  have h96 := C h33 (T (C h33 h94) (C h12 (T h85 h26)))
  have h97 := h v2 v0 v1
  have h98 := S h97
  have h99 := C h33 (C h12 h61)
  have h100 := C h22 (C h12 h88)
  have h101 := h v2 v0 z
  have h102 := S h101
  have h103 := C h12 (C h33 (T (T h40 h58) h48))
  have h104 := C h12 (C h22 (T (T h55 h50) h41))
  have h105 := C h23 (T (C h12 h36) (S h37))
  have h106 := C h14 (C h14 (T (T (T (T (T (T (T (T (C h56 (T h38 h35)) (C h56 h34)) (C h56 (T (T (T (T (T h105 h21) h20) h4) h101) h104))) (C h56 (T (T (T h103 h102) h97) h100))) (C h56 (T (T (T (T (T (T h99 h98) h3) h32) h24) h92) h96))) (C h56 (T (T (T h95 h93) h10) h91))) (C h56 (T (T (T (T (T h85 h26) h40) h58) h48) h31))) (C h56 h19)) (C h56 (T (T (T (T (T h55 h50) h41) h21) h20) h4))))
  have h107 := h y v2 x
  have h108 := C h56 (T h34 h105)
  have h109 := R v39
  T (T (T (T (T (h v39 v0 v39) (C h22 (T (T (T (C h22 (R (M v39 (M v39 v39)))) (C h33 (T (T (T (C h109 (C h109 (C h56 (T (T h107 h106) (C h33 (T (T (C h14 (T (T (T (T (T (T (T (T (C h56 (T (T (T (T (T h3 h32) h24) h40) h58) h48)) (C h56 h31)) (C h56 (T (T (T (T (T h19 h55) h50) h41) h10) h91))) (C h56 (T (T (T h85 h26) h92) h96))) (C h56 (T (T (T (T (T (T h95 h93) h21) h20) h4) h97) h100))) (C h56 (T (T (T h99 h98) h101) h104))) (C h56 (T (T (T (T (T h103 h102) h3) h32) h24) h38))) (C h56 h35)) h108)) (C h14 (T (T (T (C h56 (T (T (T (T h21 h20) h4) (h v2 x y)) (C h56 h108))) (S (h y x x))) h107) h106))) (S (h x v2 v2)))))))) (S (h v0 v39 x))) h38) h35))) (C h12 h34)) (C h22 (R (M y (M v0 y))))))) (S (h v0 v2 y))) h21) h20) h4

