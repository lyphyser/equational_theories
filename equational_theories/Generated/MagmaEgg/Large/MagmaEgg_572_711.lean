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
theorem Equation572_implies_Equation711 (G: Type _) [Magma G] (h: Equation572 G) : Equation711 G := fun x y z =>
  let v0 := M x z
  let v1 := M v0 z
  let v2 := M y v1
  let v3 := M y v2
  have h4 := h v3 y y
  have h5 := S h4
  have h6 := h y v3 x
  have h7 := R (M y v3)
  have h8 := h x v0 v1
  have h9 := S h8
  have h10 := h v0 x v0
  have h11 := S h10
  have h12 := h x z z
  have h13 := S h12
  have h14 := R v0
  have h15 := h z v0 z
  have h16 := C h14 (T h15 (C h14 h13))
  have h17 := C h14 h16
  have h18 := R x
  have h19 := R v1
  have h20 := C h19 (C h18 (T (C h18 h17) h11))
  have h21 := h v0 v1 x
  have h22 := h v0 z z
  have h23 := C h19 (T (T (S h22) h21) h20)
  have h24 := h z v1 z
  have h25 := S h15
  have h26 := C h14 (C h19 (T h21 h20))
  have h27 := C h14 (T (T h26 h9) h12)
  have h28 := C h14 (T (T (T h27 h25) h24) h23)
  have h29 := h v1 v0 v0
  have h30 := T (T h29 h28) h9
  have h31 := C h30 h7
  have h32 := h y v1 y
  have h33 := C h18 (T h32 h31)
  have h34 := R v3
  have h35 := R y
  have h36 := C h35 (C h34 (T (C h34 h33) (S h6)))
  have h37 := h x y v3
  have h38 := C h35 (T h37 h36)
  have h39 := C h35 h38
  have h40 := S h37
  have h41 := S h32
  have h42 := S h29
  have h43 := S h21
  have h44 := C h14 (T (C h14 h12) h25)
  have h45 := C h14 h44
  have h46 := C h19 (C h18 (T h10 (C h18 h45)))
  have h47 := C h14 (C h19 (T h46 h43))
  have h48 := C h14 (T (T h13 h8) h47)
  have h49 := S h24
  have h50 := C h19 (T (T h46 h43) h22)
  have h51 := C h14 (T (T (T h50 h49) h15) h48)
  have h52 := T (T h8 h51) h42
  have h53 := C h52 h7
  have h54 := C h18 (T h53 h41)
  have h55 := C h35 (C h34 (T h6 (C h34 h54)))
  have h56 := C h35 (T h55 h40)
  have h57 := h x v0 v0
  have h58 := C h30 h17
  have h59 := C h30 (T h58 h11)
  have h60 := C h52 h45
  have h61 := h v0 z v0
  have h62 := S h61
  have h63 := C h14 (T (T (T h26 h51) h42) h16)
  have h64 := C h14 (T (T (T (T (T h50 h49) h15) h48) h63) h45)
  have h65 := R z
  have h66 := C h65 (T h8 h64)
  have h67 := C h19 (T (T (T h66 h62) h10) h60)
  have h68 := C h14 (T (T (T h44 h29) h28) h47)
  have h69 := C h14 (T (T (T (T (T h17 h68) h27) h25) h24) h23)
  have h70 := C h65 (T h69 h9)
  have h71 := h v0 v1 v1
  have h72 := C h52 (T (T (T (C h19 h67) (S h71)) h61) h70)
  have h73 := h z x v1
  have h74 := T (T (T (T (T (T (T h17 h68) h27) h25) h73) h72) h67) h59
  have h75 := h x v2 x
  have h76 := S h75
  have h77 := R (M x (M x v2))
  have h78 := h y v1 x
  have h79 := R v2
  have h80 := C h79 (T h78 (C h30 h77))
  have h81 := C h35 (T (T (T (C h14 (C h14 (T (T (T (T h80 h76) h8) h64) (C h14 h74)))) (S h57)) h37) h36)
  have h82 := h v2 y v0
  have h83 := h v2 y z
  have h84 := S h83
  have h85 := C h79 (T (C h52 h77) (S h78))
  have h86 := C h65 (T (T (T h69 h9) h75) h85)
  have h87 := C h35 (T (T (T (T (C h35 (T (C h65 (T h61 h70)) (C h65 (T h66 h86)))) h84) h82) h81) h56)
  have h88 := C h65 (T (T (T h80 h76) h8) h64)
  have h89 := C h35 (T (C h65 (T h88 h70)) (C h65 (T h66 h62)))
  have h90 := S h82
  have h91 := S h73
  have h92 := C h19 (T (T (T h58 h11) h61) h70)
  have h93 := C h30 (T (T (T h66 h62) h71) (C h19 h92))
  have h94 := C h52 (T h10 h60)
  have h95 := T (T (T (T (T (T (T h94 h92) h93) h91) h15) h48) h63) h45
  have h96 := C h14 (C h14 (T (T (T (T (C h14 h95) h69) h9) h75) h85))
  have h97 := h y x y
  have h98 := S h97
  have h99 := C h35 h56
  have h100 := h v3 z v3
  have h101 := h z v0 y
  have h102 := C h35 (T (T (T h55 h40) h57) h96)
  have h103 := h v0 v3 v3
  have h104 := C h18 (T (T (T (T h38 h102) h90) h83) (C h35 (T (T (T (C h65 (T (T (T h88 h62) h103) (C h34 (T (T (C h34 (C h34 (T (T (T (T (T (C h14 (T (T h4 h99) (C h35 (T (T (T (T h38 h102) h90) h83) h89)))) (S h101)) h73) h72) h67) h59))) (C h34 (C h34 h95))) (C h34 (C h34 (T (T (T h17 h68) h27) h25))))))) (S h100)) h4) h99)))
  T (T (T (T (h x y y) (C h35 (T (T (T (C h35 (T (T (T (C h35 (T (T h33 (C h18 (T (T (T h53 h41) h97) (C h18 (T (T (T (T (C h35 (T (T (T h39 h5) h100) (C h65 (T (T (T (C h34 (T (T (C h34 (C h34 (T (T (T h15 h48) h63) h45))) (C h34 (C h34 h74))) (C h34 (C h34 (T (T (T (T (T h94 h92) h93) h91) h101) (C h14 (T (T h87 h39) h5))))))) (S h103)) h61) h86)))) h84) h82) h81) h56))))) (C h18 (T (T (T h104 h98) (h y x x)) (C h18 (T (C h18 (T (T (T h104 h98) h32) h31)) h54)))))) (S (h x y x))) h57) h96)) h90) h83) h89))) h87) h39) h5

