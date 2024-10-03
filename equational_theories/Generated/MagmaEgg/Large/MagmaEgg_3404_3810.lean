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
theorem Equation3404_implies_Equation3810 (G: Type _) [Magma G] (h: Equation3404 G) : Equation3810 G := fun x y z =>
  let v0 := M z y
  have h1 := h z x v0
  have h2 := S h1
  let v3 := M v0 z
  have h4 := S (h v0 (M x v3) y)
  let v5 := M x y
  have h6 := h v0 v0 v5
  have h7 := S h6
  have h8 := h v5 v0 v0
  have h9 := h x y x
  let v10 := M z x
  let v11 := M v0 v10
  let v12 := M x x
  let v13 := M y v12
  have h14 := h x v13 v11
  have h15 := R (M v11 x)
  have h16 := h x x v10
  have h17 := S h16
  have h18 := h v10 x v0
  have h19 := R x
  have h20 := C h19 (S h18)
  have h21 := h v11 v0 x
  have h22 := R v10
  have h23 := C h22 (T h21 h20)
  have h24 := h v11 v0 z
  have h25 := S h24
  have h26 := h v10 z v0
  have h27 := R z
  have h28 := C h22 (T (C h27 h26) h25)
  have h29 := h z z v10
  have h30 := T (T (T h29 h28) h23) h17
  have h31 := R v11
  have h32 := S h29
  have h33 := S h26
  have h34 := C h22 (T h24 (C h27 h33))
  have h35 := h v10 (M v11 v0) y
  have h36 := h y v10 x
  have h37 := S h36
  have h38 := h v10 z x
  have h39 := S h38
  have h40 := h x x z
  have h41 := C h19 h40
  have h42 := C h27 (T (T (T (C h19 h30) h41) h39) h26)
  have h43 := h z x z
  have h44 := h y v10 z
  have h45 := S h44
  have h46 := h v0 z v10
  have h47 := R y
  have h48 := h y v3 z
  have h49 := h v3 v0 y
  have h50 := h z y v0
  have h51 := h z y v10
  have h52 := C h47 (S h51)
  let v53 := M v10 z
  have h54 := h v53 v10 y
  have h55 := S h54
  have h56 := C h47 h51
  have h57 := C h47 (T (T (T (T (T (T (C h27 (T h56 h55)) (C h27 (T (T (T h54 h52) (C h47 h50)) (S h49)))) (S h48)) (C h47 (T (T h46 (C h22 (T h45 h36))) (C (T (T h43 h42) h25) h37)))) (S h35)) h34) h32)
  have h58 := h v0 z y
  have h59 := h x v3 v11
  have h60 := T (T (T h59 (C h31 (C (T (T (T (T h58 h57) (h y (M z z) v11)) (C h31 (C h30 (R (M v11 y))))) (S (h y v12 v11))) h15))) (S h14)) (S h9)
  have h61 := R v0
  have h62 := T h1 (C h61 h60)
  have h63 := h v10 v0 v0
  have h64 := h v10 v0 z
  have h65 := S h58
  have h66 := C h27 (T h54 h52)
  have h67 := C h27 (T (T (T h49 (C h47 (S h50))) h56) h55)
  have h68 := S h43
  have h69 := S h21
  have h70 := C h19 h18
  have h71 := C h22 (T h70 h69)
  have h72 := C h19 (S h40)
  have h73 := C h27 (T (T (T h33 h38) h72) (C h19 (T (T (T h16 h71) h34) h32)))
  have h74 := C h47 (T (T (C (T (T h24 h73) h68) h36) (C h22 (T h37 h44))) (S h46))
  have h75 := T (C h47 (T (T (T (T (T (T h16 h71) h35) h74) h48) h67) h66)) h65
  have h76 := T (T (T h9 h14) (C h31 (C h75 h15))) (S h59)
  have h77 := T (C h61 h76) h2
  have h78 := h v5 z v0
  have h79 := R v5
  have h80 := C h79 (T (T (T (C h27 (T h78 (C h61 (C h27 h77)))) (S h64)) h63) (C h61 (T (C h61 (C h61 h62)) (S h8))))
  have h81 := C h27 (T (C h61 (C h27 h62)) (S h78))
  have h82 := S h63
  have h83 := C h61 (C h61 h77)
  have h84 := S (h x y z)
  have h85 := C h47 h84
  have h86 := h v10 z y
  have h87 := C h22 (T (T (T (T h43 h42) h25) h21) h20)
  have h88 := C h22 (T (T (T (T h70 h69) h24) h73) h68)
  have h89 := h z z v5
  have h90 := h v0 x v0
  have h91 := C h61 (T (T (T (C h47 (T h90 (C h61 (T (T (T (T (T (C h19 (T (T (T (T (T (T h6 (C h79 (T (T (T (C h61 (T h8 h83)) h82) h64) h81))) (S h89)) h29) h28) h23) h88)) (C h19 (T h87 h17))) h41) h39) h86) h85)))) (S (h v5 v0 y))) h8) h83)
  have h92 := h x y v0
  have h93 := C h47 (T (h v5 z v5) (C h76 (T (C h27 (T (T (C h79 (T (T (T (T h92 h91) h82) h64) h81)) h80) h7)) (S (h y v0 z)))))
  let v94 := M v5 z
  have h95 := S (h y v94 x)
  have h96 := S (h v5 z y)
  have h97 := C h47 (T h42 (C h27 (T (T h33 h86) h85)))
  have h98 := C h47 h43
  T (T (T (T (T (T (T h9 (h x v13 x)) (C h19 (T (C h75 (R v12)) (C (R v3) (T (h x x x) (C h19 (T h41 h39))))))) (S (h v53 v3 x))) (h v53 v3 v0)) (C h61 (C (T h58 h57) (T (T (T (T (T (T (C h61 (T (T (T h38 h72) (C h19 (T h16 h88))) (C h19 (T (T (T (T (T (T h87 h71) h34) h32) h89) h80) h7)))) (S h90)) (h v0 x y)) (C h47 (T (T (T (T (C h19 (T (C h47 (h z y v5)) (S (h v94 v5 y)))) h95) h93) h4) h2))) h98) h97) h96)))) (C h61 (C (T (C h47 (T (T (T (T (T (T h29 h28) h35) h74) h48) h67) h66)) h65) (T (T (h v5 z z) (C h27 (T (T (T (T (C h27 (T (C h27 (T (T h92 h91) h82)) h45)) h84) h92) h91) h82))) h45)))) (C h61 (T (T (T (T (T (h v3 (M y v10) x) (C h19 (C (T (T h98 h97) h96) h60))) h95) h93) h4) h2))

