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
theorem Equation572_implies_Equation759 (G: Type _) [Magma G] (h: Equation572 G) : Equation759 G := fun x y z =>
  let v0 := M y x
  let v1 := M v0 z
  let v2 := M z v1
  let v3 := M y v2
  have h4 := h y x v1
  have h5 := S h4
  have h6 := h v0 v1 v2
  have h7 := S h6
  have h8 := h v1 v2 v1
  have h9 := S h8
  have h10 := h z v1 v1
  have h11 := R v2
  have h12 := C h11 h10
  have h13 := h z v2 z
  have h14 := S h13
  have h15 := h v0 z z
  have h16 := R z
  have h17 := C h11 (C h16 h15)
  have h18 := C h11 (T h17 h14)
  have h19 := R v0
  have h20 := h z v0 v2
  have h21 := C h11 (C h16 (S h15))
  have h22 := C h11 (T h13 h21)
  have h23 := C h11 (S h10)
  have h24 := R v1
  have h25 := C h24 (C h11 (T (T (T h8 h23) h22) (C h11 (T (T (T h17 h14) h20) (C h19 (T (T h18 h12) h9))))))
  have h26 := C h24 (T h25 h7)
  have h27 := C h24 h26
  have h28 := h v2 v1 v1
  have h29 := R x
  have h30 := T (C h29 (T h28 h27)) h5
  have h31 := R v3
  have h32 := S h28
  have h33 := S h20
  have h34 := C h11 (T (T (T (C h19 (T (T h8 h23) h22)) h33) h13) h21)
  have h35 := C h24 (C h11 (T (T (T h34 h18) h12) h9))
  have h36 := C h24 (T h6 h35)
  have h37 := C h24 h36
  have h38 := C h29 (T h37 h32)
  have h39 := h v2 y v2
  have h40 := S h39
  have h41 := h x v2 v2
  have h42 := R y
  have h43 := C h42 (T h41 (C h11 (C h11 (C h11 h30))))
  have h44 := C h29 (T (T (T h43 h40) h28) h27)
  have h45 := C h42 (T (C h11 (C h11 (C h11 (T h4 h38)))) (S h41))
  have h46 := C h29 (T (T (T h37 h32) h39) h45)
  have h47 := h y v0 y
  have h48 := S h47
  have h49 := h v0 y v0
  have h50 := S h49
  have h51 := T h44 h5
  have h52 := T h39 h45
  have h53 := C h52 h51
  have h54 := h x v0 v2
  have h55 := h x y x
  have h56 := S h55
  have h57 := C h29 h51
  have h58 := C h29 h57
  have h59 := h y x x
  have h60 := C h29 (T (T (T h44 h5) h59) h58)
  have h61 := T h4 h46
  have h62 := C h29 h61
  have h63 := C h42 (T h62 h60)
  have h64 := C h42 (T (T (T h63 h56) h54) (C h19 (C h52 h53)))
  have h65 := C h42 (T h64 h50)
  have h66 := h x y y
  have h67 := C h42 (T (T (T h63 h56) h66) h65)
  have h68 := S h59
  have h69 := C h29 h62
  have h70 := C h29 (T (T (T h69 h68) h4) h46)
  have h71 := C h42 (T h70 h57)
  have h72 := T h43 h40
  have h73 := C h72 h61
  have h74 := C h42 (T (T (T (C h19 (C h72 h73)) (S h54)) h55) h71)
  have h75 := h v0 x v0
  have h76 := S h75
  have h77 := S h66
  have h78 := C h42 (T h49 h74)
  have h79 := C h52 (T h78 h77)
  have h80 := h y v0 v2
  have h81 := C h29 (T (T (T h69 h68) h80) (C h19 (C h52 h79)))
  have h82 := C h42 (T (T (T (T (T (T h62 h60) h81) h76) h49) h74) h67)
  have h83 := C h19 (T (T (T (T h78 h77) h55) h71) h82)
  have h84 := R (M y v0)
  have h85 := C h72 (T h66 h65)
  have h86 := C h29 (T (T (T (C h19 (C h72 h85)) (S h80)) h59) h58)
  have h87 := C h42 (T (T (T h78 h77) h55) h71)
  have h88 := C h42 (T (T (T (T (T (T h87 h64) h50) h75) h86) h70) h57)
  have h89 := C h19 (T (T (T (T h88 h63) h56) h66) h65)
  have h90 := h v1 v0 v1
  have h91 := h v0 y v2
  have h92 := S h91
  have h93 := R (M x v0)
  have h94 := C h72 h93
  have h95 := C h19 (T (T (T h83 h48) h4) h46)
  have h96 := h y v0 v0
  have h97 := C h19 (T (T (T h44 h5) h47) h89)
  have h98 := C h52 h93
  have h99 := C h42 (T (T (T (T h73 h98) h97) (C h19 (T (T (T h83 h48) h96) (C h19 h95)))) (C h72 (T (C h72 h94) (C h11 h53))))
  T (T (T (T (T h55 h71) h82) (C h42 (T (T (T (T h87 h64) h50) h91) (C h42 (T (T (T (T (C h52 (T (C h11 h73) (C h52 h98))) (C h19 (T (T (T (C h19 h97) (S h96)) h47) h89))) h95) h94) h53))))) (C h42 (T (T (T h99 h92) (h v0 y y)) (C h42 (T (T (T (T (T (C h42 (T (T (T (T h99 h92) h49) h74) h67)) h88) h63) h56) (h x y v3)) (C h42 (T (T (T (C h31 (T (T (T (T (T (T (C h31 (T (T (T (T (T h62 h60) h81) h76) h6) (C h24 (T (T (C h52 (T (T (T (T (T h34 h18) h12) h9) h90) (C h19 (T (T (C h24 (T (T (T (T (T (T (T h37 h32) h39) h45) h75) h86) h70) h57)) (C h24 (T (T (T (T (T h62 h60) h81) h76) h6) h35))) h26)))) (C h19 (T (T (T (T (C h19 (T (T h36 (C h24 (T (T (T (T (T h25 h7) h75) h86) h70) h57))) (C h24 (T (T (T (T (T (T (T h62 h60) h81) h76) h43) h40) h28) h27)))) (S h90)) h8) h23) h22))) h33)))) (C h31 (C h24 (h z v1 y)))) (S (h y v3 v1))) h47) h89) (C h72 h84)) h79)) (C h31 (T (T (T (T (T h85 (C h52 h84)) h83) h48) h4) h46))) (C h31 (T h44 h38))) (C h31 h30)))))))) (S (h v3 y y))

