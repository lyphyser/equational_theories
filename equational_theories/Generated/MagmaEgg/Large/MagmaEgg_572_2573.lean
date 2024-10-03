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
theorem Equation572_implies_Equation2573 (G: Type _) [Magma G] (h: Equation572 G) : Equation2573 G := fun x y z =>
  let v0 := M z x
  let v1 := M v0 y
  let v2 := M y v1
  let v3 := M v2 z
  have h4 := h v3 v2 v0
  have h5 := S h4
  have h6 := h v2 z z
  have h7 := R v3
  have h8 := C h7 (S h6)
  have h9 := h z v3 z
  have h10 := T h9 h8
  have h11 := R v0
  have h12 := C h11 h10
  have h13 := h v0 v1 v1
  have h14 := S h13
  have h15 := h y v0 v2
  have h16 := S h15
  have h17 := h v0 y y
  have h18 := S h17
  have h19 := R y
  have h20 := R v2
  have h21 := h y v2 y
  have h22 := C h11 (C h20 (T h21 (C h20 (C h19 h18))))
  have h23 := C h11 (T h22 h16)
  have h24 := S h21
  have h25 := C h11 (C h20 (T (C h20 (C h19 h17)) h24))
  have h26 := h y v1 y
  have h27 := S h26
  have h28 := R v1
  have h29 := C h11 (T (T (T (C h28 h17) h27) h15) h25)
  have h30 := C h11 (T h29 h23)
  have h31 := C h11 (T (T (T h22 h16) h26) (C h28 h18))
  have h32 := C h11 (T h15 h25)
  have h33 := h v1 v0 v0
  have h34 := C h11 (T h32 h31)
  have h35 := C h28 (T (C h11 (T (T (T (C h11 h34) (S h33)) h32) h31)) h30)
  have h36 := h v0 v1 v0
  have h37 := C h28 (T (T h18 h36) h35)
  have h38 := C h28 (T h26 h37)
  have h39 := C h28 (T (T (T h38 h14) h36) h35)
  have h40 := C h28 h39
  have h41 := S h36
  have h42 := C h28 (T h34 (C h11 (T (T (T h29 h23) h33) (C h11 h30))))
  have h43 := C h28 (T (T h42 h41) h17)
  have h44 := C h28 (T h43 h27)
  have h45 := C h28 (T (T (T h42 h41) h13) h44)
  have h46 := h v1 y v1
  have h47 := C h20 (T h46 (C h19 (T (T h40 h14) h17)))
  have h48 := C h28 (T (T (T (T h47 h24) h26) h37) h45)
  have h49 := C h28 h45
  have h50 := C h20 (T (C h19 (T (T h18 h13) h49)) (S h46))
  have h51 := h v2 v1 v1
  have h52 := T (T (T (T h51 (C h28 (T (T (T (T (T (C h28 (T (T h48 h40) h44)) h39) h43) h27) h21) h50))) h48) h40) h14
  have h53 := C h20 (C h52 h12)
  have h54 := S h9
  have h55 := C h7 h6
  have h56 := T h55 h54
  have h57 := C h11 h56
  have h58 := h z v3 v3
  have h59 := S h58
  have h60 := R z
  have h61 := C h60 (T h53 h5)
  have h62 := h v0 z v2
  have h63 := C h11 (T (T (T (C h7 (T (C h7 (C h7 (T h13 h44))) (C h7 (C h7 (T (T (T h38 h14) h62) h61))))) h59) h9) h8)
  have h64 := h v3 v0 v3
  have h65 := C h28 (T (T (T (T h39 h43) h27) h21) h50)
  have h66 := T (T (T (T h13 h49) h65) (C h28 (T (T (T (T (T h47 h24) h26) h37) h45) (C h28 (T (T h38 h49) h65))))) (S h51)
  have h67 := C h66 (T (T h64 h63) h57)
  have h68 := C h20 h67
  have h69 := S h64
  have h70 := S h62
  have h71 := C h20 (C h66 h57)
  have h72 := C h60 (T h4 h71)
  have h73 := C h11 (T (T (T h55 h54) h58) (C h7 (T (C h7 (C h7 (T (T (T h72 h70) h13) h44))) (C h7 (C h7 (T h38 h14))))))
  have h74 := C h52 (T (T h12 h73) h69)
  have h75 := C h20 (T (T (T (T (T h68 h53) h5) h64) h63) h57)
  have h76 := C h20 h74
  have h77 := h v3 z v3
  have h78 := S h77
  have h79 := C h7 h56
  have h80 := h v0 v3 v2
  have h81 := S h80
  have h82 := C h20 (T (T (T (T (T h12 h73) h69) h4) h71) h76)
  have h83 := C h7 (T h67 h82)
  have h84 := C h7 (C h7 (T (T (T h83 h81) h62) h61))
  have h85 := h v0 v3 v3
  have h86 := C h7 (T (T (T h83 h81) h85) h84)
  have h87 := C h7 (T (T (T h86 h59) h9) h8)
  have h88 := C h7 (T h75 h74)
  have h89 := C h7 (C h7 (T (T (T h72 h70) h80) h88))
  have h90 := C h60 (T h85 (C h7 (T h86 (C h7 (T (T h89 h87) h79)))))
  have h91 := C h20 (T (T (T (T h90 h78) h4) h71) h76)
  have h92 := S h85
  have h93 := C h7 (T (T (T h89 h92) h80) h88)
  have h94 := C h7 (T (T (C h7 h10) (C h7 (T (T (T h55 h54) h58) h93))) h84)
  have h95 := C h60 (T (C h7 (T h94 h93)) h92)
  have h96 := T (T (T (T (C h20 (T h91 h75)) h53) h5) h77) h95
  have h97 := C h66 h96
  have h98 := h z v0 v2
  T (T (T (T (T (T (h x v0 v3) (C h11 (T (T (T (T (C h7 (T (T (T (T (T (C h7 (T (T (T (T (T (T (C (R x) (T h62 (C h60 (T (T (T h53 h5) h77) h95)))) (S (h z x z))) h98) h97) h91) h75) h74)) h83) h81) h85) h87) h79)) h94) h59) h98) (C h11 h96)))) (C h11 (T (T (T (T (C h11 (T (T (T (T h90 h78) h4) h71) (C h20 (T h82 (C h20 (T (T (T (T h68 h53) h5) h77) h95)))))) h97) h91) h75) h74))) (C h66 (R (M v0 v3)))) h68) h53) h5

