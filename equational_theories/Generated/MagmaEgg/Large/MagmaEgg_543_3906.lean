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
theorem Equation543_implies_Equation3906 (G: Type _) [Magma G] (h: Equation543 G) : Equation3906 G := fun x y z =>
  let v0 := M z z
  let v1 := M y v0
  let v2 := M v1 y
  let v3 := M x x
  have h4 := h v1 y v3
  have h5 := h v3 v3 z
  have h6 := S h5
  have h7 := h z z v1
  have h8 := S h7
  have h9 := h y z z
  have h10 := R v1
  have h11 := R z
  have h12 := C h11 (C h10 h9)
  have h13 := h v2 v0 z
  have h14 := S h13
  have h15 := h z z v2
  have h16 := C h11 (C h10 (S h9))
  have h17 := R v2
  have h18 := R v0
  have h19 := C h17 (C h18 (T (C h11 (C h17 (C h11 (T h7 h16)))) (S h15)))
  have h20 := h z v2 v0
  have h21 := C h11 (T h20 h19)
  have h22 := C h18 h21
  have h23 := T h22 h14
  have h24 := C h11 h23
  have h25 := S h20
  have h26 := C h17 (C h18 (T h15 (C h11 (C h17 (C h11 (T h12 h8))))))
  have h27 := C h11 (T h26 h25)
  have h28 := C h18 h27
  have h29 := h z v0 v0
  have h30 := S h29
  have h31 := T h13 h28
  have h32 := C h11 h31
  have h33 := C h18 (C h18 (T (T h7 h16) h32))
  have h34 := C h11 (T (T (T h33 h30) h20) h19)
  have h35 := C h18 h34
  have h36 := C h18 (C h18 (T (T h24 h12) h8))
  have h37 := C h11 (T (T (T h26 h25) h29) h36)
  have h38 := h v0 v0 z
  have h39 := S h38
  have h40 := C h18 h37
  have h41 := T (T h13 h40) h39
  have h42 := C h41 (T (T (T (T h22 h40) h39) h21) h37)
  have h43 := C h17 h31
  have h44 := T (T (T h43 h42) h35) h28
  have h45 := C h11 h44
  have h46 := C h17 h23
  have h47 := T (T h38 h35) h14
  have h48 := C h47 (T (T (T (T h34 h27) h38) h35) h28)
  have h49 := h v2 v3 v2
  have h50 := S h49
  have h51 := R v3
  have h52 := C h51 h23
  have h53 := C h51 h44
  have h54 := C h17 (C h17 (T h53 h52))
  have h55 := h v3 v2 v2
  have h56 := C h51 (T h55 h54)
  have h57 := C h11 (T (T (T (T (T h56 h50) h13) h40) h48) h46)
  have h58 := h z v3 v3
  have h59 := h z v2 v2
  have h60 := S h59
  have h61 := T (T (T h22 h40) h48) h46
  have h62 := C h11 h61
  have h63 := C h17 (C h17 (T (T (T h7 h16) h32) h62))
  have h64 := C h17 (C h17 (T (T (T h45 h24) h12) h8))
  have h65 := C h51 (T (T (T (T (T (T h43 h42) h39) h21) h37) (C h11 (T (T (T h33 h30) h59) h64))) (C h11 (T (T (T h63 h60) h58) (C h51 (C h51 (T (T (T (T h57 h45) h24) h12) h8))))))
  have h66 := C h51 h61
  have h67 := C h51 h31
  have h68 := T (T (T h67 h66) h65) h6
  have h69 := R y
  have h70 := C h69 h68
  have h71 := h v3 v1 y
  have h72 := C h51 (T (C h17 (C h17 (T h67 h66))) (S h55))
  have h73 := C h11 (T (T (T (T (T h43 h42) h35) h14) h49) h72)
  have h74 := C h51 (T (T (T (T (T (T (C h11 (T (T (T (C h51 (C h51 (T (T (T (T h7 h16) h32) h62) h73))) (S h58)) h59) h64)) (C h11 (T (T (T h63 h60) h29) h36))) h34) h27) h38) h48) h46)
  have h75 := h v3 v0 v0
  have h76 := C h51 (T (T (T (T (T (C h41 (C h18 h67)) (S h75)) h5) h74) h53) h52)
  have h77 := h v0 v3 v2
  have h78 := T (C h69 (T (T (T (T (T h13 h40) h39) h77) h76) (C h51 (T (T (T (T (T h67 h66) h65) h6) h71) (C h10 h70))))) (S h4)
  have h79 := R x
  have h80 := S h77
  have h81 := C h51 (T (T (T (T (T h67 h66) h65) h6) h75) (C h47 (C h18 h52)))
  have h82 := T (T (T h5 h74) h53) h52
  have h83 := C h69 h82
  have h84 := C h69 (T (T (T (T (T (C h51 (T (T (T (T (T (C h10 h83) (S h71)) h5) h74) h53) h52)) h81) h80) h38) h35) h14)
  have h85 := h v1 y v1
  have h86 := S h85
  have h87 := h y v1 y
  have h88 := h v2 z v3
  have h89 := h z v3 v2
  have h90 := h z y y
  have h91 := h y v3 v2
  have h92 := S h91
  have h93 := C h51 (C h17 h83)
  have h94 := h v2 y v3
  have h95 := C h69 (T (T (C h11 (T (T (T (C h69 (C h69 (T (T (T (T (T h7 h16) h32) h62) h73) (C h11 (T (T (T h56 h50) h94) (C h69 (T h93 h92))))))) (S h90)) h89) (C h51 (C h17 (C h11 h68))))) (S h88)) (C h10 (T h87 (C h10 (C h69 h78)))))
  have h96 := h y y z
  T (C h79 (T (h x v1 v2) (C h10 (T (C h17 (C h79 (T (T (T (C (T (T h85 (C h69 (T (T (C h10 (T (C h10 (C h69 (T h4 h84))) (S h87))) h88) (C h11 (T (T (T (C h51 (C h17 (C h11 h82))) (S h89)) h90) (C h69 (C h69 (T (T (T (T (T (C h11 (T (T (T (C h69 (T h91 (C h51 (C h17 h70)))) (S h94)) h49) h72)) h57) h45) h24) h12) h8)))))))) (S h96)) (T (T (h v2 v2 v3) (C h17 (T (T (T (T (T (T (C h51 (T (C h17 (C h17 (T h5 h74))) h54)) h50) h13) h40) h39) h77) h76))) (C h17 (T (T (T (T (T (T h81 h80) h38) h35) h14) h94) (C (T (T h96 h95) h86) (T (T (T (T (T (T h93 h92) h96) h95) h86) h4) h84)))))) (S (h v1 y v2))) h4) h84))) (C h17 (C h79 h78)))))) (S (h v2 x v1))

