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
theorem Equation3385_implies_Equation3286 (G: Type _) [Magma G] (h: Equation3385 G) : Equation3286 G := fun x y z =>
  let v0 := M z z
  have h1 := h y v0 v0
  have h2 := S h1
  have h3 := h z z z
  have h4 := R v0
  have h5 := C h4 (S h3)
  have h6 := h z z v0
  have h7 := T h6 h5
  have h8 := R y
  have h9 := C h8 h7
  have h10 := C h4 h9
  have h11 := T h10 h2
  have h12 := C h8 h11
  have h13 := S h6
  have h14 := C h4 h3
  have h15 := T h14 h13
  have h16 := C h8 h15
  have h17 := C h4 h16
  have h18 := C h4 (T (T h10 h2) h9)
  have h19 := h v0 y v0
  have h20 := C h8 (T (C h4 (T (T (T h19 h18) h2) h9)) h17)
  have h21 := h v0 v0 y
  let v22 := M y v0
  let v23 := M z (M z v22)
  have h24 := S h21
  have h25 := S h19
  have h26 := C h4 (T (T h16 h1) h17)
  have h27 := C h8 (T h10 (C h4 (T (T (T h16 h1) h26) h25)))
  have h28 := T h1 h17
  have h29 := C h8 h28
  have h30 := h y v22 y
  let v31 := M v22 y
  have h32 := h y (M y v31) v22
  have h33 := S h32
  have h34 := h v0 v0 v22
  have h35 := S h34
  have h36 := R v22
  have h37 := C h36 (T h1 h26)
  have h38 := h v0 y z
  have h39 := S h38
  have h40 := h y z z
  have h41 := S h40
  have h42 := h z y v0
  have h43 := R z
  have h44 := C h43 (T h42 (C h4 h41))
  have h45 := T (T (T (T h44 h39) h19) h18) h2
  have h46 := h y v31 (M y v22)
  have h47 := S h46
  have h48 := C h4 (T (T (T h37 h35) h14) h13)
  have h49 := h v22 y v0
  have h50 := S h49
  have h51 := C h36 (T h18 h2)
  have h52 := C h4 (T (T (T h6 h5) h34) h51)
  have h53 := T (T (T h6 h5) h52) h50
  have h54 := C h53 (T (T (T (T h49 h48) h21) h20) h12)
  have h55 := C h8 h54
  have h56 := h v0 v22 y
  have h57 := T (T (T (T h6 h5) h21) h20) h12
  have h58 := C h57 (T (T (T (T h16 h1) h17) h56) h55)
  let v59 := M z (M z y)
  have h60 := h y v59 v22
  have h61 := h y v59 v0
  have h62 := T (T (T (T h29 h27) h24) h14) h13
  have h63 := R v59
  have h64 := C h43 (T (C h4 h40) (S h42))
  have h65 := T (T (T (T h1 h26) h25) h38) h64
  have h66 := h v0 v22 v22
  have h67 := h v0 y v22
  have h68 := h y y v0
  have h69 := h v22 y y
  have h70 := T (T (T (T h29 h27) h24) h52) h50
  have h71 := T (T (T h49 h48) h14) h13
  have h72 := C h71 h70
  have h73 := S h56
  have h74 := C h8 h72
  have h75 := C h62 (T (T (T (T h74 h73) h10) h2) h9)
  have h76 := h y v31 z
  have h77 := S h76
  have h78 := h v0 z z
  have h79 := S h78
  have h80 := C h43 h7
  have h81 := h z v0 z
  have h82 := h z v0 v22
  have h83 := h v22 y z
  have h84 := h z v22 y
  have h85 := C h43 (T (T h40 h84) (C h8 (T (T (T (T (C h43 (T h83 (C h43 (T (T (T (C h36 (T h40 (C h43 h28))) (S h82)) h80) h79)))) (S h81)) h80) h79) (C h53 h43))))
  have h86 := C h43 h41
  have h87 := T (T (T (T (T h86 h85) h77) h46) h75) h2
  have h88 := C h87 (T (T (T (T h1 h17) h56) h55) (C h8 (T (T (T (T h72 (C h4 (T (T h69 (C h8 (T (T (T (T (T (T (T (C h36 h68) (S h67)) h19) h18) h17) h66) (C h36 (T (T h48 h14) h13))) (C h65 h57)))) (C h8 (C h63 h62))))) (S h61)) h60) (C (T (T h1 h58) h47) (T (C h8 (T (T (C h45 h36) h37) h35)) h16)))))
  have h89 := C h43 h40
  have h90 := C h43 h15
  have h91 := C h43 (T (T (C h8 (T (T (T (T (C h71 h43) h78) h90) h81) (C h43 (T (C h43 (T (T (T h78 h90) h82) (C h36 (T (C h43 h11) h41)))) (S h83))))) (S h84)) h41)
  have h92 := T (T (T (T (T h1 h58) h47) h76) h91) h89
  have h93 := R x
  have h94 := C h93 h15
  have h95 := h x v0 v0
  let v96 := M x (M x v22)
  T (T (T (T (T (T (T (T (T (h x x v22) (h v22 v96 v0)) (C h4 (T (T (C h36 (T (T (T (T (T (T (T (T (C (R v96) h57) (C (T (T (T (T (C h93 (T (h x v22 y) (C h8 (T (T (T (T (C h93 h71) h95) (C h4 (T (T h94 h95) (C h4 h94)))) (S (h v0 x v0))) (C h53 h93))))) (S (h y v31 x))) h46) h75) h2) (T (T (T (T (T (T (T h29 h27) h24) h52) h50) (C h65 h8)) (C (T (T (T (T (T h44 h39) h19) h18) h58) h47) h8)) (C (T (T h76 h91) h89) h8)))) (C h92 (T (T (T (T (T (T (C (T (T h86 h85) h77) h8) (C (T (T (T (T (T h46 h75) h26) h25) h38) h64) h8)) (C h45 h8)) h49) h48) h14) h13))) (C h87 (T (T (T (T (T (T (T h6 h5) h21) h20) h12) h30) h32) (C h92 (T (T (T (T (C h8 (T (T (T (T (C (T (T h46 h75) h2) (T h9 (C h8 (T (T h34 h51) (C h65 h36))))) (S h60)) h61) (C h4 (T (T (C h8 (C h63 h57)) (C h8 (T (T (T (T (T (T (T (C h45 h62) (C h36 (T (T h6 h5) h52))) (S h66)) h10) h26) h25) h67) (C h36 (S h68))))) (S h69)))) h54)) h74) h73) h10) h2))))) (C h36 (T (T h88 h33) (C h8 (T h46 (C h70 (T (T (T h74 h73) h10) h2))))))) (S (h y v31 v22))) h76) h91) h89)) (h v22 v23 v22)) (C h36 (C h92 (T (T (T (T (T (T (T h88 h33) (S h30)) h29) h27) h24) h14) h13)))))) (S (h v22 v23 v0))) (S (h z z v22))) h6) h5) h21) h20) h12

