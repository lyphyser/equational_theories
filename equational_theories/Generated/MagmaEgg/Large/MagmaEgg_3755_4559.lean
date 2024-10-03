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
theorem Equation3755_implies_Equation4559 (G: Type _) [Magma G] (h: Equation3755 G) : Equation4559 G := fun x y z w =>
  let v0 := M w x
  have h1 := h v0 z x
  let v2 := M x z
  let v3 := M z v0
  let v4 := M v0 z
  let v5 := M x v2
  have h6 := S (h x v2 v4)
  have h7 := h x z y
  have h8 := S h7
  let v9 := M y z
  let v10 := M z x
  have h11 := h v10 v9 v9
  have h12 := S h11
  have h13 := h v9 v9 z
  have h14 := S h13
  let v15 := M z v9
  let v16 := M v9 v9
  have h17 := h v16 v15 v4
  have h18 := S h17
  have h19 := h v4 v15 x
  have h20 := S h19
  have h21 := R (M x v15)
  have h22 := h v9 z v0
  have h23 := h v9 z y
  have h24 := S h23
  have h25 := C (T h24 h22) h21
  have h26 := h v9 v15 x
  have h27 := R v16
  have h28 := h z v9 z
  have h29 := S h28
  let v30 := M v9 z
  have h31 := h v30 v15 x
  have h32 := S h31
  have h33 := h v9 z v9
  have h34 := S h22
  have h35 := C (T h34 h33) h21
  have h36 := h v15 v9 v9
  have h37 := C (T (T (T h34 h23) h36) (C (T (T (T (T h26 h25) h35) h32) h29) h27)) (T (T h26 h25) h20)
  have h38 := h v4 v15 v9
  have h39 := S h33
  have h40 := C (T h39 h22) h21
  have h41 := h z v9 v9
  have h42 := h v30 v16 v4
  have h43 := R (M v4 v16)
  have h44 := R v30
  have h45 := T (T (T (T (T (T (T h28 h31) h40) h20) h38) h37) h18) h14
  have h46 := R v9
  have h47 := S h38
  have h48 := S h26
  have h49 := C (T h34 h23) h21
  have h50 := C (T (T (T (C (T (T (T (T h28 h31) h40) h49) h48) h27) (S h36)) h24) h22) (T (T h19 h49) h48)
  have h51 := T (T (T (T (T (T (T h13 h17) h50) h47) h19) h35) h32) h29
  have h52 := h v9 v16 v4
  have h53 := h v9 v10 x
  have h54 := S h53
  have h55 := R (M x v10)
  have h56 := h v10 v9 x
  let v57 := M x v9
  have h58 := R v57
  have h59 := h v9 v10 v57
  have h60 := S h59
  have h61 := h v9 x z
  have h62 := C h7 h61
  have h63 := h z x v9
  have h64 := C (T (C (T (T h63 h62) h60) h58) (S h56)) h55
  have h65 := h v57 v10 x
  have h66 := h v9 x v9
  have h67 := S h66
  have h68 := h x v9 v4
  have h69 := S h68
  let v70 := M v9 x
  let v71 := M v4 v9
  have h72 := h v71 v70 v57
  have h73 := h v71 v70 x
  have h74 := R (M x v70)
  have h75 := h x v9 v9
  have h76 := S h75
  have h77 := h v16 v70 x
  have h78 := C (T (T (T (T (T (T (T (T (T h77 (C (T h76 h68) h74)) (S h73)) h72) (C h69 h67)) h67) h61) h65) h64) h54) (T (T (T (T (T (T (T (T (T (T (T h52 (C (T (T (T (C h51 h46) h24) h33) (C h45 h44)) h43)) (S h42)) (S h41)) h28) h31) h40) h20) h38) h37) h18) h14)
  have h79 := h v70 v16 v9
  let v80 := M x v57
  have h81 := h x v9 x
  have h82 := S h72
  have h83 := C h68 h66
  have h84 := S h61
  have h85 := S h65
  have h86 := C h8 h84
  have h87 := C (T h56 (C (T (T h59 h86) (S h63)) h58)) h55
  have h88 := h z x w
  have h89 := C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (S h88) h63) h62) h60) h53) h87) h85) h84) h66) h83) h82) h73) (C (T (T (T h69 h81) (h v70 v57 x)) (C h67 (R v80))) h74)) (S (h v80 v70 x))) (S (h v57 x v9))) (C (T (T (T (T h75 h79) h78) h12) h8) (R x))) (R (M v4 v2))
  have h90 := h v0 v2 v4
  have h91 := S (h v0 v2 x)
  have h92 := C (T (S (h z x z)) h88) (R v5)
  have h93 := h v10 v2 x
  have h94 := h x z x
  have h95 := R v4
  have h96 := h z v0 z
  T (T (T (T (T h81 (h v70 v57 v4)) (C (T (T (T (T (T (T (T (T h67 h61) h65) h64) h54) h59) h86) (h v2 v70 v4)) (C (T (T (T (T (T (T (T (T (T (T (T (T (T (C (R v70) (T (T (T (T h7 h11) (C (T (T (T (T (T (T (T (T (T h53 h87) h85) h84) h66) h83) h82) h73) (C (T h69 h75) h74)) (S h77)) (T (T (T (T (T (T (T (T (T (T (T h13 h17) h50) h47) h19) h35) h32) h29) h41) h42) (C (T (T (T (C h51 h44) h39) h23) (C h45 h46)) h43)) (S h52)))) (S h79)) h76)) (S h81)) h75) h79) h78) h12) h8) h94) h93) h92) h91) h90) h89) h6) (T (T (T (T (C h95 (h v9 x w)) (S (h z v0 v57))) h96) (C h1 h96)) (S (h v2 v3 v4))))) (C h95 (T (T (T (T (T (T (T (T (T (T (T h75 h79) h78) h12) h8) h94) h93) h92) h91) h90) h89) h6)))) (S (h (M v2 v3) v5 v4))) (S (h v3 v2 x))) (S h1)

