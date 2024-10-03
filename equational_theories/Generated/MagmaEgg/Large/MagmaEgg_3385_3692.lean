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
theorem Equation3385_implies_Equation3692 (G: Type _) [Magma G] (h: Equation3385 G) : Equation3692 G := fun x y z =>
  let v0 := M z z
  let v1 := M y y
  have h2 := h v1 v0 v0
  have h3 := S h2
  have h4 := h z z z
  have h5 := R v0
  have h6 := C h5 (S h4)
  have h7 := h z z v0
  have h8 := T h7 h6
  have h9 := R v1
  have h10 := C h9 h8
  have h11 := S h7
  have h12 := C h5 h4
  have h13 := h v0 v0 z
  have h14 := h v0 z z
  have h15 := S h14
  have h16 := R z
  have h17 := C h16 h8
  have h18 := T h12 h11
  have h19 := C h16 h18
  have h20 := h z v0 v0
  let v21 := M v1 v0
  have h22 := h z (M v0 z) v21
  have h23 := R v21
  have h24 := h z v0 y
  have h25 := h v0 y y
  have h26 := S h25
  have h27 := h v0 v1 v0
  have h28 := S h27
  have h29 := C h9 h18
  have h30 := C h5 h29
  have h31 := C h5 (T (T h29 h2) h30)
  have h32 := T (T h2 h31) h28
  have h33 := R y
  have h34 := C h33 h32
  have h35 := h y v21 v1
  have h36 := S h35
  have h37 := h y y v1
  have h38 := S h37
  have h39 := h y y y
  have h40 := C h9 h39
  have h41 := h v1 v1 v0
  have h42 := h v0 v1 v21
  have h43 := T (T (T (T h2 h31) h28) h42) (C h23 (T (T (S h41) h40) h38))
  have h44 := C h5 h10
  have h45 := C h5 (T (T h44 h3) h10)
  have h46 := T (T h27 h45) h3
  have h47 := C h33 h46
  have h48 := C h9 (T (T h25 h47) (C h33 h43))
  have h49 := C h9 h26
  have h50 := h y v0 v1
  have h51 := h y v0 v0
  have h52 := S h50
  have h53 := C h9 h25
  have h54 := C h9 (S h39)
  have h55 := T (T (T (T (C h23 (T (T h37 h54) h41)) (S h42)) h27) h45) h3
  have h56 := C h9 (T (T (C h33 h55) h34) h26)
  have h57 := h y v1 v0
  have h58 := h v1 y y
  have h59 := h z v1 y
  let v60 := M z v1
  have h61 := h z v60 v21
  have h62 := T (T (T (T (T (T h61 (C h23 (C h16 (C (T (T (T (T h59 (C h33 (C h16 (T (T (T (T (T (T (T (T (T (T h58 (C h33 (T h40 h38))) h57) (C h5 (T (T (T (T h35 h56) h53) h52) (C h33 h8)))) (S h51)) h50) h49) h48) h36) h34) h26)))) (S h24)) h17) h15) h23)))) (S h22)) (C h16 (T (T (T (T h14 h19) h20) (C h5 h19)) (C h5 (T h17 h15))))) (S h13)) h12) h11
  have h63 := C h62 h10
  have h64 := S h61
  have h65 := C h23 (C h16 (C (T (T (T (T h14 h19) h24) (C h33 (C h16 (T (T (T (T (T (T (T (T (T (T h25 h47) h35) h56) h53) h52) h51) (C h5 (T (T (T (T (C h33 h18) h50) h49) h48) h36))) (S h57)) (C h33 (T h37 h54))) (S h58))))) (S h59)) h23))
  have h66 := C h16 (T (T (T (T (C h5 (T h14 h19)) (C h5 h17)) (S h20)) h17) h15)
  have h67 := h v0 v0 x
  have h68 := h v0 x v21
  have h69 := h x v21 v1
  have h70 := S h69
  have h71 := R x
  have h72 := C h9 (T (C h71 h46) (C h71 h43))
  have h73 := h x v0 v1
  have h74 := C h5 (T (T (T (C h71 h18) h73) h72) h70)
  have h75 := h x v0 v0
  have h76 := S h73
  have h77 := C h9 (T (C h71 h55) (C h71 h32))
  have h78 := T h44 h3
  have h79 := C h23 (T (T (T (T (T (C h71 h78) h69) h77) h76) h75) h74)
  have h80 := h x v0 v21
  have h81 := S h75
  have h82 := C h5 (T (T (T h69 h77) h76) (C h71 h8))
  have h83 := h v0 v0 v1
  have h84 := S h83
  have h85 := C h9 (T h44 (C h5 (T (T (T h29 h2) h31) h28)))
  have h86 := T h2 h30
  have h87 := C h9 h86
  have h88 := h v1 v21 v0
  have h89 := S h88
  have h90 := h v1 (M z v60) v21
  have h91 := h z z v1
  have h92 := C h62 (C h9 (T (T h91 h90) (C h23 (T (T (T (T (C h9 (T h63 h30)) h85) h84) h12) h11))))
  have h93 := T (T (T (T (T (T h7 h6) h13) h66) h22) h65) h64
  have h94 := C h93 h29
  have h95 := C (T (T (T (T (T (T (C h71 (T (T (T (T (T h69 h77) h76) h80) h79) (C (T (T (T (T (T (T (T (T h2 h94) h92) h89) h87) h85) h84) h12) h11) (T (T (T (T h82 h81) h80) h79) (S h68))))) (S h67)) h13) h66) h22) h65) h64) h23
  have h96 := S h80
  have h97 := C h23 (T (T (T (T (T h82 h81) h73) h72) h70) (C h71 h86))
  have h98 := C h9 (T (C h5 (T (T (T h27 h45) h3) h10)) h30)
  have h99 := T (T (T (T (T (T (T (T h7 h6) h83) h98) (C h9 h78)) h88) (C h93 (C h9 (T (T (C h23 (T (T (T (T h7 h6) h83) h98) (C h9 (T h44 h94)))) (S h90)) (S h91))))) h63) h3
  have h100 := C (T (T (T (T (T (T (T (T h2 h94) h92) h89) h87) h85) h84) h67) (C h71 (T (T (T (T (T (C h99 (T (T (T (T h68 h97) h96) h75) h74)) h97) h96) h73) h72) h70))) (T (T h95 h63) h3)
  let v101 := M x (M x v21)
  T (T (T (T (T (T (h x x v21) (h v21 v101 v0)) (C h99 (T (C h23 (C (R v101) h99)) h100))) h100) h95) h63) h3

