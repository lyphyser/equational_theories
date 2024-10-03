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
theorem Equation895_implies_Equation2722 (G: Type _) [Magma G] (h: Equation895 G) : Equation2722 G := fun x y z =>
  let v0 := M y x
  have h1 := h z v0 y
  have h2 := R y
  let v3 := M x x
  have h4 := h v0 v0 (M v3 (M v0 x))
  have h5 := S h4
  have h6 := h x v0 x
  have h7 := R v0
  have h8 := C h7 (C h6 h6)
  let v9 := M z y
  have h10 := h (M v0 v3) v9 v9
  have h11 := S h10
  have h12 := R (M v9 v9)
  have h13 := R v9
  have h14 := S h6
  have h15 := C h7 (C h14 h14)
  have h16 := T h4 h15
  have h17 := C h16 h13
  have h18 := C h17 h12
  let v19 := M v0 v9
  have h20 := h v9 v19 x
  have h21 := S h20
  have h22 := R v19
  have h23 := C h22 (C h21 h21)
  let v24 := M v9 x
  have h25 := h v19 v19 (M v24 (M v19 x))
  have h26 := C h13 (T (T h25 h23) h18)
  have h27 := T (T (T h26 h11) h8) h5
  have h28 := C h27 h2
  let v29 := M v9 v19
  have h30 := h v29 v0 v9
  have h31 := S h30
  have h32 := S h25
  have h33 := C h22 (C h20 h20)
  have h34 := T h8 h5
  have h35 := C h34 h13
  have h36 := C h35 h12
  have h37 := C h13 (T (T h36 h33) h32)
  have h38 := C (T h10 h37) h13
  have h39 := T h17 h38
  have h40 := C h27 (C h39 h22)
  have h41 := T h40 h31
  have h42 := C h41 h2
  have h43 := C (T h26 h11) h13
  have h44 := T h43 h35
  have h45 := T (T (T h4 h15) h10) h37
  have h46 := C h45 (C h44 h22)
  have h47 := C (T (T (T h10 h37) h30) h46) h2
  have h48 := h y y x
  have h49 := R (M v0 v0)
  have h50 := h y x x
  have h51 := S h50
  have h52 := h x v19 v0
  have h53 := S h52
  have h54 := C h22 (T (T (T (T (T h40 h31) h26) h11) h8) h5)
  have h55 := h v9 v19 v19
  have h56 := T h55 h54
  have h57 := R (M x v0)
  have h58 := R x
  have h59 := T h50 (C h58 h34)
  have h60 := C h35 (T (C h59 h13) (C h57 h56))
  let v61 := M y v9
  have h62 := R v61
  have h63 := C h41 h13
  have h64 := C (T h63 h43) h62
  have h65 := T h30 h46
  have h66 := C h65 h13
  have h67 := C h66 h62
  have h68 := C h39 h62
  have h69 := C (T (T (T (T h68 h67) h64) h60) h53) h16
  have h70 := C h16 (T (C (T h69 h51) h49) (S h48))
  have h71 := h (M v19 v61) v0 v0
  have h72 := C h44 h62
  have h73 := C h63 h62
  have h74 := C (T h38 h66) h62
  have h75 := T (C h58 h16) h51
  have h76 := S h55
  have h77 := C h22 (T (T (T (T (T h4 h15) h10) h37) h30) h46)
  have h78 := T h77 h76
  have h79 := C h17 (T (C h57 h78) (C h75 h13))
  have h80 := h (M v19 v0) v9 v19
  have h81 := S h80
  have h82 := h (M v29 (M v19 v19)) v9 v9
  have h83 := C h78 (T (T (C h45 h7) (C h65 h7)) (C (T h82 (C h56 (T (T (T (T (C h63 h12) (C h43 h12)) h36) h33) h32))) h45))
  have h84 := C h56 (T (T (C (T (C h78 (T (T (T (T h25 h23) h18) (C h38 h12)) (C h66 h12))) (S h82)) h27) (C h41 h7)) (C h27 h7))
  let v85 := M v0 v24
  let v86 := M y y
  have h87 := R v86
  have h88 := S h71
  have h89 := C (T (T (T (T h52 h79) h74) h73) h72) h34
  have h90 := C h34 (T h48 (C (T h50 h89) h49))
  have h91 := C (T (T (T h40 h31) h26) h11) h2
  have h92 := C h65 h2
  have h93 := C h45 h2
  have h94 := S (h y v9 x)
  have h95 := C (T (T (T (T h93 h92) h91) h90) h88) h7
  let v96 := M v0 y
  have h97 := h v96 x v0
  T (T (T (T (T (T (T (T (T (T (T (T (T (T h52 h79) h74) h73) h72) h71) h70) h47) h42) h28) h97) (C (T (T (T (T (T (T (T (T h52 h79) h74) h73) h72) h71) h70) h47) h42) (C (T (T h95 h69) h51) h75))) (C h28 h87)) (h (M v96 v86) v19 v0)) (C h22 (T (T (T (C (T (T (T (C (T (T (C h93 h87) (C (T (T (T (T (T (T (T (T h92 h91) h90) h88) h68) h67) h64) h60) h53) (C (T (T h50 h89) (C (T (T (T (T h71 h70) h47) h42) h28) h7)) h59))) (S h97)) h7) h95) h69) h51) (T (T (T (T h77 h76) (h v9 v9 v85)) (C h13 (C h94 h94))) (C (C (T h1 (C h7 (T (T (C (T (T (T h55 h54) h80) h84) (T (T (T (T (T (T (T (T (T h93 h92) h91) h90) h88) h68) h67) h64) h60) h53)) (C (T h83 h81) h58)) (C h78 h58)))) h2) h87))) (S (h v85 y y))) (C h7 (T (T (C h56 h58) (C (T h80 h84) h58)) (C (T (T (T h83 h81) h77) h76) (T (T (T (T (T (T (T (T (T h52 h79) h74) h73) h72) h71) h70) h47) h42) h28))))) (S h1)))

