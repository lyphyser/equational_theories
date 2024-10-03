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
theorem Equation887_implies_Equation2146 (G: Type _) [Magma G] (h: Equation887 G) : Equation2146 G := fun x y z =>
  let v0 := M y y
  let v1 := M v0 z
  let v2 := M x z
  let v3 := M v1 v2
  let v4 := M v1 v1
  have h5 := R v4
  have h6 := h v1 v0 z
  have h7 := S h6
  let v8 := M z z
  let v9 := M v1 v0
  let v10 := M v9 v8
  have h11 := h v10 z y
  have h12 := S h11
  have h13 := h v0 z v0
  have h14 := S h13
  have h15 := R v0
  have h16 := h v0 z v4
  have h17 := S h16
  have h18 := h v1 v1 v1
  have h19 := R z
  have h20 := C h19 h18
  have h21 := R v1
  have h22 := h z v9 y
  have h23 := S h22
  have h24 := h v0 z y
  have h25 := R v9
  have h26 := C h25 (C h24 h15)
  have h27 := C (T h26 h23) h21
  have h28 := T (T h27 h20) h17
  have h29 := C h28 h15
  have h30 := C h21 h29
  let v31 := M v0 v0
  let v32 := M v9 v31
  have h33 := h v32 v1 y
  have h34 := S h24
  have h35 := C h25 (C h34 h15)
  have h36 := T (T (T h22 h35) h33) h30
  have h37 := S h33
  have h38 := C (T h22 h35) h21
  have h39 := C h19 (S h18)
  have h40 := T (T h16 h39) h38
  have h41 := C h40 h15
  have h42 := C h21 h41
  have h43 := T (T (T h42 h37) h26) h23
  have h44 := C h43 h36
  have h45 := C h36 h19
  have h46 := T (T h45 h44) h14
  have h47 := R (M v10 z)
  have h48 := C h43 h19
  have h49 := C h36 h43
  have h50 := T (T h13 h49) h48
  have h51 := h v32 v1 z
  have h52 := R v8
  have h53 := C (T h42 h37) h21
  have h54 := C h53 h52
  have h55 := C (T h33 h30) h21
  have h56 := T (T (T (T (T h44 h14) h16) h39) h38) h55
  have h57 := C h56 h50
  have h58 := R (M (M v1 v31) z)
  have h59 := C h58 h46
  have h60 := T (T (T (T (T h53 h27) h20) h17) h13) h49
  have h61 := C h60 h50
  have h62 := C h55 h15
  have h63 := C h46 h19
  have h64 := C h25 h50
  have h65 := h v0 v0 v0
  have h66 := R (M v31 v31)
  have h67 := C h25 (T (C h34 h66) (S h65))
  have h68 := h z v9 v31
  have h69 := h v8 z v0
  have h70 := S h68
  have h71 := C h25 (T h65 (C h24 h66))
  have h72 := C h25 h46
  have h73 := C (T (T (T (T (T (T h72 h71) h70) h22) h35) h33) h30) h21
  have h74 := R (M v10 v1)
  have h75 := C (T (T (T (T (T (T h42 h37) h26) h23) h68) h67) h64) h21
  have h76 := R (M v8 z)
  have h77 := C h50 h19
  have h78 := C (T (T (C h77 h46) (C h76 h50)) (C h63 h46)) h50
  have h79 := C (T (T (T h78 h72) h71) h70) (T (T (T (T (T (T (T (T (T (T h41 h62) h61) h59) h57) h54) (C h28 h52)) (C (T (T (T (T h16 h39) h38) h55) h75) h52)) (C h74 h46)) (C (T (T (T (T (T (T (T (T (T h73 h53) h27) h20) h17) h13) h49) h48) h69) (C (T (T h68 h67) h64) (T (T (T (C h63 (T (T (T (T (T h41 h62) h61) h59) h57) h54)) (S h51)) h26) h23))) h50)) (C h47 h46))
  have h80 := C h15 (T h79 h12)
  have h81 := h (M v1 v8) v0 v0
  have h82 := C (T (T h81 h80) h7) h50
  have h83 := S h81
  have h84 := C h53 h15
  have h85 := C h56 h46
  have h86 := C h58 h50
  have h87 := C h60 h46
  have h88 := C h55 h52
  have h89 := C (T (T (C h77 h50) (C h76 h46)) (C h63 h50)) h46
  have h90 := C (T (T (T h68 h67) h64) h89) (T (T (T (T (T (T (T (T (T (T (C h47 h50) (C (T (T (T (T (T (T (T (T (T (C (T (T h72 h71) h70) (T (T (T h22 h35) h51) (C h77 (T (T (T (T (T h88 h87) h86) h85) h84) h29)))) (S h69)) h45) h44) h14) h16) h39) h38) h55) h75) h46)) (C h74 h50)) (C (T (T (T (T h73 h53) h27) h20) h17) h52)) (C h40 h52)) h88) h87) h86) h85) h84) h29)
  have h91 := C h15 (T h11 h90)
  have h92 := T (T h6 h91) h83
  have h93 := C h92 h46
  have h94 := C h46 (T (T (T (T (T (T h6 h91) h83) h93) h78) h11) h90)
  have h95 := C (T h94 h83) h46
  have h96 := C h50 (T (T (T (T (T (T h79 h12) h89) h82) h81) h80) h7)
  have h97 := R (M v8 v1)
  have h98 := C h97 h50
  have h99 := C h50 h21
  have h100 := C h99 h46
  have h101 := C (T (T (T (T (T h100 h98) h95) h82) h81) h96) h50
  have h102 := C h46 h21
  have h103 := C h102 h50
  have h104 := C h97 h46
  let v105 := M v0 v1
  let v106 := M v105 v0
  have h107 := R v106
  have h108 := C (T h81 h96) h50
  have h109 := h x z (M v2 v2)
  have h110 := h v2 v2 v2
  T (T (h x z v1) (C (T (T (T (T (T (T (T h68 h67) h64) h89) h82) h81) h80) h7) (T (C (C (T h109 (C h19 (S h110))) h19) h5) (C (T (T (C (T (C h19 h110) (S h109)) h19) (h v2 v3 v1)) (C (R v3) (T (T (T (T (T (T (T (T (T (T (T (T (T (C (T (C (R v2) (h v3 v3 v3)) (S (h v1 v2 (M v3 v3)))) h5) (C h77 h5)) (C (T (T (T h63 h6) h91) h96) h5)) (C (T (T (T (T h94 h83) h93) h108) (C (T (T (T (T (T h94 h83) h93) h108) h104) h103) h46)) h5)) (C (T (C (T (T h100 h98) (C h102 h46)) h50) (C h107 h46)) (T (T (T (T (C h92 h21) (C (T (T (T h93 h108) h104) h103) h21)) (C (R (M v105 v8)) (T (T (T (T (T (T (T h6 h91) h83) h93) h78) h72) h71) h70))) (C (T (T (T (T (T (T h100 h98) h95) h82) h81) h80) h7) (T (T (T (T (T (T h68 h67) h64) h89) h108) h104) h103))) (S (h v0 v1 z))))) (C (R (M v106 v0)) h50)) (C (T (C h107 h50) (C (T (T (C h99 h50) h104) h103) h46)) h52)) (C (T (T h101 h104) h103) h46)) h101) h95) h82) h81) h80) h7))) h5)))) (S (h v3 v1 v1))

