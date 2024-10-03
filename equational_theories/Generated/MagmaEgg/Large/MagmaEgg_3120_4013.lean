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
theorem Equation3120_implies_Equation4013 (G: Type _) [Magma G] (h: Equation3120 G) : Equation4013 G := fun x y z =>
  let v0 := M y z
  let v1 := M z v0
  let v2 := M v1 x
  have h3 := R v2
  have h4 := R x
  have h5 := C (T (h v1 v2 v2) (C (S (h x v1 v2)) h3)) h4
  have h6 := R v1
  have h7 := h v2 v1 v1
  have h8 := R v0
  have h9 := h z v1 v1
  have h10 := h v0 z v1
  have h11 := C (T (C h10 h6) (S h9)) h8
  have h12 := C (T h9 (C (S h10) h6)) h8
  have h13 := h v1 v0 v1
  have h14 := S h13
  have h15 := C (C h12 h6) h6
  have h16 := C (C h11 h6) h6
  have h17 := h v1 z z
  have h18 := S h17
  have h19 := R z
  have h20 := h z v0 v0
  have h21 := S h20
  have h22 := h v0 z z
  have h23 := T h15 h14
  have h24 := h v1 v1 z
  have h25 := C (T (C (T (T (T h15 h14) h24) (C (C h23 h19) h19)) h19) (S h22)) h19
  have h26 := C (T (T (T h15 h14) h24) h25) h8
  have h27 := h v1 v1 v0
  have h28 := S h24
  have h29 := T h13 h16
  have h30 := C (T h22 (C (T (T (T (C (C h29 h19) h19) h28) h13) h16) h19)) h19
  have h31 := C (T (T (T h30 h28) h27) (C h26 h8)) h8
  have h32 := C h29 h8
  have h33 := C (T (T (T h32 h26) h31) h21) h6
  have h34 := h v0 v1 z
  have h35 := h v0 v1 v1
  have h36 := C h23 h8
  have h37 := C (T (T (T h30 h28) h13) h16) h8
  have h38 := C (T h37 h36) h6
  have h39 := h z v0 v1
  have h40 := C (T h32 h26) h6
  have h41 := C (T (T (T (C h37 h8) (S h27)) h24) h25) h8
  have h42 := C (T (T (T h20 h41) h37) h36) h6
  have h43 := C (T (T (T (T (T h42 h40) (C (T (T (T h31 h21) h39) (C h38 h6)) h6)) (S h35)) h34) (C (C h33 h19) h19)) h19
  have h44 := S h34
  have h45 := C (C h42 h19) h19
  have h46 := C (T (T (T (T (T h45 h44) h35) (C (T (T (T (C h40 h6) (S h39)) h20) h41) h6)) h38) h33) h19
  have h47 := h v1 z x
  have h48 := S h47
  have h49 := T h17 h46
  have h50 := C (C h49 h4) h4
  have h51 := C (T (T (T h50 h48) h17) h46) h3
  have h52 := h x v2 v1
  have h53 := h x v2 v2
  have h54 := S h53
  have h55 := C (C (T h43 h18) h4) h4
  have h56 := C (T (T (T h43 h18) h47) h55) h3
  have h57 := C h56 h3
  have h58 := h v1 z v2
  have h59 := C (T (T (T h50 h48) h58) h57) h3
  have h60 := C (T (C (T (T (T h59 h54) h52) (C (C (T (T (T h51 (C (T (T (T h43 h18) h13) h16) h3)) (C (T (T h15 h14) h12) h3)) (C h11 h3)) h6) h6)) h6) (S h7)) h6
  have h61 := h x v1 y
  have h62 := S h61
  have h63 := R y
  have h64 := C (T h52 h60) h63
  let v65 := M x y
  have h66 := h v65 y v65
  have h67 := S h66
  have h68 := R v65
  have h69 := h y v65 v65
  have h70 := S h52
  have h71 := S h58
  have h72 := C h51 h3
  have h73 := C (T (T (T h72 h71) h47) h55) h3
  have h74 := C (T h7 (C (T (T (T (C (C (T (T (T (C h12 h3) (C (T (T h11 h13) h16) h3)) (C (T (T (T h15 h14) h17) h46) h3)) h56) h6) h6) h70) h53) h73) h6)) h6
  have h75 := C (T h74 h70) h63
  have h76 := C h75 h63
  have h77 := C (T (T (T h74 h70) h61) h76) h68
  have h78 := h x v1 v65
  have h79 := C h64 h63
  have h80 := C (C (T h64 (C (T (T (T h74 h70) h78) (C (T (T h77 (C (T (T (T h79 h62) h78) (C h77 h68)) h68)) (S h69)) h68)) h63)) h68) h68
  have h81 := C (T (T h80 h67) h64) h63
  have h82 := S h78
  have h83 := C (T (T (T h79 h62) h52) h60) h68
  have h84 := C h83 h68
  have h85 := C (C (T (C (T (T (T (C (T (T h69 (C (T (T (T h84 h82) h61) h76) h68)) h83) h68) h82) h52) h60) h63) h75) h68) h68
  have h86 := h v65 v65 x
  have h87 := S h86
  have h88 := C (T (T (T (C (C (T h66 h85) h4) h4) h87) h66) h85) h4
  have h89 := h y x x
  have h90 := C (T (T (T (C (T h89 h88) h4) h87) h66) h85) h63
  have h91 := C (T h80 h67) h4
  have h92 := C (T (T (T h80 h67) h86) (C (T (C (T (T (T h80 h67) h86) (C h91 h4)) h4) (S h89)) h4)) h63
  have h93 := C (T (T h75 h66) h85) h63
  have h94 := h x y x
  have h95 := C (C (T (T h90 h81) h62) h4) h4
  have h96 := C (T (T (T h74 h70) h53) h73) h3
  T (T (h v65 v1 v2) (C (C (T (T (T (T (T (C (T (T (T (T (T (C h49 h68) (C (T (T (T (T h43 h18) h58) h57) (C (T (T (T h59 h54) h52) h60) h3)) h68)) (C (T (T (T (T (T (T (T (T h96 h72) h71) (h v1 v2 z)) (C (T (T (T (C (T (T (T (T h96 h72) h71) h17) h46) h19) h45) h44) (C (T (T h89 h88) h91) h19)) h19)) (S (h y x z))) h69) (C (T (T (T (T h84 h82) h61) h93) h92) h68)) (C (T (T (T (T h90 h81) h62) h94) h95) h68)) h68)) (S (h x x v65))) h94) h95) h6) (C (T (T (T (T (C (C (T (T h61 h93) h92) h4) h4) (S h94)) h61) h93) h92) h6)) (C (T (T (T (T h90 h81) h62) h52) h60) h6)) (C (C h5 h6) h6)) (S (h v2 x v1))) h5) h3) h3)) (S (h v2 x v2))

