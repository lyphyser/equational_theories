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
theorem Equation3182_implies_Equation3500 (G: Type _) [Magma G] (h: Equation3182 G) : Equation3500 G := fun x y z =>
  let v0 := M z z
  let v1 := M v0 y
  let v2 := M y v1
  have h3 := R x
  have h4 := R v1
  have h5 := R v2
  let v6 := M x x
  have h7 := h v1 v6 y
  have h8 := R y
  have h9 := R v6
  have h10 := h v6 z v6
  have h11 := S h10
  have h12 := R z
  have h13 := h z v1 z
  have h14 := S h13
  have h15 := h y z z
  have h16 := C (C h15 h4) h12
  have h17 := h v2 z v0
  have h18 := S h17
  have h19 := R v0
  have h20 := h z v2 z
  have h21 := S h20
  have h22 := C (C (S h15) h4) h12
  have h23 := C (C (C (T h13 h22) h12) h5) h12
  have h24 := C (T h23 h21) h19
  have h25 := C h24 h5
  have h26 := h z v0 v2
  have h27 := C (T h26 h25) h12
  have h28 := C h27 h19
  have h29 := T h28 h18
  have h30 := C h29 h12
  have h31 := S h26
  have h32 := C (C (C (T h16 h14) h12) h5) h12
  have h33 := C (T h20 h32) h19
  have h34 := C h33 h5
  have h35 := C (T h34 h31) h12
  have h36 := C h35 h19
  have h37 := h z v0 v0
  have h38 := S h37
  have h39 := T h17 h36
  have h40 := C h39 h12
  have h41 := C (T h33 (C (T (T (T (T h23 h21) h13) h22) h40) h19)) h19
  have h42 := C (T (T (T h41 h38) h26) h25) h12
  have h43 := C h42 h19
  have h44 := h v0 z v0
  have h45 := S h44
  have h46 := C (T (C (T (T (T (T h30 h16) h14) h20) h32) h19) h24) h19
  have h47 := C (T (T (T h34 h31) h37) h46) h12
  have h48 := C h47 h19
  have h49 := T (T h17 h48) h45
  have h50 := C (T (T (T (T h28 h48) h45) h27) h47) h49
  have h51 := C h39 h5
  have h52 := T (T (T h51 h50) h43) h36
  have h53 := C h52 h12
  have h54 := C h29 h5
  have h55 := T (T h44 h43) h18
  have h56 := C (T (T (T (T h42 h35) h44) h43) h36) h55
  have h57 := h v2 v2 v6
  have h58 := S h57
  have h59 := C h29 h9
  have h60 := C h52 h9
  have h61 := C (C (T h60 h59) h5) h5
  have h62 := h v6 v2 v2
  have h63 := C (T h62 h61) h9
  have h64 := C (T (T (T (T (T h63 h58) h17) h48) h56) h54) h12
  have h65 := h z v6 v6
  have h66 := h z v2 v2
  have h67 := S h66
  have h68 := T (T (T h28 h48) h56) h54
  have h69 := C h68 h12
  have h70 := C (C (T (T (T h13 h22) h40) h69) h5) h5
  have h71 := C (C (T (T (T h53 h30) h16) h14) h5) h5
  have h72 := C (T (T (T (T (T (T h51 h50) h45) h27) h47) (C (T (T (T h41 h38) h66) h71) h12)) (C (T (T (T h70 h67) h65) (C (C (T (T (T (T h64 h53) h30) h16) h14) h9) h9)) h12)) h9
  have h73 := C h68 h9
  have h74 := C h39 h9
  have h75 := T (T (T h74 h73) h72) h11
  have h76 := C h75 h8
  have h77 := h v6 y v1
  have h78 := C (T (C (C (T h74 h73) h5) h5) (S h62)) h9
  have h79 := C (T (T (T (T (T h51 h50) h43) h18) h57) h78) h12
  have h80 := C (T (T (T (T (T (T (C (T (T (T (C (C (T (T (T (T h13 h22) h40) h69) h79) h9) h9) (S h65)) h66) h71) h12) (C (T (T (T h70 h67) h37) h46) h12)) h42) h35) h44) h56) h54) h9
  have h81 := h v6 v0 v0
  have h82 := C (T (T (T (T (T (C (C h74 h19) h49) (S h81)) h10) h80) h60) h59) h9
  have h83 := h v0 v2 v6
  have h84 := T (C (T (T (T (T (T h17 h48) h45) h83) h82) (C (T (T (T (T (T h74 h73) h72) h11) h77) (C h76 h4)) h9)) h8) (S h7)
  have h85 := S h83
  have h86 := C (T (T (T (T (T h74 h73) h72) h11) h81) (C (C h59 h19) h55)) h9
  have h87 := T (T (T h10 h80) h60) h59
  have h88 := C h87 h8
  have h89 := C (T (T (T (T (T (C (T (T (T (T (T (C h88 h4) (S h77)) h10) h80) h60) h59) h9) h86) h85) h44) h43) h18) h8
  have h90 := h y z y
  have h91 := h v2 v6 y
  have h92 := h y v2 v6
  have h93 := h z y y
  have h94 := h z v2 v6
  have h95 := h v2 v6 z
  have h96 := h y y v1
  have h97 := h v1 v1 y
  have h98 := S h97
  have h99 := S h92
  have h100 := C (C h88 h5) h9
  have h101 := C (T (T (C (T (T (T (C (C (T (T (T (T (T h13 h22) h40) h69) h79) (C (T (T (T h63 h58) h91) (C (T h100 h99) h8)) h12)) h8) h8) (S h93)) h94) (C (C (C h75 h12) h5) h9)) h12) (S h95)) (C (T h96 (C (C h84 h8) h4)) h4)) h8
  T (C (T (h x v2 v1) (C (T (C (C (T (T (T (C (T (T (h v2 v6 v2) (C (T (T (T (T (T (T (C (T (C (C (T h10 h80) h5) h5) h61) h9) h58) h17) h48) h45) h83) h82) h5)) (C (T (T (T (T (T (T h86 h85) h44) h43) h18) h91) (C (T (T (T (T (T (T h100 h99) h90) h101) h98) h7) h89) (T (T h90 h101) h98))) h5)) (T (T h97 (C (T (T (C (T (C (C (T h7 h89) h8) h4) (S h96)) h4) h95) (C (T (T (T (C (C (C h87 h12) h5) h9) (S h94)) h93) (C (C (T (T (T (T (T (C (T (T (T (C (T h92 (C (C h76 h5) h9)) h8) (S h91)) h57) h78) h12) h64) h53) h30) h16) h14) h8) h8)) h12)) h8)) (S h90))) (S (h v1 v2 y))) h7) h89) h3) h5) (C (C h84 h3) h5)) h4)) h3) (S (h v2 v1 x))

