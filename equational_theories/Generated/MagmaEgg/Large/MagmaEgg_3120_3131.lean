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
theorem Equation3120_implies_Equation3131 (G: Type _) [Magma G] (h: Equation3120 G) : Equation3131 G := fun x y z =>
  let v0 := M y x
  let v1 := M v0 z
  let v2 := M v1 z
  let v3 := M v2 y
  have h4 := R v3
  have h5 := h v2 v1 v3
  have h6 := S h5
  have h7 := R v1
  have h8 := R v2
  have h9 := h v1 z v2
  have h10 := S h9
  have h11 := R z
  have h12 := h z v1 v1
  have h13 := S h12
  have h14 := h v2 z v2
  have h15 := S h14
  have h16 := h z v1 v2
  have h17 := h v1 v2 v2
  have h18 := C (T h17 (C (S h16) h8)) h11
  have h19 := C (C h18 h8) h8
  have h20 := h v2 v2 v1
  have h21 := C (T (T (T h19 h15) h20) (C (C (T h19 h15) h7) h7)) h7
  have h22 := C (T h21 h13) h7
  have h23 := C (T h20 h22) h11
  have h24 := C (C h23 h8) h8
  have h25 := h z v2 v2
  have h26 := C (T (T (T h21 h13) h25) (C (T h24 h10) h8)) h7
  have h27 := h v2 v1 z
  have h28 := S h27
  have h29 := C (T (C h16 h8) (S h17)) h11
  have h30 := C (C h29 h8) h8
  have h31 := S h20
  have h32 := C (T (T (T (C (C (T h14 h30) h7) h7) h31) h14) h30) h7
  have h33 := C (T h12 h32) h7
  have h34 := C (T h33 h26) h11
  have h35 := C (T (T (T (C h34 h11) h28) h20) h26) h11
  have h36 := h v1 z z
  have h37 := h v1 z v1
  have h38 := S h37
  have h39 := S h25
  have h40 := C (T h33 h31) h11
  have h41 := C (C h40 h8) h8
  have h42 := C (T (T (T (C (T h9 h41) h8) h39) h12) h32) h7
  have h43 := C (T h42 h22) h11
  have h44 := C (C (T (T h36 h35) h43) h7) h7
  have h45 := S h36
  have h46 := C (T (T (T h42 h31) h27) (C h43 h11)) h11
  have h47 := C (C (T (T h34 h46) h45) h7) h7
  have h48 := h v1 v1 v0
  have h49 := S h48
  have h50 := R v0
  have h51 := h z v0 v0
  have h52 := C (T (T (T (T (T h23 h34) h46) h45) h9) h41) h8
  have h53 := C (T (T (T (T (T h24 h10) h36) h35) h43) h40) h8
  have h54 := h z v2 z
  have h55 := S h54
  have h56 := C (C (T h25 h53) h11) h11
  have h57 := C (C (T h52 h39) h11) h11
  have h58 := C (T (T (T (T (C (T (T (T (T (T (C (T h54 h57) h50) (C (T (T (T h56 h55) h25) h53) h50)) (C (T (T (T h52 h39) h51) (C (T (T (T (C (C (T h37 h47) h50) h50) h49) h37) h47) h50)) h50)) h49) h37) h47) h11) (C (T (T (T h44 h38) h36) h35) h11)) h28) h20) h26) h4
  have h59 := C h58 h4
  have h60 := h v0 z v3
  have h61 := T (T h60 h59) h6
  have h62 := C (T (T (T (T (T h44 h38) h48) (C (T (T (T (C (T (T (T h44 h38) h48) (C (C (T h44 h38) h50) h50)) h50) (S h51)) h25) h53) h50)) (C (T (T (T h52 h39) h54) h57) h50)) (C (T h56 h55) h50)) h11
  have h63 := C (T (T (T h46 h45) h37) h47) h11
  have h64 := C (T (T (T (T (C (T (T (T (T (T h60 h59) h6) h27) h63) h62) h4) h58) (C (T (T (T h42 h31) h14) h30) h4)) (C (T (T h19 h15) h18) h4)) (C h29 h4)) h61
  have h65 := S h60
  have h66 := C (C (T (T (T (T h42 h31) h27) h63) h62) h4) h4
  have h67 := h v2 y v3
  have h68 := S h67
  have h69 := R y
  have h70 := h y v2 v0
  have h71 := S h70
  have h72 := T (T h5 h66) h65
  have h73 := C h4 h61
  have h74 := h v3 y v3
  have h75 := S h74
  have h76 := h y v2 v3
  have h77 := h v0 v3 v3
  have h78 := C (C (C (T (T (T (T h5 h66) h65) h77) (C (T (C (C h73 h4) h4) (S h76)) h4)) h69) h4) h4
  have h79 := R (M (M v3 v3) v3)
  have h80 := C h79 h61
  have h81 := h v3 v3 v0
  have h82 := C (T (T (T h78 h75) h81) (C (T (T h80 (C (T h78 h75) h72)) h73) h50)) h72
  have h83 := C (T (T h80 h82) h71) h61
  have h84 := C (T h81 h83) h69
  have h85 := C (C h84 h4) h4
  have h86 := h y v3 v3
  have h87 := C (T (T (T (T h80 h82) h71) h86) (C (T (T (T (T h85 h68) h5) h66) h65) h4)) h50
  have h88 := C h79 h72
  have h89 := C h4 h72
  have h90 := C (C (C (T (T (T (T (C (T h76 (C (C h89 h4) h4)) h4) (S h77)) h60) h59) h6) h69) h4) h4
  have h91 := C (T (T h89 (C (T h74 h90) h61)) h88) h50
  have h92 := S h86
  have h93 := S h81
  have h94 := C (T (T (T h91 h93) h74) h90) h61
  have h95 := C (T (T h70 h94) h88) h72
  have h96 := C (T h95 h93) h69
  have h97 := C (C h96 h4) h4
  have h98 := h v2 y y
  have h99 := C (T (T (T (T (C (T (T (T (T h60 h59) h6) h67) h97) h4) h92) h70) h94) h88) h50
  have h100 := C (T h99 h83) h69
  have h101 := h v3 v0 y
  have h102 := C (T h95 h87) h69
  have h103 := C (T (T (T (T (T h84 h102) (C (T (T (T h99 h93) h101) (C h100 h69)) h69)) (S h98)) h67) h97) h4
  have h104 := C (T (T (T (T (T h85 h68) h98) (C (T (T (T (C h102 h69) (S h101)) h81) h87) h69)) h100) h96) h4
  have h105 := h y v3 y
  have h106 := C (C (T h103 h92) h69) h69
  have h107 := R x
  T (T (h x v2 v3) (C (T (C (T (T (T (T (T (T (T (C (T (T (T (C (T (T (T h5 h66) h65) (C (T h105 h106) h107)) h107) (S (h y y x))) h105) h106) h72) (C (R (M (M y y) y)) h61)) (C (T (T (T (C (C (T h86 h104) h69) h69) (S h105)) h86) h104) h72)) (C (R (M (M v3 y) v3)) h61)) (C (T (T (T (T (T h103 h92) h70) (C (T h91 h87) h61)) (C h64 h72)) (C (R (M (M v2 v3) v2)) h61)) h8)) (S (h v3 v2 v2))) h81) h87) h4) (C h64 h4)) h4)) (S (h v3 v2 v3))

