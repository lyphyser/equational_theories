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
theorem Equation1293_implies_Equation26 (G: Type _) [Magma G] (h: Equation1293 G) : Equation26 G := fun x y =>
  let v0 := M x y
  let v1 := M v0 y
  have h2 := R v0
  have h3 := R y
  let v4 := M (M (M v1 v1) x) x
  have h5 := h v0 y v4
  have h6 := S h5
  have h7 := R v4
  have h8 := h v1 v1 x
  have h9 := C h3 (T h8 (C h8 h7))
  have h10 := R v1
  let v11 := M v0 v1
  let v12 := M v11 v1
  have h13 := h y v12 y
  have h14 := S h13
  have h15 := h x y v1
  have h16 := R v12
  have h17 := C h16 (C (C h15 h3) h3)
  have h18 := C (T h17 h14) h10
  have h19 := T (T h18 h9) h6
  have h20 := C h19 h3
  have h21 := C h16 (C (C (S h15) h3) h3)
  let v22 := M (M (M v0 v0) x) x
  let v23 := M v1 v0
  let v24 := M v23 v0
  have h25 := h y v24 v22
  have h26 := S h25
  have h27 := R v22
  have h28 := h v0 y v0
  have h29 := h v0 v0 x
  have h30 := R v24
  have h31 := C h30 (T h29 (C (T h29 (C h28 h27)) h27))
  have h32 := C h10 h19
  have h33 := h v11 v1 v1
  have h34 := C (C (T h33 h32) h2) h2
  have h35 := C (T (T (T (T h34 h31) h26) h13) h21) h10
  have h36 := C h35 h3
  let v37 := M (M v11 v0) v0
  have h38 := h v37 v0 y
  have h39 := S h38
  have h40 := S h33
  have h41 := C (T h13 h21) h10
  have h42 := S h8
  have h43 := C h3 (T (C h42 h7) h42)
  have h44 := T (T h5 h43) h41
  have h45 := C h10 h44
  have h46 := C (C (T h45 h40) h2) h2
  have h47 := S h29
  have h48 := C h30 (T (C (T (C (S h28) h27) h47) h27) h47)
  have h49 := C (T (T h25 h48) h46) h2
  have h50 := C h3 (T (C h47 h27) h47)
  have h51 := h x y v22
  have h52 := C (T (T h51 h50) h49) h3
  have h53 := C (T (T (T (T h35 h18) h9) h6) h52) h3
  have h54 := C (T (T (T (T h17 h14) h25) h48) h46) h10
  have h55 := C h54 h3
  have h56 := C h44 h3
  have h57 := T (T h56 h55) h53
  have h58 := T (T (T h35 h18) h9) h6
  have h59 := C h58 h57
  have h60 := C (T h59 h39) h10
  have h61 := T (T (T h5 h43) h41) h54
  have h62 := C (T (T h45 h40) (C h61 h10)) h10
  have h63 := h (M v23 v1) y v0
  have h64 := S h63
  have h65 := C (T (T (C h58 h10) h33) h32) h10
  have h66 := S h51
  have h67 := C h3 (T h29 (C h29 h27))
  have h68 := C (T (T h34 h31) h26) h2
  have h69 := C (T (T h68 h67) h66) h3
  have h70 := C (T (T (T (T h69 h5) h43) h41) h54) h3
  have h71 := T (T h70 h36) h20
  have h72 := C h61 h71
  have h73 := C (T h38 h72) h10
  have h74 := C (T (T (T (T (T (T h69 h5) h43) h41) h54) h73) h65) h3
  have h75 := C (T (T (T h56 h55) h53) h74) (T (T (T (T h60 h35) h18) h9) h6)
  have h76 := h v37 v1 v1
  have h77 := C (T h76 h75) h2
  have h78 := T (T (T h51 h50) h49) h77
  have h79 := C (T (T (T (T (T (T (T (C h3 h78) h64) h62) h60) h35) h18) h9) h6) h57
  let v80 := M (M y x) v1
  have h81 := h v80 v0 y
  have h82 := S h81
  have h83 := S h76
  have h84 := C (T (T (T (T (T (T h62 h60) h35) h18) h9) h6) h52) h3
  have h85 := C (T (T (T h84 h70) h36) h20) (T (T (T (T h5 h43) h41) h54) h73)
  have h86 := C (T h85 h83) h2
  have h87 := T (T (T h86 h68) h67) h66
  have h88 := C (T (T (T (T (T (T (T h5 h43) h41) h54) h73) h65) h63) (C h3 h87)) h71
  have h89 := C (T (T (T h85 h83) h38) h88) h2
  have h90 := C (T (T (T (T (T (T (T (C (T (T (T (T h79 h39) h34) h31) h26) h78) h64) h62) h60) h35) h18) h9) h6) (T (T (T (T h56 h55) h53) h74) (C (T (T (T (T (T (T (T h62 h60) h35) h18) h9) h6) h52) (C (T h77 h89) h3)) h3))
  have h91 := R x
  have h92 := h v80 v0 v0
  have h93 := C (T (T (T h90 h82) h79) h72) h10
  have h94 := h v80 x v1
  have h95 := C (T (T (C (C h44 h91) h91) (C (C h54 h91) h91)) (C (T (C h58 (T (T (T (T (T h51 h50) h49) h77) h89) (C (T h94 (C (T (T (T (T h51 h50) h49) h77) h89) (T (T (T (T (T h93 h60) h35) h18) h9) h6))) h2))) (S h92)) h91)) h10
  have h96 := C (C h19 h91) h91
  have h97 := C (C h35 h91) h91
  have h98 := C (T (T (T h79 h39) h76) h75) h2
  have h99 := C (T (T (T (T h25 h48) h46) h38) h88) h87
  have h100 := C (T h92 (C h61 (T (T (T (T (T (C (T (C (T (T (T (T h98 h86) h68) h67) h66) (T (T (T (T (T h5 h43) h41) h54) h73) (C (T (T (T h59 h88) h81) (C (T (T (T (T (T (T (T h5 h43) h41) h54) h73) h65) h63) h99) (T (T (T (T (C (T (T (T (T (T (T (T (C (T h98 h86) h3) h69) h5) h43) h41) h54) h73) h65) h3) h84) h70) h36) h20))) h10))) (S h94)) h2) h98) h86) h68) h67) h66))) h91
  T (T (h x y v0) (C h3 (T (T (T (C (C h44 h2) h2) (C (C h54 h2) h2)) (C (C (T h73 h65) h2) h2)) (C (C (T (T (T (T (T (T (T (T h63 h99) h100) h97) h96) (h (M (M v0 x) x) v1 v1)) (C (T h56 h55) (T (T (T (T (T (T (T (T (C (T (T (T (T (T (T (T (C h95 h10) h93) h65) h63) h99) h100) h97) h96) h10) h95) h90) h82) h79) h39) h34) h31) h26))) (C h36 h3)) (C h20 h3)) h2) h2)))) (S (h v1 y v0))

