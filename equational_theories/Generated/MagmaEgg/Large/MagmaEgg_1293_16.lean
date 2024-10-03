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
theorem Equation1293_implies_Equation16 (G: Type _) [Magma G] (h: Equation1293 G) : Equation16 G := fun x y =>
  let v0 := M y x
  have h1 := R v0
  let v2 := M (M (M v0 v0) x) x
  have h3 := h y x v2
  have h4 := S h3
  have h5 := R v2
  have h6 := h v0 v0 x
  have h7 := R x
  have h8 := C h7 (T h6 (C h6 h5))
  have h9 := T h8 h4
  have h10 := C h9 h1
  have h11 := h (M (M x v0) v0) y y
  have h12 := S h11
  have h13 := R y
  have h14 := S h6
  have h15 := C h7 (T (C h14 h5) h14)
  have h16 := T h3 h15
  have h17 := C h16 h1
  have h18 := C (C (C h17 h13) h13) h13
  have h19 := h y y x
  have h20 := S h19
  let v21 := M (M (M y y) x) x
  have h22 := R v21
  have h23 := h y v0 y
  let v24 := M y v0
  let v25 := M (M v24 y) y
  have h26 := R v25
  have h27 := C h26 (T (C (T (C (S h23) h22) h20) h22) h20)
  have h28 := h v0 v25 v21
  let v29 := M (M (M v24 v24) x) x
  have h30 := h y v0 v29
  have h31 := S h30
  have h32 := R v29
  have h33 := h v24 v24 x
  have h34 := C h1 (T h33 (C h33 h32))
  have h35 := R v24
  have h36 := C h9 h7
  have h37 := C h36 h35
  have h38 := C (T (T h37 h34) h31) (T (T h28 h27) h18)
  have h39 := C h16 h7
  have h40 := C h39 h35
  have h41 := S h33
  have h42 := C h1 (T (C h41 h32) h41)
  let v43 := M (M (M x y) y) y
  have h44 := h y v43 v0
  have h45 := h x y y
  let v46 := M v0 y
  let v47 := M v46 y
  have h48 := h x v47 v21
  have h49 := S h48
  have h50 := h y x y
  have h51 := R v47
  have h52 := C h51 (T h19 (C (T h19 (C h50 h22)) h22))
  have h53 := C h36 h13
  have h54 := C h53 h13
  have h55 := C h54 h13
  have h56 := S h28
  have h57 := C h26 (T h19 (C (T h19 (C h23 h22)) h22))
  have h58 := T (T h57 h56) h39
  have h59 := C (C h58 h13) h13
  have h60 := C h59 h13
  have h61 := h (M v25 y) y y
  have h62 := T (T h36 h28) h27
  have h63 := C (C h62 h13) h13
  have h64 := C h63 h13
  have h65 := C (C h39 h13) h13
  have h66 := C h65 h13
  have h67 := C h51 (T (C (T (C (S h50) h22) h20) h22) h20)
  have h68 := T h34 h31
  have h69 := T (C h68 (T (T (T h48 h67) h66) h64)) (S h61)
  have h70 := C (C h69 h13) h13
  have h71 := C h70 h13
  have h72 := T h30 h42
  have h73 := T h61 (C h72 (T (T (T h60 h55) h52) h49))
  have h74 := C (C h73 h13) h13
  have h75 := h v47 y v0
  have h76 := C (T h48 h67) h1
  have h77 := C h58 h35
  have h78 := C h69 h35
  have h79 := T (T (T (T (T (T (T h78 h77) h37) h34) h31) h3) h15) h76
  have h80 := C (C (C h10 h13) h13) h13
  have h81 := h v24 y y
  have h82 := S h81
  have h83 := C h68 (T h28 h27)
  have h84 := C h73 h35
  have h85 := C h62 h35
  let v86 := M v0 v24
  have h87 := h (M v86 v0) y y
  have h88 := C h72 (T h57 h56)
  have h89 := C (T h52 h49) h1
  have h90 := C (T (T (T (T (T (T (C (T (T h40 h85) h84) h35) (C h79 h35)) (C (T (T h89 h8) h4) (T (T (T (T h81 h88) h87) (C (T (T (T (T h30 h42) h40) h85) h84) (T (T (T (C (C (C (T (T h83 h82) h17) h13) h13) h13) h80) h57) h56))) (C h79 h1)))) (S h75)) h65) h63) h74) h13
  have h91 := T h77 h37
  have h92 := T (T (T (T h8 h4) h30) h42) h40
  have h93 := C (T (T (C h92 h35) (C h85 h35)) (C h91 h35)) h13
  have h94 := C (C h16 h35) h13
  have h95 := C (C h9 h35) h13
  have h96 := C (T (T (C (T h40 h85) h35) (C h77 h35)) (C (T (T (T (T h37 h34) h31) h3) h15) h35)) h13
  have h97 := T (T (T (T (T (T (T h89 h8) h4) h30) h42) h40) h85) h84
  have h98 := C (T (T (T (T (T (T h70 h59) h54) h75) (C (T (T h3 h15) h76) (T (T (T (T (C h97 h1) (C (T (T (T (T h78 h77) h37) h34) h31) (T (T (T h28 h27) h18) (C (C (C (T (T h10 h81) h88) h13) h13) h13)))) (S h87)) h83) h82))) (C h97 h35)) (C (T (T h78 h77) h37) h35)) h13
  have h99 := C h74 h13
  have h100 := C (T (T h30 h42) h40) (T (T h80 h57) h56)
  have h101 := R v43
  have h102 := S (h v86 y x)
  have h103 := T (C (C (C h16 h13) h7) h7) (C (C (T (T (C h92 h13) (C h85 h13)) (C h91 h13)) h7) h7)
  have h104 := C h39 (T (T (T (C (T (T (T (C h9 h103) h102) h34) h31) h103) h102) h34) h31)
  have h105 := h x v0 v21
  T (T (T (T (T (T (T (T (T h105 h104) h53) (h v46 y y)) (C h13 (C (T (T (T (T h52 h49) h105) h104) (C (T (T (T h36 (h v0 v24 v21)) (C (T h81 h88) (T (T (T (C (T (T (T (C h68 h103) h102) h34) h31) h103) h102) h34) h31))) (C (T (T (T (T (T h83 h82) h17) h11) h100) (C (T (T (T (T h37 h34) h31) h44) (C h101 (T (T (T (C (T (T (T (T (T (T (T (T (T (C (T (T (T (T (T (T (T (T (S h45) h48) h67) h66) h64) h99) h98) h96) h95) h1) (C h94 h1)) (C h93 h1)) (C (T (T (T h90 h71) h60) h55) h1)) h89) h8) h4) h30) h42) h40) h1) h38) h12) h10))) h1)) h13)) h13)) h13))) (S (h (M (M v43 v24) v0) y y))) (C (T (T (T (T (C h101 (T (T (T h17 h11) h100) (C (T (T (T (T (T (T (T (T (T h37 h34) h31) h3) h15) h76) (C (T (T (T h66 h64) h99) h98) h1)) (C h96 h1)) (C h95 h1)) (C (T (T (T (T (T (T (T (T h94 h93) h90) h71) h60) h55) h52) h49) h45) h1)) h1))) (S h44)) h30) h42) h40) h1)) h38) h12) h10

