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
theorem Equation3566_implies_Equation3803 (G: Type _) [Magma G] (h: Equation3566 G) : Equation3803 G := fun x y z =>
  let v0 := M x y
  let v1 := M z y
  let v2 := M v1 v0
  have h3 := h v1 v0 v2
  have h4 := S h3
  have h5 := R v0
  have h6 := h z y v0
  have h7 := S h6
  let v8 := M v0 z
  have h9 := h y (M v8 y) x
  have h10 := S h9
  have h11 := h v8 y v2
  have h12 := R y
  have h13 := h v0 z y
  have h14 := R z
  have h15 := h x y y
  have h16 := S h15
  have h17 := h y x z
  have h18 := S h17
  have h19 := R x
  have h20 := h z y y
  have h21 := S h20
  let v22 := M y z
  have h23 := h y (M v22 y) z
  have h24 := h v22 y z
  have h25 := h y z z
  have h26 := S h25
  have h27 := h z y v1
  have h28 := S h27
  let v29 := M v1 z
  have h30 := h y (M v29 y) v2
  have h31 := S h30
  have h32 := h v29 y z
  have h33 := S h32
  have h34 := C h12 (C h25 h12)
  have h35 := T (T h20 h34) h33
  have h36 := R (M v2 y)
  have h37 := C h35 (C h36 h35)
  have h38 := h y v1 v2
  have h39 := T (T (T h38 h37) h31) h28
  have h40 := C h39 h14
  have h41 := C h14 h40
  have h42 := h v1 z y
  have h43 := S h38
  have h44 := C h12 (C h26 h12)
  have h45 := T (T h32 h44) h21
  have h46 := C h45 (C h36 h45)
  have h47 := T (T (T h27 h30) h46) h43
  have h48 := C h47 h14
  have h49 := C h14 h48
  have h50 := T (T (T h20 h34) (C h12 (C (T h49 (C h14 (T (T (T h40 h42) h41) h26))) h12))) (S h24)
  have h51 := h v1 v1 y
  have h52 := C (T (T (T h51 (C h50 (C h39 h50))) (S h23)) h21) h19
  have h53 := C h19 h52
  have h54 := S h51
  have h55 := S h42
  have h56 := T (T (T h24 (C h12 (C (T (C h14 (T (T (T h25 h49) h55) h48)) h41) h12))) h44) h21
  have h57 := C h56 (C h47 h56)
  have h58 := C (T (T (T h20 h23) h57) h54) h19
  have h59 := h v1 x v1
  have h60 := C h19 h58
  have h61 := C (T (T (C h19 (T (T (T h17 h60) (S h59)) h58)) h53) h18) h12
  have h62 := C h12 h61
  let v63 := M y x
  have h64 := h v63 y x
  have h65 := C (T (T h17 h60) (C h19 (T (T (T h52 h59) h53) h18))) h12
  have h66 := C h12 h65
  have h67 := T (T h15 h66) (C h12 (T (T (T h61 h64) h62) h16))
  have h68 := h y z x
  have h69 := R v2
  have h70 := h v29 y v2
  have h71 := T (T (T (T (T h20 h34) h33) h70) (C h12 (C (C h69 (T (T (T (T (T h42 h41) h26) h68) (C h14 (C h67 h14))) (S h13))) h12))) (S h11)
  have h72 := T (T (C h12 (T (T (T h15 h66) (S h64)) h65)) h62) h16
  have h73 := C h71 (C h72 h71)
  have h74 := h v0 v1 y
  have h75 := C h69 (T (T (T h74 h73) h10) h7)
  have h76 := C h5 (C h75 h5)
  let v77 := M v0 v1
  have h78 := h v77 v0 v2
  have h79 := h v77 v0 v1
  have h80 := S h79
  have h81 := h y v1 x
  let v82 := M v1 v1
  let v83 := M v1 x
  have h84 := T (T (T (T (T (h v83 y v2) (C h12 (C (C h69 (T (T h59 h53) h18)) h12))) (S (h v63 y v2))) h64) h62) h16
  have h85 := h v0 v1 v1
  have h86 := S h85
  have h87 := S h74
  have h88 := T (T (T (T (T h11 (C h12 (C (C h69 (T (T (T (T (T h13 (C h14 (C h72 h14))) (S h68)) h25) h49) h55)) h12))) (S h70)) h32) h44) h21
  have h89 := C h88 (C h67 h88)
  let v90 := M v2 v1
  have h91 := h v0 (M v90 v0) y
  have h92 := h v90 v0 v1
  have h93 := S h92
  have h94 := C h5 (C (T (T (T (T (T (T (T (T (T (S h81) h38) h37) h31) h28) h6) h9) h89) h87) h85) h5)
  have h95 := h v1 v0 v0
  have h96 := C h69 (T (T (T h6 h9) h89) h87)
  have h97 := R v1
  have h98 := h v2 v1 v2
  have h99 := S h98
  have h100 := C h5 (C (T (T (T (T (T (T (T (T (T h86 h74) h73) h10) h7) h27) h30) h46) h43) h81) h5)
  have h101 := C h97 (T (T h96 (C h69 (T (T (T (T (T (T (T h74 h73) h10) h7) h27) h30) h46) h43))) (C (T (T h3 h91) (C (T (T (T (T (T h92 h100) h80) h78) h76) h4) (T (C h72 (T (T h92 h100) h80)) (S h95)))) h39))
  T (T (T (T (T (T (T (T (T (h x y v1) (h y (M v83 y) z)) (C h84 (C (T (T (T (T (T (T (T (T (T h6 h9) h89) h87) h85) h101) h99) h96) (C h69 (T (T h85 h101) h99))) (C h69 (T (T (T (T (T (T (T (T (T (T h98 (C h97 (T (T (C (T (T (C (T (T (T (T (T h3 (C h5 (C h96 h5))) (S h78)) h79) h94) h93) (T h95 (C h67 (T (T h79 h94) h93)))) (S h91)) h4) h47) (C h69 (T (T (T (T (T (T (T h38 h37) h31) h28) h6) h9) h89) h87))) h75))) h86) h74) h73) h10) h7) h20) h23) h57) h54))) h84))) (S (h v82 v0 v2))) (h v82 v0 v1)) (C h5 (C (T (S (h y v1 z)) h81) h5))) h80) h78) h76) h4

