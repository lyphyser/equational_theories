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
theorem Equation2374_implies_Equation2 (G: Type _) [Magma G] (h: Equation2374 G) : Equation2 G := fun x y =>
  have h0 := h y y y
  have h1 := S h0
  have h2 := R y
  let v3 := M y y
  let v4 := M y v3
  have h5 := h (M y v4) x y
  have h6 := S h5
  have h7 := h y x y
  have h8 := R x
  have h9 := C (C h8 (T (C h2 (S h7)) (C h2 h0))) h2
  have h10 := h (M x v4) x y
  have h11 := h v3 y y
  have h12 := C (T (T (T (C h8 (C h2 (S h11))) h10) h9) h6) h2
  let v13 := M y (M v3 y)
  let v14 := M y v13
  have h15 := h v14 x y
  have h16 := S h15
  have h17 := S h10
  have h18 := C (C h8 (T (C h2 h1) (C h2 h7))) h2
  have h19 := C (T (T (T h5 h18) h17) (C h8 (C h2 h11))) h2
  have h20 := h y x x
  let v21 := M y x
  have h22 := h v21 y x
  have h23 := S h22
  have h24 := h (M y (M x (M v21 x))) x x
  have h25 := h v3 x y
  have h26 := h (M x v13) x y
  have h27 := C (T (T h26 (C (T (T (T (C h8 (C h2 (S h25))) h10) h9) h6) h2)) h1) h8
  have h28 := C (T (T h0 (C (T (T (T h5 h18) h17) (C h8 (C h2 h25))) h2)) (S h26)) h8
  let v29 := M x v21
  have h30 := h v29 y y
  have h31 := S h30
  let v32 := M y (M v29 y)
  have h33 := h (M y v32) x y
  let v34 := M y v29
  have h35 := h v34 y x
  have h36 := S h35
  have h37 := h y y x
  have h38 := C (C h2 (C h8 h37)) h8
  have h39 := C h8 (S h37)
  have h40 := C (C h2 h39) h8
  have h41 := h v29 x y
  have h42 := h (M x v32) x y
  have h43 := h x x y
  have h44 := C h2 (S h43)
  have h45 := C h8 h44
  let v46 := M x y
  let v47 := M y v46
  let v48 := M x v47
  have h49 := h v48 x y
  have h50 := h v48 y y
  have h51 := C (T (T (T (T (C h8 (C h2 (T (T (S h50) h49) (C h45 h2)))) h42) (C (C h8 (T (T (C h2 (S h41)) h35) h40)) h2)) (C (C h8 (T (T h38 h36) (C h2 h30))) h2)) (S h33)) h2
  have h52 := h (M y (M y (M v48 y))) x y
  have h53 := C h2 h43
  have h54 := h v21 x y
  have h55 := S h54
  have h56 := h (M x (M y (M v21 y))) y y
  have h57 := C h2 (T h44 h54)
  have h58 := S h52
  have h59 := S h49
  have h60 := C h8 h53
  have h61 := C (T (T (T (T h33 (C (C h8 (T (T (C h2 h31) h35) h40)) h2)) (C (C h8 (T (T h38 h36) (C h2 h41))) h2)) (S h42)) (C h8 (C h2 (T (T (C h60 h2) h59) h50)))) h2
  have h62 := C h2 (T (T (T (C h2 (T h55 h53)) h52) h51) h31)
  have h63 := h x y y
  have h64 := S h63
  have h65 := h (M y v47) x y
  have h66 := S h65
  have h67 := C (T h45 (C h8 (C h2 h63))) h2
  have h68 := h v46 x y
  have h69 := C (T (T (T (C h8 (C h2 (S h68))) h49) h67) h66) h2
  let v70 := M y (M v46 y)
  have h71 := h (M x v70) x y
  have h72 := h v70 y y
  have h73 := S h72
  have h74 := h (M y (M y (M v70 y))) x y
  have h75 := h (M y v70) x y
  have h76 := S h75
  have h77 := h v46 y y
  have h78 := C (T (C h8 (C h2 h64)) h60) h2
  have h79 := C (T (T (T h65 h78) h59) (C h8 (C h2 h77))) h2
  have h80 := h x x x
  have h81 := S h80
  let v82 := M x x
  have h83 := h v82 y x
  have h84 := S h83
  have h85 := C (C h8 (C h8 h84)) h8
  let v86 := M v82 x
  let v87 := M x v86
  have h88 := h (M y v87) x x
  have h89 := T (T h88 h85) h81
  have h90 := C (T (C (T h83 (C h89 (T (T (T h63 h79) h76) (C h2 h72)))) h2) (S h74)) h2
  have h91 := h (M (M v82 y) y) y x
  have h92 := C (T (T (T (C h8 (C h2 (S h77))) h49) h67) h66) h2
  have h93 := S h88
  have h94 := C (C h8 (C h8 h83)) h8
  have h95 := T (T h80 h94) h93
  have h96 := C (T h74 (C (T (C h95 (T (T (T (C h2 h73) h75) h92) h64)) h84) h2)) h2
  have h97 := h (M y (M x (M v70 x))) x x
  have h98 := h v70 y x
  have h99 := S h71
  have h100 := C (T (T (T h65 h78) h59) (C h8 (C h2 h68))) h2
  have h101 := C h8 (T (T (T (C (T (T (C (T h83 (C h89 (T (T (T h63 h100) h99) (C h8 h98)))) h8) (S h97)) (C h2 (C h8 (C (T h72 h96) h8)))) h8) (S h91)) h90) h73)
  let v102 := M x (M v86 x)
  have h103 := C (T (T (T (T (T (T h101 h71) h69) h64) h80) h94) h93) h8
  have h104 := C h8 (T (T (T h72 h96) h91) (C (T (T (C h2 (C h8 (C (T h90 h73) h8))) h97) (C (T (C h95 (T (T (T (C h8 (S h98)) h71) h69) h64)) h84) h8)) h8))
  have h105 := C (T (T h71 h69) h64) h8
  have h106 := C (T (T (T h75 h92) h100) h99) h8
  have h107 := C (T (T (T h71 h69) h79) h76) h8
  have h108 := C (T (T h63 h100) h99) h8
  let v109 := M x v82
  T (T (T (T (T (T (T (T (T h63 h100) h99) h104) (h v102 x x)) (C (T (T (T (T (T (T (T (T (T (T (T (T (T (C h8 (C h8 (T (T (T h103 h84) h108) h107))) (C h8 (C h8 h106))) (C h8 (C h8 h105))) (h (M x v109) x x)) (C (T (C h8 (C h8 h81)) (C h8 (C h8 (h x y x)))) h8)) (S (h (M y v109) x x))) (C h2 (T (T (C h8 h108) (C h8 h107)) (C h8 (T (T (T h106 h105) h83) (C (T (T (T (T (T (T h88 h85) h81) h63) h100) h99) h104) h8)))))) (C h2 (T (T (T (T (T (T (C h8 (T (T (T h103 (C (T (T (T (T h88 h85) (C (C h8 (C h8 (h v82 x x))) h8)) (S (h (M x v87) x x))) (C h8 (C h8 (h v86 y x)))) h8)) (S (h (M y v102) x x))) (C (T (T h0 h19) h16) (T (T (T h101 h71) h69) h64)))) (C h8 (T (T (C (T (T (T (T (T h15 h12) h1) h20) (C (C h8 (C h8 h22)) h8)) (S h24)) h8) h23) h28))) (C h8 h27)) h30) h61) h58) h57))) h62) (h v34 x x)) (C (C h8 (T h39 (C h8 h20))) h8)) (S (h (M x v29) x x))) (C h8 (T (T (T h30 h61) h58) (C h2 (T (T h44 h54) (C (T h56 (C h62 h2)) h2)))))) (C h8 (T (T (T (T (T (C h2 (T (T (C (T (C (C h2 (T (T (T h30 h61) h58) h57)) h2) (S h56)) h2) h55) h53)) h52) h51) h31) (C h8 h28)) (C h8 (T (T h27 h22) (C (T (T (T (T (T h24 (C (C h8 (C h8 h23)) h8)) (S h20)) h0) h19) h16) h8)))))) h8)) (S (h v14 x x))) h15) h12) h1

