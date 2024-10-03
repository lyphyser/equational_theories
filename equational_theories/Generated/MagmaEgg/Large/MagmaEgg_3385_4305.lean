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
theorem Equation3385_implies_Equation4305 (G: Type _) [Magma G] (h: Equation3385 G) : Equation4305 G := fun x y z =>
  let v0 := M y z
  have h1 := h z v0 z
  have h2 := S h1
  let v3 := M v0 z
  have h4 := h z (M z v3) v0
  have h5 := S h4
  have h6 := R v0
  let v7 := M z v0
  have h8 := h z v3 v7
  have h9 := R v7
  have h10 := h v0 z y
  have h11 := S h10
  have h12 := h z y z
  have h13 := S h12
  have h14 := C h6 h13
  have h15 := h z z v0
  have h16 := R y
  have h17 := C h16 (T h15 h14)
  have h18 := R z
  have h19 := h z (M y (M z z)) v7
  have h20 := h y z z
  have h21 := C (T (T (T h20 h19) (C h9 (C h18 (C (T h17 h11) h9)))) (S h8)) h6
  have h22 := C h18 h21
  have h23 := h v0 y z
  have h24 := h v0 y y
  have h25 := S h24
  have h26 := h y y z
  have h27 := S h26
  have h28 := C h6 h27
  have h29 := h z y v0
  have h30 := h z y v7
  have h31 := C h16 (T (T (C h6 (T h23 h22)) h5) h2)
  have h32 := h v0 v0 y
  have h33 := S h20
  have h34 := S h15
  have h35 := C h6 h12
  have h36 := C h16 (T h35 h34)
  have h37 := C (T (T (T h8 (C h9 (C h18 (C (T h10 h36) h9)))) (S h19)) h33) h6
  have h38 := h y z v7
  have h39 := C h16 (T (T (T (T h38 (C h9 (T (T (T (T (C h16 (T (T h13 h29) h28)) h25) h23) h22) (C h18 (T (T h37 h32) h31))))) (S h30)) h29) h28)
  have h40 := h y v0 x
  have h41 := h v0 x y
  have h42 := h x y z
  have h43 := S h42
  have h44 := C h6 h43
  have h45 := h z x v0
  have h46 := S h45
  have h47 := C h6 h42
  let v48 := M x y
  have h49 := h v0 v48 x
  have h50 := h v48 x x
  have h51 := S h50
  have h52 := h x x y
  have h53 := R v48
  have h54 := h y x v48
  have h55 := h y x v0
  have h56 := h x v0 v0
  have h57 := S h32
  have h58 := S h23
  have h59 := C h18 h37
  have h60 := C h16 (T (T h1 h4) (C h6 (T h59 h58)))
  have h61 := h y v7 v0
  have h62 := S h61
  have h63 := h y z v0
  have h64 := h v0 y v7
  have h65 := C h6 (C h16 (T (T (T h39 h25) h64) (C h9 (S h63))))
  have h66 := h y y v0
  have h67 := h y y v48
  have h68 := h y x y
  have h69 := R x
  have h70 := h v48 y x
  have h71 := h v0 v48 y
  have h72 := C h69 (T (T (T (C h6 (T (T (T h45 h44) h71) (C h16 (T (C h6 (T h70 (C h69 (T (T (T (T (T (T (C h53 h68) (S h67)) h66) h65) h62) h60) h57)))) (S h56))))) (S h55)) h54) (C h53 (S h52)))
  have h73 := h v0 z x
  have h74 := h z z v48
  have h75 := h z v48 x
  have h76 := S h75
  have h77 := C h69 (T h20 (C h18 (T (T (T (T h17 h11) h73) h72) h51)))
  have h78 := h x y v48
  have h79 := h y v48 v48
  have h80 := S h79
  have h81 := h v48 x y
  have h82 := C h53 h81
  have h83 := h v48 v48 x
  have h84 := h v48 v48 v48
  have h85 := h v48 v48 v0
  have h86 := h v48 v0 z
  have h87 := S h73
  have h88 := S h66
  have h89 := S h29
  have h90 := C h6 h26
  have h91 := C h16 (T (T (T (T h90 h89) h30) (C h9 (T (T (T (T (C h18 (T (T h60 h57) h21)) h59) h58) h24) (C h16 (T (T h90 h89) h12))))) (S h38))
  have h92 := C h6 (C h16 (T (T (T (C h9 h63) (S h64)) h24) h91))
  have h93 := S h54
  have h94 := C h53 h52
  have h95 := C h69 (T (T (T h94 h93) h55) (C h6 (T (T (T (C h16 (T h56 (C h6 (T (C h69 (T (T (T (T (T (T h32 h31) h61) h92) h88) h67) (C h53 (S h68)))) (S h70))))) (S h71)) h47) h46)))
  have h96 := C h53 (S h81)
  have h97 := h z y v48
  have h98 := h v0 v0 v0
  have h99 := h y v0 v0
  have h100 := h x v0 y
  let v101 := M v48 x
  T (T (T (T (h x v48 x) (h x (M x v101) v0)) (C h6 (T (T (T (T (T (C h69 (T (T (C (T (T (T (h x v101 v7) (C h9 (C h69 (C (T h50 (C h69 (T h94 h93))) h9)))) (S (h x (M x (M y x)) v7))) (S (h x y x))) h6) (h v48 v0 y)) (C h16 (T (T (T (T (T (C h53 (T (T (T h24 h91) h40) (C h69 (T (T (T (C h16 (T (T (T (T (T h41 (C h16 (T h47 h46))) (C h16 (T (T (T h45 h44) h49) (C h69 (T (T (T (C h6 (T (T (T (T (T h50 h95) h87) h10) (C h16 (T (T (T (T (T (T (T (T (T h35 h34) h74) (C h53 (T (T (T (C h18 (T h75 (C h69 (T (C h18 (T (T (T (T h50 h95) h87) h10) h36)) h33)))) h43) h78) (C h53 (T (C h69 (T h79 h96)) (S h83)))))) (S h84)) h85) (C h6 (T (T (T (C h53 (T h86 (C h18 (T (T (C h53 (T (T h73 h72) h51)) h82) h80)))) (S h97)) h29) (C h6 (T (T (T (T (T h27 h66) h65) h62) h60) h57))))) (S h98)) h32) h31))) (C h16 (T h60 h57)))) (S h99)) h39) h25))))) (S h100)) h77) h76)) (S (h z x y))) h45) h44)))) (S (h x v0 v48))) h100) (C h16 (T (T (T (C h69 (T (T (T h24 h91) h99) (C h6 (T (T (T (T (T (C h16 (T h32 h31)) (C h16 (T (T (T (T (T (T (T (T (T h60 h57) h98) (C h6 (T (T (T (C h6 (T (T (T (T (T h32 h31) h61) h92) h88) h26)) h89) h97) (C h53 (T (C h18 (T (T h79 h96) (C h53 (T (T h50 h95) h87)))) (S h86)))))) (S h85)) h84) (C h53 (T (T (T (C h53 (T h83 (C h69 (T h82 h80)))) (S h78)) h42) (C h18 (T h77 h76))))) (S h74)) h15) h14))) h11) h73) h72) h51)))) (S h49)) h47) h46))) (C h16 (T h45 h44))) (S h41))))) (S h40)) h39) h25) h23) h22))) h5) h2

