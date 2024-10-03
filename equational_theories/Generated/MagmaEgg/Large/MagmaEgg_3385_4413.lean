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
theorem Equation3385_implies_Equation4413 (G: Type _) [Magma G] (h: Equation3385 G) : Equation4413 G := fun x y z =>
  let v0 := M y z
  have h1 := S (h v0 z z)
  let v2 := M v0 z
  let v3 := M z z
  let v4 := M v0 v3
  have h5 := h v0 z y
  have h6 := S h5
  let v7 := M z y
  have h8 := h y (M v0 v7) v2
  have h9 := S h8
  have h10 := R v2
  have h11 := h z y z
  have h12 := R v0
  have h13 := C h12 (S h11)
  have h14 := h z z v0
  have h15 := R y
  have h16 := C h10 (C h15 (C (T h14 h13) h10))
  have h17 := h y v3 v2
  have h18 := S h14
  have h19 := C h12 h11
  have h20 := h v0 v7 v0
  have h21 := S h20
  have h22 := h y z y
  have h23 := S h22
  have h24 := h y v7 v2
  have h25 := S h24
  have h26 := h z y v2
  have h27 := S h26
  have h28 := h y v0 z
  have h29 := h y v0 v2
  have h30 := S h29
  have h31 := h y z z
  have h32 := S h31
  have h33 := h z (M y v3) v2
  have h34 := S h33
  have h35 := S h17
  have h36 := C h10 (C h15 (C (T h19 h18) h10))
  have h37 := T (T (T h5 h8) h36) h35
  have h38 := C h37 h10
  have h39 := R z
  have h40 := C h10 (C h39 h38)
  have h41 := h z v2 v2
  have h42 := C h10 (C h15 (C (T (T (T h41 h40) h34) h32) h10))
  have h43 := h y (M z v2) v2
  have h44 := C h10 (T (T (T h43 h42) h30) h28)
  have h45 := h y z v2
  have h46 := C h10 (C h15 (C (T (T (T (T (T (T h41 h40) h34) h32) h45) h44) h27) h10))
  have h47 := S h41
  have h48 := T (T (T h17 h16) h9) h6
  have h49 := C h48 h10
  have h50 := C h39 h49
  have h51 := C h10 h50
  have h52 := C h10 (C h15 (C (T (T (T h31 h33) h51) h47) h10))
  have h53 := T (T h45 h44) h27
  have h54 := C h53 (T (C h15 (T (T (T h29 h52) h46) h25)) h23)
  have h55 := h y y v0
  have h56 := h y y z
  have h57 := C h12 (T (T (S h56) h55) h54)
  have h58 := h z y v0
  have h59 := S h45
  have h60 := S h28
  have h61 := C h10 (T (T (T h60 h29) h52) (S h43))
  have h62 := T (T h26 h61) h59
  have h63 := C h62 (T (T (T (T h45 h44) h27) h58) h57)
  have h64 := C h15 (T (T (T h63 h21) h19) h18)
  have h65 := T (T (T (T h64 h17) h16) h9) h6
  have h66 := h z z z
  have h67 := h y v7 v0
  have h68 := S h67
  have h69 := S h58
  have h70 := S h55
  have h71 := C h10 (C h15 (C (T (T (T (T (T (T h26 h61) h59) h31) h33) h51) h47) h10))
  have h72 := C h62 (T h22 (C h15 (T (T (T h24 h71) h42) h30)))
  have h73 := C h12 (T (T h72 h70) h56)
  have h74 := C h53 (T (T (T (T h73 h69) h26) h61) h59)
  have h75 := C h15 (T (T (T h14 h13) h20) h74)
  have h76 := C h62 (T (T (T (T h5 h8) h36) h35) h75)
  have h77 := C h15 (T h76 h68)
  have h78 := C h53 h65
  have h79 := C h15 (T h67 h78)
  have h80 := C h10 (T h22 h79)
  have h81 := C h15 (T (T (T h80 h25) h67) h78)
  have h82 := C h12 (T (T (T (T (T (T (T h81 h77) h23) h45) h44) h27) h58) h57)
  have h83 := h y v2 v0
  have h84 := h z v2 v0
  have h85 := T (T (T (T (T h31 h33) h51) h47) h84) (C h12 (T (C h39 (T (T (T (T (T h80 h71) h42) h30) h28) (C h39 (T (T (T (T h83 h82) h21) h19) h18)))) (S h66)))
  have h86 := C h10 (T h77 h23)
  have h87 := S h83
  have h88 := C h12 (T (T (T (T (T (T (T h73 h69) h26) h61) h59) h22) h79) (C h15 (T (T (T h76 h68) h24) h86)))
  have h89 := C h39 (T (T (T (T (T (C h39 (T (T (T (T h14 h13) h20) h88) h87)) h60) h29) h52) h46) h86)
  have h90 := S (h z z x)
  let v91 := M x y
  have h92 := S (h y v91 v0)
  have h93 := S (h v91 v0 z)
  have h94 := S (h v91 v2 v2)
  have h95 := C h37 (T (T (T (T (T (C h15 (T (T h83 h82) h74)) h64) h17) h16) h9) h6)
  have h96 := h y y v2
  have h97 := R v91
  have h98 := C h15 (T (C h39 (T (T (h v91 y v2) (C h10 (C h97 (T (T (T (T (T (T (T h83 h82) h74) h72) h70) h96) h95) h49)))) h94)) h93)
  have h99 := h z v91 y
  have h100 := C h39 (T (C h15 (T (T (h v91 z v0) (C h12 (T (T (C h97 (T (T (T (T (C h39 (T (T (T (T h31 h33) h51) h47) (C h39 (C h85 h39)))) (S (h z v4 z))) h1) (h v0 z v91)) (C h97 (T (C h12 (T h99 h98)) h92)))) (S (h v91 y v91))) (h v91 y z)))) (S (h z v91 v0)))) (S (h z x y)))
  have h101 := h y v91 z
  have h102 := R x
  let v103 := M v91 x
  T (T (T (T (h x v91 x) (h x (M x v103) v2)) (C h10 (T (T (T (T (T (C h102 (C (T (T (T (h x v103 v2) (C h10 (C h102 (C (T (h v91 x x) (C h102 (T (C h97 (h x x y)) (S (h y x v91))))) h10)))) (S (h x (M x (M y x)) v2))) (S (h x y x))) h10)) (C h102 (T (T (T (T (h v91 v2 v0) (C h12 (T (T (T (C h97 (T (T (T (T (T (T (T (T h80 h71) h42) h30) h28) (C h39 (T (T (T (T (T (T h83 h82) h74) h72) h70) h96) h95))) h50) (C h39 (T (T (T (T (T (T (T h38 (C h48 (T (T (T (T (T h5 h8) h36) h35) h75) (C h15 (T (T h63 h88) h87))))) (S h96)) h55) h54) h63) h88) (C h85 (T (T h81 h77) h23))))) (C h39 (T (C (T (T (T (T (T (C h12 (T h66 h89)) (S h84)) h41) h40) h34) h32) (T (T (T (T (T h31 h33) h51) h47) (h z v2 v91)) (C h97 (T (C h39 (T (C h10 (T (h x y v91) (C h97 (T (T (T (T (T (T (T (T (T (T (C h102 (T h101 h100)) h90) h14) h13) h20) h74) h72) h70) h96) h95) h49)))) h94)) h93)))) (S (h v91 v91 v0)))))) (S (h z v91 v91))) h99) h98))) h92) h101) h100))) h90) h66) h89) (C h39 (T (T (T h80 h25) h67) (C h85 h65)))))) (S (h z v4 v2))) h1

