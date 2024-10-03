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
theorem Equation522_implies_Equation2170 (G: Type _) [Magma G] (h: Equation522 G) : Equation2170 G := fun x y z =>
  let v0 := M z y
  let v1 := M y z
  let v2 := M v1 x
  let v3 := M v2 v0
  have h4 := h y z z
  have h5 := S h4
  have h6 := h v1 v1 v2
  have h7 := S h6
  have h8 := h v2 v2 v1
  have h9 := S h8
  have h10 := h v1 v2 x
  have h11 := R v2
  have h12 := h x v2 v2
  have h13 := R v1
  have h14 := C h13 (T h12 (C h11 (S h10)))
  have h15 := C h11 (C h11 h14)
  have h16 := T h15 h9
  have h17 := C h13 h16
  have h18 := C h13 (T (C h11 h10) (S h12))
  have h19 := C h11 (C h11 h18)
  have h20 := h v2 x v2
  have h21 := S h20
  have h22 := T h8 h19
  have h23 := R x
  have h24 := C h23 h22
  have h25 := C h23 (T (T (T (C h23 h24) h21) h8) h19)
  have h26 := h v1 x x
  have h27 := C h23 (T h26 h25)
  have h28 := C h13 (T (T (T h27 h21) h8) h19)
  have h29 := C h11 (T h28 h17)
  have h30 := S h26
  have h31 := C h23 h16
  have h32 := C h23 (T (T (T h15 h9) h20) (C h23 h31))
  have h33 := C h23 (T h32 h30)
  have h34 := h v2 v1 v2
  have h35 := S h34
  have h36 := C h13 h28
  have h37 := C h13 (T (T (T h36 h35) h20) h33)
  have h38 := h x v1 v1
  have h39 := h x v2 v1
  have h40 := S h39
  have h41 := C h13 (T (T (T h15 h9) h20) h33)
  have h42 := C h13 h22
  have h43 := C h11 (T h42 h41)
  have h44 := C h11 h43
  have h45 := C h11 (T (T (T h44 h40) h38) h37)
  have h46 := h v1 v2 v2
  have h47 := T (T h46 h45) h29
  have h48 := C h13 (C h13 h47)
  have h49 := R z
  have h50 := C h49 (T h48 h7)
  have h51 := C h49 h50
  have h52 := h v1 z v1
  have h53 := C h49 (T (T (T h48 h7) h52) h51)
  have h54 := C h49 (T h53 h5)
  have h55 := h v1 v2 v0
  have h56 := S h55
  have h57 := S h52
  have h58 := S h46
  have h59 := C h11 h29
  have h60 := S h38
  have h61 := C h13 h41
  have h62 := C h13 (T (T (T h27 h21) h34) h61)
  have h63 := C h11 (T (T (T h62 h60) h39) h59)
  have h64 := T (T h43 h63) h58
  have h65 := C h13 (C h13 h64)
  have h66 := C h49 (T h6 h65)
  have h67 := C h49 h66
  have h68 := C h49 (T (T (T h67 h57) h6) h65)
  have h69 := C h49 (T h4 h68)
  have h70 := T h69 h57
  have h71 := R v0
  have h72 := C h71 (C h70 (T (T (T (T h24 h32) h30) h52) h54))
  have h73 := h v1 v0 x
  have h74 := h v1 v0 v2
  have h75 := S h74
  have h76 := T h52 h54
  have h77 := C h76 (C h71 h47)
  have h78 := T (T (T h77 h75) h73) h72
  have h79 := C h70 (C h71 h64)
  have h80 := h v2 x x
  have h81 := S h80
  have h82 := C h11 (T (T (T h42 h41) h62) h60)
  have h83 := h v1 x v2
  have h84 := C h11 (T (T (T h38 h37) h28) h17)
  have h85 := C h23 (T (T (T (T (T h84 h43) h63) h58) h83) (C h23 (C h23 h82)))
  have h86 := C h23 (T (T (T (T (T (C h23 (C h23 h84)) (S h83)) h46) h45) h29) h82)
  have h87 := T (T (T h15 h9) h80) h86
  have h88 := C h11 (T (T (T (T (T (T (T (T (T (C h71 h14) (C h71 (T (T h18 h8) h19))) (C h70 h87)) (C h13 (T (T (T h85 h81) h34) h61))) h60) h39) h59) (C h11 (T (T (T (T h43 h63) h58) h6) h65))) (C h11 (T (T (T h48 h7) h74) h79))) (C h11 h78))
  have h89 := R v3
  have h90 := C h76 (T (T (T h85 h81) h8) h19)
  have h91 := C h13 (T (T (T h36 h35) h80) h86)
  have h92 := S h73
  have h93 := C h71 (C h76 (T (T (T (T h69 h57) h26) h25) h31))
  have h94 := T (T (T h93 h92) h74) h79
  have h95 := C h11 (T (T (T (T (T (T (T (T (T (C h11 h94) (C h11 (T (T (T h77 h75) h6) h65))) (C h11 (T (T (T (T h48 h7) h46) h45) h29))) h44) h40) h38) h91) h90) (C h71 (T (T h15 h9) h14))) (C h71 h18))
  have h96 := h v0 z v2
  have h97 := h y v0 z
  have h98 := h y v1 z
  have h99 := R (M v1 (M z v1))
  have h100 := C h71 (T (T (T (T (C h70 h99) (S h98)) h4) h68) h50)
  have h101 := h z v0 v1
  have h102 := S h101
  have h103 := C h71 (T (T (T (T h66 h53) h5) h98) (C h76 h99))
  have h104 := R y
  T (T (h x v3 v1) (C h89 (C h89 (T (T (T (T h62 h91) h90) (C h71 h87)) (C h71 (T (T (T (T (T (T h85 h81) (h v2 v3 x)) (C h89 (T (T (C h89 (T (T (T h85 h81) (h v2 v3 v0)) (C h89 (C h89 (C h70 h89))))) (S (h v1 v3 v3))) (C h104 (T (T h101 h100) (C h70 (T (T h66 h53) h5))))))) (C h89 (T (T (T (T (C h104 (T (T (C h76 (T (T h4 h68) h50)) h103) h102)) h52) h54) h96) (C h49 (T (T (T (T (T (C h49 (T (T (T h88 h56) h73) h72)) (C h49 h94)) (C h49 (T (T (T h77 h75) h52) h51))) h5) h97) (C h70 (T h103 h102))))))) (C h89 (T (T (T (T (T (C h49 (T (T (T (T (T (C h76 (T h101 h100)) (S h97)) h4) (C h49 (T (T (T h67 h57) h74) h79))) (C h49 h78)) (C h49 (T (T (T h93 h92) h55) h95)))) (S h96)) h69) h57) h55) h95))) (C h89 (T (T (T h88 h56) h52) h54)))))))) (S (h v3 v3 v0))

