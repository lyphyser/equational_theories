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
theorem Equation522_implies_Equation1504 (G: Type _) [Magma G] (h: Equation522 G) : Equation1504 G := fun x y z =>
  let v0 := M y z
  let v1 := M z v0
  let v2 := M y x
  let v3 := M v2 v1
  have h4 := h y v3 z
  have h5 := S h4
  have h6 := h v0 v1 v1
  have h7 := h z v1 v0
  have h8 := R v1
  have h9 := R z
  have h10 := C h9 (T (C h8 h7) (S h6))
  have h11 := R v3
  have h12 := C h11 (C h11 h10)
  have h13 := h v1 v3 z
  have h14 := T (T (T h10 h13) h12) h5
  have h15 := C h9 (T h6 (C h8 (S h7)))
  have h16 := C h11 h15
  have h17 := S h13
  have h18 := C h11 h16
  have h19 := h y y z
  have h20 := S h19
  have h21 := R (M y v1)
  have h22 := T (T h13 h12) h5
  have h23 := C h22 h21
  have h24 := T (T h4 h18) h17
  have h25 := C h24 h21
  have h26 := h y v2 v0
  have h27 := S h26
  have h28 := h v0 y z
  have h29 := h z v0 v0
  have h30 := S h29
  have h31 := h y v0 z
  have h32 := R v0
  have h33 := C h32 h31
  have h34 := h v1 v1 z
  have h35 := S h34
  have h36 := C h24 (C h24 (T (T (T h4 h18) h17) h15))
  have h37 := C h32 (T (T (T (T h36 h35) h13) h12) h5)
  have h38 := h y v0 y
  have h39 := R y
  have h40 := h z y y
  have h41 := C h32 (T (T (T (T h37 h33) h30) h40) (C h39 (T (C h39 (C h39 (C h9 (T h38 (C h32 (T (T h37 h33) h30)))))) (S h28))))
  have h42 := R v2
  have h43 := C h42 (T (T (T (T (T (T h36 h35) h13) h12) h5) h38) h41)
  have h44 := C h22 (C h22 h14)
  have h45 := C h42 (T (T h10 h34) h44)
  have h46 := C h42 (T (T (T (T (T h23 h20) h4) h18) h17) h15)
  have h47 := h y v3 v3
  have h48 := S h47
  have h49 := C h22 h11
  have h50 := C h11 h49
  have h51 := C h11 h50
  have h52 := h v2 v3 v1
  have h53 := C h11 (T h52 h51)
  have h54 := C h42 (T (T (T h53 h48) h19) h25)
  have h55 := S h52
  have h56 := C h24 h11
  have h57 := C h11 h56
  have h58 := C h11 h57
  have h59 := C h11 (T h58 h55)
  have h60 := h y v2 v1
  have h61 := C h42 (T (T (T (C h42 h54) (S h60)) h47) h59)
  have h62 := h v3 v2 v2
  have h63 := h v3 v1 v3
  have h64 := S h63
  have h65 := S h62
  have h66 := C h42 (T (T (T h23 h20) h47) h59)
  have h67 := C h42 (T (T (T h53 h48) h60) (C h42 h66))
  have h68 := C h11 (C h11 (T h67 h65))
  have h69 := h v3 v3 v2
  have h70 := T (T (T (T (T h10 h13) h12) h5) h19) h25
  have h71 := C h42 h70
  have h72 := T (T h36 h35) h15
  have h73 := C h42 h72
  have h74 := S h38
  have h75 := C h32 (T (T (T (T h4 h18) h17) h34) h44)
  have h76 := C h32 (S h31)
  have h77 := C h32 (T (T (T (T (C h39 (T h28 (C h39 (C h39 (C h9 (T (C h32 (T (T h29 h76) h75)) h74)))))) (S h40)) h29) h76) h75)
  have h78 := T (T (T (T (T (T h77 h74) h4) h18) h17) h34) h44
  have h79 := C h42 h78
  have h80 := T h38 h41
  have h81 := C h42 h80
  have h82 := C h24 (T (T (T (T (T (T (T (T h81 h79) h73) h71) h66) h67) h65) h69) h68)
  have h83 := C h24 h82
  have h84 := R (M y (M v2 y))
  have h85 := C h22 h84
  have h86 := C h8 (T (T (T (T h85 h83) h64) h69) h68)
  have h87 := h v2 v1 y
  have h88 := C h42 (T (T (T (T (T (T (T (C h24 (T h87 h86)) h64) h62) h61) h54) h46) h45) h43)
  have h89 := S h87
  have h90 := C h42 (T h77 h74)
  have h91 := S h69
  have h92 := C h11 (C h11 (T h62 h61))
  have h93 := C h22 (T (T (T (T (T (T (T (T h92 h91) h62) h61) h54) h46) h45) h43) h90)
  have h94 := C h8 (T (T (T (T h92 h91) h63) (C h22 h93)) (C h24 h84))
  have h95 := C h42 (T (T (T (T (T (T (T h79 h73) h71) h66) h67) h65) h63) (C h22 (T h94 h89)))
  have h96 := C h11 (T (T (T (T h82 h94) h89) h52) h51)
  have h97 := h v2 v2 y
  have h98 := C h42 (C h42 (T (T h82 h94) h89))
  have h99 := S (h v2 x v2)
  have h100 := R x
  T (T (h x v3 y) (C h11 (C h11 (T (T (T (T (T (T (T (C h39 (T (T (T (T (T (T (T (T (T (T (C h100 h80) (C h100 h78)) (C h100 h72)) (C h100 h70)) (C h100 (T (T (T h23 h20) h26) h95))) (C h100 (T (T (T (T h88 h27) h47) (C h11 (T (T (T (T h58 h55) h87) h86) h93))) (C h11 (T (C h24 (T (T (T (T (T (T h81 h79) h73) h71) h66) h67) h65)) h49))))) (C h100 h57)) (C h100 (T (T (T (T (T h50 (C h11 (T h56 (C h22 (T (T (T (T (T (T h62 h61) h54) h46) h45) h43) h90))))) h96) h48) (h y x x)) (C h100 (T (T (T (C h100 (C h100 (T h97 h98))) h99) h97) h98))))) h99) h97) h98)) (C h24 (R (M v2 (M v2 v2))))) (C h8 (T (T (T (T (C h42 (C h42 (T (T h87 h86) h93))) (S h97)) h87) h86) h93))) h85) h83) h64) (h v3 y v3)) (C h39 (T (T (T (T (T (T (T (T (C h24 (R (M v3 (M v3 v3)))) h94) h89) (h v2 v3 y)) (C h11 (T (T (T h96 h48) h26) h95))) (C h11 (T (T (T h88 h27) h19) h25))) (C h11 (T (T (T (T h23 h20) h4) h18) h17))) h16) (C h11 h14))))))) (S (h v3 v3 y))

