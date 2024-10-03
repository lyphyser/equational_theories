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
theorem Equation3404_implies_Equation4424 (G: Type _) [Magma G] (h: Equation3404 G) : Equation4424 G := fun x y z =>
  let v0 := M x y
  let v1 := M z z
  have h2 := h v0 v1 x
  let v3 := M x v0
  have h4 := h x v0 v3
  have h5 := S h4
  let v6 := M v1 y
  let v7 := M v3 x
  have h8 := h v3 (M v0 v7) v6
  have h9 := S h8
  have h10 := R (M v6 v3)
  have h11 := h x v0 z
  have h12 := S h11
  let v13 := M z x
  have h14 := h z (M v0 v13) v6
  have h15 := S h14
  have h16 := R (M v6 z)
  have h17 := h z x z
  have h18 := h z z z
  have h19 := S h18
  let v20 := M z v1
  have h21 := h z v20 z
  have h22 := S h21
  have h23 := h v20 v1 z
  have h24 := R v1
  have h25 := R z
  have h26 := h z v1 z
  have h27 := h v1 z z
  have h28 := h v1 z v1
  have h29 := C h25 (T (T (T (T (T (T (C h24 h26) (S h28)) h27) (C h25 h19)) h26) (C h25 (C h24 h18))) (S h23))
  have h30 := h v1 v1 z
  have h31 := R x
  have h32 := C h31 (T (T (T h30 h29) h22) h19)
  have h33 := h v1 v1 x
  have h34 := S h33
  have h35 := C h24 h32
  have h36 := h v1 x v1
  have h37 := C h31 (T h36 h35)
  have h38 := C h24 (T (T (T (T (T h37 h34) h30) h29) h22) h19)
  have h39 := h x x v1
  have h40 := C h31 (T h39 h38)
  have h41 := h x x x
  have h42 := S h41
  have h43 := S h39
  have h44 := S h36
  have h45 := S h30
  have h46 := S h26
  have h47 := C h25 (T (T (T (T (T (T h23 (C h25 (C h24 h19))) h46) (C h25 h18)) (S h27)) h28) (C h24 h46))
  have h48 := C h31 (T (T (T h18 h21) h47) h45)
  have h49 := C h31 (T (C h24 h48) h44)
  have h50 := C h24 (T (T (T (T (T h18 h21) h47) h45) h33) h49)
  have h51 := C h31 (T h50 h43)
  have h52 := C h31 (T h48 h51)
  have h53 := h v1 x x
  have h54 := h v1 x v0
  have h55 := h v0 v1 v6
  have h56 := S h55
  have h57 := R (M v6 v0)
  have h58 := R v6
  have h59 := C h58 (C (T (T (T (T (T h39 h38) h30) h29) h22) h19) h57)
  have h60 := h v0 (M x x) v6
  have h61 := h x v0 x
  have h62 := R v0
  have h63 := T (T (T (T (T (C h62 (T h61 (C h31 (T (T h60 h59) h56)))) (S h54)) h53) (C h31 (T h52 h42))) h40) h32
  have h64 := h v3 z v0
  have h65 := C h58 (C (T h64 (C h62 (T (C h25 h63) (S h17)))) h16)
  let v66 := M v3 z
  have h67 := h z v66 v6
  have h68 := T (T (T h67 h65) h15) h12
  have h69 := C h62 (T (C h68 (h v0 v3 x)) (S (h v3 x v3)))
  have h70 := h v3 (M z v66) v0
  have h71 := h z z v3
  have h72 := C h58 (C (T (T h71 h70) h69) h10)
  have h73 := h v3 v1 v6
  have h74 := h v3 v1 v3
  have h75 := S h61
  have h76 := S h60
  have h77 := C h58 (C (T (T (T (T (T h18 h21) h47) h45) h50) h43) h57)
  have h78 := C h62 (T (T (T (T (T (T (T (T (C h31 h63) h52) h42) h39) h38) h30) h29) h22) h19)
  have h79 := h v3 x v0
  have h80 := R v3
  have h81 := C h80 (T (C h31 (T (T (T (T h79 h78) h55) h77) h76)) h75)
  have h82 := h x x v3
  have h83 := S h82
  have h84 := C h31 (T h40 h32)
  have h85 := T (T (T (T (T h48 h51) (C h31 (T h41 h84))) (S h53)) h54) (C h62 (T (C h31 (T (T h55 h77) h76)) h75))
  have h86 := C h80 (T h61 (C h31 (T (T (T (T h60 h59) h56) (C h62 (T (T (T (T (T (T (T (T h18 h21) h47) h45) h50) h43) h41) h84) (C h31 h85)))) (S h79))))
  have h87 := S h67
  have h88 := C h58 (C (T (C h62 (T h17 (C h25 h85))) (S h64)) h16)
  have h89 := h v3 v1 v0
  let v90 := M v1 x
  have h91 := h v1 (M v0 v90) v1
  have h92 := h x v0 v1
  let v93 := M y x
  have h94 := C h62 (T (T (C h24 (T (T (T (T (C h62 h11) (S (h v13 z v0))) (h v13 z v1)) (C h24 (T (S (h x v1 z)) h48))) h44)) (C h24 (T (T (T (T h36 (C h24 (T h32 (h x v1 v1)))) (S (h v90 v1 v1))) (h v90 v1 x)) (C h31 h38)))) h44)
  have h95 := S h73
  have h96 := T (C h62 (T (h v3 x z) (C h25 (S (h v0 z x))))) (S (h z z v0))
  have h97 := C h58 (C h96 h10)
  T (T (T (T (T h4 (C h80 h96)) h89) h94) (C h62 (T (h v1 x y) (C (R y) (T (C h31 (T (T (T (T (T (T (h y v1 v6) (C h58 (C (T (T (T (T (T h71 h70) h69) (h v0 v7 v6)) (C h58 (C (T (T (T (T h79 h78) h2) (C h31 (T (T (C h24 (T (T (T (T (T (T h4 h8) h97) h95) h74) (C (T (T (T h11 h14) h88) h87) (T (T (T (T (C h24 (T h86 h83)) (C h24 (T (T (T h39 h38) h33) h49))) h43) h82) h81))) (C (T (T (T (T (T (T (T (T (T h67 h65) h15) h12) h4) h8) h97) h95) h89) h94) (T (T (T h86 h83) h39) h38)))) (S h91)) (S h92)))) (S (h y x x))) h57))) (S (h v0 v93 v6))) (R (M v6 y))))) (S (h y (M v0 v93) v6))) (S (h x v0 y))) h92) h91) (C h24 (T (T (T (T (T (T (C (T (T (T (T (T (T (T (T (T (C h62 (T (T h36 h35) (C h24 h85))) (S h89)) h73) h72) h9) h5) h11) h14) h88) h87) (T (T (T h50 h43) h82) h81)) (C h68 (T (T (T (T h86 h83) h39) (C h24 (T (T (T h37 h34) h50) h43))) (C h24 (T h82 h81))))) (S h74)) h73) h72) h9) h5)))) (S h2)))))) (S (h v1 y v0))

