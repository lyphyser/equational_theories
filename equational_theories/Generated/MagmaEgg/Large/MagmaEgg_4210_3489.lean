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
theorem Equation4210_implies_Equation3489 (G: Type _) [Magma G] (h: Equation4210 G) : Equation3489 G := fun x y z =>
  let v0 := M y z
  let v1 := M v0 z
  let v2 := M y v1
  let v3 := M x x
  have h4 := R v3
  have h5 := R v1
  have h6 := h v0 z v0
  have h7 := S h6
  have h8 := h v0 v0 y
  have h9 := S h8
  have h10 := R y
  have h11 := R v0
  have h12 := h y v0 v0
  have h13 := S h12
  have h14 := h v0 z y
  have h15 := C h14 h11
  have h16 := T h15 h13
  have h17 := C h16 h11
  have h18 := C (T h6 h17) h10
  have h19 := h z z y
  have h20 := h z z v0
  have h21 := S h20
  let v22 := M v1 z
  have h23 := h v22 v0 v2
  have h24 := S h23
  have h25 := R v2
  have h26 := h v1 z y
  have h27 := R (M v2 v0)
  have h28 := C (C h27 (S h26)) h25
  have h29 := h (M (M v0 v1) y) v0 v2
  have h30 := h y v1 v0
  have h31 := h x x v3
  have h32 := h x x x
  have h33 := h x x y
  have h34 := S h33
  let v35 := M (M y x) x
  have h36 := h v35 y v3
  have h37 := S h36
  have h38 := R v35
  have h39 := h v35 y v2
  have h40 := R x
  have h41 := h y x v2
  have h42 := h x v1 y
  have h43 := h v2 v1 x
  have h44 := h v2 v1 z
  have h45 := S h44
  have h46 := R z
  have h47 := h z v1 y
  have h48 := h y z v2
  have h49 := C (T h48 (C (S h47) h25)) h46
  have h50 := h v2 y v0
  have h51 := S h50
  have h52 := h y z z
  let v53 := M z z
  have h54 := h (M v53 y) z v2
  have h55 := h v53 y y
  have h56 := S h19
  have h57 := S h14
  have h58 := C h57 h11
  have h59 := T h12 h58
  have h60 := C h59 h11
  have h61 := C (T h60 h7) h10
  have h62 := R (M y y)
  have h63 := h (M v0 v0) y y
  have h64 := R (M v2 z)
  have h65 := h v1 z v2
  have h66 := T (T (T h65 (C (C h64 (T (T (T h14 h63) (C (C h62 (T (T h8 h61) h56)) h10)) (S h55))) h25)) (S h54)) (S h52)
  have h67 := h v0 y v2
  have h68 := R (M v2 y)
  have h69 := h v22 y v2
  have h70 := h v22 y v1
  have h71 := R v22
  have h72 := T (T (T h52 h54) (C (C h64 (T (T (T h55 (C (C h62 (T (T h19 h18) h9)) h10)) (S h63)) h57)) h25)) (S h65)
  have h73 := h y z y
  have h74 := C (S h73) h11
  have h75 := h y y v0
  have h76 := S h75
  have h77 := C h73 h11
  have h78 := h v1 v0 v2
  have h79 := C (T (T (T h12 h58) h78) (C (T (T (T (T (C (T (T (C (T (T (T (T (T (T (T (T (T h30 h29) h28) h24) h21) h19) h18) h9) h77) h76) h11) (C (T h75 h74) h72)) (C (T h8 h61) h71)) h5) (S h70)) h69) (C (C h68 h66) h25)) (S h67)) h25)) h66
  have h80 := C h16 h71
  have h81 := C (T (T h80 h79) h51) (T (T (T h49 h45) h43) (C (T (C h42 h25) (S h41)) h40))
  have h82 := h v22 v0 v1
  have h83 := h v2 v1 y
  have h84 := C h59 h71
  have h85 := S h30
  have h86 := S h29
  have h87 := C (C h27 h26) h25
  have h88 := C (T (T (T (C (T (T (T (T h67 (C (C h68 h72) h25)) (S h69)) h70) (C (T (T (C (T h18 h9) h71) (C (T h77 h76) h66)) (C (T (T (T (T (T (T (T (T (T h75 h74) h8) h61) h56) h20) h23) h87) h86) h85) h11)) h5)) h25) (S h78)) h15) h13) h72
  have h89 := C (T (T (T (T (T (T h30 h29) h28) h24) h82) h81) (C (T (T (T (T (T (T (T (T (T h50 h88) h84) (C h16 h66)) h60) h7) h49) h45) h83) (C (T (T (C (T (T (T (T (T h30 h29) h28) h24) h82) h81) h25) (S h39)) h34) h10)) h38)) h4
  have h90 := C (T (T (T h89 h37) h34) h32) h4
  have h91 := h v3 v3 v2
  have h92 := S h32
  have h93 := C h92 h4
  have h94 := S h82
  have h95 := C (T (C h47 h25) (S h48)) h46
  have h96 := C (T (T h50 h88) h84) (T (T (T (C (T h41 (C (S h42) h25)) h40) (S h43)) h44) h95)
  T (T (T (T h31 (C (T (T (T h92 h33) h36) (C (T (T (T (T (T (T (C (T (T (T (T (T (T (T (T (T (C (T (T h33 h39) (C (T (T (T (T (T h96 h94) h23) h87) h86) h85) h25)) h10) (S h83)) h44) h95) h6) h17) (C h59 h72)) h80) h79) h51) h38) h96) h94) h23) h87) h86) h85) h4)) h4)) (C (T (T (T (T (T (T h89 h37) h34) h31) h93) h91) (C (T (T (T h90 h93) h91) (C (T h90 (S h31)) h25)) (T (T (T (T (T (T (T (T (T (T h30 h29) h28) h24) h21) h19) h18) h9) (h v0 v0 v1)) (C h7 h5)) (h v1 v1 y)))) h4)) (S (h (M (M v2 v1) y) v2 v3))) (S (h y v1 v2))

