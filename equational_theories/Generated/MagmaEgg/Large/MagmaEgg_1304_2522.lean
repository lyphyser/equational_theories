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
theorem Equation1304_implies_Equation2522 (G: Type _) [Magma G] (h: Equation1304 G) : Equation2522 G := fun x y z =>
  let v0 := M x z
  let v1 := M v0 z
  let v2 := M y v1
  let v3 := M v2 y
  have h4 := R v3
  let v5 := M (M v3 y) y
  have h6 := R v2
  have h7 := R v5
  have h8 := h y y x
  have h9 := S h8
  let v10 := M (M (M y x) x) y
  have h11 := R v10
  have h12 := R v1
  let v13 := M (M (M v1 x) x) v1
  have h14 := h v1 x v13
  have h15 := S h14
  have h16 := R x
  have h17 := R v13
  have h18 := h v1 v1 x
  have h19 := C h16 (C (T h18 (C h18 h17)) h16)
  have h20 := h x x z
  have h21 := h x v0 z
  let v22 := M (M (M v0 x) x) v0
  have h23 := h v0 z v22
  have h24 := S h23
  have h25 := R z
  have h26 := R v22
  have h27 := h v0 v0 x
  have h28 := C h25 (C (T h27 (C h27 h26)) h25)
  have h29 := T (T h20 h19) h15
  let v30 := M (M (M z x) x) z
  let v31 := M v1 z
  have h32 := h z v31 v30
  have h33 := S h32
  have h34 := R v31
  have h35 := R v30
  have h36 := h z z x
  have h37 := h x z z
  have h38 := S h20
  have h39 := S h18
  have h40 := C h16 (C (T (C h39 h17) h39) h16)
  have h41 := C h34 (T (T (T (T h14 h40) h38) h37) (C (T h36 (C h36 h35)) h34))
  have h42 := T h41 h33
  have h43 := C h42 h29
  have h44 := T (T h14 h40) h38
  let v45 := M v31 v1
  have h46 := R v45
  have h47 := C h46 h44
  have h48 := C (T (T (T h47 h43) h28) h24) h25
  have h49 := S h36
  have h50 := C h34 (T (T (T (T (C (T (C h49 h35) h49) h34) (S h37)) h20) h19) h15)
  have h51 := T h32 h50
  have h52 := C h51 h48
  have h53 := C h46 h29
  have h54 := C h51 h44
  have h55 := S h27
  have h56 := C h25 (C (T (C h55 h26) h55) h25)
  have h57 := C (T (T (T h23 h56) h54) h53) h25
  have h58 := h v31 z v1
  have h59 := S h58
  have h60 := C h42 h57
  have h61 := C (T h60 h59) h12
  have h62 := C (T (T h61 h41) h33) h57
  have h63 := R (M (M v45 v1) v1)
  have h64 := C h29 (T (T (T (T (T (T (C h63 h29) h62) h52) h47) h43) h28) h24)
  have h65 := h v45 x v1
  have h66 := C (T h58 h52) h12
  have h67 := S h65
  have h68 := C (T (T h32 h50) h66) h48
  have h69 := C h44 (T (T (T (T (T (T h23 h56) h54) h53) h60) h68) (C h63 h44))
  have h70 := C (T (T h69 h67) h66) h12
  have h71 := C (T (T h70 h62) h59) h12
  have h72 := T (T h71 h65) h64
  have h73 := C h72 h12
  let v74 := M v1 v0
  have h75 := R (M (M v74 v1) v1)
  have h76 := C h75 h29
  have h77 := C (T (T h61 h65) h64) h12
  have h78 := C (T (T h58 h68) h77) h12
  have h79 := T (T h69 h67) h78
  have h80 := C h79 h16
  have h81 := C (T (T (T (C (T (T h80 h76) h73) h29) h71) h65) h64) h44
  have h82 := R (M (M v74 x) x)
  have h83 := C h82 h29
  have h84 := C h72 h16
  have h85 := C h75 h44
  have h86 := C h79 h12
  have h87 := C (C h53 h29) h29
  have h88 := R (M (M v45 x) x)
  have h89 := C h88 h44
  have h90 := C (C (T (T h23 h56) h54) h44) h12
  have h91 := C (C (T (T (T (T (T (T h90 h89) h87) h77) h86) h85) h84) h44) h44
  have h92 := C (C (T (T h43 h28) h24) h29) h12
  have h93 := C h88 h29
  have h94 := C (C h47 h44) h44
  have h95 := C (C (T (T (T (T (T (T h80 h76) h73) h70) h94) h93) h92) h29) h29
  have h96 := C h82 h44
  have h97 := C (T (T (T h69 h67) h78) (C (T (T h86 h85) h84) h44)) h29
  T (T (h x v3 z) (C h4 (T (C (T (T (T (T (T h14 h40) h38) h21) (C (T (T (T (T (T (T (T (T (T (T (T (T h23 h56) h54) h53) h60) h68) h77) h86) h85) h84) h97) h96) h95) (T (T (T h69 h67) h41) h33))) (C (T (T (T (T (T (T (T (T (T h91 h83) h81) h80) h76) h73) h70) h94) h93) h92) h25)) h4) (C (T (T (h (M (M (M v0 v1) v1) z) v3 v2) (C h4 (C (C (T (T (T (T (C (T (T (T (T (T (C (T (T (T (T (T (T (T (T (T h90 h89) h87) h77) h86) h85) h84) h97) h96) h95) h25) (C (T (T (T (T (T (T (T (T (T (T (T (T h91 h83) h81) h80) h76) h73) h70) h62) h52) h47) h43) h28) h24) (T (T (T h32 h50) h65) h64))) (S h21)) h20) h19) h15) h6) (C h12 (C (T h8 (C h8 h11)) h12))) (S (h y v1 v10))) (h y v5 v10)) (C h7 (T (C (T (C h9 h11) h9) h7) (S (h v2 y y))))) h6) h4))) (S (h v5 v3 v2))) h4)))) (S (h v3 v3 y))

