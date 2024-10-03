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
theorem Equation2522_implies_Equation4162 (G: Type _) [Magma G] (h: Equation2522 G) : Equation4162 G := fun x y z =>
  let v0 := M y x
  let v1 := M v0 z
  let v2 := M v1 z
  have h3 := h v2 x v2
  have h4 := S h3
  have h5 := R x
  have h6 := h v0 v2 z
  have h7 := C h5 h6
  have h8 := h v0 z y
  have h9 := S h8
  have h10 := R z
  let v11 := M z (M (M v0 y) y)
  have h12 := h v11 z z
  have h13 := C h8 h10
  have h14 := C (T (C h5 (T (C (T (C (C h10 h13) h10) (S h12)) h10) h9)) h7) h5
  have h15 := h (M z v1) x z
  have h16 := R v1
  have h17 := h z v1 y
  have h18 := S h17
  have h19 := h (M v1 (M (M z y) y)) x v1
  have h20 := C h9 h10
  have h21 := C h5 (S h6)
  have h22 := h (M x v2) x x
  have h23 := h v0 x z
  have h24 := h y x x
  let v25 := M x y
  have h26 := h v0 v2 v25
  have h27 := S h26
  have h28 := R v2
  have h29 := h (M v2 (M (M v0 v25) v25)) x v2
  have h30 := h v0 v2 x
  let v31 := M v0 x
  have h32 := h (M v2 (M v31 x)) x v2
  have h33 := h v31 v2 v0
  have h34 := R v0
  have h35 := h x v25 v25
  have h36 := S h35
  have h37 := R v25
  let v38 := M (M x v25) v25
  let v39 := M v25 v38
  have h40 := h v39 v25 v25
  have h41 := S h40
  have h42 := h x x v1
  have h43 := S h42
  have h44 := h (M x (M (M x v1) v1)) x x
  have h45 := h x x x
  have h46 := h (M x (M (M x x) x)) x x
  have h47 := h x y v25
  have h48 := S h47
  have h49 := R y
  have h50 := h (M y v38) y y
  have h51 := h (M y v25) x y
  have h52 := h y v25 v2
  let v53 := M y v2
  have h54 := h (M v25 (M v53 v2)) x v25
  have h55 := h y x y
  have h56 := S h55
  have h57 := h (M x (M (M y y) y)) x x
  have h58 := T (T h3 (C (T h21 (C h5 (C h55 h5))) h5)) (S h57)
  have h59 := C h58 h5
  have h60 := C (T h59 h56) h28
  have h61 := h (M v2 x) v25 v2
  have h62 := T (T h57 (C (T (C h5 (C h56 h5)) h7) h5)) h4
  have h63 := C h62 h5
  have h64 := T (T (T (T h55 h63) h61) (C (T (T (T (C h37 (C h60 h28)) h54) (C (T (T (T (C h5 (T (T (C (S h52) h37) h51) (C (C h5 (T (C (T (C (C h49 (C h47 h49)) h49) (S h50)) h49) h48)) h5))) h46) (C (C h5 (T (C (S h45) h5) (C h42 h5))) h5)) (S h44)) h5)) h43) h37)) (C h35 h37)
  have h65 := C h37 h64
  have h66 := C h65 h37
  have h67 := C (T h66 h41) h37
  have h68 := C (T h55 h63) h28
  have h69 := T (T (T (T (C h36 h37) (C (T (T (T h42 (C (T (T (T h44 (C (C h5 (T (C h43 h5) (C h45 h5))) h5)) (S h46)) (C h5 (T (T (C (C h5 (T h47 (C (T h50 (C (C h49 (C h48 h49)) h49)) h49))) h5) (S h51)) (C h52 h37)))) h5)) (S h54)) (C h37 (C h68 h28))) h37)) (S h61)) h59) h56
  have h70 := C h37 h69
  have h71 := C h70 h37
  have h72 := h (M v25 y) v2 v25
  have h73 := S h72
  have h74 := C (T h40 h71) h37
  have h75 := C (T h59 (C h62 (T h35 h74))) h28
  have h76 := T (T (C (T (C (T (T (T h68 h75) h73) h65) h37) h71) h37) h67) h36
  have h77 := h v53 v0 v25
  have h78 := h v53 y v25
  have h79 := C (T (C h58 (T h67 h36)) h63) h28
  have h80 := T (T h35 h74) (C (T h66 (C (T (T (T h70 h72) h79) h60) h37)) h37)
  have h81 := h v39 v0 v25
  have h82 := h v53 v25 v25
  have h83 := h (M v25 x) v2 v25
  have h84 := C (T (T (T (C h28 (C (T (T h83 (C (C h28 (T (T (T (C (T (T (T (T (T (C (C h37 h80) h37) (S h82)) h68) h75) h73) h65) h37) h41) h81) (C (T (T (T (C (C h49 h80) h69) (S h78)) h77) (C (C h34 h76) h34)) h34))) h28)) (S h33)) h5)) h32) (C (C h5 (T (C (S h30) h28) (C h26 h28))) h5)) (S h29)) h28
  have h85 := h v25 v2 x
  have h86 := C (T (T (T (T h85 h84) h27) (C (T (T (T h24 (C (C h5 (C h23 h5)) h5)) (S h22)) (C h5 (T (T (T h3 (C (T h21 (C h5 (T h8 (C (T h12 (C (C h10 h20) h10)) h10)))) h5)) (S h15)) (C h17 h16)))) h5)) (S h19)) h16
  have h87 := h (M v25 v1) v2 v2
  have h88 := S h87
  have h89 := C (T (T (T (T h19 (C (T (T (T (C h5 (T (T (T (C h18 h16) h15) h14) h4)) h22) (C (C h5 (C (S h23) h5)) h5)) (S h24)) h5)) h26) (C (T (T (T h29 (C (C h5 (T (C h27 h28) (C h30 h28))) h5)) (S h32)) (C h28 (C (T (T h33 (C (C h28 (T (T (T (C (T (T (T (C (C h34 h80) h34) (S h77)) h78) (C (C h49 h76) h64)) h34) (S h81)) h40) (C (T (T (T (T (T h70 h72) h79) h60) h82) (C (C h37 h76) h37)) h37))) h28)) (S h83)) h5))) h28)) (S h85)) h16
  have h90 := C (T h17 h89) h28
  have h91 := h (M z v2) x z
  have h92 := S h91
  have h93 := h v0 z z
  have h94 := C (T (C h5 h20) (C h5 (C h93 h10))) h5
  have h95 := h v11 x z
  have h96 := h v11 v2 z
  have h97 := C (C h28 (T (C (T (C (C h28 h13) h28) (S h96)) h28) (C (T (T (T h95 h94) h92) h90) h28))) h28
  have h98 := h (M v2 v1) v2 v2
  have h99 := h v2 v1 v25
  have h100 := T (T (T (T (T (C (S h99) h16) h98) h97) h88) h86) h18
  let v101 := M v1 (M (M v2 v25) v25)
  have h102 := h v101 v1 v1
  have h103 := h v101 v2 v1
  have h104 := S h98
  have h105 := C (C h28 (T (C (T (T (T (C (T h86 h18) h28) h91) (C (T (C h5 (C (S h93) h10)) (C h5 h13)) h5)) (S h95)) h28) (C (T h96 (C (C h28 h20) h28)) h28))) h28
  have h106 := T (T (T (T (T h17 h89) h87) h105) h104) (C h99 h16)
  have h107 := h v0 v1 v1
  T (T (T (T (T (T (T h85 h84) h27) h107) (C (T (T (T (T (T (T (T (T (T (T (T (h (M v1 (M (M v0 v1) v1)) x v1) (C (C h5 (T (C (S h107) h16) (C (h v0 v1 z) h16))) h5)) (S (h (M v1 v2) x v1))) (C (T (T (T (h v1 v2 v1) (C (C h28 (T (T (T (T (T (T (C (C h16 h13) h16) (S (h v11 v1 z))) h95) h94) h92) h90) (C (T (T (T (T (T (T h87 h105) h104) (C (C h16 h106) h16)) (S h102)) h103) (C (C h28 h100) h28)) h28))) h28)) (S (h (M v2 z) v2 v2))) (C h28 h106)) h28)) (S h103)) h102) (C (C h16 h100) h16)) h98) h97) h88) h86) h18) h16)) h15) h14) h4

