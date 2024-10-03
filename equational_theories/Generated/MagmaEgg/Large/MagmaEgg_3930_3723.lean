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
theorem Equation3930_implies_Equation3723 (G: Type _) [Magma G] (h: Equation3930 G) : Equation3723 G := fun x y z =>
  let v0 := M x z
  let v1 := M x y
  let v2 := M v1 v0
  have h3 := h v1 v0 v2
  have h4 := S h3
  have h5 := R v1
  have h6 := R v2
  have h7 := h x z v1
  have h8 := S h7
  let v9 := M z v1
  have h10 := h (M x v9) x y
  have h11 := S h10
  have h12 := h x v9 v2
  have h13 := R x
  have h14 := h z v1 x
  have h15 := R z
  have h16 := h x y x
  have h17 := S h16
  have h18 := h y x z
  have h19 := S h18
  have h20 := R y
  have h21 := h x z x
  have h22 := S h21
  let v23 := M z x
  have h24 := h (M x v23) x z
  have h25 := h x v23 z
  have h26 := h z x z
  have h27 := S h26
  have h28 := h x z v0
  have h29 := S h28
  let v30 := M z v0
  have h31 := h (M x v30) x v2
  have h32 := S h31
  have h33 := h x v30 z
  have h34 := S h33
  have h35 := C (C h13 h26) h13
  have h36 := T (T h21 h35) h34
  have h37 := R (M x v2)
  have h38 := C (C h36 h37) h36
  have h39 := h v0 x v2
  have h40 := T (T (T h39 h38) h32) h29
  have h41 := C h15 h40
  have h42 := C h41 h15
  have h43 := h z v0 x
  have h44 := S h39
  have h45 := C (C h13 h27) h13
  have h46 := T (T h33 h45) h22
  have h47 := C (C h46 h37) h46
  have h48 := T (T (T h28 h31) h47) h44
  have h49 := C h15 h48
  have h50 := C h49 h15
  have h51 := T (T (T h21 h35) (C (C h13 (T h50 (C (T (T (T h41 h43) h42) h27) h15))) h13)) (S h25)
  have h52 := h v0 v0 x
  have h53 := C h20 (T (T (T h52 (C (C h51 h40) h51)) (S h24)) h22)
  have h54 := C h53 h20
  have h55 := S h52
  have h56 := S h43
  have h57 := T (T (T h25 (C (C h13 (T (C (T (T (T h26 h50) h56) h49) h15) h42)) h13)) h45) h22
  have h58 := C (C h57 h48) h57
  have h59 := C h20 (T (T (T h21 h24) h58) h55)
  have h60 := h y v0 v0
  have h61 := C h59 h20
  have h62 := C h13 (T (T (C (T (T (T h18 h61) (S h60)) h59) h20) h54) h19)
  have h63 := C h62 h13
  let v64 := M y x
  have h65 := h x v64 y
  have h66 := C h13 (T (T h18 h61) (C (T (T (T h53 h60) h54) h19) h20))
  have h67 := C h66 h13
  have h68 := T (T h16 h67) (C (T (T (T h62 h65) h63) h17) h13)
  have h69 := h z x y
  have h70 := h x v30 v2
  have h71 := T (T (T (T (T h21 h35) h34) h70) (C (C h13 (C (T (T (T (T (T h43 h42) h27) h69) (C (C h15 h68) h15)) (S h14)) h6)) h13)) (S h12)
  have h72 := T (T (C (T (T (T h16 h67) (S h65)) h66) h13) h63) h17
  have h73 := C (C h71 h72) h71
  have h74 := h v0 v1 x
  have h75 := C (T (T (T h74 h73) h11) h8) h6
  have h76 := C (C h5 h75) h5
  let v77 := M v0 v1
  have h78 := h v1 v77 v2
  have h79 := h v1 v77 v0
  have h80 := S h79
  have h81 := h v0 x y
  let v82 := M v0 v0
  let v83 := M y v0
  have h84 := T (T (T (T (T (h x v83 v2) (C (C h13 (C (T (T h60 h54) h19) h6)) h13)) (S (h x v64 v2))) h65) h63) h17
  have h85 := h v0 v1 v0
  have h86 := S h85
  have h87 := R v0
  have h88 := S h74
  have h89 := T (T (T (T (T h12 (C (C h13 (C (T (T (T (T (T h14 (C (C h15 h72) h15)) (S h69)) h26) h50) h56) h6)) h13)) (S h70)) h33) h45) h22
  have h90 := C (C h89 h68) h89
  let v91 := M v0 v2
  have h92 := h (M v1 v91) v1 x
  have h93 := h v1 v91 v0
  have h94 := S h93
  have h95 := C (C h5 (T (T (T (T (T (T (T (T (T (S h81) h39) h38) h32) h29) h7) h10) h90) h88) h85)) h5
  have h96 := C (T (T (T h7 h10) h90) h88) h6
  have h97 := h v1 v0 v1
  have h98 := h v0 v2 v2
  have h99 := S h98
  have h100 := C (C h5 (T (T (T (T (T (T (T (T (T h86 h74) h73) h11) h8) h28) h31) h47) h44) h81)) h5
  have h101 := C (T (T h96 (C (T (T (T (T (T (T (T h74 h73) h11) h8) h28) h31) h47) h44) h6)) (C h40 (T (T h3 h92) (C (T (C (T (T h93 h100) h80) h72) (S h97)) (T (T (T (T (T h93 h100) h80) h78) h76) h4))))) h87
  T (T (T (T (T (T (T (T (T (h x y v0) (h (M x v83) x z)) (C (C h84 (T (T (T (T (T (T (T (T (T h7 h10) h90) h88) h85) h101) h99) h96) (C (T (T h85 h101) h99) h6)) (C (T (T (T (T (T (T (T (T (T (T h98 (C (T (T (C h48 (T (T (C (T h97 (C (T (T h79 h95) h94) h68)) (T (T (T (T (T h3 (C (C h5 h96) h5)) (S h78)) h79) h95) h94)) (S h92)) h4)) (C (T (T (T (T (T (T (T h39 h38) h32) h29) h7) h10) h90) h88) h6)) h75) h87)) h86) h74) h73) h11) h8) h21) h24) h58) h55) h6))) h84)) (S (h v1 v82 v2))) (h v1 v82 v0)) (C (C h5 (T (S (h v0 x z)) h81)) h5)) h80) h78) h76) h4

