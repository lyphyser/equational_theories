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
theorem Equation2789_implies_Equation1504 (G: Type _) [Magma G] (h: Equation2789 G) : Equation1504 G := fun x y z =>
  let v0 := M y x
  let v1 := M y z
  let v2 := M z v1
  let v3 := M v0 v2
  have h4 := R v0
  have h5 := R v3
  have h6 := h v2 (M (M x v2) (M x z)) v2
  have h7 := S h6
  have h8 := R v2
  have h9 := h z x v2
  have h10 := C (C h9 h9) h8
  let v11 := M z z
  have h12 := h (M v11 v2) v0 v0
  have h13 := S h12
  have h14 := S h9
  have h15 := C (C h14 h14) h8
  have h16 := T h6 h15
  have h17 := C h4 h16
  have h18 := R (M v0 v0)
  have h19 := C h18 h17
  have h20 := h v0 x v3
  have h21 := S h20
  have h22 := C (C h21 h21) h5
  have h23 := h v3 (M (M x v3) (M x v0)) v3
  have h24 := C (T (T h23 h22) h19) h4
  let v25 := M v3 v0
  have h26 := h v25 v0 v2
  have h27 := S h26
  have h28 := T (T (T h24 h13) h10) h7
  have h29 := S h23
  have h30 := C (C h20 h20) h5
  have h31 := T h10 h7
  have h32 := C h4 h31
  have h33 := C h18 h32
  have h34 := C (T (T h33 h30) h29) h4
  have h35 := T h12 h34
  have h36 := C h4 h35
  have h37 := C (T (C h5 h17) (C h5 h36)) h28
  have h38 := T (T (T (T (T h37 h27) h24) h13) h10) h7
  have h39 := h v0 v3 v3
  have h40 := T h39 (C h38 h5)
  have h41 := T (T (T h6 h15) h12) h34
  have h42 := T h24 h13
  have h43 := C h4 h42
  have h44 := C (T (C h5 h43) (C h5 h32)) h41
  have h45 := T (T (T (T (T h6 h15) h12) h34) h26) h44
  have h46 := T (C h45 h5) (S h39)
  let v47 := M v2 v3
  have h48 := h v47 v3 v0
  have h49 := T h37 h27
  have h50 := C h4 h49
  have h51 := C (T (T (T (T (C h18 h50) (C h18 h43)) h33) h30) h29) h40
  let v52 := M (M v3 v3) v25
  have h53 := h v52 v0 v0
  have h54 := C h41 (T h53 h51)
  have h55 := T h26 h44
  have h56 := C h8 h55
  have h57 := C h8 h35
  have h58 := C h8 h16
  have h59 := T (C (T (T (T h58 h57) h56) h54) h46) (S h48)
  have h60 := h v1 z z
  have h61 := S h60
  have h62 := R z
  have h63 := C h16 h62
  let v64 := M v2 z
  have h65 := h v64 z v1
  have h66 := h v64 z z
  have h67 := h z v2 v3
  have h68 := S h67
  have h69 := R v64
  have h70 := C h31 h62
  have h71 := T h60 h70
  have h72 := C (T (C h4 h71) (C h40 h69)) (T (T h50 h43) h32)
  have h73 := C h4 h55
  let v74 := M v0 v1
  have h75 := R v74
  have h76 := C h75 h73
  have h77 := C h75 h36
  have h78 := C h75 h17
  have h79 := C h62 h71
  have h80 := R v11
  have h81 := S h53
  have h82 := C (T (T (T (T h23 h22) h19) (C h18 h36)) (C h18 h73)) h46
  have h83 := C h5 h59
  have h84 := R v25
  have h85 := C h8 h31
  have h86 := C h8 h42
  have h87 := C h8 h49
  have h88 := C h28 (T h82 h81)
  have h89 := T h48 (C (T (T (T h88 h87) h86) h85) h40)
  have h90 := C h5 h89
  have h91 := C (T (T (T (C (T (T (T (T (T (T h58 h57) h56) h54) (C h84 h90)) (C h84 (T (T (T (T h83 h82) h81) h37) h27))) (C h28 (T (T (T (T h24 h13) h10) h7) h79))) (T (T (T (C (T (T h6 h15) (C h80 h79)) (T (T (T (T h78 h77) h76) h72) h68)) (S h66)) h63) h61)) (S h65)) h63) h61) h45
  have h92 := h (M v74 v3) v2 v2
  have h93 := C h75 h32
  have h94 := C h75 h43
  have h95 := C h75 h50
  have h96 := T h63 h61
  have h97 := C (T (C h46 h69) (C h4 h96)) (T (T h17 h36) h73)
  have h98 := h z y z
  have h99 := C h62 h96
  let v100 := M v1 v1
  have h101 := R v100
  have h102 := R v1
  have h103 := R y
  have h104 := S (h y x v1)
  T (T (h x y v0) (C (C (T (T (T (T (C h103 h40) (C h103 h89)) (C (T (T (T (T (T (T (T (T (h y v1 v3) (C (C (R (M v1 v3)) (T (T (T (T (T (T (T (T (T (T (T (T (T (C (T (T (h v1 (M (M x v1) (M x y)) v1) (C (C h104 h104) h102)) (C (R (M y y)) (C h103 (T (T (T (T h98 (C h101 (T (T (T (T (T (T h67 h97) h95) h94) h93) h92) h91))) (C h101 (C h102 h49))) (C h101 (C h102 h42))) (C h101 (C h102 h31)))))) h103) (S (h (M v100 (M v1 v2)) y y))) (C h101 (C h102 h16))) (C h101 (C h102 h35))) (C h101 (C h102 h55))) (C h101 (T (T (T (T (T (T (C (T (T (T h60 h70) h65) (C (T (T (T (T (T (T (C h41 (T (T (T (T h99 h6) h15) h12) h34)) (C h84 (T (T (T (T h26 h44) h53) h51) h90))) (C h84 h83)) h88) h87) h86) h85) (T (T (T h60 h70) h66) (C (T (T (C h80 h99) h10) h7) (T (T (T (T h67 h97) h95) h94) h93))))) h38) (S h92)) h78) h77) h76) h72) h68))) (S h98)) h67) h97) h95) h94) h93) h92) h91)) h5)) (S (h v52 v1 v3))) h37) h27) h24) h13) h10) h7) (R (M (M v2 v2) v47)))) (C h8 h59)) (C h8 h46)) h40) h4)) (S (h v3 v2 v0))

