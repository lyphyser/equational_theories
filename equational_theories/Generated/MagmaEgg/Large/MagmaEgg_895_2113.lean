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
theorem Equation895_implies_Equation2113 (G: Type _) [Magma G] (h: Equation895 G) : Equation2113 G := fun x y z =>
  let v0 := M y x
  let v1 := M y z
  let v2 := M v0 z
  let v3 := M v2 v1
  let v4 := M v3 v0
  have h5 := R v4
  have h6 := R v0
  let v7 := M v1 x
  have h8 := h v3 v3 (M v7 (M v3 x))
  have h9 := S h8
  have h10 := h v1 v3 x
  have h11 := R v3
  have h12 := C h11 (C h10 h10)
  have h13 := T h12 h9
  have h14 := C h13 h6
  have h15 := h (M v3 (M v1 v1)) v0 v2
  have h16 := S h15
  have h17 := h v2 v1 v1
  have h18 := S h17
  have h19 := S h10
  have h20 := C h11 (C h19 h19)
  have h21 := T h8 h20
  have h22 := R v1
  have h23 := C h22 h21
  have h24 := T h23 h18
  have h25 := h v0 y z
  have h26 := S h25
  have h27 := h (M v1 v3) v2 v1
  have h28 := S h27
  have h29 := C h22 h13
  have h30 := T h17 h29
  have h31 := C h30 h22
  have h32 := C (T (T h12 h9) h31) h11
  have h33 := C h21 h11
  have h34 := C h24 (T h33 h32)
  have h35 := h v1 v3 v3
  have h36 := C (T h35 (C h21 (T (T (T h34 h28) h23) h18))) (C h26 h24)
  have h37 := h y v1 v3
  have h38 := C h6 (T h37 h36)
  have h39 := C (T h38 h16) h6
  have h40 := h v0 v0 y
  have h41 := S h37
  have h42 := C h13 h11
  have h43 := C h24 h22
  have h44 := C (T (T h43 h8) h20) h11
  have h45 := C h30 (T h44 h42)
  have h46 := C (T (C h13 (T (T (T h17 h29) h27) h45)) (S h35)) (C h25 h30)
  have h47 := C h6 (T h46 h41)
  have h48 := T (T (T h8 h20) h15) h47
  let v49 := M v0 y
  have h50 := R v49
  have h51 := C (T h34 h28) h22
  have h52 := C (T h27 h45) h22
  let v53 := M v0 v2
  have h54 := R v53
  have h55 := R v2
  have h56 := C (C h21 h55) h54
  have h57 := T (C (T (C (T (T h56 h46) h41) h11) h26) (T (T (T (T h33 h32) (C h52 h11)) (C (T (T (T (T (T h51 h43) h8) h20) h15) h47) h11)) (C h50 h48))) (S h40)
  have h58 := C h48 h57
  have h59 := T (T (T h38 h16) h12) h9
  have h60 := C (C h13 h55) h54
  have h61 := T h40 (C (T h25 (C (T (T h37 h36) h60) h11)) (T (T (T (T (C h50 h59) (C (T (T (T (T (T h38 h16) h12) h9) h31) h52) h11)) (C h51 h11)) h44) h42))
  have h62 := h v49 v3 v0
  have h63 := h (M (M v3 v2) v53) v3 v3
  have h64 := T (T (T (T (T (T h37 h36) h60) h63) h58) h39) h14
  have h65 := C (T (T (T (T (T (C h59 (C (T (T (T (T h37 h36) h60) h63) h58) h64)) (S h62)) h38) h16) h12) h9) h61
  have h66 := T h65 h58
  have h67 := S h63
  have h68 := C h59 h61
  have h69 := C (T h15 h47) h6
  have h70 := C h21 h6
  have h71 := C (T (T (T (T (T h8 h20) h15) h47) h62) (C h48 (C (T (T (T (T h68 h67) h56) h46) h41) (T (T (T (T (T (T h70 h69) h68) h67) h56) h46) h41)))) h57
  have h72 := h y y x
  have h73 := S h72
  let v74 := M v0 v0
  have h75 := R v74
  have h76 := C (T (T (T (T h65 h67) h56) h46) h41) h75
  have h77 := C (T h68 h71) h75
  have h78 := C h69 h75
  have h79 := C h70 h75
  have h80 := h (M v4 v74) z z
  have h81 := S h80
  have h82 := R (M z z)
  have h83 := R z
  have h84 := C h14 h75
  have h85 := C h39 h75
  have h86 := C h66 h75
  have h87 := C (T (T (T (T h37 h36) h60) h63) h71) h75
  have h88 := h z v1 x
  have h89 := S h88
  have h90 := h v1 v1 (M (M z x) v7)
  have h91 := C h83 (T (T h90 (C h22 (C h89 h89))) (C (C (T (T (T (T h72 h87) h86) h85) h84) h83) h82))
  have h92 := h (M z v1) x x
  have h93 := S h92
  let v94 := M x x
  have h95 := R v94
  have h96 := R x
  have h97 := C h83 (T (T (C (C (T (T (T (T h79 h78) h77) h76) h73) h83) h82) (C h22 (C h88 h88))) (S h90))
  have h98 := h x v0 x
  have h99 := S h98
  have h100 := h v0 v0 (M v94 (M v0 x))
  have h101 := C h96 (T (T h100 (C h6 (C h99 h99))) (C (C (T (T (T (T (T (T h72 h87) h86) h85) h84) h80) h97) h96) h95))
  have h102 := R (M x v0)
  T (T (h x v3 v0) (C h11 (T (T (T (T (T (T (T (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h101 h93) h91) h81) h79) h78) h77) h76) h73) h37) h36) h60) h63) h58) h39) h14) (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T h70 h69) h68) h67) h56) h46) h41) h72) h87) h86) h85) h84) h80) h97) h92) (C h96 (T (T (C (C (T (T (T (T (T (T h91 h81) h79) h78) h77) h76) h73) h96) h95) (C h6 (C h98 h98))) (S h100))))) (C h70 h102)) (C (T (T h69 h68) h71) h102)) (C (T (T (T (T (T (T (T (T (T (T (T h65 h67) h56) h46) h41) h72) h87) h86) h85) h84) h80) h97) (T (T (T (T (T (T (T (T h101 h93) h91) h81) h79) h78) h77) h76) h73))) (C (T (T (T (T (T (T (T (T (T (T (T h91 h81) h79) h78) h77) h76) h73) h37) h36) h60) h63) h71) h64)) (C h66 h5)) (C h39 h5)) (C h14 h5)))) (S (h v3 v3 v0))

