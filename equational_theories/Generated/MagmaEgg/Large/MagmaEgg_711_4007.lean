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
theorem Equation711_implies_Equation4007 (G: Type _) [Magma G] (h: Equation711 G) : Equation4007 G := fun x y z =>
  have h0 := R z
  have h1 := R x
  let v2 := M y x
  let v3 := M v2 x
  let v4 := M y v3
  let v5 := M x y
  have h6 := h y v5 v4
  have h7 := S h6
  have h8 := R v4
  have h9 := h y y x
  have h10 := T h9 (C h9 h8)
  have h11 := R v5
  have h12 := C h11 (C h11 h10)
  have h13 := R y
  let v14 := M x (M (M x x) x)
  have h15 := h x y v14
  have h16 := S h15
  have h17 := R v14
  have h18 := h x x x
  have h19 := C h13 (C h13 (T h18 (C h18 h17)))
  have h20 := T h19 h16
  have h21 := C h20 h13
  have h22 := C h21 h13
  have h23 := C h11 h22
  have h24 := S h18
  have h25 := C h13 (C h13 (T (C h24 h17) h24))
  have h26 := T h15 h25
  have h27 := C h26 h13
  have h28 := h (M y v2) v5 y
  have h29 := T (T (T h15 h25) h28) (C h27 (T (T h23 h12) h7))
  have h30 := C h11 h29
  have h31 := C (T (T (T h30 h23) h12) h7) h1
  let v32 := M v5 x
  have h33 := h (M v32 x) x y
  have h34 := S h33
  have h35 := h v32 v2 x
  have h36 := C h27 h13
  have h37 := C h11 h36
  have h38 := S h9
  have h39 := T (C h38 h8) h38
  have h40 := C h11 (C h11 h39)
  have h41 := T (T (T (C h21 (T (T h6 h40) h37)) (S h28)) h19) h16
  have h42 := C h11 h41
  have h43 := C (T (T (T h6 h40) h37) h42) h1
  have h44 := R v2
  have h45 := C h44 (T (C h44 h36) (C h43 h41))
  have h46 := h x v2 y
  have h47 := C h43 (T (T (T (T (T (C h31 (T h46 h45)) (S h35)) h30) h23) h12) h7)
  have h48 := C (T (T (T (T h19 h16) h46) h45) h47) h13
  have h49 := T h27 h48
  have h50 := h y x v4
  have h51 := S h46
  have h52 := C h44 (T (C h31 h29) (C h44 h22))
  have h53 := C h31 (T (T (T (T (T h6 h40) h37) h42) h35) (C h43 (T h52 h51)))
  have h54 := C (T (T h53 h52) h51) (T (T (T h50 (C h1 (C h1 h39))) (C h26 h11)) (C h20 h49))
  have h55 := T (T h54 h34) h31
  have h56 := C h0 h55
  have h57 := C h0 h49
  have h58 := T h57 h56
  have h59 := C h58 h0
  let v60 := M z v2
  let v61 := M v60 z
  have h62 := h (M z v5) v61 z
  have h63 := S h62
  let v64 := M z (M (M z x) x)
  have h65 := h z v61 v64
  have h66 := S h65
  have h67 := R v64
  have h68 := h z z x
  have h69 := R v61
  have h70 := C h69 (C h69 (T h68 (C h68 h67)))
  have h71 := C h69 (C h59 h0)
  have h72 := T (C (T (T (T (T h53 h52) h51) h15) h25) h13) h21
  have h73 := C h0 h72
  have h74 := T (T h43 h33) (C (T (T h46 h45) h47) (T (T (T (C h26 h72) (C h20 h11)) (C h1 (C h1 h10))) (S h50)))
  have h75 := C h0 h74
  have h76 := T h75 h73
  have h77 := C h76 h0
  have h78 := C h69 (T (T (T h75 h73) h62) (C h77 (T (T h71 h70) h66)))
  have h79 := h (M v61 v60) v60 v2
  have h80 := S h79
  have h81 := C h69 (C h77 h0)
  have h82 := S h68
  have h83 := C h69 (C h69 (T (C h82 h67) h82))
  have h84 := C h69 (T (T (T (C h59 (T (T h65 h83) h81)) h63) h57) h56)
  have h85 := C (T (T (T h65 h83) h81) h84) h55
  have h86 := R v60
  have h87 := T (T (C h86 h74) (C h76 h55)) (C (T h57 h85) h44)
  have h88 := C h86 h87
  have h89 := h v2 v2 x
  have h90 := S h89
  let v91 := M v2 (M v3 x)
  have h92 := R v91
  have h93 := C h86 (C h86 (T (C h90 h92) h90))
  have h94 := h v2 v60 v91
  have h95 := C (T (T (T h78 h71) h70) h66) h74
  have h96 := C (T h95 h56) (T (T h94 h93) h88)
  have h97 := T (T (C (T h95 h73) h44) (C h58 h74)) (C h86 h55)
  T (T (T (T (T (T (T (T (T (T h27 h48) h54) h34) h31) h94) h93) h88) (C (T (T (T (T h75 h73) h62) (C h69 (T (T h84 h79) (C (T h75 h85) (T (T (C h86 h97) (C h86 (C h86 (T h89 (C h89 h92))))) (S h94)))))) (C h69 h97)) (T (T (T (T (T h96 h80) h78) h71) h70) h66))) (C (T (T (C h69 h87) (C h69 (T (T h96 h80) h78))) h63) h0)) h59

