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
theorem Equation711_implies_Equation2399 (G: Type _) [Magma G] (h: Equation711 G) : Equation2399 G := fun x y z =>
  have h0 := R y
  let v1 := M z x
  have h2 := R v1
  let v3 := M z v1
  have h4 := h z v3 v1
  have h5 := h v1 v1 x
  have h6 := S h5
  let v7 := M v1 (M (M v1 x) x)
  have h8 := R v7
  have h9 := R v3
  have h10 := h v1 v3 v7
  let v11 := M v3 (M (M v3 x) x)
  have h12 := h v3 y v11
  have h13 := S h12
  have h14 := R v11
  have h15 := h v3 v3 x
  have h16 := C h0 (C h0 (T h15 (C h15 h14)))
  have h17 := T h16 h13
  have h18 := C (T (C h17 (T h10 (C h9 (C h9 (T (C h6 h8) h6))))) (S h4)) h2
  have h19 := C h0 h18
  have h20 := S h15
  have h21 := C h0 (C h0 (T (C h20 h14) h20))
  have h22 := T h12 h21
  have h23 := C (C h22 h2) h2
  have h24 := C h0 h23
  have h25 := T h24 h19
  have h26 := C h25 h0
  let v27 := M y v3
  let v28 := M v27 y
  have h29 := h (M y (M (M v3 v1) v1)) v28 y
  have h30 := S h29
  let v31 := M y (M (M y x) x)
  have h32 := h y v28 v31
  have h33 := S h32
  have h34 := R v31
  have h35 := h y y x
  have h36 := T h35 (C h35 h34)
  have h37 := R v28
  have h38 := C h37 (C h37 h36)
  have h39 := C h37 (C h26 h0)
  have h40 := C (C h17 h2) h2
  have h41 := C h0 h40
  have h42 := C (T h4 (C h22 (T (C h9 (C h9 (T h5 (C h5 h8)))) (S h10)))) h2
  have h43 := C h0 h42
  have h44 := T h43 h41
  have h45 := C h44 h0
  have h46 := C h37 (T (T (T h43 h41) h29) (C h45 (T (T h39 h38) h33)))
  let v47 := M v28 v27
  have h48 := h v47 v27 v3
  have h49 := S h48
  have h50 := C h37 (C h45 h0)
  have h51 := S h35
  have h52 := C h37 (C h37 (T (C h51 h34) h51))
  have h53 := C h37 (T (T (T (C h26 (T (T h32 h52) h50)) h30) h24) h19)
  have h54 := C (T (T (T h32 h52) h50) h53) h18
  have h55 := C (T h24 h54) h9
  have h56 := C h44 h18
  have h57 := R v27
  have h58 := h v3 v27 v1
  have h59 := T h58 (C h57 (T (T (C h57 h23) h56) h55))
  have h60 := C (T (T (T h46 h39) h38) h33) h42
  have h61 := C h37 (T (T (C (T h60 h19) h59) h49) h46)
  have h62 := C h37 (T (T (C h57 h42) h56) h55)
  have h63 := h (M v28 (M v27 v3)) v3 v3
  have h64 := S h63
  have h65 := C h25 h42
  have h66 := C (T h60 h41) h9
  have h67 := T (C h57 (T (T h66 h65) (C h57 h40))) (S h58)
  have h68 := C h37 (T (T h66 h65) (C h57 h18))
  have h69 := C h37 (T (T h53 h48) (C (T h43 h54) h67))
  have h70 := C (T (T (T (T h43 h41) h29) h69) h68) h67
  have h71 := C (T h48 h70) h9
  have h72 := C h9 (C h17 (T (T h43 h54) h71))
  have h73 := C (T (T (T (T h72 h64) h62) h61) h30) h0
  let v74 := M y v27
  let v75 := M v3 (M v74 v27)
  have h76 := h v75 x x
  let v77 := M x (M (M x x) x)
  have h78 := h x z v77
  have h79 := S h78
  have h80 := R v77
  have h81 := h x x x
  have h82 := R z
  have h83 := C h82 (C h82 (T h81 (C h81 h80)))
  have h84 := h v74 y v1
  have h85 := C (T (T (T (T h62 h61) h30) h24) h19) h59
  have h86 := C (T h85 h49) h9
  have h87 := T h72 h64
  have h88 := C h87 h9
  have h89 := C h88 h9
  have h90 := C h9 (C h22 (T (T h86 h60) h19))
  have h91 := C (T h63 h90) h9
  have h92 := C h91 h9
  have h93 := h v75 v28 v3
  have h94 := h v47 v28 v3
  have h95 := T h83 h79
  have h96 := R v75
  have h97 := h v75 y y
  have h98 := h y v3 v27
  have h99 := C (T (C (T (T (T h16 h13) h83) h79) (T h98 (C h95 (T h97 (C (T (T (T (T (T (T (T h32 h52) h50) h53) h48) h70) h91) (C h96 h95)) (T (T (T (T (T (T (C h0 (T (T (T (T (T (T (T (T (T (T (C (T h73 h26) (T (T (T (T (T (T h32 h52) h50) h53) h94) (C h37 (T (T (T (T h61 h30) h24) h54) h71))) (C h37 h92))) (S h93)) h72) h64) h62) h61) h30) h24) h54) h71) h92)) (C h0 (T (T h89 h86) h60))) (S h84)) h16) h13) h83) h79)))))) (S h76)) h0
  have h100 := S h81
  have h101 := C h82 (C h82 (T (C h100 h80) h100))
  have h102 := T h78 h101
  T (T (T (T (T (T (T (T h78 h101) h12) h21) (h v74 v27 y)) (C (T (T (T (T (T (T (T (T h43 h41) h29) h69) h68) h63) h90) h76) (C (T (T (T h78 h101) h12) h21) (T (C h102 (T (C (T (T (T (T (T (T (T (C h96 h102) h88) h85) h49) h46) h39) h38) h33) (T (T (T (T (T (T h78 h101) h12) h21) h84) (C h0 (T (T h54 h71) h92))) (C h0 (T (T (T (T (T (T (T (T (T (T h89 h86) h60) h41) h29) h69) h68) h63) h90) h93) (C (T h45 (C (T (T (T (T h29 h69) h68) h63) h90) h0)) (T (T (T (T (T (T (C h37 h89) (C h37 (T (T (T (T h86 h60) h41) h29) h69))) (S h94)) h46) h39) h38) h33)))))) (S h97))) (S h98)))) (T (T (T (T (T (C (T (T (T (T (T (T h43 h41) h29) h69) h68) h63) h90) (T (T h99 h73) h26)) (C h87 h37)) (C (T (T h62 h61) h30) h37)) (C h25 h37)) (C h57 (C h57 h36))) (S (h y v27 v31))))) h99) h73) h26

