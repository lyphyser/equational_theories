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
theorem Equation3404_implies_Equation3620 (G: Type _) [Magma G] (h: Equation3404 G) : Equation3620 G := fun x y z =>
  let v0 := M z y
  have h1 := h v0 x y
  have h2 := S h1
  have h3 := h y v0 z
  have h4 := S h3
  have h5 := h v0 v0 y
  have h6 := R v0
  have h7 := h v0 z v0
  let v8 := M v0 x
  have h9 := h v0 z v8
  have h10 := S h9
  have h11 := h y v8 z
  have h12 := h y v8 x
  have h13 := R v8
  have h14 := C h13 (T (S h12) h11)
  let v15 := M x y
  have h16 := h v15 x v8
  have h17 := R y
  let v18 := M z v8
  have h19 := h y (M v15 x) v18
  have h20 := R (M v18 y)
  have h21 := S h16
  have h22 := S h11
  have h23 := C h13 (T h22 h12)
  have h24 := T (T h9 h23) h21
  have h25 := R v18
  let v26 := M v0 z
  have h27 := h y v26 v18
  have h28 := h y v26 z
  have h29 := h v26 v0 y
  have h30 := h z y v0
  have h31 := h z y v18
  have h32 := C h17 (S h31)
  let v33 := M v18 z
  have h34 := h v33 v18 y
  have h35 := R z
  have h36 := h v8 v33 z
  have h37 := h v18 z x
  have h38 := S h37
  have h39 := h v8 x z
  have h40 := R x
  have h41 := C h40 h39
  have h42 := C h13 (T h41 h38)
  have h43 := h x x v8
  have h44 := h x x v15
  have h45 := S h44
  have h46 := h v0 z y
  have h47 := S h46
  have h48 := C h17 (T (T (T h43 h42) h36) (C h35 (T h34 h32)))
  have h49 := C h40 (T (T (T (T h48 h47) h9) h23) h21)
  have h50 := h x y x
  have h51 := R v15
  have h52 := C h51 (T h50 h49)
  have h53 := C h35 (T (T (T (T (T (T (T (T (T (T (T h52 h45) h43) h42) h36) (C h35 (T (T (T h34 h32) (C h17 h30)) (S h29)))) (S h28)) h27) (C h25 (C h24 h20))) (S h19)) (C h17 (T (T (T (T h16 h14) h10) h7) (C h6 h4)))) (S h5))
  have h54 := S h50
  have h55 := S h43
  have h56 := S h39
  have h57 := C h40 h56
  have h58 := C h13 (T h37 h57)
  have h59 := S h36
  have h60 := S h34
  have h61 := C h17 h31
  have h62 := C h17 (T (T (T (C h35 (T h61 h60)) h59) h58) h55)
  have h63 := C h51 (T (C h40 (T (T (T (T h16 h14) h10) h46) h62)) h54)
  have h64 := T h44 h63
  have h65 := C h35 h64
  have h66 := h x z x
  have h67 := C h17 (T h66 (C h40 (T (T h65 h53) h4)))
  let v68 := M x z
  have h69 := S h66
  have h70 := T h52 h45
  have h71 := C h35 h70
  have h72 := C h35 (T (T (T (T (T (T (T (T (T (T (T h5 (C h17 (T (T (T (T (C h6 h3) (S h7)) h9) h23) h21))) h19) (C h25 (C (T (T h16 h14) h10) h20))) (S h27)) h28) (C h35 (T (T (T h29 (C h17 (S h30))) h61) h60))) h59) h58) h55) h44) h63)
  have h73 := C h40 (T (T h3 h72) h71)
  have h74 := h z y x
  have h75 := S h74
  have h76 := C h40 (C h17 h75)
  let v77 := M y v68
  have h78 := h v77 y x
  have h79 := T (T (T h1 (h y (M x (M y v0)) v18)) (C h25 (C (T h73 h69) h20))) (S (h y v68 v18))
  have h80 := C h79 h17
  have h81 := R v26
  have h82 := T h67 h2
  have h83 := C h82 h17
  have h84 := S h78
  have h85 := C h17 h74
  have h86 := h z x y
  have h87 := h y z v8
  have h88 := h z y v15
  have h89 := C h17 (S h88)
  have h90 := h (M v15 z) v15 y
  have h91 := S h90
  have h92 := C h17 h88
  have h93 := h x z v0
  have h94 := h v8 v0 z
  have h95 := h v8 v0 x
  have h96 := h x x v0
  have h97 := h v18 z z
  have h98 := S h97
  have h99 := h v8 z z
  have h100 := C h35 h99
  have h101 := h v77 z x
  have h102 := C h35 (T (T (C h40 (C h35 h74)) (S h101)) (C h82 h35))
  have h103 := h v0 x z
  have h104 := h v8 x v8
  have h105 := h v8 v0 y
  have h106 := h x y v0
  have h107 := S h94
  T (T (T (T (T h50 (C h40 (T h48 h47))) (h x v26 z)) (C h35 (C h81 (T (T (T (T (T (T (T (T (T (T h86 (C h17 (T (C h40 (T (T (T h87 (C h13 (T (T (T (T (T (C h35 (T (T (T (T (T (T h80 h78) h76) (C h40 (T h92 h91))) (C h40 (T (T (T (T h90 h89) h3) h72) h71))) h69) h93)) h107) h95) (C h40 (S h96))) (C h40 h64)) (C h40 (T (T (T h52 h45) h43) (C h13 (T (T (T (T (T h41 h38) h97) (C h35 (S h99))) (C h35 (T (T (C h79 h35) h101) (C h40 (C h35 h75))))) (S h103)))))))) (S h104)) h39)) h38))) (C h17 (T (h v18 z v0) (C h6 h107)))) (C h17 (C h6 (T h105 (C h17 (S h106)))))) (S (h v15 v0 y))) (C h51 (T (T (h z y z) (C h35 (T (T (T (T (h y (M z z) v18) (C h25 (C (T (T (h z z v15) (C h51 (T (T (T (C h35 (T (h v15 z y) (C h17 (T (T (T (C h35 (T (C h17 h106) (S h105))) h22) (C h17 (T (T (T (T (T h103 h102) h100) h98) h37) (C h40 (T (T (T h56 h104) (C h13 (T (T (T (T (T (C h40 (T (T (T (C h13 (T (T (T (T (T h103 h102) h100) h98) h37) h57)) h55) h44) h63)) (C h40 h70)) (C h40 h96)) (S h95)) h94) (C h35 (T (T (T (T (T (T (S h93) h66) (C h40 (T (T (T (T h65 h53) h4) h92) h91))) (C h40 (T h90 h89))) (C h40 h85)) h84) h83))))) (S h87)))))) (S h86))))) (S (h x y z))) h50) h49))) h45) h20))) (S (h y (M x x) v18))) h48) h47))) (C h35 h24)))) (S (h x z v15))) h66) (C h40 (T (T (T h65 h53) h4) h85))) h84) h83)))) (C h35 (C h81 (T (T (T (T h80 h78) h76) h73) h69)))) (C h35 (T (T (T (T (h v26 v68 x) (C h40 (C (R v68) (T (C h40 (T h46 h62)) h54)))) (S (h y v68 x))) h67) h2))

