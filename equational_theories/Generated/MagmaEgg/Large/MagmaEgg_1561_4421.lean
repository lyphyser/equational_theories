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
theorem Equation1561_implies_Equation4421 (G: Type _) [Magma G] (h: Equation1561 G) : Equation4421 G := fun x y z =>
  let v0 := M z y
  let v1 := M v0 z
  have h2 := h v1 v1 z
  have h3 := S h2
  let v4 := M z v1
  have h5 := h v4 y x
  let v6 := M x y
  let v7 := M x v6
  let v8 := M y x
  have h9 := h v6 v8 v7
  have h10 := S h9
  have h11 := h v7 x y
  have h12 := h x y x
  have h13 := C h12 h11
  let v14 := M x v7
  have h15 := h v14 v0 v6
  let v16 := M v6 v0
  have h17 := h v16 y z
  have h18 := h v0 y x
  have h19 := S h18
  have h20 := R v16
  have h21 := h v8 v6 v0
  have h22 := h v8 v6 v6
  have h23 := h v6 y x
  have h24 := R (M v6 v6)
  have h25 := h v14 v7 x
  have h26 := C (S h12) (S h11)
  have h27 := T h9 h26
  let v28 := M v7 x
  have h29 := h v28 x v6
  have h30 := S h29
  let v31 := M v6 x
  have h32 := h v31 v7 v6
  have h33 := h v6 v6 x
  let v34 := M v7 v6
  have h35 := R v34
  have h36 := T h13 h10
  have h37 := R v28
  have h38 := h v34 v7 x
  have h39 := R v7
  have h40 := C h39 (T h38 (C h37 (T (T (C h35 h36) (C h35 h33)) (S h32))))
  have h41 := h (M v7 v34) v6 v6
  have h42 := C h39 (T (C h37 (T (T h32 (C h35 (S h33))) (C h35 h27))) (S h38))
  let v43 := M y z
  have h44 := h v43 v0 z
  have h45 := h z y z
  have h46 := R v1
  have h47 := T (C h46 h45) (S h44)
  have h48 := R v14
  let v49 := M v1 z
  have h50 := h v49 x v7
  let v51 := M v0 v6
  have h52 := R v51
  have h53 := R v4
  have h54 := h v51 z v1
  have h55 := R v8
  have h56 := T (T h18 (C h55 (T h54 (C h53 (T (T (T (C h52 (T h50 (C h48 (T (C h47 (T (T (T (T (T (T (T h29 h42) h41) (C h24 (T (T (T (C (T h40 h30) (C h27 h27)) (S h25)) h13) h10))) (C h24 h23)) (S h22)) h21) (C h20 h19))) (S h17))))) (S h15)) h13) h10))))) (S h5)
  let v57 := M v1 v0
  have h58 := h v57 y z
  have h59 := S h58
  have h60 := h v0 z v0
  have h61 := R v57
  let v62 := M z v0
  have h63 := h v62 v1 v0
  have h64 := R v43
  have h65 := C h64 (T h63 (C h61 (S h60)))
  have h66 := h z z v0
  have h67 := R v49
  have h68 := C h67 (T (T (T (T (S h66) h45) h65) h59) (C h46 h56))
  have h69 := h v62 v1 z
  have h70 := S h45
  have h71 := C h46 h70
  have h72 := T h44 h71
  have h73 := T (T h5 (C h55 (T (C h53 (T (T (T h9 h26) h15) (C h52 (T (C h48 (T h17 (C h72 (T (T (T (T (T (T (T (C h20 h18) (S h21)) h22) (C h24 (S h23))) (C h24 (T (T (T h9 h26) h25) (C (T h29 h42) (C h36 h36))))) (S h41)) h40) h30)))) (S h50))))) (S h54)))) h19
  have h74 := R z
  have h75 := h y z v0
  have h76 := S h75
  let v77 := M y v1
  have h78 := R v77
  have h79 := S h69
  have h80 := T (C h61 h60) (S h63)
  have h81 := C h67 (T (T (T (T (C h46 h73) h58) (C h64 h80)) h70) h66)
  have h82 := C (T (T h2 h81) h79) h78
  have h83 := S (h (M v1 v77) v0 v1)
  have h84 := R (M v0 v1)
  have h85 := C h84 (T (C (R y) (T (T h45 h65) h59)) (C (T h75 (C (T (T h69 h68) h3) h78)) h61))
  have h86 := C h84 h47
  have h87 := h v49 x v6
  have h88 := h v31 v7 v0
  have h89 := h v0 v6 x
  let v90 := M v7 v0
  have h91 := R v90
  have h92 := h v90 y z
  have h93 := C h84 (T (T (T (C h46 (T h58 (C (T (T (T h44 h71) h87) (C h39 (T (C h47 (T h88 (C h91 (S h89)))) (S h92)))) h80))) (S (h (M v7 v90) v0 z))) (C h39 (T h92 (C h72 (T (C h91 h89) (S h88)))))) (S h87))
  have h94 := h v1 v0 v1
  have h95 := h v62 x y
  have h96 := h v8 v6 v1
  have h97 := h v1 y x
  let v98 := M v6 v1
  have h99 := R v98
  have h100 := R v62
  have h101 := h v98 z v0
  have h102 := R v6
  T (T (T (T (T (C (T (h x v0 z) (C (T (T (T (T (T (T h94 h93) h86) h85) h83) h82) h76) (C (R x) (T (T (T (T (T (T (T (T (T h69 h68) h3) h94) h93) h86) h85) h83) h82) h76)))) (T (h v6 v0 z) (C (T (T (T h2 h81) h79) (C h74 h56)) (T (C h102 (T h95 (C h102 (T (C h100 (T h96 (C h99 (S h97)))) (S h101))))) (C h102 (T (T (T (T (T (T (T (T (T (T (T (C h102 (T h101 (C h100 (T (C h99 h97) (S h96))))) (S h95)) h69) h68) h3) h94) h93) h86) h85) h83) h82) h76)))))) (S (h (M z v4) y v6))) (C h74 h73)) h69) h68) h3

