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
theorem Equation3620_implies_Equation3997 (G: Type _) [Magma G] (h: Equation3620 G) : Equation3997 G := fun x y z =>
  let v0 := M x z
  let v1 := M z v0
  let v2 := M v1 y
  let v3 := M v2 y
  let v4 := M v3 v1
  have h5 := R y
  have h6 := R v2
  have h7 := R v1
  have h8 := R x
  let v9 := M x y
  have h10 := h x y v2
  let v11 := M v3 x
  have h12 := R v0
  let v13 := M v2 v0
  let v14 := M v9 v0
  have h15 := R v9
  have h16 := h v9 v0 v0
  have h17 := S h16
  let v18 := M v0 v0
  have h19 := S (h v0 (M v18 v9) v0)
  have h20 := C h16 h12
  have h21 := h x y v1
  let v22 := M v2 x
  let v23 := M v9 v1
  have h24 := h v1 y x
  have h25 := h x z z
  let v26 := M z z
  have h27 := R z
  let v28 := M v0 z
  have h29 := h v28 x z
  let v30 := M v28 x
  have h31 := h x z v0
  have h32 := h x z v1
  have h33 := S h32
  let v34 := M v1 z
  let v35 := M v34 x
  have h36 := R v35
  have h37 := h z v0 x
  have h38 := C h8 (T (C (S h37) h36) h33)
  let v39 := M x v0
  have h40 := h v35 (M v39 z) x
  have h41 := h v39 z x
  have h42 := S h31
  have h43 := h v0 v30 v0
  have h44 := C h8 (T (T (C h12 (C h31 h12)) (S h43)) h42)
  have h45 := h v18 z x
  have h46 := h z v0 v0
  have h47 := S h46
  have h48 := h v0 (M v18 z) v0
  let v49 := M v1 v0
  have h50 := h v49 z x
  have h51 := C h36 (T (T (T h50 (C h8 (T (T (C h12 (C h46 h12)) (S h48)) h47))) (C h8 (T h46 (C h12 (T h45 h44))))) (S h41))
  have h52 := h v35 (M v49 z) v1
  have h53 := S h52
  have h54 := h z v0 v1
  have h55 := C h7 (T h32 (C h54 h36))
  have h56 := h z v0 y
  have h57 := S h56
  let v58 := M (M y v0) z
  have h59 := h y v58 y
  have h60 := T (T h56 h59) (C h5 (C h57 h5))
  have h61 := T (T h31 h43) (C h12 (C h42 h12))
  let v62 := M v0 v1
  have h63 := h x z y
  let v64 := M y z
  let v65 := M v0 y
  let v66 := M v65 v1
  have h67 := h v1 y v0
  have h68 := h v9 y z
  let v69 := M v9 y
  let v70 := M v2 z
  have h71 := h v2 z x
  have h72 := S h71
  have h73 := h x z v2
  have h74 := S h73
  have h75 := C h74 h6
  have h76 := C h8 h75
  let v77 := M v70 x
  let v78 := M (M v2 v77) v2
  have h79 := h x v78 v2
  have h80 := h v2 v77 v2
  let v81 := M v0 x
  have h82 := h v1 z x
  have h83 := C h7 (T (C (S h54) h36) h33)
  have h84 := S h45
  have h85 := C h8 h61
  have h86 := C h36 (T (T (T h41 (C h8 (T (C h12 (T h85 h84)) h47))) (C h8 (T (T h46 h48) (C h12 (C h47 h12))))) (S h50))
  have h87 := S h40
  have h88 := C h8 (T h32 (C h37 h36))
  have h89 := h x z v9
  let v90 := M v9 z
  let v91 := M v90 x
  have h92 := h v91 y x
  have h93 := h v90 x y
  have h94 := S h93
  have h95 := h y (M (M y x) v90) y
  have h96 := S h67
  have h97 := h v0 v66 v0
  have h98 := h v13 z x
  have h99 := h v13 z v0
  have h100 := C h8 (C h73 h6)
  have h101 := h v0 z y
  let v102 := M z v35
  have h103 := h x y v0
  let v104 := M v65 x
  let v105 := M y v104
  T (T (T (T (T (T h103 (h v0 v104 y)) (h y (M v105 v0) x)) (C h8 (C (T (T (T (T (C h8 (T (T (T (T (h v105 v0 z) (C h27 (T (C h7 (T (T (h y v104 v0) (C h12 (C (S h103) h5))) (C (T (T (T (T (T h32 (h v1 v35 z)) (h z (M v102 v1) v2)) (C h6 (C (C h6 (T (T (h v102 v1 v1) (C h7 (C (R (M v1 v1)) (T (T (T (T (h z v35 v1) (C h7 (C h33 h27))) (C h7 (T (T (T (T h101 (h y (M v64 v0) y)) (C h5 (T (T (C (S h101) h5) (h v28 y v1)) (C h60 (T (C h6 (C h73 h27)) (S (h z v77 v2))))))) (S (h (M z v77) v2 y))) (C (T (T (T (T (h z v77 x) (C h8 (T (C (T (T (T (C h8 (C (T h71 h100) h8)) (S (h x v78 x))) h76) h72) h27) (C (T (T (T (T (T h71 h100) h79) (C h6 (C (T (S h80) h74) h8))) (h v2 v81 x)) (C h8 (T (T (T (T (T (T (T (T (T (C (T (S (h x z x)) h73) h6) h75) (h v0 v2 x)) (C h8 (T (C (T (T (C h8 (T (T h67 h97) (C h12 (C h96 h12)))) (S h98)) h99) h12) (C (T (T (T (T (T (S h99) h98) (C h8 (T (T (C h12 (C h67 h12)) (S h97)) h96))) (h x v2 y)) (C h5 (T (C (T (T (C h5 (C h56 h5)) (S h59)) h57) h8) (C h56 h8)))) (S (h x v58 y))) h12)))) (S (h v0 v58 x))) (h v0 v58 y)) (C h5 (T (T (T (T (T (T (T (C h57 h12) h55) h53) h51) h40) h38) h85) h84))) (C h5 (T (T (T (T h45 h44) (C h8 h89)) (S h92)) (C h93 h5)))) (S h95)) h94))) h27)))) (S (h z v91 x))) (h z v91 v1)) (C h7 (C (T (T (T (T (T (C h7 (T (T (T (T (T h93 h95) (C h5 (T (T (T (T (C h94 h5) h92) (C h8 (S h89))) h85) h84))) (C h5 (T (T (T (T (T (T (T (T (T (T h45 h44) h88) h87) h86) h52) h83) (h v1 v0 x)) (C h8 (T (C (T (T (T (T h88 h87) h86) h52) h83) h7) (C (T (T (T (T (T (T (T h55 h53) h51) h40) h38) (h x v0 z)) (C h27 (C (h z v0 z) h8))) (S (h x v34 z))) h7)))) (S (h v1 v34 x))) (C h60 (R v34))))) (S (h v34 v2 y))) (C (T (T (T (T h82 (h x v62 x)) (C h8 (C (S h82) h8))) (h x v35 v1)) (C h7 (C h33 h8))) h6))) (S (h v2 v81 v1))) (C h6 (C (T h73 h80) h8))) (S h79)) h76) h72) h27))) h6)))) (S (h v2 (M v70 z) v1))) (S (h z z v2)))))) (S (h v26 v1 v1)))) h27))) (S (h z (M v26 v1) v2))) (S (h v1 z z))) (R v69)))) (S (h v69 z v1))))) (C h27 (C h68 h27))) (S (h z (M (M z y) v9) z))) (S h68))) (S (h y y x))) (h y y v2)) (h v2 (M v3 y) x)) (C h8 (C (T (C h8 (C (T (T (T (T (T (h v2 y v1) (h v1 (M v2 v2) v0)) (C h12 (T (C (T (C h12 (C h67 h6)) (S (h v2 v66 v0))) h7) (C (T (T (C h6 (T (T (T (h v65 v1 v0) (C h12 (T (T (T (h v62 v65 y) (C h5 (T (T (T (C (T (T (C h5 (C h63 h5)) (S (h y (M v64 x) y))) (S h63)) (R v62)) (C h12 (C h61 h7))) (S (h v1 v18 v0))) (C h60 (R v18))))) (S (h v18 v2 y))) (C (T (T (T (h v0 v0 v9) (h v9 (M v14 v0) v0)) (C h12 (C (T (T (C h12 h20) h19) h17) h15))) (C h12 (T (T (h v14 v9 v2) (C h6 (C (R (M v2 v9)) (T (T (T h16 (C h12 (C (T (T (T (T (T (T (h v0 v0 z) (C h27 (T (T (T (T (T (T (T h55 h53) h51) h40) h38) (C h8 h31)) (S (h v30 z x))) (C h29 h27)))) (S (h z (M (M z x) v28) z))) (S h29)) (h v28 x v2)) (h v2 (M v22 v28) v0)) (C h12 (C (T (T (C h12 (T (T (T (h v22 v28 z) (C h27 (T (T (T (T (T (T (C (T (T (C h27 (C h25 h27)) (S (h z (M v26 x) z))) (S h25)) (R v22)) (h v0 v22 x)) (C h8 (C (T (T (C h8 (C h24 h8)) (S (h x v23 x))) (S h24)) h12))) (C h8 (C h24 h12))) (S (h v0 v23 x))) (h v0 v23 v1)) (C h7 (C (T (T (C h7 (C h21 h7)) (S (h v1 v22 v1))) (S h21)) h12))))) (S (h v14 v0 z))) h20)) h19) h17) h6))) h15))) (S (h v9 (M v14 v2) v0))) (S (h v2 v0 v9)))))) (S (h v13 v9 v2))))) h6)))) (S (h v2 (M v13 v9) v0))) (S (h v9 v0 v2)))) (C h6 (C h10 h12))) (S (h v0 v11 v2))) h7)))) (S (h v1 v11 v0))) (h v1 v11 x)) (C h8 (C (T (T (T (T (h x v11 v2) (C h6 (C (S h10) h8))) (h v2 (M v9 x) x)) (C h8 (C (S (h x y x)) h6))) (S (h v2 y x))) h7))) h5)) (S (h y v4 x))) h6))) h5))) (S (h y (M (M y v4) v2) x))) (S (h v2 v4 y))) (S (h v1 y v2))

