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
theorem Equation2917_implies_Equation2180 (G: Type _) [Magma G] (h: Equation2917 G) : Equation2180 G := fun x y z =>
  let v0 := M x z
  let v1 := M y z
  let v2 := M v1 y
  let v3 := M v2 v0
  have h4 := h v3 y v3
  have h5 := S h4
  have h6 := R v3
  let v7 := M y (M v3 y)
  have h8 := h (M v7 v3) v3 x
  have h9 := S h8
  have h10 := R x
  have h11 := h v3 v3 v3
  have h12 := C h6 (S h11)
  have h13 := C (T (C h12 h10) (C (C h6 h4) h10)) h10
  have h14 := C h6 h11
  have h15 := C h14 h10
  let v16 := M z (M v3 z)
  have h17 := h v16 x x
  have h18 := S h17
  have h19 := h (M v16 x) x x
  have h20 := h v3 z x
  have h21 := h v3 v0 x
  let v22 := M v0 (M v3 v0)
  have h23 := h (M v22 x) x x
  have h24 := C (C (C h10 (T (T h23 (C (C (T (C h10 (S h21)) (C h10 h20)) h10) h10)) (S h19))) h10) h10
  have h25 := h v22 x x
  have h26 := h v22 y x
  have h27 := S h26
  have h28 := h (M v22 y) y x
  have h29 := h v3 v0 y
  have h30 := R y
  have h31 := h v3 v2 y
  have h32 := C h30 (S h31)
  have h33 := h (M (M v2 (M v3 v2)) y) y x
  have h34 := C (C (C h30 (T (T h33 (C (C (T h32 (C h30 h29)) h10) h10)) (S h28))) h10) h10
  have h35 := S h33
  have h36 := C h30 h31
  have h37 := h v3 y y
  have h38 := h (M v7 y) y x
  have h39 := C (C (C h30 (T (T h38 (C (C (T (C h30 (S h37)) h36) h10) h10)) h35)) h10) h10
  have h40 := h v7 y x
  have h41 := h v7 v3 v3
  have h42 := S h41
  let v43 := M (M v3 (M v3 v3)) v3
  have h44 := h v43 v3 x
  have h45 := h v43 v3 v3
  have h46 := h v0 v3 v2
  have h47 := R v2
  have h48 := C h47 (S h46)
  let v49 := M (M v3 (M v0 v3)) v2
  have h50 := h v49 v2 v3
  have h51 := C (C (C h6 (T (T (T (T (C (T h50 (C (T (C h48 h6) h14) h6)) h6) (S h45)) h44) h13) h9)) h6) h6
  have h52 := h v49 v3 v3
  have h53 := h v49 v0 v3
  have h54 := R v0
  have h55 := C h47 h46
  have h56 := h (M v16 v0) v0 x
  have h57 := h v3 z v0
  have h58 := h v2 v0 x
  have h59 := h v2 z v0
  have h60 := T (C h54 (S h59)) (C h54 (T (T (T h58 (C (C (C h54 h57) h10) h10)) (S h56)) (C (T (T (T (T (T (T (T (T (T h17 (C (C (C h10 (T (T h19 (C (C (T (C h10 (S h20)) (C h10 h21)) h10) h10)) (S h23))) h10) h10)) (S h25)) h26) (C (C (C h30 (T (T h28 (C (C (T (C h30 (S h29)) h36) h10) h10)) h35)) h10) h10)) (C (C (C h30 (T (T h33 (C (C (T h32 (C h30 h37)) h10) h10)) (S h38))) h10) h10)) (S h40)) h41) (C (C (C h6 (T (T (T (T h8 (C (T (C (C h6 h5) h10) h15) h10)) (S h44)) h45) (C (T (C (T h12 (C h55 h6)) h6) (S h50)) h6))) h6) h6)) (S h52)) h54)))
  let v61 := M (M z (M v2 z)) v0
  have h62 := h v61 v0 v3
  have h63 := C h54 h59
  have h64 := h z v2 x
  have h65 := C h10 (S h64)
  let v66 := M (M v2 (M z v2)) x
  have h67 := h v66 x v3
  have h68 := S h67
  have h69 := C h10 h64
  have h70 := C (C h69 h6) h6
  have h71 := C (C h65 h6) h6
  have h72 := h v66 x x
  have h73 := S h72
  have h74 := C h69 h10
  have h75 := h z v1 y
  have h76 := S h75
  have h77 := h (M (M v1 (M z v1)) y) y y
  have h78 := h y y v1
  have h79 := R v1
  have h80 := C h79 (S h78)
  let v81 := M (M y (M y y)) v1
  have h82 := h v81 v1 y
  have h83 := h v81 v1 x
  have h84 := C h79 h78
  have h85 := C (T (C (C h10 (T (T (T (T (C (C h84 h10) h10) (S h83)) h82) (C (T (T (C h80 h30) (C (C (C h30 h75) h30) h30)) (S h77)) h30)) h76)) h10) h74) h10
  have h86 := h (M v2 x) x x
  have h87 := h x v2 v2
  let v88 := M v2 (M x v2)
  let v89 := M v88 v2
  have h90 := C h65 h10
  have h91 := h x v3 v0
  let v92 := M v3 (M x v3)
  have h93 := h (M v92 v0) v0 x
  let v94 := M x (M x x)
  have h95 := h x v0 y
  let v96 := M v0 (M x v0)
  have h97 := h (M v96 y) y x
  let v98 := M y (M x y)
  have h99 := h x v0 v3
  have h100 := C h6 (S h99)
  have h101 := C h6 h99
  have h102 := h v49 v2 x
  have h103 := h x v2 v3
  let v104 := M v88 v3
  let v105 := M v96 v3
  have h106 := h x x v3
  T (T h106 (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (h (M v94 v3) v3 x) (C (C (T (C h6 (S h106)) h101) h10) h10)) (S (h v105 v3 x))) (h v105 v3 y)) (C (C (T h100 (C h6 h103)) h30) h30)) (S (h v104 v3 y))) (h v104 v3 x)) (C (T (T (C (T (C h6 (S h103)) h101) h10) (C (T h100 (C h55 h10)) h10)) (S h102)) h10)) (C (T (T h102 (C (T (C h48 h10) h101) h10)) (C (T h100 (C h6 (h x y v3))) h10)) h10)) (S (h (M v98 v3) v3 x))) (C (T (T (T (T (T (T (T (T (T (h v98 x x) (C (C (C h10 (T (T (h (M v98 x) x x) (C (T (C (C h10 (S (h x y x))) h10) (C (C h10 (h x v3 x)) h10)) h10)) (S (h (M v92 x) x x)))) h10) h10)) (S (h v92 x x))) (h v92 y x)) (C (C (C h30 (T (T (h (M v92 y) y x) (C (C (T (C h30 (S (h x v3 y))) (C h30 h95)) h10) h10)) (S h97))) h10) h10)) (C (C (C h30 (T (T h97 (C (C (T (C h30 (S h95)) (C h30 (h x x y))) h10) h10)) (S (h (M v94 y) y x)))) h10) h10)) (S (h v94 y x))) (h v94 v2 v3)) (C (C (C h47 (T (T (T (T (T (h (M v94 v2) v2 x) (C (T (T (C (T (T (T (T (T (C h47 (S (h x x v2))) h86) h85) h73) h67) h71) h10) (C (T (T (T h70 h68) h72) (C (T h90 (C h54 h91)) h10)) h10)) (S h93)) h10)) (C (T (T h93 (C (T (T (T (C (T (C h54 (S h91)) h74) h10) h73) h67) h71) h10)) (C (T (T (T (T (T h70 h68) h72) (C (T h90 (C (C h10 (T (T (T (T h75 (C (T (T h77 (C (C (C h30 h76) h30) h30)) (C h84 h30)) h30)) (S h82)) h83) (C (C h80 h10) h10))) h10)) h10)) (S h86)) (C h47 h87)) h10)) h10)) (S (h v89 v2 x))) (h v89 v2 v2)) (C (T (T (T (T (T (C (T (T (T (T (T (C h47 (S h87)) h86) h85) h73) h67) h71) h47) (C (T (T (T (T h70 h68) (h v66 x v2)) (C (T (C h65 h47) h63) h47)) (C h60 h47)) h47)) (S (h v49 v0 v2))) h53) (C (C (T (C h54 (T (T (T (C (T (T (T (T (T (T (T (T (T h52 h51) h42) h40) h39) h34) h27) h25) h24) h18) h54) h56) (C (C (C h54 (S h57)) h10) h10)) (S h58))) h63) h6) h6)) (S h62)) h47))) h6) h6)) (S (h v61 v2 v3))) h6)) (C (T (T (T (T (T (T (T (T (T (T (T (T h62 (C (C h60 h6) h6)) (S h53)) h52) h51) h42) h40) h39) h34) h27) h25) h24) h18) h6)) (h (M v16 v3) v3 x)) (C (T (C (C h6 (S (h v3 z v3))) h10) h15) h10)) h13) h9) h6)) h5

