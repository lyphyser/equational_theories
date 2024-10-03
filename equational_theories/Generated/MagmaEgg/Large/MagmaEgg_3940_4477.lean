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
theorem Equation3940_implies_Equation4477 (G: Type _) [Magma G] (h: Equation3940 G) : Equation4477 G := fun x y z =>
  let v0 := M x z
  have h1 := h v0 z v0
  have h2 := S h1
  have h3 := R v0
  let v4 := M v0 z
  let v5 := M v0 v4
  have h6 := h v5 v0 v0
  let v7 := M v0 v0
  have h8 := R v7
  have h9 := h v0 z x
  have h10 := h v0 x v7
  have h11 := R x
  let v12 := M y y
  let v13 := M x v12
  have h14 := h x z v13
  let v15 := M v13 z
  have h16 := h (M x v15) v12 x
  have h17 := R v12
  have h18 := h x v15 v0
  have h19 := S h18
  have h20 := h v0 v15 x
  have h21 := h v13 z x
  have h22 := h x v12 v4
  let v23 := M v4 v12
  let v24 := M x v23
  have h25 := h v24 z v0
  have h26 := R z
  have h27 := h x v23 v4
  have h28 := S h27
  have h29 := R v4
  have h30 := h v4 v12 y
  have h31 := R y
  let v32 := M y v12
  have h33 := R v32
  have h34 := h v0 z v12
  have h35 := S h34
  have h36 := h y y y
  have h37 := S h36
  let v38 := M v12 z
  let v39 := M v0 v38
  have h40 := R v39
  have h41 := h v39 y v32
  have h42 := h v0 v38 v12
  have h43 := S h42
  let v44 := M v0 (M v12 v38)
  have h45 := h v44 y y
  have h46 := h v44 y v32
  have h47 := R v44
  have h48 := h v39 v12 y
  have h49 := C (C h11 (C h29 (T (T (T h34 h48) (C (T (T (T (T (T (C (T h42 (C h47 h36)) h33) (S h46)) h45) (C h43 h31)) h41) (C (T (C h40 h37) h35) h33)) h31)) (S h30)))) h29
  have h50 := h x v4 v4
  have h51 := T (T h50 h49) h28
  let v52 := M z z
  let v53 := M x v52
  let v54 := M x v4
  have h55 := h v54 z v53
  have h56 := R v53
  have h57 := h x z z
  have h58 := R v54
  have h59 := h x z v0
  have h60 := h v0 v52 x
  let v61 := M v0 v52
  have h62 := R v61
  have h63 := h x z v4
  have h64 := S h63
  have h65 := h v0 z z
  let v66 := M v4 z
  let v67 := M x v66
  have h68 := R v67
  have h69 := h v67 z v61
  have h70 := h v67 z v0
  have h71 := h x v0 v0
  let v72 := M x v0
  have h73 := R v72
  have h74 := S h59
  have h75 := h x z x
  have h76 := h v54 x v72
  have h77 := S h50
  have h78 := S h48
  have h79 := C (T (T (T (T (T (C (T h34 (C h40 h36)) h33) (S h41)) (C h42 h31)) (S h45)) h46) (C (T (C h47 h37) h43) h33)) h31
  have h80 := C (C h11 (C h29 (T (T (T h30 h79) h78) h35))) h29
  have h81 := h x v23 v0
  have h82 := S h81
  let v83 := M x (M v0 v23)
  have h84 := h v83 v0 v54
  have h85 := R v83
  have h86 := h v24 v4 x
  have h87 := h v54 v4 v67
  have h88 := h v0 v66 x
  have h89 := h x v66 v0
  have h90 := h v67 v12 v39
  have h91 := h v0 v38 v0
  have h92 := T (T (T h91 (C (T (T (T (T (T (T (C (T h63 (C h68 h34)) h40) (S h90)) (C (T (T h89 (C (C h11 (T (T h88 (C (T (T (T (T (T (T (T (C (T h59 (C h58 h63)) h68) (S h87)) (C h51 h29)) h86) (C (T (T (T (T (T (C (T h81 (C h85 h59)) h58) (S h84)) h82) h27) h80) h77) h11)) h76) (C (T (C h58 (S h75)) h74) h73)) (C h3 (T (T h71 (C (C h11 (T (T (T (T (C h63 h3) (S h70)) h69) (C (T (C h68 (S h65)) h64) h62)) (C h3 (T (T h60 (C (T (T (T (T (C (T h59 (C h58 h57)) h56) (S h55)) (C h51 h26)) h25) (C (S h22) h3)) h11)) (S h21))))) h3)) h19))) h11)) (S h20))) h3)) h19) h17)) h16) (C (S h14) h11)) h10) (C (C h3 (S h9)) h8)) h3)) (S h6)) h2
  have h93 := T (T h27 h80) h77
  have h94 := C (T (C (T (T (h x v38 v0) (C (C h11 h92) h3)) h74) (T (T (T (T (T (T (T h30 h79) h78) h35) h1) h6) (C (T (T (T (T (T (T (C (C h3 h9) h8) (S h10)) (C h14 h11)) (S h16)) (C (T (T h18 (C (C h11 (T (T h20 (C (T (T (T (T (T (T (T (C h3 (T (T h18 (C (C h11 (T (T (T (T (C h3 (T (T h21 (C (T (T (T (T (C h22 h3) (S h25)) (C h93 h26)) h55) (C (T (C h58 (S h57)) h74) h56)) h11)) (S h60))) (C (T h63 (C h68 h65)) h62)) (S h69)) h70) (C h64 h3))) h3)) (S h71))) (C (T h59 (C h58 h75)) h73)) (S h76)) (C (T (T (T (T (T h50 h49) h28) h81) h84) (C (T (C h85 h74) h82) h58)) h11)) (S h86)) (C h93 h29)) h87) (C (T (C h58 h64) h74) h68)) h11)) (S h88))) h3)) (S h89)) h17)) h90) (C (T (C h68 h35) h64) h40)) h3)) (S h91))) (C h3 h92)) h3
  let v95 := M x v38
  let v96 := M v95 v23
  have h97 := S (h v96 v0 v5)
  have h98 := R v5
  have h99 := C (T (T (h x z v12) (h v95 v12 v4)) (C (R v96) h1)) h98
  let v100 := M v54 (M v4 v0)
  T (T (T (T (T (T (T (T h22 (h v24 v4 v0)) (C (C h93 (T (h v0 v4 v0) (C (T (T (T h99 h97) h94) h2) h3))) h3)) (h v100 v0 v5)) (C (T (T (C (R v100) h2) (S (h v54 v0 v4))) h74) h98)) h99) h97) h94) h2

