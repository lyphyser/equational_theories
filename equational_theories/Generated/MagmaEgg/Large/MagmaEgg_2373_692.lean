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
theorem Equation2373_implies_Equation692 (G: Type _) [Magma G] (h: Equation2373 G) : Equation692 G := fun x y z =>
  let v0 := M z y
  let v1 := M v0 z
  let v2 := M x v1
  let v3 := M y v2
  have h4 := h v3 v3 x
  have h5 := R v3
  have h6 := R x
  have h7 := h v3 v3 z
  let v8 := M v1 (M v3 v1)
  have h9 := R v1
  have h10 := h v1 v3 v2
  have h11 := S h10
  let v12 := M v1 v2
  let v13 := M v2 v12
  let v14 := M v3 v13
  have h15 := R v2
  have h16 := h x v2 v2
  have h17 := S h16
  have h18 := C h15 h17
  have h19 := C h6 h18
  let v20 := M v2 (M x v2)
  let v21 := M v2 v20
  have h22 := h v21 x v2
  have h23 := h v21 z v2
  have h24 := S h23
  have h25 := R z
  have h26 := C h15 h16
  have h27 := h z v0 x
  have h28 := S h27
  have h29 := R v0
  have h30 := h (M v0 (M x (M z x))) x v0
  have h31 := h y z v0
  have h32 := S h31
  let v33 := M v2 x
  have h34 := R v33
  let v35 := M v0 (M y v0)
  have h36 := h (M z v35) v33 z
  have h37 := C (T h36 (C (T (T (C h34 (C h25 h32)) (C (T (C (C h6 (C h29 h27)) h6) (S h30)) h29)) h28) h26)) h25
  have h38 := h y v3 v0
  have h39 := S h38
  let v40 := M v3 v35
  have h41 := h v40 x v3
  have h42 := S h41
  have h43 := h y v3 y
  have h44 := C h5 (S h43)
  have h45 := C (C h6 (T h44 (C h5 h38))) h6
  let v46 := M v3 (M y (M y y))
  have h47 := h v46 x v3
  have h48 := h v46 v3 v3
  have h49 := S h48
  have h50 := C h5 h43
  have h51 := R y
  have h52 := h v1 x v2
  have h53 := C h6 (S h52)
  have h54 := C (C h51 h53) h51
  let v55 := M x v13
  have h56 := h v55 y x
  have h57 := h v55 v21 x
  have h58 := S h57
  have h59 := S h22
  have h60 := C h6 h26
  have h61 := C h60 h6
  have h62 := C h6 h52
  have h63 := R v21
  have h64 := C (T h16 (C h63 h62)) (T h61 h59)
  have h65 := C (C h5 (T (T (T (T h64 h58) h56) h54) h50)) h5
  let v66 := M x v33
  have h67 := h v66 v3 x
  have h68 := C (T (T (T (T (T h67 h65) h49) h47) h45) h42) h5
  have h69 := S h67
  have h70 := C h19 h6
  have h71 := C (T (C h63 h53) h17) (T h22 h70)
  have h72 := S h56
  have h73 := C (C h51 h62) h51
  have h74 := C (C h5 (T (T (T (T h44 h73) h72) h57) h71)) h5
  have h75 := S h47
  have h76 := C (C h6 (T (C h5 h39) h50)) h6
  have h77 := h v40 v3 x
  have h78 := C (T (T (T (T (T (T h19 h67) h65) h49) h47) h45) h42) h6
  have h79 := C h6 (T (T (T (T h31 h37) h24) h22) h78)
  have h80 := h y x z
  have h81 := C h6 (S h80)
  have h82 := h (M x (M z (M y z))) v3 x
  have h83 := C (T (T (T (T (T (T (T (T h82 (C (C h5 (T h81 h79)) h5)) (S h77)) h41) h76) h75) h48) h74) h69) h5
  have h84 := C h6 h80
  have h85 := C (T (T (T (T (T (T h41 h76) h75) h48) h74) h69) h60) h6
  have h86 := C h6 (T (T (T (T h85 h59) h23) (C (T (C (T (T h27 (C (T h30 (C (C h6 (C h29 h28)) h6)) h29)) (C h34 (C h25 h31))) h18) (S h36)) h25)) h32)
  have h87 := C (T (T (T (T (T h41 h76) h75) h48) h74) h69) h5
  have h88 := h v2 v1 v3
  have h89 := h v1 x y
  have h90 := S h89
  have h91 := h (M x (M y (M v1 y))) x x
  have h92 := h v55 x x
  have h93 := C h6 (T h85 h70)
  have h94 := h (M v3 (M v2 v3)) x v3
  have h95 := h y v3 v2
  have h96 := h (M v1 v66) x v1
  have h97 := h v2 v1 x
  have h98 := h x x v1
  have h99 := C (C h51 (T (C (T (T (T h98 (C (C h6 (C h9 h97)) h6)) (S h96)) (C h9 (T (T (T (T (T h67 h65) h49) h47) (C (C h6 (T h44 (C h5 h95))) h6)) (S h94)))) (T (C (T (T (T (T (T (T h79 h93) h64) h58) h92) (C (T (C h6 h53) (C h6 (C h6 h89))) h6)) (S h91)) h6) h90)) (S h88))) (T (T h38 h87) (C (T (T (T (T (T (T (T (T h67 h65) h49) h47) h45) h42) h77) (C (C h5 (T h86 h84)) h5)) (S h82)) h5))
  let v100 := M x y
  have h101 := h v100 y x
  have h102 := C h6 (T h61 h78)
  have h103 := h x v3 v0
  have h104 := h x v3 v2
  T (T h104 (C (T (T (T (T (T (T (T (T (h (M v3 v20) x v3) (C (T (C h6 (C h5 (S h104))) (C h6 (C h5 h103))) h6)) (C (T (C h6 (C h5 (S h103))) (C h6 (C h5 (h x v3 v1)))) h6)) (S (h (M v3 v12) x v3))) (C h5 (T (T (h v12 v3 v1) (C (C h5 (T (T (T (T (T (T (C h9 (T (T (T (T (C (C h9 h62) h9) (S (h v55 v1 x))) h56) h54) h50)) (C h9 (T h44 (C h5 (T h38 h87))))) (C h9 (T (T (T (T (T (C h5 (T h68 h39)) h73) h72) h57) h71) h102))) (C h9 h93)) (C h9 (T (T (T h102 h86) h101) h99))) (C h9 (T (T (C (C h51 (T h88 (C (T (T (T (C h9 (T (T (T (T (T h94 (C (C h6 (T (C h5 (S h95)) h50)) h6)) h75) h48) h74) h69)) h96) (C (C h6 (C h9 (S h97))) h6)) (S h98)) (T h89 (C (T (T (T (T (T (T h91 (C (T (C h6 (C h6 h90)) (C h6 h62)) h6)) (S h92)) h57) h71) h102) h86) h6))))) (T (T h83 h68) h39)) (S h101)) h84))) (C h9 (T (T (T (T (T h81 (h v100 v3 v3)) (C (C h5 (T (C h5 (T (C (T (T h101 h99) (C h5 (T (T (T (T (T (T (T (T h83 h68) h39) h31) h37) h24) h22) (C (T h19 (C h6 (C h15 (h x v2 v1)))) h6)) (S (h v13 x v2))))) h5) h11)) (C h5 h10))) h5)) (S (h v14 v3 v3))) (h v14 v1 v3)) (C (C h9 (C h5 h11)) h9))))) h5)) (S (h v8 v3 v1))))) (h (M v3 v8) x v3)) (C (C h6 (T (C h5 (S (h v3 v3 v1))) (C h5 h7))) h6)) (C (C h6 (T (C h5 (S h7)) (C h5 h4))) h6)) (S (h (M v3 (M x (M v3 x))) x v3))) h5)) (S h4)

