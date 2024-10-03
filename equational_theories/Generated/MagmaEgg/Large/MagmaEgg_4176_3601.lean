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
theorem Equation4176_implies_Equation3601 (G: Type _) [Magma G] (h: Equation4176 G) : Equation3601 G := fun x y z =>
  let v0 := M y x
  let v1 := M v0 z
  let v2 := M z v1
  have h3 := h z v1 v2
  have h4 := S h3
  have h5 := R v2
  have h6 := R z
  have h7 := C (T (h z z z) (C (T (C (h z z v1) h6) (S (h v1 v2 z))) h6)) h5
  have h8 := R x
  let v9 := M x y
  have h10 := h x x y
  have h11 := R y
  have h12 := T (h x v0 x) (C (S (h x y x)) h8)
  have h13 := R v0
  have h14 := h v0 v0 z
  have h15 := S h14
  let v16 := M v1 v0
  have h17 := h v16 z v2
  have h18 := S h17
  have h19 := h v0 z v1
  have h20 := C (S h19) h13
  have h21 := h v1 v2 v0
  let v22 := M z v2
  have h23 := R v22
  have h24 := C (C h23 (T h21 h20)) h5
  let v25 := M v1 v2
  have h26 := h v25 z v2
  have h27 := h v1 v2 v1
  have h28 := R v1
  have h29 := h v1 z v1
  have h30 := C (T (C h29 h28) (S h27)) h6
  have h31 := h v1 v1 z
  have h32 := T (T (T (T (T h31 h30) h26) h24) h18) h15
  have h33 := h v1 v1 v2
  have h34 := S h33
  have h35 := S h21
  have h36 := C h19 h13
  have h37 := h v1 v0 z
  have h38 := S h37
  have h39 := h z v1 v1
  have h40 := T h39 (C (T (T h38 h36) h35) h28)
  have h41 := C h40 h5
  have h42 := T h41 h34
  have h43 := S h39
  have h44 := C (T (C (T (T h21 h20) h37) h28) h43) h5
  have h45 := S h31
  have h46 := S h29
  have h47 := C (T h27 (C h46 h28)) h6
  have h48 := h v2 v0 z
  have h49 := T (T (T (T h48 h47) h45) h33) h44
  have h50 := T (T (h x v2 v0) (C (T (T (C h49 h8) (C h42 h8)) (C h32 h8)) h13)) (S (h x v0 v0))
  have h51 := C (T (T (T (T (T (C h50 h11) (C h12 h11)) (S h10)) (h x x x)) (C (T (T (T (C h10 h8) (S (h y v9 x))) (h y v9 z)) (C (S (h z x y)) h6)) h8)) (S (h z z x))) h5
  have h52 := h y x v2
  have h53 := h y x v9
  let v54 := M (M x v9) y
  have h55 := R v9
  have h56 := h y v9 y
  have h57 := S h56
  have h58 := h y x y
  have h59 := C h58 h11
  have h60 := h z y x
  have h61 := S (h y x v0)
  let v62 := M x v0
  have h63 := S (h (M v62 y) v0 v0)
  have h64 := h z v1 v0
  let v65 := M v16 z
  have h66 := h v2 v0 v0
  have h67 := h v0 z v2
  have h68 := h v2 v22 v0
  have h69 := h z v2 v0
  have h70 := S h48
  have h71 := T (T (T (T h41 h34) h31) h30) h70
  have h72 := T h33 h44
  have h73 := S h26
  have h74 := C (C h23 (T h36 h35)) h5
  have h75 := T (T (T (T (T h14 h17) h74) h73) h47) h45
  have h76 := h z v0 v0
  have h77 := h (M z v0) z v1
  have h78 := h z z v0
  let v79 := M z z
  let v80 := M v79 v0
  have h81 := h v0 z z
  have h82 := C (T (C (T (T (T (T (T (T (T h14 h17) h74) h73) h47) h45) h33) h44) (T (T (T (T (T (T (T (T h17 h74) h73) h70) h66) (C (T (T (T (T (T (C (T (T (T h14 h17) h74) h73) h5) h4) h39) (C h38 h28)) (C (T (T (C h67 h13) (S h68)) (C h5 (T (T h69 (C (T (T (C h49 h6) (C h42 h6)) (C h32 h6)) h13)) (S h76)))) h28)) (S h77)) h13)) (S h78)) (h z z y)) (C (T (T (C (T h60 (C h81 h8)) h6) (S (h x v80 z))) (C h8 (T (T (T (h v79 v0 v2) (C (C (R (M v0 v2)) (T (T (T (T (T (T h78 (C (T (T (T (T (T h77 (C (T (T (C h5 (T (T h76 (C (T (T (C h75 h6) (C h72 h6)) (C h71 h6)) h13)) (S h69))) h68) (C (S h67) h13)) h28)) (C h37 h28)) h43) h3) (C (T (T (T h26 h24) h18) h15) h5)) h13)) (S h66)) h48) h26) h24) h18)) h5)) (S (h v65 v0 v2))) (S h64)))) h11))) (C (T (T (T (T (T (T (T h41 h34) h31) h30) h26) h24) h18) h15) (T (T (h (M x v2) y v2) (C (C (R (M y v2)) h50) h5)) (S (h v62 y v2))))) h13
  have h83 := h v65 v0 v0
  have h84 := C (T (T (T (T h64 h83) h82) h63) h61) h11
  have h85 := h y v2 v0
  have h86 := h y v0 v0
  have h87 := h y v0 z
  have h88 := h v1 y v9
  have h89 := h y z v1
  have h90 := h v9 y z
  have h91 := T (T (T h52 h51) h7) h4
  have h92 := R v25
  have h93 := S h90
  have h94 := C (T h88 (C (T (C (T (T h56 (C (S h58) h11)) (C h91 h11)) h28) (S h89)) h55)) h6
  have h95 := S h86
  have h96 := C (T (T (C h49 h11) (C h42 h11)) (C h32 h11)) h13
  T (T (T (T (T (T (T (T (T (T (T (h x y v2) (C (T (C (T (T (T (T (T h85 h96) h95) h87) h94) h93) h8) (C (T (T (h v9 y v2) (C (T (C (T (T (T (T (T (T (T h85 h96) h95) h87) h94) h93) (h v9 y x)) (C (C h91 h55) h8)) h55) (S (h x v2 v9))) h5)) (C h50 h5)) h8)) h5)) (S (h x v62 v2))) (h x v62 v1)) (C (T (C (C h12 h28) h8) (S (h v1 v9 x))) h28)) (C (T (T (C (T (T (T (T (T h81 (h v80 z v1)) (C (T (T (T (h v2 v80 z) (C (C (S h81) h5) h6)) h70) (C h40 h13)) h28)) (S (h v0 v25 v1))) (C h91 h92)) (C (T (T (T (T (T h64 h83) h82) h63) h61) h53) h92)) h55) (S (h v25 v54 v9))) (C (T (T (T h21 h20) (h v1 v0 v1)) (C (T (T (T (T (C (C h91 h28) h28) h46) (h v1 z v9)) (C (T (T (T (C (T (h z v9 y) (C (T (C (T (T (T (T (T (T (T h90 (C (T (C (T h89 (C (T (T h84 h59) h57) h28)) h55) (S h88)) h6)) (S h87)) h86) (C (T (T (C h75 h11) (C h72 h11)) (C h71 h11)) h13)) (S h85)) (h y v2 y)) (C (T (C (T (T (T (T h84 h59) h57) (h y v9 v1)) (C (T (S (h v1 x y)) (S h60)) h28)) h11) (S (h v1 z y))) h11)) h6) (S (h y v1 z))) h11)) h28) (S (h y y v1))) (h y y x)) (C (T h59 h57) h8)) h55)) (S (h x y v9))) h28)) (R v54))) h28)) (S (h v54 v9 v1))) (S h53)) h52) h51) h7) h4

