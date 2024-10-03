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
theorem Equation1561_implies_Equation2522 (G: Type _) [Magma G] (h: Equation1561 G) : Equation2522 G := fun x y z =>
  let v0 := M x z
  let v1 := M v0 z
  let v2 := M y v1
  let v3 := M v2 y
  have h4 := S (h v3 y v2)
  let v5 := M v3 v3
  have h6 := R v5
  have h7 := h v2 v0 z
  have h8 := h y z v0
  have h9 := S h8
  have h10 := C h9 (S h7)
  let v11 := M z v0
  have h12 := h v1 v11 v2
  have h13 := T h12 h10
  let v14 := M y v2
  have h15 := R v14
  have h16 := h v14 v3 y
  have h17 := S h16
  have h18 := h y y v2
  have h19 := h y v1 y
  have h20 := R v3
  have h21 := h (M v1 y) v2 y
  have h22 := C (T h21 (C h20 (S h19))) (T h9 h18)
  have h23 := h v11 v1 y
  have h24 := T (T h23 h22) h17
  have h25 := R v1
  let v26 := M v3 v0
  have h27 := h v26 z x
  have h28 := h v0 y v2
  have h29 := R v26
  have h30 := h v14 v3 v0
  let v31 := M z x
  have h32 := R v31
  have h33 := h v11 v1 v0
  have h34 := S h33
  have h35 := h v0 z v0
  let v36 := M v1 v0
  have h37 := R v36
  have h38 := C h37 h35
  have h39 := h v36 z x
  have h40 := C h25 (T (T (T h39 (C h32 (T (T (T (T h38 h34) h23) h22) h17))) (C h32 (T h30 (C h29 (S h28))))) (S h27))
  have h41 := S h39
  have h42 := C h32 (T h33 (C h37 (S h35)))
  have h43 := C h25 (T h42 h41)
  have h44 := h v31 v0 z
  have h45 := h v31 v0 v1
  have h46 := S h45
  have h47 := h v1 z x
  have h48 := h z z x
  have h49 := S h48
  have h50 := C h32 (T h38 h34)
  have h51 := T (T h39 h50) h49
  have h52 := h v0 v1 v0
  have h53 := S h52
  let v54 := M v0 v1
  have h55 := h v54 z v0
  have h56 := S h55
  have h57 := S h47
  have h58 := R v54
  have h59 := C h58 h57
  have h60 := R v11
  have h61 := R v0
  have h62 := h v11 x z
  have h63 := h v11 z v1
  have h64 := C h58 h47
  let v65 := M z v1
  have h66 := R v65
  have h67 := C h37 (T (T (T (C h66 (T h55 (C h60 (T (T (T h64 h46) h44) (C h25 h49))))) (S h63)) h62) (C h61 (T (C h60 (T h45 h59)) h56)))
  have h68 := h v65 v1 v0
  have h69 := S h12
  have h70 := C h8 h7
  have h71 := R z
  have h72 := C h71 (T h70 h69)
  have h73 := C h58 (T (C (T (T (T h72 h68) h67) h53) h51) h47)
  have h74 := h (M z v14) v0 v1
  have h75 := C h71 h13
  have h76 := S h68
  have h77 := S h44
  have h78 := C h66 (T (C h60 (T (T (T (C h25 h48) h77) h45) h59)) h56)
  have h79 := h v11 z v3
  let v80 := M v3 z
  have h81 := h v80 v0 v1
  have h82 := h z y v2
  have h83 := R v80
  have h84 := h v14 v3 z
  have h85 := S h23
  have h86 := C (T (C h20 h19) (S h21)) (T (S h18) h8)
  have h87 := h v54 v0 z
  let v88 := M z v3
  have h89 := R v88
  have h90 := h v88 v1 v0
  let v91 := M v0 v3
  have h92 := C h37 (T (C h61 (T h55 (C h60 (T h64 h46)))) (S h62))
  have h93 := h x z x
  let v94 := M x v0
  have h95 := R v94
  have h96 := T (T (T (T h52 h92) (C h37 (T h63 h78))) h76) h75
  T (T (T (T (T (T (T (T (T (T (T (T h93 (C (T (T (T (T (T (T h45 (C h58 (T h57 (C h96 (T (T h48 h42) h41))))) (S h74)) h72) h68) h67) h53) h95)) (h (M v0 v94) v0 v1)) (C h58 (C (T (T (T (C h96 h95) (C (T (T (T (T (T h74 h73) h46) h44) h43) h40) h95)) (C (T (T (C h25 (T (T (T h27 (C h32 (T (T (T (T (C h29 h28) (S h30)) h16) h86) h85))) h42) h41)) (C h25 (T h39 h50))) h77) h95)) (S h93)) h51))) (C h58 (T (T (T h52 h92) (C h37 (T h79 (C h89 (T (C (T (T (T (T h23 h22) h17) h70) h69) (T h81 (C h58 (T (T (T (T (C h83 (T (T (T h39 h50) h49) h82)) (S h84)) h16) h86) h85)))) (S h87)))))) (S h90)))) (C (T (T h55 (C h24 (T (T (T h64 h46) (h v31 v0 v3)) (C (R v91) (S (h v3 z x)))))) (S (h v91 y v2))) (T (T (T (T (T (T (T (T (T h90 (C h37 (T (T (T (C h89 (T h87 (C (T (T (T (T h12 h10) h16) h86) h85) (T (C h58 (T (T (T (T h23 h22) h17) h84) (C h83 (T (T (T (S h82) h48) h42) h41)))) (S h81))))) (S h79)) h63) h78))) h76) h75) h74) h73) h46) h44) h43) h40))) (S (h v1 v0 v3))) h12) h10) (h v14 v0 z)) (C h25 (T (T (C h15 h24) (C h15 (T (h v14 v3 v3) (C h6 h4)))) (S (h v5 y v2))))) (C h13 h6)) h4

