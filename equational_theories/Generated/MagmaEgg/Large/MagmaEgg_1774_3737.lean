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
theorem Equation1774_implies_Equation3737 (G: Type _) [Magma G] (h: Equation1774 G) : Equation3737 G := fun x y z =>
  let v0 := M y z
  let v1 := M x z
  let v2 := M v1 v0
  have h3 := h v2 v1 v0
  have h4 := S h3
  let v5 := M x y
  let v6 := M (M v1 v5) v0
  let v7 := M (M v1 v2) v0
  have h8 := h v7 v2 v6
  have h9 := R v6
  have h10 := h v5 v1 v0
  have h11 := T (C h10 (T h10 (C h3 h9))) (S h8)
  have h12 := R v2
  have h13 := C h12 h11
  have h14 := S h10
  have h15 := C h14 (T (C h4 h9) h14)
  have h16 := h v7 v2 v2
  have h17 := h v2 x z
  have h18 := h z x v0
  let v19 := M x v2
  have h20 := R v19
  have h21 := h v0 x v2
  have h22 := T h21 (C h20 (S h18))
  have h23 := h v1 x z
  have h24 := S h23
  have h25 := C h12 (T (C h24 h22) (S h17))
  let v26 := M x v1
  let v27 := M v26 z
  have h28 := h v27 v1 v0
  have h29 := h v27 v1 v1
  have h30 := S h29
  have h31 := R v1
  have h32 := h v1 x y
  have h33 := S h32
  let v34 := M v26 y
  have h35 := R v34
  have h36 := h v5 x y
  have h37 := S h36
  have h38 := C h33 (T (C h37 h35) h33)
  let v39 := M (M x v5) y
  have h40 := h v39 v5 v34
  have h41 := h v39 v5 v2
  have h42 := S h41
  have h43 := h (M v5 v2) v19 z
  have h44 := S h43
  have h45 := R z
  have h46 := h y x v2
  have h47 := C h22 (C h46 h45)
  have h48 := R v0
  have h49 := h v0 y z
  have h50 := S h49
  have h51 := C (T h47 h44) (T (T (T (C h50 h48) h47) h44) (C h36 h12))
  let v52 := M (M y v0) z
  have h53 := h v52 v0 v0
  let v54 := M (M y x) z
  have h55 := h v52 v0 v54
  have h56 := S h55
  have h57 := R v54
  have h58 := h x y z
  have h59 := C h58 (T h58 (C h49 h57))
  let v60 := M x x
  have h61 := h v60 v0 v60
  have h62 := S h61
  have h63 := R v60
  have h64 := S h58
  have h65 := C h64 (T (C h50 h57) h64)
  have h66 := C h48 (T h55 h65)
  have h67 := S h53
  have h68 := T (C h20 h18) (S h21)
  have h69 := C h68 (C (S h46) h45)
  have h70 := C (T h43 h69) (T (T (T (C h37 h12) h43) h69) (C h49 h48))
  have h71 := S h40
  have h72 := C h32 (T h32 (C h36 h35))
  have h73 := C h48 (T (T (T (T h72 h71) h41) h70) h67)
  have h74 := C (T h73 h66) (T (T h49 h66) (C (T h49 h66) h63))
  have h75 := T (T (T (T h53 h51) h42) h40) h38
  have h76 := C h48 h75
  have h77 := C (T h49 h76) h48
  have h78 := C (T (T (T (T (T (T (T (T (T h77 h74) h62) h59) h56) h53) h51) h42) h40) h38) (T (T (T (T (T (T (T (T (T h74 h62) h59) h56) h53) h51) h42) h40) h38) (C h23 h31))
  let v79 := M v1 v1
  have h80 := h v79 v0 v0
  have h81 := C h48 (T h59 h56)
  have h82 := C (T h81 h76) (T (T (C (T h81 h50) h63) h81) h50)
  have h83 := C (T h73 h50) h48
  have h84 := C (T (T (T (T (T (T (T (T (T h72 h71) h41) h70) h67) h55) h65) h61) h82) h83) (T (T (T (T (T (T (T (T (T (C h24 h31) h72) h71) h41) h70) h67) h55) h65) h61) h82)
  have h85 := S h28
  have h86 := C h12 (T h17 (C h23 h68))
  have h87 := T (T (T (T (T (T (T h86 h85) h29) h84) (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T h77 h74) h62) h59) h56) h53) h51) h42) h40) h38) h80) h78) h30) h28) h25) (T (T (T (T (T (T (T (T (T (T (T (T (T (T h74 h62) h59) h56) h53) h51) h42) h40) h38) h80) h78) h30) h28) h25) (C h3 h12)))) (S h16)) h8) h15
  let v88 := M v5 z
  let v89 := M v2 v2
  have h90 := h v89 v1 v88
  have h91 := S h90
  have h92 := R v88
  have h93 := T h23 (C h31 (T h28 h25))
  have h94 := h y x z
  have h95 := C h94 (T h94 (C h93 h92))
  have h96 := S h94
  have h97 := T (C h31 (T h86 h85)) h24
  let v98 := M v1 z
  have h99 := h v89 v1 v98
  have h100 := R v98
  have h101 := h z x z
  have h102 := T (T (T (C h101 (T h101 (C h93 h100))) (S h99)) h90) (C h96 (T (C h97 h92) h96))
  have h103 := S h101
  have h104 := C h103 (T (C h97 h100) h103)
  have h105 := S h80
  T (T (T (T (T (T (T h10 (C h12 (T (T (T (T (T (T (T (T (T (h v6 v2 v2) (C (T (T (T (T h86 h85) h29) h84) h105) (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (C h14 h12) h43) h69) h77) h74) h62) h59) h56) h53) h51) h42) h40) h38) h80) h78) h30) h28) h25) (h v89 v1 v89)) (C (R (M v1 v89)) (T (T (T (C h97 (T h99 h104)) (C h31 h102)) (C h31 (T (T (T h95 h91) h86) h85))) h24))) (C (C h31 h87) h31)) (C (C h31 h11) h31)) (C (C h31 (T (T (T (T (T (T (T h16 (C (T (T (T (T (T (T (T (T (T (T (T (T (T (T h86 h85) h29) h84) h105) h72) h71) h41) h70) h67) h55) h65) h61) h82) h83) (T (T (T (T (T (T (T (T (T (T (T (T (T (T (C h4 h12) h86) h85) h29) h84) h105) h72) h71) h41) h70) h67) h55) h65) h61) h82))) h105) h72) h71) h41) h70) h67)) h31)) (C (C h31 h75) h31)))) (S (h v79 v1 v1))) h80) h78) h30) h28) h25) h99) h104))) (C h12 h102)) (C h12 (T h95 h91))) (C (T h3 (C h12 (T h8 h15))) h87)) (C (T h13 h4) (R (M v5 v5)))) h13) h4

