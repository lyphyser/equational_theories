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
theorem Equation1761_implies_Equation1726 (G: Type _) [Magma G] (h: Equation1761 G) : Equation1726 G := fun x y z =>
  let v0 := M x z
  let v1 := M v0 z
  let v2 := M y y
  let v3 := M v2 v1
  have h4 := R v3
  let v5 := M v3 v3
  have h6 := h y y v1
  have h7 := S h6
  let v8 := M y v1
  have h9 := h v8 v3 y
  have h10 := R y
  let v11 := M v3 y
  have h12 := R v11
  have h13 := R v2
  have h14 := h v11 y z
  have h15 := R z
  have h16 := h y v1 v3
  let v17 := M v1 v3
  have h18 := R v17
  have h19 := T (C h18 h6) (S h16)
  have h20 := h v1 v3 y
  let v21 := M v1 z
  have h22 := h v21 z v3
  have h23 := h z z v1
  have h24 := S h23
  have h25 := h x z z
  have h26 := h v1 x z
  have h27 := R (M z v1)
  let v28 := M v1 x
  have h29 := R v28
  have h30 := h z v1 x
  have h31 := T h30 (C h29 (T (C h27 h25) h24))
  have h32 := h v0 z x
  have h33 := S h25
  have h34 := T (C h29 (T h23 (C h27 h33))) (S h30)
  have h35 := C h34 (T (C (S h32) h31) (S h26))
  let v36 := M z x
  have h37 := h v36 v28 z
  have h38 := C (T h37 h35) h25
  let v39 := M v36 x
  have h40 := h v39 x v1
  have h41 := S h40
  have h42 := h v1 x v3
  have h43 := S h42
  have h44 := h v28 z v3
  have h45 := T h38 h24
  have h46 := h v39 x x
  have h47 := R v1
  have h48 := C (C h45 h15) h47
  have h49 := R x
  have h50 := S h37
  have h51 := C h31 (T h26 (C h32 h34))
  have h52 := C (T h51 h50) h33
  have h53 := T h23 h52
  have h54 := T (T h51 h50) (C h53 h49)
  have h55 := h v39 z v1
  let v56 := M x x
  have h57 := R v56
  have h58 := R (M z v3)
  have h59 := h v56 z v3
  have h60 := R (M x v3)
  have h61 := C h60 (C (T (T h59 (C h58 (T (T (C (T (C h57 (T (T (T h23 h52) h55) (C h54 (T h48 h33)))) (S h46)) h4) (C h45 h4)) (C h31 h4)))) (S h44)) h4)
  have h62 := h x x v3
  have h63 := T (T (T (T h48 h33) h62) h61) h43
  let v64 := M x v1
  have h65 := R v64
  have h66 := C h65 (T (T (T h23 h52) h55) (C h54 h63))
  have h67 := h (M v64 z) v1 v1
  have h68 := S h55
  have h69 := C (C h53 h15) h47
  have h70 := T (T (C h45 h49) h37) h35
  have h71 := T (T (T (T h42 (C h60 (C (T (T h44 (C h58 (T (T (C h34 h4) (C h53 h4)) (C (T h46 (C h57 (T (T (T (C h70 (T h25 h69)) h68) h38) h24))) h4)))) (S h59)) h4))) (S h62)) h25) h69
  have h72 := C h65 (T (T (T (C h70 h71) h68) h38) h24)
  have h73 := R (M v1 v1)
  have h74 := R v21
  have h75 := C h74 (T (T (T (T (T (C h73 (T (T (T h23 h52) h55) (C (T (C h53 h47) (C (T h40 h72) h47)) h63))) (S h67)) h66) h41) h38) h24)
  have h76 := h v1 v1 z
  have h77 := h v0 z v3
  let v78 := M y z
  have h79 := R v78
  have h80 := T (C h79 (T (T (T h77 (C h58 (C (T h76 h75) h4))) (S h22)) (C (T h20 (C h12 h19)) h15))) (S h14)
  have h81 := C (T (T (C h80 h13) (C h12 (C h6 h10))) (S h9)) h4
  have h82 := C (T (C h74 (T (T (T (T (T h23 h52) h40) h72) h67) (C h73 (T (T (T (C (T (C (T h66 h41) h47) (C h45 h47)) h71) h68) h38) h24)))) (S h76)) h4
  have h83 := T h14 (C h79 (T (T (T (C (T (C h12 (T h16 (C h18 h7))) (S h20)) h15) h22) (C h58 h82)) (S h77)))
  have h84 := C h83 h13
  have h85 := C h12 (C h7 h10)
  have h86 := h v8 v3 v3
  have h87 := h y y v3
  let v88 := M v2 v3
  have h89 := h v88 y v3
  have h90 := R v88
  have h91 := h (M v78 v0) v2 v3
  let v92 := M y v3
  have h93 := R v92
  have h94 := h v3 y v3
  have h95 := C (T (C h93 (T (T h94 (C h93 (T (C h83 h4) (C (T h91 (C h90 (T h81 h7))) h4)))) (S h89))) (S h87)) h4
  have h96 := R v5
  have h97 := h v92 v3 v3
  have h98 := C (T h87 (C h93 (T (T h89 (C h93 (T (C (T (C h90 (T h6 (C (T (T h9 h85) h84) h4))) (S h91)) h4) (C h80 h4)))) (S h94)))) h4
  have h99 := S h97
  have h100 := C h96 (T (C h7 h4) h98)
  T (T (T (T (T (T (T h62 h61) h43) h76) h75) (h (M v21 z) v3 v3)) (C h96 (C (T (T (T h82 (h v17 y v1)) (C (T (T h86 h100) h99) (T (T (T (T (T (C h19 h47) h86) h100) h99) h98) (C (T (h (M v92 v3) v3 v3) (C h96 (T (T (C (T (T (T (T (T (T h95 h97) (C h96 (T h95 (C h6 h4)))) (S h86)) h9) h85) h84) h4) h81) h7))) h4)))) (S (h v5 y v3))) h4))) (S (h v3 v3 v3))

