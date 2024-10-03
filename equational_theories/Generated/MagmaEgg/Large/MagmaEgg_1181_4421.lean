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
theorem Equation1181_implies_Equation4421 (G: Type _) [Magma G] (h: Equation1181 G) : Equation4421 G := fun x y z =>
  let v0 := M z y
  let v1 := M v0 z
  have h2 := h v1 z z
  let v3 := M z (M z v1)
  have h4 := R x
  have h5 := R z
  have h6 := h y z x
  have h7 := C h5 (S h6)
  let v8 := M x y
  let v9 := M x v8
  let v10 := M v9 z
  have h11 := h z v9 v1
  have h12 := R v9
  have h13 := h v10 y z
  have h14 := S h13
  have h15 := R y
  have h16 := C h5 h6
  have h17 := h y v1 v1
  have h18 := S h17
  have h19 := h (M (M v1 (M v1 y)) v1) x v1
  have h20 := R v1
  have h21 := h y v1 z
  have h22 := C h20 (S h21)
  have h23 := C h20 h21
  have h24 := h y v1 x
  have h25 := h (M v9 v1) x v1
  have h26 := h v9 z y
  have h27 := S h26
  let v28 := M (M y (M y v9)) z
  have h29 := h v28 x z
  have h30 := h v9 z v0
  have h31 := C h5 (S h30)
  have h32 := C h5 h30
  have h33 := h v9 z v9
  have h34 := h y v9 x
  let v35 := M y z
  have h36 := h v35 x z
  have h37 := h z x x
  have h38 := S h37
  have h39 := h (M (M x (M x z)) x) x x
  have h40 := S h39
  have h41 := C h4 h37
  have h42 := h z x v0
  have h43 := h (M (M v0 v1) x) x x
  have h44 := h v1 v0 z
  have h45 := R v0
  have h46 := C h4 (T (T (T (C (C h45 (S h44)) h4) h43) (C h4 (C (T (C h4 (S h42)) h41) h4))) h40)
  let v47 := M v3 v0
  have h48 := h v47 x v0
  have h49 := h v47 x z
  have h50 := S h48
  have h51 := C h4 h38
  have h52 := C h4 (T (T (T h39 (C h4 (C (T h51 (C h4 h42)) h4))) (S h43)) (C (C h45 h44) h4))
  have h53 := h z v0 z
  have h54 := S h53
  let v55 := M z (M z z)
  let v56 := M v55 v0
  have h57 := h v56 v0 v0
  have h58 := S h57
  have h59 := C h45 h53
  have h60 := C h59 h45
  have h61 := T (C h45 (T (C h45 h60) h58)) h54
  let v62 := M v1 v0
  have h63 := h v62 z v0
  have h64 := h v0 v1 v0
  have h65 := C h20 (S h64)
  have h66 := C h20 h64
  have h67 := h v62 y v0
  have h68 := C h45 h54
  have h69 := C h68 h45
  have h70 := T h53 (C h45 (T h57 (C h45 h69)))
  have h71 := h v0 y v8
  have h72 := S h71
  have h73 := h (M (M v8 (M v8 v0)) y) x y
  have h74 := C h15 (T (T (T (T (T (T h73 (C h4 (C (T (T (T (C h15 h72) (C h15 (C h70 h15))) (S h67)) h66) h4))) (C h4 (C (T (T (T h65 h63) (C h5 (C h61 h5))) (C h5 (C h5 (T (T h37 h52) h50)))) h4))) (S h49)) h48) h46) h38)
  have h75 := C h5 (T (T (T (T (T h71 h74) h36) (C h4 (C (T (C h5 (T (C h5 (C h34 h5)) (S h33))) h32) h4))) (C h4 (C (T h31 (C h5 h26)) h4))) (S h29))
  have h76 := h (M z v0) v0 v1
  have h77 := C h15 (T (T (T (T (T (T h37 h52) h50) h49) (C h4 (C (T (T (T (C h5 (C h5 (T (T h48 h46) h38))) (C h5 (C h70 h5))) (S h63)) h66) h4))) (C h4 (C (T (T (T h65 h67) (C h15 (C h61 h15))) (C h15 h71)) h4))) (S h73))
  have h78 := S h36
  have h79 := C h4 (C (T h31 (C h5 (T h33 (C h5 (C (S h34) h5))))) h4)
  have h80 := C h4 (C (T (C h5 h27) h32) h4)
  have h81 := C h5 (T (T (T (T (T h29 h80) h79) h78) h77) h72)
  have h82 := h (M (M v1 (M v1 v9)) v0) x v0
  have h83 := h v9 v0 v1
  have h84 := h (M v0 v9) x v9
  have h85 := h v10 v9 z
  have h86 := h (M (M v9 v10) x) x x
  have h87 := h z x v9
  have h88 := h v62 x v0
  have h89 := h v56 v1 v0
  have h90 := h v1 v1 v1
  have h91 := T (T h90 (C h20 (T (T (T (T (C (T (T (T (T (T (T (C h20 (C h59 h20)) (S h89)) h57) (C h45 (T (T (T (T h69 h88) (C h4 (T (C h61 h4) (C (T (T (T h37 (C h4 (T (T (T h39 (C h4 (C (T h51 (C h4 h87)) h4))) (S h86)) (C (C h12 (T h85 (C h12 (C h7 h12)))) h4)))) (S h84)) (C h45 h83)) h4)))) (S h82)) (C (C h20 (C h20 (T h26 h81))) h45)))) (S h76)) h75) h27) h20) h25) (C h4 (C (T (C h20 (S h24)) h23) h4))) (C h4 (C (T h22 (C h20 h17)) h4))) (S h19)))) h18
  have h92 := h z y z
  have h93 := C h91 (T (C (T (T (C h15 (S h92)) h77) h72) h91) (C h16 h15))
  have h94 := T (T h17 (C h20 (T (T (T (T h19 (C h4 (C (T (C h20 h18) h23) h4))) (C h4 (C (T h22 (C h20 h24)) h4))) (S h25)) (C (T (T (T (T (T (T h26 h81) h76) (C h45 (T (T (T (T (C (C h20 (C h20 (T h75 h27))) h45) h82) (C h4 (T (C (T (T (T (C h45 (S h83)) h84) (C h4 (T (T (T (C (C h12 (T (C h12 (C h16 h12)) (S h85))) h4) h86) (C h4 (C (T (C h4 (S h87)) h41) h4))) h40))) h38) h4) (C h70 h4)))) (S h88)) h60))) h58) h89) (C h20 (C h68 h20))) h20)))) (S h90)
  have h95 := C h15 h92
  let v96 := M v55 y
  have h97 := h z y y
  T (T h26 (C h5 (T (T (T (h v28 x y) (C h4 (C (T (T (T (C h94 (T (T (C h94 (T (T (T (T (T (T h29 h80) h79) h78) h77) h72) (C (T (T h97 (C h15 (T (T (T (T (T (h (M (M y v35) y) x y) (C h4 (C (T (C h15 (S h97)) h95) h4))) (S (h v96 x y))) (h v96 v1 y)) h93) h14))) (C h15 (T h13 (C h15 (C h7 h15))))) h94))) (S (h (M v0 y) v1 y))) (C (T (T h71 h74) h95) h94))) h93) h14) (C h12 h11)) h4))) (C h4 (C (T (T (T (C h12 (S h11)) (h v10 z z)) (C h5 (C h7 h5))) (C h5 h2)) h4))) (S (h (M v3 z) x z))))) (S h2)

