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
theorem Equation2925_implies_Equation26 (G: Type _) [Magma G] (h: Equation2925 G) : Equation26 G := fun x y =>
  let v0 := M x y
  let v1 := M v0 y
  have h2 := h v1 v1 v0
  have h3 := S h2
  have h4 := R v0
  have h5 := R v1
  let v6 := M v1 v0
  have h7 := h v6 x x
  have h8 := S h7
  have h9 := R x
  have h10 := h y v1 x
  have h11 := S h10
  let v12 := M (M v1 (M y x)) v1
  have h13 := h v12 v0 x
  have h14 := h v12 x x
  have h15 := C (C (C h9 (T (T (T (C (C (C h9 h10) h9) h9) (S h14)) h13) (C (C (C h4 h11) h4) h9))) h9) h9
  let v16 := M v0 x
  have h17 := h v16 x x
  have h18 := R y
  have h19 := h x v1 y
  have h20 := S h19
  let v21 := M v6 v1
  have h22 := h v21 v1 y
  have h23 := S h22
  have h24 := h x v1 x
  have h25 := S h24
  have h26 := C h5 h25
  have h27 := C h5 h24
  have h28 := h x x y
  have h29 := S h28
  have h30 := C (T (C (T (C h5 h29) h27) h5) (C (T h26 (C h5 h19)) h5)) h18
  let v31 := M (M x v0) x
  have h32 := h v31 v1 y
  have h33 := h v0 y y
  have h34 := C (T (T (T (C (C h9 (S h33)) h9) h32) h30) h23) h18
  let v35 := M y v1
  let v36 := M v35 y
  have h37 := h v36 x y
  have h38 := h v36 x x
  have h39 := h v1 v1 x
  have h40 := S h39
  let v41 := M (M v1 (M v1 x)) v1
  have h42 := h v41 y x
  have h43 := h v41 x x
  let v44 := M x v1
  have h45 := h (M v44 x) x x
  have h46 := h v1 x y
  let v47 := M (M x (M v1 y)) x
  have h48 := h v47 x y
  have h49 := C (T h48 (C (T (T (T (T (T (T (C (C h9 (S h46)) h9) h45) (C (C (C h9 (T (T (T (C (C (C h9 h39) h9) h9) (S h43)) h42) (C (C (C h18 h40) h18) h9))) h9) h9)) (S h38)) h37) h34) h20) h18)) h9
  have h50 := h v47 x x
  have h51 := S h50
  have h52 := S h37
  have h53 := S h32
  have h54 := C (T (C (T (C h5 h20) h27) h5) (C (T h26 (C h5 h28)) h5)) h18
  have h55 := C (T (T (T h22 h54) h53) (C (C h9 h33) h9)) h18
  have h56 := C (T (C (T (T (T (T (T (T h19 h55) h52) h38) (C (C (C h9 (T (T (T (C (C (C h18 h39) h18) h9) (S h42)) h43) (C (C (C h9 h40) h9) h9))) h9) h9)) (S h45)) (C (C h9 h46) h9)) h18) (S h48)) h9
  have h57 := S h17
  have h58 := C (C (C h9 (T (T (T (C (C (C h4 h10) h4) h9) (S h13)) h14) (C (C (C h9 h11) h9) h9))) h9) h9
  have h59 := C (C h9 (T (T (T h7 h58) h57) h56)) h9
  have h60 := h (M (M x v6) x) x v0
  have h61 := S h60
  have h62 := h v1 x v0
  have h63 := C (T (C (C h9 h3) h9) (C (C h9 h62) h9)) h4
  let v64 := M (M v1 v6) v1
  have h65 := h v64 x v0
  have h66 := h v64 y v0
  have h67 := h v0 v1 x
  have h68 := S h67
  let v69 := M (M v1 v16) v1
  have h70 := h v69 x x
  have h71 := C (C h5 (T (T (T (T (T h70 (C (T (T (C (T (T (C h9 h68) (C (T (T (T h19 h55) h52) (C (C h18 h2) h18)) h4)) (S h66)) h9) (C (T (T (T h65 h63) h61) h59) h9)) h51) h9)) h49) h17) h15) h8)) h5
  have h72 := h v69 y x
  have h73 := h (M (M y v0) y) x y
  have h74 := h x y y
  have h75 := C h9 h25
  have h76 := C h9 h24
  have h77 := C (T (C h9 h29) h76) h9
  have h78 := h v31 x y
  have h79 := C (C h5 (T (C (T (T (T (T (T (T h22 h54) h53) h78) (C (T h77 (C (T h75 (C h9 h74)) h9)) h18)) (S h73)) (C (C h18 h67) h18)) h9) (S h72))) h5
  have h80 := h v0 v0 x
  let v81 := M v0 v16
  have h82 := h (M v81 v0) x x
  have h83 := C (T (T (C (C h5 (T h82 (C (T (T (T (C (C h9 (S h80)) h9) h32) h30) h23) h9))) h5) h79) h71) h4
  have h84 := h v81 v1 v0
  have h85 := S h84
  have h86 := S h78
  have h87 := C (T h75 (C h9 h28)) h9
  have h88 := C (T (T (C (C h5 (T (T (T (T (T h7 h58) h57) h56) (C (T (T h50 (C (T (T (T (C (C h9 (T (T (T h49 h17) h15) h8)) h9) h60) (C (T (C (C h9 (S h62)) h9) (C (C h9 h2) h9)) h4)) (S h65)) h9)) (C (T (T h66 (C (T (T (T (C (C h18 h3) h18) h37) h34) h20) h4)) (C h9 h67)) h9)) h9)) (S h70))) h5) (C (C h5 (T h72 (C (T (T (T (T (T (T (C (C h18 h68) h18) h73) (C (T (C (T (C h9 (S h74)) h76) h9) h87) h18)) h86) h32) h30) h23) h9))) h5)) (C (C h5 (T (C (T (T (T h22 h54) h53) (C (C h9 h80) h9)) h9) (S h82))) h5)) h4
  have h89 := T (T h2 h88) h85
  have h90 := h v35 x y
  have h91 := h v81 v1 v1
  let v92 := M v1 (M v1 v1)
  have h93 := h v92 x v1
  have h94 := h (M v92 v1) y v1
  have h95 := h v1 v1 v1
  have h96 := h (M (M x v44) x) x v1
  have h97 := h x x v1
  have h98 := h x v1 v1
  have h99 := C (T (C h9 (S h98)) h76) h9
  have h100 := C (T h75 (C h9 h98)) h9
  have h101 := h x v0 v1
  have h102 := S h101
  have h103 := h (M (M v0 v44) v0) x v1
  T (T (T (T (T (T h19 (C (T (T (T (T (T (T h22 h54) h53) h78) (C (T h77 (C (T h75 (C h9 (T (T h19 h55) h52))) h9)) h18)) (S h90)) (C h18 (T (T (T (T h2 h88) h85) h91) (C (C (T (T (T (C h5 (C (T (T h84 h83) h3) h5)) h93) (C (T (T (T (T (C (C h9 (T h94 (C (T (T (T (C (C h18 (S h95)) h18) h37) h34) h20) h5))) h9) h96) (C (T (C (T (C h9 (S h97)) h76) h9) h100) h5)) (C (T h99 (C (T h75 (C h9 h101)) h9)) h5)) (S h103)) h5)) h102) h5) h5)))) h18)) (C (T (T (T (T (T (T (T (T (T (T (C h18 (T (T (T (T (C (C (T (T (T h101 (C (T (T (T (T h103 (C (T (C (T (C h9 h102) h76) h9) h100) h5)) (C (T h99 (C (T h75 (C h9 h97)) h9)) h5)) (S h96)) (C (C h9 (T (C (T (T (T h19 h55) h52) (C (C h18 h95) h18)) h5) (S h94))) h9)) h5)) (S h93)) (C h5 (C h89 h5))) h5) h5) (S h91)) h84) h83) h3)) h90) (C (T (C (T (C h9 (T (T h37 h34) h20)) h76) h9) h87) h18)) h86) h32) h30) h23) (h v21 v1 x)) (C (T (T (T (T (T h79 h71) h65) h63) h61) h59) h9)) h51) (C (C h9 (C h89 h18)) h9)) h18)) (S (h v81 x y))) h84) h83) h3

