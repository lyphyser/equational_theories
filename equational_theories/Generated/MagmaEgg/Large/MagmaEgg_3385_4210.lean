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
theorem Equation3385_implies_Equation4210 (G: Type _) [Magma G] (h: Equation3385 G) : Equation4210 G := fun x y z =>
  let v0 := M z y
  let v1 := M v0 x
  let v2 := M v1 z
  have h3 := R v2
  have h4 := h z x y
  have h5 := S h4
  let v6 := M x y
  have h7 := h z v6 v1
  have h8 := h v0 x y
  have h9 := S h8
  have h10 := R v6
  have h11 := h y v0 v6
  have h12 := T h11 (C h10 h9)
  have h13 := R z
  have h14 := h z y v2
  have h15 := S h14
  have h16 := h y v1 z
  have h17 := h v0 x z
  have h18 := S h17
  let v19 := M x z
  have h20 := h z (M v0 v19) v2
  have h21 := S h20
  have h22 := h v0 v19 v2
  have h23 := S h22
  have h24 := h x z v1
  have h25 := h z v0 x
  have h26 := R v1
  have h27 := R v0
  have h28 := C h3 (C h27 (C (T (C h26 h25) (S h24)) h3))
  have h29 := h v0 (M v1 (M z v0)) v2
  have h30 := h v1 z v0
  have h31 := C h3 (C h13 (C (T (T (T h30 h29) h28) h23) h3))
  have h32 := h z v2 v2
  have h33 := T (T (T h32 h31) h21) h18
  have h34 := R y
  have h35 := C h3 (T (C h34 h33) h16)
  have h36 := h y z v2
  have h37 := C h13 (C h34 (T (T h36 h35) h15))
  have h38 := h y y z
  have h39 := h y y x
  have h40 := h y x y
  have h41 := S h40
  have h42 := h y v6 v1
  have h43 := h y z y
  have h44 := S h36
  have h45 := S h32
  have h46 := S h30
  have h47 := S h29
  have h48 := S h25
  have h49 := C h3 (C h27 (C (T h24 (C h26 h48)) h3))
  have h50 := C (T (T (T h22 h49) h47) h46) h3
  have h51 := C h3 (C h13 h50)
  have h52 := T (T (T h17 h20) h51) h45
  have h53 := S h16
  have h54 := C h3 (T h53 (C h34 h52))
  have h55 := C h34 (T (C h26 (T (T (T (T h14 h54) h44) h43) (C h34 h12))) (S h42))
  have h56 := h v1 z y
  have h57 := h y v2 v0
  have h58 := S h57
  have h59 := h z y v0
  have h60 := S h59
  have h61 := h y y v6
  have h62 := C h27 (T (T (T (C h10 (T h56 h55)) (S h61)) h38) h37)
  have h63 := C h3 (T h62 h60)
  have h64 := h v0 v6 v2
  have h65 := C h34 (T h64 h63)
  have h66 := C h27 (T h8 h65)
  have h67 := R x
  have h68 := h x v0 v1
  have h69 := C h34 (T (T h68 (C h26 (T (T (T (T (C h67 (T (T h66 h58) (C h34 (T (T h56 h55) h41)))) (S h39)) h38) h37) (C h13 h12)))) (S h7))
  have h70 := h x z y
  have h71 := h x z v2
  have h72 := S h71
  have h73 := C h67 h52
  have h74 := h x v1 v2
  have h75 := S h74
  have h76 := S h56
  have h77 := T (C h10 h8) (S h11)
  have h78 := C h34 (T h42 (C h26 (T (T (T (T (C h34 h77) (S h43)) h36) h35) h15)))
  have h79 := C (T (T (T (T (T (T h40 h78) h76) h30) h29) h28) h23) h3
  let v80 := M y x
  have h81 := h z v80 v2
  have h82 := C h3 (C h67 (C (T (T (T h81 (C h3 (C h13 h79))) h21) h18) h3))
  have h83 := h x (M z v80) v2
  have h84 := h z y x
  have h85 := h y x z
  have h86 := S h85
  have h87 := S h70
  have h88 := S h68
  have h89 := S h38
  have h90 := C h13 (C h34 (T (T h14 h54) h44))
  have h91 := C h27 (T (T (T h90 h89) h61) (C h10 (T h78 h76)))
  have h92 := C h3 (T h59 h91)
  have h93 := C h34 (T h92 (S h64))
  have h94 := C h67 (T (T (C h34 (T (T h40 h78) h76)) h57) (C h27 (T h93 h9)))
  have h95 := C h34 (T (T h7 (C h26 (T (T (T (T (C h13 h77) h90) h89) h39) h94))) h88)
  have h96 := C h13 (T (T (T (T (T (T (T h32 h31) h21) h18) h8) h65) (C h34 (T (T (T (T (T h92 (C h3 (T (T (T (T (T (T h62 h60) h84) h83) h82) h75) h73))) h72) h70) h69) h5))) (C h34 (T (T h4 h95) h87)))
  have h97 := h z v1 z
  have h98 := T (T (T (T (T h97 h96) h86) h40) h78) h76
  have h99 := S h84
  have h100 := S h83
  have h101 := C h3 (C h67 (C (T (T (T h17 h20) (C h3 (C h13 (C (T (T (T (T (T (T h22 h49) h47) h46) h56) h55) h41) h3)))) (S h81)) h3))
  have h102 := C h67 h33
  have h103 := C h13 (T (T (T (T (T (T (T (C h34 (T (T h70 h69) h5)) (C h34 (T (T (T (T (T h4 h95) h87) h71) (C h3 (T (T (T (T (T (T h102 h74) h101) h100) h99) h59) h91))) h63))) h93) h9) h17) h20) h51) h45)
  have h104 := T (T (T (T (T h56 h55) h41) h85) h103) (S h97)
  have h105 := h z z v2
  T (T (T (T (h x y x) (h x (M x v80) v2)) (C h3 (C h67 (C (T (T (T (T (T (T (T (h x v80 v2) (C h3 (C h67 (T h79 h50)))) (S (h x v2 v2))) (C h67 h104)) h48) (h z v0 v1)) (C h26 (T (T (T (T (T (T (T (T (T (T (C h13 (T h66 h58)) h53) (h y v1 v0)) (C h27 h76)) (C h27 (T (h v1 z z) (C h13 (T (T (C h26 (T h105 (C h104 (T (T (T (T h96 h86) h40) h78) h76)))) (C h26 (T (T (T (T (T (T (C h98 (T (T (T (T h56 h55) h41) h85) h103)) (S h105)) (h z z v0)) (C h27 (T (T (T (T (T (T (T (T (T (C h13 (T h25 (C h67 h98))) (S (h x v1 z))) h74) h101) h100) h99) h14) h54) h44) h43))) (S (h y y v0))) h39) h94))) h88))))) (S (h z x v0))) h4) h95) h87) h71) (C h104 (T (T (T (T h102 h74) h101) h100) h99))))) (C h26 (T (T (T (T (C h98 (T (T (T (T h84 h83) h82) h75) h73)) h72) h70) h69) h5))) h3)))) (S (h x (M v1 (M z x)) v2))) (S (h v1 z x))

