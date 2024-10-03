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
theorem Equation572_implies_Equation2482 (G: Type _) [Magma G] (h: Equation572 G) : Equation2482 G := fun x y z =>
  let v0 := M y z
  let v1 := M v0 y
  let v2 := M x v1
  let v3 := M v2 z
  have h4 := h v3 v2 v2
  have h5 := S h4
  have h6 := h v2 z z
  have h7 := R v3
  have h8 := C h7 (S h6)
  have h9 := h z v3 z
  have h10 := T h9 h8
  have h11 := R v2
  have h12 := C h11 (C h11 (C h11 h10))
  have h13 := h v3 v2 y
  have h14 := S h13
  have h15 := R y
  have h16 := C h11 (C h15 (C h15 h10))
  have h17 := h v0 y y
  have h18 := S h17
  have h19 := h v1 y z
  have h20 := S h19
  have h21 := h y v1 y
  have h22 := S h21
  have h23 := R v1
  have h24 := C h23 h17
  have h25 := T h24 h22
  have h26 := R z
  have h27 := h y z v1
  have h28 := C h15 (C h26 (T h27 (C h26 (C h23 h25))))
  have h29 := h z y y
  have h30 := h z v0 v3
  have h31 := S h30
  have h32 := h v0 v1 v1
  have h33 := R v0
  have h34 := C h33 h25
  have h35 := C h33 h34
  have h36 := C h23 h18
  have h37 := T h21 h36
  have h38 := C h33 h37
  have h39 := h v1 v0 v0
  have h40 := C h33 h38
  have h41 := h v0 v1 v0
  have h42 := C h33 (C h7 (C h7 (T (T (T h24 h22) h27) (C h26 (T (C h23 (T h24 (C h23 (T (T h18 h41) (C h23 (T (C h33 (T (T (C h33 h40) (S h39)) h38)) h35)))))) (S h32))))))
  have h43 := h v1 v0 v3
  have h44 := C h15 (T (T (T (T (T (T h28 h20) h43) h42) h31) h29) (C h15 (C h15 (T h28 h20))))
  have h45 := C h15 (T h44 h18)
  have h46 := T (T (T (T h43 h42) h31) h29) h45
  have h47 := C h11 h46
  have h48 := C h11 (T (T h47 h16) h14)
  have h49 := S h43
  have h50 := S h27
  have h51 := C h33 (C h7 (C h7 (T (T (T (C h26 (T h32 (C h23 (T (C h23 (T (T (C h23 (T h40 (C h33 (T (T h34 h39) (C h33 h35))))) (S h41)) h17)) h36)))) h50) h21) h36)))
  have h52 := S h29
  have h53 := C h15 (C h26 (T (C h26 (C h23 h37)) h50))
  have h54 := C h15 (T (T (T (T (T (T (C h15 (C h15 (T h19 h53))) h52) h30) h51) h49) h19) h53)
  have h55 := C h15 (T h17 h54)
  have h56 := T (T (T (T h55 h52) h30) h51) h49
  have h57 := C h11 h56
  have h58 := S h9
  have h59 := C h7 h6
  have h60 := T h59 h58
  have h61 := C h11 (C h15 (C h15 h60))
  have h62 := h v3 v1 v3
  have h63 := S h62
  have h64 := C h7 (C h7 h56)
  have h65 := h v0 y v2
  have h66 := C h11 (T (T h13 h61) h57)
  have h67 := C h15 (T (T (T (C h15 h66) (S h65)) h17) h54)
  have h68 := C h7 (T h67 h45)
  have h69 := h v2 v3 y
  have h70 := C h7 (T h69 h68)
  have h71 := C h7 (T (T (T (T (T h67 h52) h9) h8) h70) h64)
  have h72 := C h23 (T h69 h71)
  have h73 := C h11 (T (T (T (T h72 h63) h13) h61) h57)
  have h74 := C h11 (T h73 h48)
  have h75 := S h69
  have h76 := C h15 (T (T (T h44 h18) h65) (C h15 h48))
  have h77 := C h7 (T h55 h76)
  have h78 := C h7 (T h77 h75)
  have h79 := C h7 (C h7 h46)
  have h80 := C h7 (T (T (T (T (T h79 h78) h59) h58) h29) h76)
  have h81 := C h23 (T h80 h75)
  have h82 := C h11 (T (T (T (T h47 h16) h14) h62) h81)
  have h83 := C h11 h82
  have h84 := C h11 (T (T (T (T h74 h12) h5) h62) h81)
  have h85 := h v1 v2 v2
  have h86 := T (T h30 h51) h49
  have h87 := C h23 (T (T (T h83 h74) h12) h5)
  have h88 := h v2 v1 v2
  have h89 := T (T h43 h42) h31
  have h90 := S h88
  have h91 := C h11 (T h66 h82)
  have h92 := C h11 (C h11 (C h11 h60))
  have h93 := C h23 (T (T (T h4 h92) h91) (C h11 h73))
  have h94 := C h7 (T (T (T h93 h90) h69) h68)
  have h95 := C h7 (T (T (T h77 h75) h88) h87)
  have h96 := R x
  T (T (T (T (T (h x v2 v3) (C h11 (T (T (T (T (T (C h7 (T (T (T (T (T (C h7 (T (C h96 (T h88 h87)) (C h96 (T (T h93 h90) (C h96 (T (T (T h85 h84) h73) h48)))))) (S (h v2 v3 x))) h69) h71) (C h7 (T h79 h95))) (C h7 (T (T (T (T (T (T (T (T (T (T h94 h78) h59) h58) h30) h51) h49) h85) h84) h73) h48)))) (C h7 (T (T (T (T (T (T (C h7 (T (T (T (T (T (T (T (T (T (T h66 h82) (C h11 (T (T (T (T h72 h63) h4) h92) h91))) (S h85)) h43) h42) h31) h9) h8) h70) h95)) (C h7 (T h94 h64))) h80) h75) h88) (C h89 (T (T (T (T (T h83 h74) h12) h5) h62) (C h89 (T (T (T h80 h75) h88) h87))))) (C h86 (C h86 (R (M v1 v3))))))) (S (h v1 v3 v1))) h85) h84) h73))) h83) h74) h12) h5

