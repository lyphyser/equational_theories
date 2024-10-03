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
theorem Equation572_implies_Equation2271 (G: Type _) [Magma G] (h: Equation572 G) : Equation2271 G := fun x y z =>
  let v0 := M y z
  let v1 := M y v0
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
  have h17 := h v1 v0 z
  have h18 := S h17
  have h19 := h v0 v1 v0
  have h20 := S h19
  have h21 := h y v0 v0
  have h22 := R v1
  have h23 := C h22 h21
  have h24 := T h23 h20
  have h25 := C h22 h24
  have h26 := h y v1 y
  have h27 := S h26
  have h28 := C h15 h24
  have h29 := C h15 h28
  have h30 := C h15 h29
  have h31 := h v1 y y
  have h32 := C h15 (T (T h28 h31) h30)
  have h33 := S h21
  have h34 := C h22 h33
  have h35 := T h19 h34
  have h36 := C h15 h35
  have h37 := C h15 h36
  have h38 := C h22 (T h37 h32)
  have h39 := C h22 (T h38 h27)
  have h40 := C h22 h39
  have h41 := h y v1 v1
  have h42 := S h31
  have h43 := C h15 h37
  have h44 := C h15 (T (T h43 h42) h36)
  have h45 := h v1 y z
  have h46 := C h22 (T h44 h29)
  have h47 := S h41
  have h48 := C h22 (T h26 h46)
  have h49 := C h22 h48
  have h50 := C h22 (T (T (T h49 h47) h26) h46)
  have h51 := C h22 h35
  have h52 := C h22 h51
  have h53 := R z
  have h54 := h y z v1
  have h55 := C h15 (T (C h15 (T (T (T (C h15 (C h53 (T h54 (C h53 (T (T h52 h50) h39))))) (S h45)) h31) h30)) h44)
  have h56 := h z y y
  have h57 := S h9
  have h58 := C h7 h6
  have h59 := R v0
  have h60 := h v0 z v0
  have h61 := C h59 (T h54 (C h53 (T (T (T (T (T (T h52 h50) h39) h23) h20) h60) (C h53 (T (T (T (T (C h59 (T (C h59 (C h59 h10)) (C h59 (C h59 (T (T (T (T h58 h57) h56) h55) h42))))) h33) h41) h40) h25)))))
  have h62 := C h11 (T h61 h18)
  have h63 := C h11 (T (T h62 h16) h14)
  have h64 := S h54
  have h65 := C h22 h25
  have h66 := C h22 (T (T (T h38 h27) h41) h40)
  have h67 := T h58 h57
  have h68 := S h56
  have h69 := C h15 (T h32 (C h15 (T (T (T h43 h42) h45) (C h15 (C h53 (T (C h53 (T (T h48 h66) h65)) h64))))))
  have h70 := C h59 (T (C h53 (T (T (T (T (T (T (C h53 (T (T (T (T h51 h49) h47) h21) (C h59 (T (C h59 (C h59 (T (T (T (T h31 h69) h68) h9) h8))) (C h59 (C h59 h67)))))) (S h60)) h19) h34) h48) h66) h65)) h64)
  have h71 := C h11 (T h17 h70)
  have h72 := C h11 (C h15 (C h15 h67))
  have h73 := h v3 z v3
  have h74 := S h73
  have h75 := C h7 (C h7 (T (T (T (T h61 h18) h31) h69) h68))
  have h76 := h v1 y v1
  have h77 := S h76
  have h78 := h v0 y v2
  have h79 := C h11 (T (T h13 h72) h71)
  have h80 := C h15 (T (T (T (T (T (C h15 h79) (S h78)) h19) h34) h48) h66)
  have h81 := C h7 (T (T (T h80 h77) h17) h70)
  have h82 := h v2 v3 y
  have h83 := C h7 (T h82 h81)
  have h84 := C h7 (T (T (T (T (T (T (T (T h80 h77) h31) h69) h68) h9) h8) h83) h75)
  have h85 := C (T (T h31 h69) h68) (T h82 h84)
  have h86 := C h11 (T (T (T (T h85 h74) h13) h72) h71)
  have h87 := C h11 (T h86 h63)
  have h88 := S h82
  have h89 := C h15 (T (T (T (T (T h50 h39) h23) h20) h78) (C h15 h63))
  have h90 := C h7 (T (C h7 (T (T (T h61 h18) h76) h89)) h88)
  have h91 := C h7 (C h7 (T (T (T (T h56 h55) h42) h17) h70))
  have h92 := C h7 (T (T (T (T (T (T (T (T h91 h90) h58) h57) h56) h55) h42) h76) h89)
  have h93 := C (T (T h56 h55) h42) (T h92 h88)
  have h94 := C h11 (T (T (T (T h87 h12) h5) h73) h93)
  have h95 := h v1 v2 v2
  have h96 := C h11 (T (T (T (T h62 h16) h14) h73) h93)
  have h97 := R x
  T (T (T (T (h x v2 v3) (C h11 (T (T (T (T (T (T (T (T (T (C h7 (T (T (T (T (C h7 (C h97 (C h97 (T (T (T h95 h94) h86) h63)))) (S (h v2 v3 x))) h82) h84) (C h7 (T (T (T (T (T (T (T (T (T (T h91 h90) h58) h57) h56) h55) h42) h95) h94) h86) h63)))) (C h7 (T (T (C h7 (T (T (T (T (T (T (T (T (T (T h79 h96) (C h11 (T (T (T (T h85 h74) h4) (C h11 (C h11 (C h11 h67)))) (C h11 (T h79 h96))))) (S h95)) h31) h69) h68) h9) h8) h83) h75)) h92) h81))) h90) h58) h57) h56) h55) h42) h95) h94))) h87) h12) h5

