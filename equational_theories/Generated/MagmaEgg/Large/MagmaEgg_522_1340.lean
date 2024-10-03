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
theorem Equation522_implies_Equation1340 (G: Type _) [Magma G] (h: Equation522 G) : Equation1340 G := fun x y z =>
  let v0 := M y z
  let v1 := M v0 z
  let v2 := M v1 x
  let v3 := M y v2
  have h4 := h z v1 v1
  have h5 := S h4
  have h6 := h v0 v1 z
  have h7 := R v1
  have h8 := R v0
  have h9 := C h8 (T (C h7 h6) h5)
  have h10 := R v3
  have h11 := S h6
  have h12 := C h8 (T h4 (C h7 h11))
  have h13 := h v1 v1 v0
  have h14 := S h13
  have h15 := C h7 (C h7 h12)
  have h16 := T (T h15 h14) h12
  have h17 := C h7 (C h7 h9)
  have h18 := h v1 z v1
  have h19 := S h18
  have h20 := R z
  have h21 := C h20 (T h13 h17)
  have h22 := C h20 (T (T (T (C h20 h21) h19) h13) h17)
  have h23 := h v0 z z
  have h24 := C h10 (T (T (T (C h20 (T h23 h22)) h19) h13) h17)
  have h25 := S h23
  have h26 := C h20 (T h15 h14)
  have h27 := C h20 (T (T (T h15 h14) h18) (C h20 h26))
  have h28 := C h20 (T h27 h25)
  have h29 := h v0 y z
  have h30 := h y v3 z
  have h31 := S h30
  have h32 := C h10 (C h10 (T (T (T h15 h14) h18) h28))
  have h33 := h v1 v3 v1
  have h34 := T (T h33 h32) h31
  have h35 := C h20 (T (T (T (C h34 (T h4 (C h34 (T (T (T h11 h23) h22) h26)))) (S h29)) h23) h22)
  have h36 := S h33
  have h37 := C h10 h24
  have h38 := T (T h30 h37) h36
  have h39 := C h20 (T (T (T h27 h25) h29) (C h38 (T (C h38 (T (T (T h21 h27) h25) h6)) h5)))
  have h40 := h y v3 v2
  have h41 := S h40
  have h42 := C h10 h41
  have h43 := h v2 v3 v3
  have h44 := h v2 v1 v1
  have h45 := S h44
  have h46 := R v2
  have h47 := C h46 h9
  have h48 := C h46 h16
  have h49 := C h46 (T (T (T h35 h19) h13) h17)
  have h50 := h v1 v2 v2
  have h51 := S h50
  have h52 := S h43
  have h53 := C h10 h40
  have h54 := C h38 (T h53 h52)
  have h55 := h v3 v2 y
  have h56 := C h46 (T h55 (C h46 (C h46 h54)))
  have h57 := C h46 (T (T (T h56 h51) h18) h39)
  have h58 := C h34 (T h43 h42)
  have h59 := C h46 (T (C h46 (C h46 h58)) (S h55))
  have h60 := C h10 (T (T (T (T (T h41 h30) h37) h36) h50) h59)
  have h61 := C h10 (T h43 h60)
  have h62 := C h46 (T (T (T (T (T (T h61 h41) h30) h37) h36) h50) h59)
  have h63 := C h10 (T (T (T (T (T h56 h51) h33) h32) h31) h40)
  have h64 := C h10 (T h63 h52)
  have h65 := h y v2 v2
  have h66 := C h46 (T (T (T (C h46 h62) (S h65)) h40) h64)
  have h67 := h v3 v2 v2
  have h68 := h v3 v3 v2
  have h69 := S h68
  have h70 := C h10 (C h10 (T h67 h66))
  have h71 := C h7 (T (T (T (T (T (T (T (T h70 h69) h67) h66) h62) h57) h49) h48) h47)
  have h72 := R (M v3 (M v3 v3))
  have h73 := C h38 h72
  have h74 := h v3 y v3
  have h75 := C h7 (T (T (T h70 h69) h74) (C h38 (T h73 h71)))
  have h76 := R y
  have h77 := C h76 (T (T (T (T h73 h75) h45) h43) h42)
  have h78 := S h67
  have h79 := C h46 (T (T (T (T (T (T h56 h51) h33) h32) h31) h40) h64)
  have h80 := C h46 (T (T (T h61 h41) h65) (C h46 h79))
  have h81 := C h10 (C h10 (T h80 h78))
  have h82 := S h74
  have h83 := C h34 h72
  have h84 := T (T (T h35 h19) h50) h59
  have h85 := C h46 h84
  have h86 := C h46 (T (T (T h15 h14) h18) h39)
  have h87 := C h46 (T (T h9 h13) h17)
  have h88 := C h46 h12
  have h89 := C h7 (T (T (T (T (T (T (T (T h88 h87) h86) h85) h79) h80) h78) h68) h81)
  have h90 := C h7 (T (T (T (C h34 (T h89 h83)) h82) h68) h81)
  have h91 := h v2 v2 v1
  have h92 := C h46 (C h46 (T (T h89 h75) h45))
  have h93 := S (h v2 x v2)
  have h94 := R x
  have h95 := h v1 v3 v2
  have h96 := h v1 v2 v0
  have h97 := T (T (T (T h56 h51) h96) (C h46 (T (T (T (T (T (T (T h87 h86) h85) h79) h80) h78) h68) h81))) (C h46 (T (T (T (T h70 h69) h74) h77) h54))
  have h98 := S h96
  have h99 := C h46 (T (T (T (T (T (T (T h70 h69) h67) h66) h62) h57) h49) h48)
  have h100 := C h46 (T (T (T (T h58 (C h76 (T (T (T (T h53 h52) h44) h90) h83))) h82) h68) h81)
  T (T (h x v3 v1) (C h10 (C h10 (T (T (T (T (T (T (C h34 (T (T (T (T (T (T (T (C h94 (T h18 h39)) (C h94 h84)) (C h94 h97)) (C h94 (T (T (T (T h100 h99) h98) h95) (C h10 (T (T (T (T (T (T (C h10 (T (T (T (T h100 h99) h98) h50) h59)) h63) h52) h44) h90) h71) (C h7 (T (T (T (T (T (T h88 h87) h86) h85) h79) h80) h78))))))) (C h94 (T (T (T (C h10 (T (T (T (T (T (T (C h7 (T (T (T (T (T (T h67 h66) h62) h57) h49) h48) h47)) h89) h75) h45) h43) h60) (C h10 h97))) (S h95)) (h v1 x x)) (C h94 (T (T (T (C h94 (C h94 (T h91 h92))) h93) h91) h92))))) h93) h91) h92)) (C h38 (R (M v2 (M v2 v2))))) (C h7 (T (T (T (C h46 (C h46 (T (T h44 h90) h71))) (S h91)) h44) h90))) (S (h v3 v1 v3))) h74) h77) (C h38 (T (T (T (T (C h10 (T (T (T (T h30 h37) h36) h18) h39)) (C h10 (T h35 h28))) h24) (C h10 h16)) (C h10 h9))))))) (S (h v3 v3 v1))

