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
theorem Equation572_implies_Equation1181 (G: Type _) [Magma G] (h: Equation572 G) : Equation1181 G := fun x y z =>
  let v0 := M z x
  let v1 := M z v0
  let v2 := M v1 y
  let v3 := M y v2
  have h4 := h v3 y y
  have h5 := S h4
  have h6 := h y v3 y
  have h7 := S h6
  have h8 := h v1 y y
  have h9 := R y
  have h10 := R v3
  have h11 := C h10 (C h9 h8)
  have h12 := h v1 z v1
  have h13 := h z v1 z
  have h14 := S h13
  have h15 := h v0 v1 v0
  have h16 := S h15
  have h17 := h z v0 v0
  have h18 := R v1
  have h19 := C h18 h17
  have h20 := T h19 h16
  have h21 := R z
  have h22 := C h21 h20
  have h23 := C h21 h22
  have h24 := C h21 h23
  have h25 := h v1 z z
  have h26 := C h21 (T (T h22 h25) h24)
  have h27 := C h18 (S h17)
  have h28 := T h15 h27
  have h29 := C h21 h28
  have h30 := C h21 h29
  have h31 := C h18 (T h30 h26)
  have h32 := C h18 (T h31 h14)
  have h33 := C h18 h32
  have h34 := h z v1 v1
  have h35 := C h18 (T (T (T h31 h14) h34) h33)
  have h36 := S h25
  have h37 := C h21 h30
  have h38 := C h21 (T (T h37 h36) h29)
  have h39 := C h18 (T h38 h23)
  have h40 := C h18 (T h13 h39)
  have h41 := h v0 z v2
  have h42 := S h41
  have h43 := S h34
  have h44 := C h18 h40
  have h45 := C h18 (T (T (T h44 h43) h13) h39)
  have h46 := C h18 (C h18 h28)
  have h47 := C h18 (T h46 h45)
  have h48 := R v0
  have h49 := h v1 v0 v1
  have h50 := R v2
  have h51 := C h50 (T h49 (C h48 (T h47 h43)))
  have h52 := S h8
  have h53 := C h50 h52
  have h54 := h y v2 y
  have h55 := C h50 (T (T h54 h53) h51)
  have h56 := C h9 (T (C h21 (T (T (T (T (T (C h21 h55) h42) h15) h27) h40) h35)) (S h12))
  have h57 := h v2 y z
  have h58 := h v2 y v2
  have h59 := S h58
  have h60 := S h54
  have h61 := C h50 h8
  have h62 := C h18 (C h18 h20)
  have h63 := C h18 (T h35 h62)
  have h64 := C h50 (T (C h48 (T h34 h63)) (S h49))
  have h65 := C h50 (T (T h64 h61) h60)
  have h66 := C h10 (T h57 h56)
  have h67 := C h50 (T (T (T (T (T h66 h11) h7) h54) h53) h51)
  have h68 := C h50 (C h50 (T h67 h65))
  have h69 := h v3 v2 v2
  have h70 := C h9 (T h69 h68)
  have h71 := C h10 (T (T (T h70 h59) h57) h56)
  have h72 := C h10 (T (T h71 h11) h7)
  have h73 := S h69
  have h74 := S h57
  have h75 := C h9 (T h12 (C h21 (T (T (T (T (T h45 h32) h19) h16) h41) (C h21 h65))))
  have h76 := C h10 (T h75 h74)
  have h77 := C h10 (C h9 h52)
  have h78 := C h50 (T (T (T (T (T h64 h61) h60) h6) h77) h76)
  have h79 := C h50 (C h50 (T h55 h78))
  have h80 := C h9 (T h79 h73)
  have h81 := C h10 (T (T (T h75 h74) h58) h80)
  have h82 := h y v3 v3
  have h83 := C h10 (T (T h6 h77) h81)
  have h84 := h v3 y v3
  have h85 := C h9 (T h70 (C h9 (T (T (T h79 h73) h84) (C h9 (T (C h10 (T (T (T (T (C h10 h83) (S h82)) h6) h77) h81)) h72)))))
  have h86 := C h9 (T (C h9 (T (T (T (C h9 (T h83 (C h10 (T (T (T (T h71 h11) h7) h82) (C h10 h72))))) (S h84)) h69) h68)) h80)
  have h87 := h v3 z v1
  have h88 := S h87
  have h89 := R (M v3 z)
  have h90 := T (T h4 h86) h52
  have h91 := T (T h8 h85) h5
  have h92 := C h91 (T h44 h43)
  have h93 := C h21 (T (C h10 (T (T h34 h63) (C h91 (T h46 h92)))) (C h90 (C h90 h89)))
  have h94 := C h21 (T (C h91 (C h91 h89)) (C h10 (T (T (C h90 (T (C h90 (T h34 h33)) h62)) h47) h43)))
  have h95 := h v1 v2 v1
  have h96 := h y v3 v1
  have h97 := C h50 (T (T (T (T (C h91 (C h18 (C h18 (T h58 h80)))) (S h96)) h6) h77) h76)
  have h98 := R x
  T (T (T (T (T (T (h x z z) (C h21 (T (T (T (T (C h21 (T (T (T (T (T (T (T (C h21 (C h98 (T (h z x z) (C h98 (T (T (T (T (T (T (T (T (T h30 h26) (C h21 (T (T (T (T (T (T h37 h36) h8) h85) h5) h87) h94))) (C h21 (T (T (T (T (T (T (T h93 h88) h4) h86) h52) h95) h97) h67))) h42) h15) h27) h40) h35) h92))))) (S (h v3 z x))) h4) h86) h52) h95) h97) h67)) (C h21 (T (T (T (T (T (T (T h78 (C h50 (T (T (T (T h66 h11) h7) h96) (C h90 (C h18 (C h18 (T h70 h59))))))) (S h95)) h8) h85) h5) h87) h94))) (C h21 (T (T (T (T (T (T h93 h88) h4) h86) h52) h25) h24))) h38) h23))) h37) h36) h8) h85) h5

