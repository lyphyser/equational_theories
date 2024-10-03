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
theorem Equation3404_implies_Equation4182 (G: Type _) [Magma G] (h: Equation3404 G) : Equation4182 G := fun x y z =>
  let v0 := M y z
  let v1 := M v0 z
  have h2 := h v0 z x
  have h3 := S h2
  have h4 := R x
  let v5 := M z (M x v0)
  let v6 := M v1 x
  have h7 := h x v0 v6
  have h8 := S h7
  have h9 := R (M v6 x)
  have h10 := h y z z
  have h11 := S h10
  let v12 := M z (M z y)
  have h13 := h z v12 v0
  have h14 := S h13
  have h15 := h v12 v1 z
  have h16 := S h15
  have h17 := R v1
  have h18 := h v1 v0 x
  have h19 := S h18
  have h20 := h z x v0
  have h21 := C h4 h20
  have h22 := h z x y
  have h23 := C h4 (S h22)
  have h24 := h v0 y x
  have h25 := R z
  have h26 := C h25 (T (T (T (T h24 h23) h21) h19) (C h17 h10))
  let v27 := M v0 y
  have h28 := h z v27 y
  have h29 := h v27 v0 z
  have h30 := h y z v0
  have h31 := h y z x
  have h32 := C h25 (S h31)
  let v33 := M x y
  have h34 := h v33 x z
  have h35 := h v33 x v1
  have h36 := S h35
  have h37 := h y v1 x
  have h38 := h y v1 v0
  have h39 := S h38
  have h40 := h v0 y v0
  have h41 := h z v0 y
  have h42 := R v0
  have h43 := S h34
  have h44 := C h25 h31
  have h45 := h y z v1
  have h46 := S h45
  have h47 := C h25 h46
  let v48 := M v1 y
  have h49 := h v48 v1 z
  have h50 := h z v48 v0
  have h51 := C h17 (T (T (T h50 (C h42 (T (T (T h49 h47) h44) h43))) (C h42 (T (T h34 h32) h41))) (S h40))
  have h52 := S h50
  have h53 := S h49
  have h54 := C h25 h45
  have h55 := C h42 (T h45 h51)
  have h56 := h v0 v1 v0
  have h57 := C h42 (T (C h17 (T (T h56 (C h42 (T (T (T (T (T (C h17 (T (T h55 h39) h37)) h36) h34) h32) h54) h53))) h52)) h51)
  have h58 := h v1 v1 v0
  have h59 := h v0 z y
  have h60 := h z (M y v0) v6
  have h61 := R (M v6 z)
  have h62 := h y v0 v1
  have h63 := h v1 y z
  have h64 := S h63
  have h65 := h v0 z v0
  let v66 := M v0 v0
  have h67 := h v66 v0 z
  have h68 := R y
  have h69 := h z v66 y
  have h70 := h v0 v0 v0
  have h71 := S (h v0 v0 z)
  have h72 := C h25 (T (T (T (T (T h24 h23) h21) h19) (h v1 v0 v0)) (C h42 (S (h z v0 v0))))
  have h73 := C h25 (T (C h17 (h z v1 y)) (S (h v0 y v1)))
  have h74 := h v1 v1 z
  have h75 := h z v1 v0
  have h76 := h v1 v0 z
  have h77 := C h25 (T (T (T (T (T (T (T h24 h23) h21) h19) h76) (C h25 (T (C h42 (T h75 (C h42 (T (T (T h74 h73) h72) h71)))) (S h70)))) h69) (C h68 (T h67 (C h25 (S h65)))))
  have h78 := S h24
  have h79 := C h4 h22
  have h80 := C h4 (S h20)
  have h81 := C h25 (T (T (T (T (C h17 h11) h18) h80) h79) h78)
  have h82 := R v6
  have h83 := h z v27 v6
  have h84 := S h75
  have h85 := S h58
  have h86 := S h41
  have h87 := C h17 (T (T (T h40 (C h42 (T (T h86 h44) h43))) (C h42 (T (T (T h34 h32) h54) h53))) h52)
  have h88 := S h37
  have h89 := C h42 (T h87 (C h17 (T (T h50 (C h42 (T (T (T (T (T h49 h47) h44) h43) h35) (C h17 (T (T h88 h38) (C h42 (T h87 h46))))))) (S h56))))
  have h90 := C h25 (T (T (T (T (T (T (T (C h68 (T (C h25 h65) (S h67))) (S h69)) (C h25 (T h70 (C h42 (T (C h42 (T (T h55 h89) h85)) h84))))) (S h76)) h18) h80) h79) h78)
  have h91 := h y y v1
  have h92 := h y y x
  have h93 := h x y v1
  have h94 := h v6 v1 y
  have h95 := h v5 v6 x
  have h96 := h x v5 v1
  have h97 := C h82 (C (T (T (T h75 (C h42 (T (T (T (T (T (T h58 h57) h39) (C h68 (T (T (T (T (T (T (T (T h2 h96) (C h17 (T (T (T (T (T h95 (C h4 (C h82 h3))) (C h4 (T h94 (C h68 (S h93))))) (S h92)) h91) (C h17 (T (C h68 (T (T (T (T h63 h90) h83) (C h82 (C (T (T (T (T (T h24 h23) h21) h19) (C h17 (T (T h10 h13) (C h42 (T (T (T h15 h81) h77) h64))))) (S h62)) h61))) (S h60))) (S h59)))))) (C h17 (T (T (T h58 h57) h39) h37))) h36) h34) h32) (C h25 h30)) (S h29)))) (S h28)) h26) h16))) h14) h11) h9)
  have h98 := h x (M z v1) v6
  have h99 := h v1 x z
  have h100 := T h99 (C h25 (T (T h98 h97) h8))
  have h101 := h v5 y x
  have h102 := S h91
  have h103 := C h17 (T h59 (C h68 (T (T (T (T h60 (C h82 (C (T (T (T (T (T h62 (C h17 (T (T (C h42 (T (T (T h63 h90) h26) h16)) h14) h11))) h18) h80) h79) h78) h61))) (S h83)) h77) h64)))
  have h104 := C h17 (T (T (T h88 h38) h89) h85)
  let v105 := M v6 y
  T (T (T (T (T (T (T h93 (C h17 (C h68 (h v1 x v1)))) (S (h (M x (M v1 v1)) y v1))) (C (T (T (C h4 (T (T (T (T (T (T h74 h73) h72) h71) h55) h39) (C h68 h2))) (S h101)) (C (T (C h25 (T (T h7 (C h82 (C (T (T (T h10 h13) (C h42 (T (T (T (T (T (T h15 h81) h28) (C h68 (T (T (T (T (T (T (T (T h29 (C h25 (S h30))) h44) h43) h35) h104) (C h17 (T (T (T (T (T h103 h102) h92) (C h4 (T (C h68 h93) (S h94)))) (C h4 (C h82 h2))) (S h95)))) (S h96)) h3))) h38) h89) h85))) h84) h9))) (S h98))) (S h99)) h68)) h68)) (h v105 y x)) (C h4 (T (C h68 (T (T (T (T (T (T (T (h x v105 v1) (C h17 (T (T (T (h v105 v6 z) (C h25 (S (h y z v6)))) h44) h43))) (C h17 (T h35 h104))) (S (h v1 v1 v1))) h74) h73) h72) h71)) h86))) (C h4 (T (T (T (T (T (T (h z v0 v6) (C h82 (T (C h42 (T (T (T (T (T (T (C h100 h25) (h v5 z x)) (C h4 (C h25 h3))) h98) h97) h8) (h x v0 v1))) (S (h v6 v1 v0))))) (C h82 (T (T (T (T (C h100 h17) (h v5 v1 x)) (C h4 (C h17 h3))) (C h4 (T h103 h102))) (C h4 (T (h y y v6) (C h82 (T (C h68 (T (T (C h100 h68) h101) (C h4 (C h68 h3)))) (S (h v1 x y))))))))) (S (h v6 x v6))) (C h100 h4)) (h v5 x x)) (C h4 (C h4 h3))))) (S (h v1 x x))

