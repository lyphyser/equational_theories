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
theorem Equation2349_implies_Equation26 (G: Type _) [Magma G] (h: Equation2349 G) : Equation26 G := fun x y =>
  let v0 := M x y
  let v1 := M x (M x (M v0 v0))
  have h2 := h y v1 x
  have h3 := S h2
  have h4 := R x
  have h5 := h v0 x v0
  have h6 := R v1
  have h7 := C (T h5 (C h6 h5)) h4
  have h8 := T h7 h3
  have h9 := R v0
  have h10 := C h9 h8
  let v11 := M v0 x
  have h12 := h (M v0 v11) y y
  let v13 := M v0 y
  let v14 := M x (M x (M v13 v13))
  have h15 := h y v14 v0
  have h16 := S h15
  have h17 := h v13 x v13
  have h18 := R v14
  have h19 := C (T h17 (C h18 h17)) h9
  have h20 := C h4 h8
  have h21 := R v13
  have h22 := C h21 h20
  have h23 := S h5
  have h24 := C (T (C h6 h23) h23) h4
  have h25 := T h2 h24
  have h26 := C h9 h25
  have h27 := R y
  let v28 := M y (M y v13)
  have h29 := R v28
  have h30 := h y x y
  have h31 := S h30
  have h32 := h y y v0
  let v33 := M x (M x (M y y))
  have h34 := R v33
  have h35 := C (T (C h34 (T (C h34 (S h32)) h31)) h31) h29
  have h36 := h v0 v33 v28
  have h37 := C h4 h25
  have h38 := C h21 h37
  have h39 := S h17
  have h40 := C (T (C h18 h39) h39) h9
  have h41 := S h36
  have h42 := C (T h30 (C h34 (T h30 (C h34 h32)))) h29
  let v43 := M v13 (M v13 (M v13 x))
  have h44 := h v13 v0 v43
  have h45 := S h44
  have h46 := R v43
  have h47 := h x v13 v13
  let v48 := M y (M y v0)
  have h49 := h x v33 v48
  have h50 := S h49
  have h51 := R v48
  have h52 := h y y x
  have h53 := C (T h30 (C h34 (T h30 (C h34 h52)))) h51
  have h54 := C h27 (C h27 h20)
  have h55 := C h27 h54
  have h56 := h (M x v11) y y
  have h57 := S h56
  have h58 := C h27 (C h27 h37)
  have h59 := C h27 h58
  have h60 := C (T (C h34 (T (C h34 (S h52)) h31)) h31) h51
  have h61 := C (T (T h49 h60) h59) (T h19 h16)
  have h62 := T h61 h57
  have h63 := C h27 (C h27 h62)
  have h64 := C h27 h63
  have h65 := C (T (T h55 h53) h50) (T h15 h40)
  have h66 := T (T (T (T h42 h41) h37) h56) h65
  have h67 := C h27 (C h27 h66)
  have h68 := C h27 h67
  have h69 := T (T (T (T h61 h57) h20) h36) h35
  have h70 := C h27 (C h27 h69)
  have h71 := T h56 h65
  have h72 := C h27 (C h27 h71)
  have h73 := h v48 v0 y
  have h74 := T h53 h50
  have h75 := C h9 h74
  have h76 := T (T h75 h7) h3
  have h77 := T h49 h60
  have h78 := C h9 h77
  have h79 := T (T h2 h24) h78
  have h80 := C (T h42 h41) h79
  have h81 := h v13 y y
  have h82 := C h21 h62
  have h83 := C h21 h66
  have h84 := C h21 h69
  have h85 := C h21 h71
  have h86 := C h27 (T (T (T (T (T (T (T (C h21 (T h38 h85)) (C h21 h84)) (C h21 (T (T (T (T (T (T (T h83 h82) h22) h19) h16) h2) h24) h78))) (C (T h81 h80) h76)) (S h73)) h58) h72) h70)
  have h87 := C h27 (T (C h21 (T (T (T (T h7 h3) h15) h40) h38)) (C h21 h22))
  have h88 := C h27 (T (C h21 h38) (C h21 (T (T (T (T h22 h19) h16) h2) h24)))
  have h89 := S h81
  have h90 := C (T h36 h35) h76
  have h91 := C h27 (T (T (T (T (T (T (T h67 h63) h54) h73) (C (T h90 h89) h79)) (C h21 (T (T (T (T (T (T (T h75 h7) h3) h15) h40) h38) h85) h84))) (C h21 h83)) (C h21 (T h82 h22)))
  have h92 := C h27 h70
  have h93 := C h27 h72
  have h94 := T (T (T h59 h93) h92) h91
  have h95 := C (T (T (T (T h81 h80) (C h9 (C h9 h94))) (C h9 (C h9 h88))) (C h9 (C h9 (T (T (T (T (T (T (T h87 h86) h68) h64) h55) h53) h50) h47)))) h46
  have h96 := T (T (T h86 h68) h64) h55
  let v97 := M x (M x (M x x))
  have h98 := h x v97 v97
  have h99 := R v97
  have h100 := h x x x
  have h101 := C h27 (C h21 h25)
  have h102 := C h27 (C h21 h8)
  have h103 := C h4 (C h4 (T (T (T (C h4 (T (T (T (T (T h59 h93) h92) h91) h88) h102)) (C h4 h101)) (C h4 h87)) (C h4 (T (T (T (T (T h86 h68) h64) h55) h53) h50))))
  have h104 := h (M y v48) x x
  have h105 := C h21 (T (C h21 (T (T (C h21 (C h21 (T (T (T (T (T (T (T (T (C (T (T (T h49 h60) h104) (C h103 (T (T (T h49 h60) h104) (C h103 h100)))) h99) (S h98)) h49) h60) h59) h93) h92) h91) h88))) (C h21 (C h21 h87))) (C h21 (C h21 h96)))) (C h21 (C h21 (C h21 h74))))
  have h106 := S h104
  have h107 := C h4 (C h4 (T (T (T (C h4 (T (T (T (T (T h49 h60) h59) h93) h92) h91)) (C h4 h88)) (C h4 h102)) (C h4 (T (T (T (T (T h101 h87) h86) h68) h64) h55))))
  have h108 := C (T (T (T (C h107 (T (T (T (C h107 (S h100)) h106) h53) h50)) h106) h53) h50) h99
  let v109 := M x v97
  T (T (T (T (T (T (T (T h98 h108) (h v109 v13 v13)) (C (C h21 (C h21 (T (T (T (h (M v13 v109) v13 v13) (C (T (T h105 h95) h45) (T (T h44 (C (T (T (T (T (C h9 (C h9 (T (T (T (T (T (T (T (S h47) h49) h60) h59) h93) h92) h91) h88))) (C h9 (C h9 h87))) (C h9 (C h9 h96))) h90) h89) h46)) (C h21 (T (C h21 (C h21 (C h21 h77))) (C h21 (T (T (C h21 (C h21 h94)) (C h21 (C h21 h88))) (C h21 (C h21 (T (T (T (T (T (T (T (T h87 h86) h68) h64) h55) h53) h50) h98) h108)))))))))) (C h21 (T (T (T h105 h95) h45) h26))) (C h21 (T (T h12 (C (T (T (C h27 (C h27 (C h27 h10))) h42) h41) (T (T h15 h40) h38))) (C h9 h22)))))) h21)) (S (h (M v0 (M v13 v0)) v13 v13))) (C h9 h38)) (C (T (T h36 h35) (C h27 (C h27 (C h27 h26)))) (T (T h22 h19) h16))) (S h12)) h10

