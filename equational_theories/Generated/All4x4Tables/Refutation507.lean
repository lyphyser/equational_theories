
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0, 1, 3, 3], [3, 1, 2, 2], [0, 1, 2, 3], [1, 2, 2, 3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0, 1, 3, 3], [3, 1, 2, 2], [0, 1, 2, 3], [1, 2, 2, 3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[0, 1, 3, 3], [3, 1, 2, 2], [0, 1, 2, 3], [1, 2, 2, 3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0, 1, 3, 3], [3, 1, 2, 2], [0, 1, 2, 3], [1, 2, 2, 3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [3, 333, 1045, 1921, 2337, 2743, 2936, 3068, 3346, 3546, 3759, 3887, 4155, 4320, 4445] [4, 5, 9, 16, 28, 55, 72, 75, 100, 101, 102, 104, 105, 107, 108, 114, 115, 117, 118, 124, 125, 127, 152, 153, 154, 156, 157, 159, 160, 166, 167, 169, 170, 176, 177, 179, 208, 218, 256, 257, 258, 260, 261, 263, 264, 270, 271, 273, 274, 280, 281, 283, 315, 323, 377, 378, 384, 385, 419, 429, 436, 466, 473, 500, 513, 619, 639, 676, 703, 832, 835, 872, 906, 1025, 1035, 1082, 1109, 1228, 1231, 1238, 1248, 1312, 1325, 1434, 1478, 1481, 1488, 1634, 1681, 1691, 1847, 1850, 1884, 1887, 2050, 2060, 2087, 2090, 2124, 2137, 2243, 2253, 2290, 2446, 2456, 2466, 2493, 2503, 2530, 2649, 2659, 2696, 2706, 2733, 2852, 2862, 2872, 2899, 2909, 2946, 3055, 3065, 3075, 3102, 3112, 3139, 3149, 3278, 3306, 3512, 3758, 3928, 3955, 3962, 4362, 4442] :=
    ⟨Fin 4, «FinitePoly [[0, 1, 3, 3], [3, 1, 2, 2], [0, 1, 2, 3], [1, 2, 2, 3]]», by decideFin!⟩
