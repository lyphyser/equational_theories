
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3, 1, 1, 3], [3, 3, 1, 3], [3, 0, 0, 3], [0, 1, 2, 3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3, 1, 1, 3], [3, 3, 1, 3], [3, 0, 0, 3], [0, 1, 2, 3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3, 1, 1, 3], [3, 3, 1, 3], [3, 0, 0, 3], [0, 1, 2, 3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3, 1, 1, 3], [3, 3, 1, 3], [3, 0, 0, 3], [0, 1, 2, 3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [211, 231, 2277, 2281, 2318, 2351, 2385, 2406, 2662, 2812, 3458, 3464, 3509, 4276] [2, 3, 8, 23, 38, 39, 40, 43, 47, 99, 151, 204, 205, 206, 208, 209, 212, 218, 219, 221, 222, 228, 229, 255, 307, 359, 411, 614, 817, 1020, 1223, 1426, 1629, 1832, 2035, 2239, 2240, 2241, 2244, 2247, 2254, 2257, 2263, 2264, 2267, 2291, 2293, 2294, 2300, 2301, 2304, 2327, 2328, 2331, 2337, 2338, 2372, 2441, 2645, 2646, 2647, 2649, 2650, 2652, 2653, 2659, 2660, 2663, 2669, 2670, 2673, 2697, 2699, 2700, 2706, 2707, 2709, 2710, 2733, 2734, 2736, 2737, 2743, 2744, 2847, 3050, 3253, 3457, 3459, 3461, 3462, 3465, 3472, 3474, 3475, 3481, 3482, 3484, 3511, 3512, 3518, 3519, 3521, 3522, 3545, 3546, 3548, 3549, 3555, 3556, 3558, 3659, 3862, 4065, 4268, 4269, 4270, 4272, 4273, 4275, 4283, 4284, 4290, 4291, 4293, 4314, 4320, 4321, 4343, 4380, 4583, 4584, 4585, 4587, 4588, 4590, 4591, 4598, 4599, 4605, 4606, 4608, 4629, 4635, 4636, 4658] :=
    ⟨Fin 4, «FinitePoly [[3, 1, 1, 3], [3, 3, 1, 3], [3, 0, 0, 3], [0, 1, 2, 3]]», by decideFin!⟩
