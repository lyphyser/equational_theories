
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following refutation as produced by
random generation of polynomials:
'(2 * x**2 + 1 * y**2 + 0 * x + 3 * y + 0 * x * y) % 4' (0, 3252, 3260, 3270, 3277, 3305, 3318, 3333, 3345, 3352, 3387, 3413, 3455, 3457, 3460, 3463, 3466, 3508, 3511, 3514, 3518, 3521, 3524, 3528, 3532, 3536, 3540, 3658, 3663, 3673, 3683, 3693, 3711, 3721, 3731, 3748, 3758, 3768, 3785, 3802, 3819, 3836, 4274, 4306, 4319, 4361, 4379, 4381, 4384, 4387, 4390, 4395, 4398, 4401, 4405, 4408, 4411, 4415, 4419, 4423, 4427, 4583, 4586, 4589, 4592, 4598, 4601, 4605, 4610, 4614, 4618, 4621, 4624, 4630, 4634, 4637, 4641, 4644, 4648, 4654, 4662, 4665, 4668, 4674, 4676, 4681, 4688, 4692)
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly 2 * x² + y² + 3 * y % 4» : Magma (Fin 4) where
  op := memoFinOp fun x y => 2 * x*x + y*y + 3 * y

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly 2 * x² + y² + 3 * y % 4» :
  ∃ (G : Type) (_ : Magma G), Facts G [3388, 3541, 3837, 4428] [47, 99, 151, 203, 255, 307, 411, 614, 817, 1020, 1223, 1426, 1629, 1832, 2035, 2238, 2441, 2644, 2847, 3050, 3254, 3255, 3256, 3258, 3259, 3262, 3268, 3269, 3272, 3279, 3281, 3308, 3309, 3315, 3316, 3318, 3342, 3343, 3345, 3352, 3457, 3459, 3462, 3465, 3472, 3474, 3475, 3481, 3482, 3484, 3511, 3518, 3521, 3545, 3546, 3548, 3549, 3555, 3558, 3660, 3661, 3662, 3665, 3667, 3668, 3675, 3677, 3678, 3685, 3687, 3714, 3721, 3724, 3725, 3748, 3751, 3752, 3761, 3862, 4065, 4268, 4269, 4270, 4272, 4273, 4276, 4283, 4284, 4290, 4291, 4293, 4314, 4321, 4343, 4398, 4405, 4408, 4433, 4435, 4436, 4442, 4443, 4445, 4470, 4472, 4473, 4479, 4480, 4482, 4583, 4585, 4588, 4591, 4598, 4605, 4608, 4629, 4636, 4658] :=
    ⟨Fin 4, «FinitePoly 2 * x² + y² + 3 * y % 4», by decideFin!⟩
