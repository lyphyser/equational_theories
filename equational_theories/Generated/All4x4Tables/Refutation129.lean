
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2, 0, 1, 0], [1, 3, 1, 1], [2, 2, 3, 2], [3, 3, 3, 3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[2, 0, 1, 0], [1, 3, 1, 1], [2, 2, 3, 2], [3, 3, 3, 3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[2, 0, 1, 0], [1, 3, 1, 1], [2, 2, 3, 2], [3, 3, 3, 3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[2, 0, 1, 0], [1, 3, 1, 1], [2, 2, 3, 2], [3, 3, 3, 3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [832, 843, 846, 1039] [2, 3, 8, 23, 38, 39, 40, 43, 47, 99, 151, 203, 255, 307, 360, 361, 362, 364, 365, 367, 375, 377, 385, 411, 614, 818, 819, 820, 822, 823, 825, 826, 833, 836, 842, 845, 869, 870, 872, 873, 879, 880, 882, 883, 906, 907, 909, 910, 916, 917, 919, 1021, 1022, 1023, 1025, 1026, 1028, 1029, 1036, 1038, 1046, 1048, 1049, 1072, 1073, 1075, 1076, 1082, 1083, 1085, 1086, 1109, 1110, 1112, 1113, 1119, 1120, 1122, 1223, 1426, 1629, 1832, 2035, 2238, 2441, 2644, 2847, 3050, 3253, 3456, 3659, 3862, 4066, 4067, 4068, 4070, 4071, 4073, 4074, 4080, 4083, 4084, 4090, 4091, 4093, 4118, 4120, 4121, 4127, 4128, 4130, 4155, 4157, 4158, 4164, 4165, 4167, 4268, 4269, 4270, 4272, 4273, 4275, 4276, 4283, 4284, 4290, 4291, 4293, 4314, 4320, 4321, 4343, 4380, 4583, 4584, 4585, 4587, 4588, 4590, 4591, 4598, 4599, 4605, 4606, 4608, 4629, 4635, 4636, 4658] :=
    ⟨Fin 4, «FinitePoly [[2, 0, 1, 0], [1, 3, 1, 1], [2, 2, 3, 2], [3, 3, 3, 3]]», by decideFin!⟩
