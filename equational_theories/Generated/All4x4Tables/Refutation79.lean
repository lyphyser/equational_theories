
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0, 2, 1, 3], [2, 0, 3, 1], [3, 1, 2, 0], [1, 3, 0, 2]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0, 2, 1, 3], [2, 0, 3, 1], [3, 1, 2, 0], [1, 3, 0, 2]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[0, 2, 1, 3], [2, 0, 3, 1], [3, 1, 2, 0], [1, 3, 0, 2]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0, 2, 1, 3], [2, 0, 3, 1], [3, 1, 2, 0], [1, 3, 0, 2]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [209, 264, 562, 633, 1452, 1793, 3724, 4436] [2, 3, 8, 23, 38, 39, 40, 43, 47, 99, 151, 204, 205, 206, 208, 211, 212, 218, 219, 221, 222, 228, 229, 231, 256, 257, 258, 260, 261, 263, 270, 271, 273, 274, 280, 281, 283, 307, 359, 412, 413, 414, 416, 417, 419, 420, 426, 427, 430, 436, 437, 439, 440, 463, 464, 466, 467, 474, 476, 477, 500, 501, 503, 504, 510, 511, 615, 616, 617, 619, 620, 622, 623, 629, 630, 632, 639, 640, 642, 643, 666, 667, 669, 670, 676, 677, 679, 680, 703, 704, 706, 707, 713, 714, 716, 817, 1020, 1223, 1427, 1428, 1429, 1431, 1432, 1434, 1435, 1441, 1442, 1444, 1445, 1451, 1454, 1455, 1478, 1479, 1481, 1482, 1488, 1489, 1491, 1492, 1515, 1516, 1518, 1519, 1525, 1526, 1528, 1630, 1631, 1632, 1634, 1635, 1637, 1638, 1644, 1645, 1647, 1648, 1655, 1657, 1658, 1681, 1682, 1685, 1691, 1692, 1694, 1695, 1718, 1719, 1721, 1722, 1728, 1729, 1832, 2035, 2238, 2441, 2644, 2847, 3050, 3253, 3456, 3660, 3661, 3662, 3664, 3665, 3667, 3668, 3674, 3675, 3677, 3678, 3684, 3685, 3687, 3712, 3714, 3721, 3722, 3725, 3748, 3749, 3751, 3752, 3759, 3761, 3862, 4065, 4268, 4269, 4270, 4272, 4273, 4275, 4276, 4283, 4284, 4290, 4291, 4293, 4314, 4320, 4321, 4343, 4381, 4382, 4383, 4385, 4386, 4388, 4396, 4398, 4399, 4405, 4406, 4408, 4433, 4435, 4442, 4443, 4445, 4470, 4472, 4473, 4479, 4480, 4482, 4583, 4584, 4585, 4587, 4588, 4590, 4591, 4598, 4599, 4605, 4606, 4608, 4629, 4635, 4636, 4658] :=
    ⟨Fin 4, «FinitePoly [[0, 2, 1, 3], [2, 0, 3, 1], [3, 1, 2, 0], [1, 3, 0, 2]]», by decideFin!⟩
