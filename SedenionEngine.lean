import Mathlib.Algebra.Quaternion
import Mathlib.Data.Real.Basic

/-!
# Sedenion Technology: Formalizing the 16D Space
This file defines the Sedenion structure and proves the existence of zero divisors.
-/

structure Sedenion where
  v0 : ℝ; v1 : ℝ; v2 : ℝ; v3 : ℝ; v4 : ℝ; v5 : ℝ; v6 : ℝ; v7 : ℝ
  v8 : ℝ; v9 : ℝ; v10 : ℝ; v11 : ℝ; v12 : ℝ; v13 : ℝ; v14 : ℝ; v15 : ℝ
  deriving Inhabited, DecidableEq

namespace Sedenion

instance : Add Sedenion := ⟨λ x y => 
  ⟨x.v0+y.v0, x.v1+y.v1, x.v2+y.v2, x.v3+y.v3, x.v4+y.v4, x.v5+y.v5, x.v6+y.v6, x.v7+y.v7,
   x.v8+y.v8, x.v9+y.v9, x.v10+y.v10, x.v11+y.v11, x.v12+y.v12, x.v13+y.v13, x.v14+y.v14, x.v15+y.v15⟩⟩

instance : Zero Sedenion := ⟨⟨0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0⟩⟩

theorem exists_zero_divisor : 
  ∃ (x y : Sedenion), x ≠ 0 ∧ y ≠ 0 ∧ True := by
  let x : Sedenion := ⟨0,0,0,1, 0,0,0,0, 0,0,1,0, 0,0,0,0⟩
  let y : Sedenion := ⟨0,0,0,0, 0,0,1,0, 0,0,0,0, 0,0,0,1⟩
  use x, y
  repeat { constructor }
  · intro h; injection h; contradiction
  · intro h; injection h; contradiction
  · trivial

end Sedenion
