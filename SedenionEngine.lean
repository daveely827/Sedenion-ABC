import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Prime.Basic

/-! # SEDENION FINAL ENGINE (Direct-Eval Version) -/

def a : ℕ := 2
def b : ℕ := 3^10 * 109
def c : ℕ := 6436343

#eval "--- FINAL ENGINE REPORT ---"
#eval s!"Triple: {a} + {b} = {c}"

-- Calculate Radical directly in the output line
#eval! s!"Radical: { (a * b * c).factorization.support.prod (λ p => p) }"

-- Calculate Quality (q) directly in the output line
#eval! s!"Quality (q): { (Float.log c.toFloat) / (Float.log ((a * b * c).factorization.support.prod (λ p => p)).toFloat) }"
