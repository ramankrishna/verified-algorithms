import Mathlib

namespace VerifiedAlgorithms

/-- One DP step carries the pair (F(n), F(n+1)). -/
def fibPair : ℕ → ℕ × ℕ
  | 0 => (0, 1)
  | n + 1 => ((fibPair n).2, (fibPair n).1 + (fibPair n).2)

/-- Linear-time Fibonacci. -/
def fibDP (n : ℕ) : ℕ := (fibPair n).1

/-- The DP computes the Fibonacci numbers. -/
theorem fibDP_eq (n : ℕ) : fibDP n = Nat.fib n := by
  sorry

end VerifiedAlgorithms
