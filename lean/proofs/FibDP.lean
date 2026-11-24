import Mathlib

namespace VerifiedAlgorithms

/-- One DP step carries the pair (F(n), F(n+1)). -/
def fibPair : ℕ → ℕ × ℕ
  | 0 => (0, 1)
  | n + 1 => ((fibPair n).2, (fibPair n).1 + (fibPair n).2)

/-- Linear-time Fibonacci. -/
def fibDP (n : ℕ) : ℕ := (fibPair n).1

theorem fibPair_eq (n : ℕ) : fibPair n = (Nat.fib n, Nat.fib (n + 1)) := by
  induction n with
  | zero => simp [fibPair]
  | succ n ih =>
    rw [fibPair, ih]
    simp [Nat.fib_add_two]

/-- The DP computes the Fibonacci numbers. -/
theorem fibDP_eq (n : ℕ) : fibDP n = Nat.fib n := by
  simp [fibDP, fibPair_eq]

end VerifiedAlgorithms
