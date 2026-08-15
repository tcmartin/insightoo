import Mathlib

/-- Toolchain smoke test: no `sorry`, proved by normalization. -/
theorem lean_runner_smoke_test : (37 : ℕ) + 5 = 42 := by
  norm_num
