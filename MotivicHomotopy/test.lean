
import Mathlib.Order.Lattice
import Mathlib.Data.Real.Basic

variable (a b : ℝ )

example (h : a < b) : (a ≠ b) := by exact ne_of_lt h
