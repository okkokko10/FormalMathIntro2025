import Mathlib

namespace AaltoFormalMath2025



open Filter Set

section eventually_and_frequently

-- Let `F` be a filter on a set `X` (well, on a type `X` in Lean).
variable {X : Type} (F : Filter X)

-- Let `P` be a *predicate* on `X`, i.e., a statement `P x` for each `x ∈ X`, which is true or
-- false, depending on `x`.
variable (P : X → Prop)

-- The predicate `P` holds **eventually** along the filter `F` if...
example : F.Eventually P ↔ {x | P x} ∈ F := by
  rfl

-- The predicate `P` holds **frequently** along the filter `F` if...
example : F.Frequently P ↔ ∀ s ∈ F, ∃ x ∈ s, P x := by
  exact frequently_iff

-- The real-number sequence `(aₙ)` with `aₙ = √n` is eventually larger than an arbitrary fixed
-- constant `c ∈ ℝ` (along the `atTop` filter, i.e., as `n → ∞`).
example (c : ℝ) :
    atTop.Eventually (fun (n : ℕ) ↦ Real.sqrt n > c) := by
  set m := ⌈c^2⌉₊ with def_m
  have key : ∀ n > m, Real.sqrt n > c := by
    intro n n_large
    suffices Real.sqrt n > Real.sqrt (c^2) by
      apply lt_of_le_of_lt _ this
      simpa [← Real.sqrt_sq_eq_abs] using le_abs_self c
    apply Real.sqrt_lt_sqrt
    · exact sq_nonneg c
    · have aux : c^2 ≤ m := by exact Nat.le_ceil (c ^ 2)
      apply lt_of_le_of_lt aux
      exact Nat.cast_lt.mpr n_large
  have filt : Ioi m ∈ atTop := by exact Ioi_mem_atTop m
  filter_upwards [filt] with n n_large
  exact key n n_large

-- The real-number sequence `(aₙ)` with `aₙ = (-1)ⁿ` is frequently negative (along the `atTop`
-- filter, i.e., as `n → ∞`).
example :
    atTop.Frequently (fun (n : ℕ) ↦ (-1 : ℝ)^n < 0) := by
  rw [frequently_atTop]
  intro a
  use 2*a+1
  refine ⟨?_, ?_⟩
  · linarith
  · have aux : (-1 : ℝ)^(2*a + 1) = -1 := by
      apply Odd.neg_one_pow
      exact odd_two_mul_add_one a
    simp [aux]

end eventually_and_frequently



end AaltoFormalMath2025
