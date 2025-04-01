import Mathlib



namespace AaltoFormalMath2025

noncomputable section integration_of_nonnegative_functions
/-!
### An example related to Section13 and ProblemSet5
-/

/-
In `ProblemSet5.lean` you prove that: if `f` is a continuous nonnegative function on
a nondegenerate interval `[a,b]` which is not identically zero on the interval, then the
integral of `f` is positive,  `∫ₐᵇ f(x) dx > 0`.

Let us demonstrate here that the continuity assumption is necessary: it is not true that
over every nondegenerate interval every nonnegative nonzero function has a nonzero integral.
-/

open Set MeasureTheory Filter

example : -- A counterexample to positivity of integrals without continuity requirement.
    ¬ ∀ (a b : ℝ) (_ : a < b) (f : ℝ → ℝ) (_ : 0 ≤ f) (_ : ∃ z ∈ Ioo a b, f z ≠ 0),
      0 < ∫ x in a..b, f x := by
  push_neg
  use 36
  use 38
  use (by linarith)
  set f : ℝ → ℝ := fun (x : ℝ) ↦ if x = 37 then 1 else 0 with f_def
  have f_nonneg : 0 ≤ f := by
    intro x
    simp [f_def]
    by_cases hx : x = 37
    · simp [hx]
    · simp [hx]
  have f_ae_zero : f =ᵐ[volume] 0 := by
    filter_upwards [show {37}ᶜ ∈ ae _ by apply compl_mem_ae_iff.mpr (by simp)] with x hx
    simp [f_def]
    exact hx
  use f
  refine ⟨?_, ?_, ?_⟩
  · -- nonnegativity of f
    exact f_nonneg
  · -- nonzeroness of f:
    use 37
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · linarith
    · linarith
    · simp [f_def]
  · -- vanishing integral of f
    apply le_of_eq
    apply (intervalIntegral.integral_eq_zero_iff_of_nonneg_ae ..).mpr
    · exact f_ae_zero.restrict
    · apply Eventually.of_forall
      exact f_nonneg
    · apply IntervalIntegrable.congr (f := 0)
      · rw [IntervalIntegrable]
        exact ⟨integrable_zero .., integrable_zero ..⟩
      · exact f_ae_zero.symm.restrict

end integration_of_nonnegative_functions


end AaltoFormalMath2025
