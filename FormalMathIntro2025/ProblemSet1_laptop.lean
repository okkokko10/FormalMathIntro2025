import Mathlib.Tactic -- imports all the Lean tactics

set_option linter.unusedTactic false

namespace AaltoFormalMath2025

section
/-!
# Problem set 1: Cauchy sequences and bounded sequences on `ℝ`
-/


/-
## Convergent sequences are necessarily Cauchy
-/

-- This is the same definition as in *Kevin Buzzard's Section01reals*.
/-- If `n ↦ a(n)` is a sequence of reals and `t` is a real, `TendsTo a t`
is the assertion that the limit of `a(n)` as `n → ∞` is `t`. -/
def TendsTo (a : ℕ → ℝ) (t : ℝ) : Prop :=
  ∀ ε > 0, ∃ B : ℕ, ∀ n, B ≤ n → |a n - t| < ε

theorem tendsTo_def {a : ℕ → ℝ} {t : ℝ} :
    TendsTo a t ↔ ∀ ε, 0 < ε → ∃ B : ℕ, ∀ n, B ≤ n → |a n - t| < ε := by
  rfl -- true by definition

/-- If `n ↦ a(n)` is a sequence of reals, `IsCauchy a` is the assertion that
`n ↦ a(n)` is a Cauchy sequence (just as in MS-C1541 Metric Spaces). -/
def IsCauchy (a : ℕ → ℝ) : Prop :=
  ∀ ε > 0, ∃ B, ∀ n m, B ≤ n → B ≤ m → |a n - a m| < ε

theorem isCauchy_def {a : ℕ → ℝ} :
    IsCauchy a ↔ ∀ ε > 0, ∃ B : ℕ, ∀ n m, B ≤ n → B ≤ m → |a n - a m| < ε := by
  rfl -- true by definition

-- EXERCISE 1
/-- Any convergent real-number sequence is necessarily a Cauchy sequence. -/
theorem isCauchy_of_tendsTo {a : ℕ → ℝ} {t : ℝ} (a_lim : TendsTo a t) :
    IsCauchy a := by
  -- This is some work --- make sure you know the math proof first!
  -- You may take some inspiration from the uniqueness of limits proof.
  sorry



/-
## Cauchy sequences are necessarily bounded
-/

/-- If `n ↦ a(n)` is a sequence of reals, `IsBounded a` is the assertion that
`n ↦ a(n)` is a bounded sequence (just as in MS-C1541 Metric Spaces). -/
def IsBounded (a : ℕ → ℝ) :=
  ∃ M, ∀ n, |a n| ≤ M

-- EXERCISE 2
-- Before we can prove that all Cauchy-sequences are bounded, we need an auxiliary result.
lemma exists_forall_abs_initial_le (a : ℕ → ℝ) (m : ℕ) :
    ∃ M, ∀ n < m, |a n| ≤ M := by
  -- Let us prove this by induction on `m`.
  -- (This is our first induction proof.
  --  Maybe look up the explanations for the tactic `induction'` in Buzzard's course.)
  induction' m with m ih_m
  · -- Base case.
    use 0 -- |a 0|
    tauto
  · -- Induction step.
    -- You might find, e.g., `Nat.lt_of_le_of_ne` and `Nat.succ_lt_succ_iff`
    -- and `Nat.succ_ne_succ` useful here.
    cases' ih_m with M ih_m
    use max M |a m|
    intros n n_le_m
    by_cases w : n < m
    . exact le_sup_of_le_left (ih_m n w)
      done
    . have h : n = m := by exact Nat.eq_of_lt_succ_of_not_lt n_le_m w
      rw [h]
      exact le_max_right M |a m|
      done
    done


-- EXERCISE 3
/-- Any Cauchy sequence is bounded. -/
theorem isBounded_of_isCauchy {a : ℕ → ℝ} (a_cauchy : IsCauchy a) :
    IsBounded a := by
  -- This is some work --- make sure you know the math proof first!

  -- Cauchy: for any positive diameter, we can find a tail contained in such a diameter.
  -- the above lemma: for a head (...m), there exists a radius M in which it is contained.
  --  or: all heads are bounded
  -- take any positive diameter. we can find a tail contained in it. this tail is bounded.
  --  take the head associated with the tail. by the lemma, it is bounded.
  --  since both the head and tail are bounded, everything is bounded.

  rw [isCauchy_def] at *
  change ∃ M, ∀ n, |a n| ≤ M

  specialize a_cauchy 1 zero_lt_one
  cases' a_cauchy with B a_cauchy
  specialize a_cauchy B
  simp at a_cauchy
  have tail_bounded : ∃ M1, ∀ (m : ℕ), B ≤ m → |a m| < M1 := by
    use |a B| + 1
    intro m B_le_m
    specialize a_cauchy m B_le_m
    suffices |a m| - |a B| < 1 by exact lt_add_of_tsub_lt_left this
    suffices |a m| - |a B| ≤ |a B - a m| by exact lt_of_le_of_lt this a_cauchy
    rw [abs_sub_comm]
    exact abs_sub_abs_le_abs_sub (a m) (a B)
    done
  cases' tail_bounded with t_bound tail_bounded
  have uu := exists_forall_abs_initial_le a B
  cases' uu with h_bound head_bounded
  use max h_bound t_bound
  intro n
  simp only [le_sup_iff]
  by_cases sw : n<B
  .
    specialize head_bounded n sw
    exact Or.symm (Or.inr head_bounded)
  .
    specialize tail_bounded n (Nat.le_of_not_lt sw)
    -- have : |a n| ≤ t_bound := by exact le_of_lt tail_bounded
    exact Or.inr (le_of_lt tail_bounded)
    done
  done






-- EXERCISE 4
-- Now we easily get that:
/-- Any convergent real-number sequence is bounded. -/
theorem isBounded_of_tendsTo {a : ℕ → ℝ} {t : ℝ} (a_lim : TendsTo a t) :
    IsBounded a := by
  -- This is easy now!
  have a_cauchy : IsCauchy a := by exact isCauchy_of_tendsTo a_lim
  exact isBounded_of_isCauchy (isCauchy_of_tendsTo a_lim)

  done

end

end AaltoFormalMath2025
