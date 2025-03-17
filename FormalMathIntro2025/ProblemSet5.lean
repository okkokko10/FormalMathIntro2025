import Mathlib

set_option linter.unusedVariables false

namespace AaltoFormalMath2025


noncomputable section nonvanishing_integral
/-!
# Nonzero nonnegative continuous functions have nonvanishing integrals

The goal of this problem set is to prove that if `f` is a continuous nonnegative function on
a nondegenerate interval `[a,b]` which is not identically zero on the interval, then the
integral of `f` is positive,  `∫ₐᵇ f(x) dx > 0`.

As you probably observed right away, the key lemma is that such a continuous `f` has to be
larger than some positive constant `c > 0` on some small interval around a point `z ∈ (a,b)`
where `f(z) ≠ 0`. And therefore by monotonicity of integrals we get `∫ₐᵇ f(x) dx ≥ c * L > 0`
where `L > 0` is the length of the small interval.

Very easy, right? (An informal text might call the above paragraph a complete proof.)

But as you are about to learn...
    ...it takes some work to provide a complete Lean proof...
    ...and some thinking is required even to formulate a precise Lean statement!

Regarding the statement, note that mathematically there are two kinds of integrals
(in fact many more, but two good measure-theoretic notions of integral that are worth
using; forget about poorly-behaved Riemann integrals etc.!):
 * *Lebesgue integrals* of functions with values in [0,+∞] (i.e., in `ENNReal`)
 * *Bochner integrals* of functions with values in Banach spaces (e.g., in `ℝ`).
In informal math we just denote both by `∫` and we seldom explicitly mention which one
we are using when.

Lebesgue integrals are nice because they always exist (under measurability assumption
of the integrand), but it can get quite annoying to make everything `ENNReal`-valued.

Bochner integrals are annoying, because their existence requires integrability in addition
to measurability of the integrand, but on the other hand, they allow to work directly with
real values of the integrand and of the integral, which is definitely nicer than coercing
back and forth with `ENNReal`.

Either choice is annoying, for different reasons. So let's do both!
-/

open MeasureTheory Set

open scoped ENNReal NNReal

-- We will consider an interval `[a,b] ⊆ ℝ` which is nondegenerate, `a < b`.
variable {a b : ℝ} (a_lt_b : a < b)

-- The closed interval `[a,b] ⊆ ℝ` is denoted by
#check Icc a b
-- In the precise reasoning, we will also use the open interval `(a,b) ⊆ ℝ`
#check Ioo a b
-- and the half-open interval `(a,b] ⊆ ℝ` (this is the implicit choice in `IntervalIntegral`)
#check Ioc a b

-- We assume that `f` is a continuous real-valued function on `[a,b]`.
-- In fact it is nicer to have `f` defined on all of `ℝ`, and assuming continuity
-- on all of `ℝ` makes life easier and can be done without loss of generality.
variable (f : ℝ → ℝ) (f_cont : Continuous f)

-- And of course we wanted `f` to be nonnegative, and nonzero at some point in the interval.
-- Again to make this slightly easier, let's directly assume (without loss of generality)
-- that `f` is nonzero at some point of the open interval `(a,b)`.
variable (f_nn : 0 ≤ f) (f_ne_zero : ∃ z ∈ Ioo a b, f z ≠ 0)

-- The following is the key lemma --- regardless of which of the two integrals (Lebesgue
-- or Bochner) one chooses to use.
-- **EXERCISE:** Prove that...
lemma exists_forall_mem_Ioo_gt (a_lt_b : a < b)
    (f_cont : Continuous f) (f_nn : 0 ≤ f) (f_ne_zero : ∃ z ∈ Ioo a b, f z ≠ 0) :
    ∃ c > 0, ∃ a' ∈ Icc a b, ∃ b' ∈ Icc a b,
      (a' < b') ∧ (∀ x ∈ Ioo a' b', c ≤ f x) := by
  -- This is in principle straightforward, although you may find that there is quite a lot
  -- to do and a few mathematically simple pieces of the puzzle are slightly tricky to set
  -- up nicely (hint: `linarith` is good for proving the many needed interval membership
  -- inequalities if you have arranged the tactic state appropriately for it).
  -- As usual, of course --- first make sure that you know the complete math proof!
  sorry

/-
The following is the *Lebesgue integral version of the main statement* of this problem sheet.
I think it is slightly easier of the two, because Lebesgue integrals are better behaved and the
library contains more useful and easier to apply results about the Lebesgue integral. -/
-- **EXERCISE:** Prove that...
theorem main_goal₁ (a_lt_b : a < b)
    (f_cont : Continuous f) (f_nn : 0 ≤ f) (f_ne_zero : ∃ z ∈ Ioo a b, f z ≠ 0) :
    0 < ∫⁻ x in Ioc a b, ENNReal.ofReal (f x) := by
  -- Hint: Mathematically the key is the lemma `exists_forall_mem_Ioo_gt` above
  --       and monotonicity of integrals. Make sure you know the full maths proof first!
  -- Hint: The appropriate monotonicity of integrals in this case is `setLIntegral_mono`.
  -- Hint: One possible way of writing the lower bound for the integral is by comparing the
  --       integrand `f` to a suitable indicator function, see `Set.indicator`.
  -- Hint: Once you have manipulated the integrals to useful forms, `simp` can make progress.
  --
  -- In this version there will be a few casts from ℝ (`Real`) to [0,+∞] (`ENNReal`) and back.
  -- The casting functions are `ENNReal.ofReal` and `ENNReal.toReal`.
  -- Some relevant lemmas about these are `ENNReal.ofReal_pos`, `ENNReal.ofReal_le_ofReal`,
  -- and you may need more, although sometimes `simp` knows about these and can help.
  sorry

/-
The following is the *Bochner integral version of the main statement* of this problem sheet.
The statement looks slightly nicer because we do not need to coerce the function values, but
I think this is in fact slightly trickier, because Bochner integrals and especially their special
case of integrals along intervals of the real line have fewer good general results about them
directly available in the library. -/
-- **EXERCISE:** Prove that...
theorem main_goal₂ (a_lt_b : a < b)
    (f_cont : Continuous f) (f_nn : 0 ≤ f) (f_ne_zero : ∃ z ∈ Ioo a b, f z ≠ 0) :
    0 < ∫ x in a..b, f x := by
  -- Hint: Mathematically the key is the lemma `exists_forall_mem_Ioo_gt` above
  --       and monotonicity of integrals. Make sure you know the full maths proof first!
  -- Hint: The appropriate monotonicity of integrals in this case is
  --       `intervalIntegral.integral_mono_on`. (Or if you unfold `intervalIntegral`, then
  --       something else; you will find many monotonicity results of integrals in Mathlib.)
  -- Hint: One possible way of writing the lower bound for the integral is again by comparing
  --       the integrand `f` to a suitable indicator function, see `Set.indicator`.
  -- Hint: The library doesn't have a very extensive collection of simp-lemmas
  --       about `intervalIntegral`, so at some point you may want to `rw [intervalIntegral]`
  --       and then use `simp`. (Or just `simp [intervalIntegral]`.)
  --
  -- In this version you will need to provide a few integrability proofs. Searching the
  -- library is the key! (And when you don't find anything for `IntervalIntegrable`, you
  -- can `rw [IntervalIntegrable]` and search the library for results on `IntegrableOn`.)
  sorry

end nonvanishing_integral

end AaltoFormalMath2025
