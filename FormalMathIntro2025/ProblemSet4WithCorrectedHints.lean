import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic

namespace AaltoFormalMath2025


noncomputable section left_continuous_inverse
/-!
# The left-continuous pseudoinverse of the left-continuous pseudoinverse

The goal of this problem set is to build some basic API for a particular situation
which arises for example in probability theory with cumulative distribution functions.
We will abstract the situation a little to (i) improve generality and (ii) simplify
some aspects of the problem.

So instead of a cumulative distribution function `F : ℝ → [0,1]`, we will be talking
about a function `F : R → S` between two complete linear ordered sets (well, types) `R`
and `S`. In a complete linear order `R` (or more generally in a complete lattice) any
set `A : Set R` has a supremum (a least upper bound) `sSup A` and an infimum (a greatest
lower bound) `sInf A`.

In fact `ℝ` is not a *complete* linear order, it is only *conditionally complete*:
the empty set and unbounded sets fail to have supremums and infimums in `ℝ`. So in this
way we are making a stronger hypothesis in order to simplify the problem. The extended real
line `[-∞,+∞] = ℝ ∪ {-∞} ∪ {+∞}` or the unit interval `[0,1]` are actual valid examples
of complete linear orders.

Lean knows that `ℝ` is a conditionally complete linear order:
 * `Real.instConditionallyCompleteLinearOrder : ConditionallyCompleteLinearOrder ℝ`.
Lean also knows that `[-∞,+∞]` is a complete linear order:
 * `instCompleteLinearOrderEReal : CompleteLinearOrder EReal`.
But note that `CompleteLinearOrder ℝ` is simply not true.
(In particular, you will not find such a false statement in Lean or Mathlib.)

Towards the end we will moreover need to assume also that `S` is densely ordered,
i.e., that between any two different elements `y₁ < y₂` in `S` there exists another
one, `y` such that `y₁ < y < y₂`. This assumption is valid in `ℝ`, `[-∞,+∞]`, `[0,1]`
etc., see, e.g.
 * `LinearOrderedSemiField.toDenselyOrdered : DenselyOrdered ℝ`
 * `instDenselyOrderedEReal : DenselyOrdered EReal`.

In this case, we will define a "kind of an inverse function to `F : R → S`",
    `G : S → R` given by
    `G(y) = inf {x ∈ R | F(x) ≥ y}`.
Let us call this the *left-continuous pseudoinverse* of `F`. Or in fact, since that is
a mouthful, let us call that just `G := lcInv F` (we will give `def lcInv := ...` below).
See if you can grasp the intuition of why this `G` is kind of like an inverse to `F`.
Think first about for example `F : [0,1] → [0,1]` which is increasing and bijective (and
then moreover continuous). Then think about what if the surjectivity assumption is removed:
then there is a bit of ambiguity in assigning some values of `G` and the choice we make is
the "smallest one which does not break monotonicity". If the injectivity assumption is
removed, then among the many preimages for some values we can only choose one, and the
choice we make is "the smallest preimage".)

The main goal will be to prove:
   `inf {y ∈ S | G(y) ≥ x} = sup {F(x') | x' < x}`.
Note that:
 * The left hand side is *by definition* the left-continuous pseudoinverse of the
   left-continuous pseudoinverse of `F`.
 * If `F` is increasing, then the right-hand side `sup {F(x') | x' < x}` is essentially `F(x)`
   itself, except it is modified to become continuous from the left.
So this statement is a variant of the fact that the inverse function of the inverse function
is the original function.

(In principle, proving this could be a slightly tricky exercise in some probability course. If
you want a math challenge, you can figure out the proof for yourself! I have, however, broken
the proof to a number of easier steps for you --- so you can focus on teaching the proof to Lean.)

There are a number of steps before we get to the main goal above. Each step requires quite careful
thinking and careful book-keeping. Lean helps with the book-keeping. The thinking part is
mostly left to you, although I have given hints for most of the steps below.
-/

open Set

-- Lean versions of some of the main assumptions above:
#check CompleteLinearOrder
#check DenselyOrdered

-- Some API of infimums and supremums that you might need:
#check sInf_le        -- The infimum is a lower bound.
#check le_sInf        -- The infimum is greater than any other lower bound.
#check sInf_le_sInf   -- The infimum of a larger set is smaller.
-- You should be able to find (name-guess) similar results about the supremum.

-- And some other useful basic lemmas.
#check lt_of_le_of_lt -- A kind of a transitivity lemma combining strict and nonstrict inequalities.
#check lt_of_lt_of_le -- A kind of a transitivity lemma combining strict and nonstrict inequalities.

-- There will probably be other results that you need to find. That is a part of formalization.


-- ## The setup.

-- So now let `R` and `S` be complete linear ordered sets (well, types in Lean).
variable {R : Type} [CompleteLinearOrder R]
variable {S : Type} [CompleteLinearOrder S]

/-- The left-continuous pseudoinverse of a function. -/
def lcInv (F : R → S) (y : S) := sInf {x | y ≤ F x}

variable {F : R → S}

#check lcInv F -- `lcInv F : S → R`

-- **EXERCISE:** Prove that...
/-- The function `lcInv F` is increasing. -/
lemma lcInv_mono (F : R → S) :
    Monotone (lcInv F) := by
  -- Quite straightforward, but make sure you know the maths proof first.
  intro a b a_b

  -- rw [le_iff_eq_or_lt] at a_b
  -- cases' a_b with ab_eq ab_lt
  -- · rw [ab_eq]

  unfold lcInv

  refine sInf_le_sInf ?_
  simp only [setOf_subset_setOf]
  intro x bFx
  trans b
  exact a_b
  exact bFx




-- **EXERCISE:** Prove that...
lemma lcInv_apply_self_le (x : R) :
    (lcInv F) (F x) ≤ x := by
  -- Very easy, but again make sure you know the maths proof first.
  unfold lcInv
  refine sInf_le ?_
  rw [mem_setOf_eq]


-- **EXERCISE:** Prove that...
lemma le_sInf_setOf_lcInv_ge {F : R → S} (x x' : R) (hx : x' < x) :
    F x' ≤ sInf {y | x ≤ lcInv F y} := by
  -- Hint: First prove that when `x' < x` we have ` (lcInv F) (F x') ≤ x' < x `.
  -- Hint: Use a proof by contradiction, where the contradiction is with the property that the
  -- infimum (in the statement) being the greatest lower bound for a set.

  -- rw [←lcInv]
  have lem : (lcInv F) (F x') < x := by
    exact lt_of_le_of_lt (lcInv_apply_self_le x') hx
  by_contra cont
  apply lt_of_not_le at cont
  rw [sInf_lt_iff] at cont
  have ⟨a, ain, aFx⟩ := cont
  rw [mem_setOf_eq] at ain
  have mono := lcInv_mono F
  unfold Monotone at mono
  specialize mono (aFx.le)
  have ax := lt_of_le_of_lt mono lem
  have ax1 := lt_of_lt_of_le ax ain
  simp only [lt_self_iff_false] at ax1


-- **EXERCISE:** Prove that...
lemma sInf_setOf_lcInv_ge_ge_sSup (x : R) :
    sInf {y | x ≤ lcInv F y} ≥ sSup (F '' Iio x) := by
  -- Hint: The key to the maths proof is the lemma `le_sInf_setOf_lcInv_ge` above;
  -- First sort out the math details, then this is straightforward.
  change _ ≤ _
  -- set l :=  sInf {y | x ≤ lcInv F y}
  simp only [sSup_le_iff, mem_image, mem_Iio, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂]
  intro x' hx
  exact le_sInf_setOf_lcInv_ge x x' hx



-- **EXERCISE:** Prove that...
lemma lcInv_ge_of_sSup_lt (x : R) (z : S) (hz : sSup (F '' Iio x) < z) :
    lcInv F z ≥ x := by
  -- Hint: The key to that is that for all `x' < x` we have `F x' < z`.
  -- Hint: Use a proof by contradiction, where the contradiction is with the property that the
  -- infimum (in the definition of `lcInv F`) is the greatest lower bound for a set.
  change _ ≤ _
  -- have := DenselyOrdered.dense (sSup (F '' Iio x)) z

  -- let sw := sSup (F '' Iio x)
  -- simp_rw [sSup_le_iff, mem_image, mem_Iio, forall_exists_index, and_imp,
  --   forall_apply_eq_imp_iff₂] at sw
  have ⟨ hz_le,hz_ne ⟩ := lt_iff_le_and_ne.mp hz
  simp_rw [sSup_le_iff, mem_image, mem_Iio, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂] at hz_le
  simp only [ne_eq] at hz_ne
  -- simp_rw [le_iff_lt_or_eq] at hz_le
  have : ∀ a < x, ¬ F a = z := by
    intro x' hx
    -- let q := F '' Iio x
    intro Fxz
    rw [←Fxz] at hz
    have iio_sub : Iio x' ⊆ Iio x := by
      simp only [Iio_subset_Iio_iff]
      exact le_of_lt hx
    have Fii_sub : (F '' Iio x') ⊆ (F '' Iio x) := by
      exact image_mono iio_sub
    have := sSup_le_sSup Fii_sub

    -- change  sSup ({w | w ∈  F '' Iio x}) < _ at hz
    -- simp only [mem_image, mem_Iio] at hz




    apply ne_of_lt









  sorry

-- **EXERCISE:** Prove that...
lemma ge_sInf_setOf_lcInv_ge (x : R) (z : S) (hz : sSup (F '' Iio x) < z) :
    z ≥ sInf {y | x ≤ lcInv F y} := by
  -- Hint: This follows straightforwardly from `lcInv_ge_of_sSup_lt`.
  sorry


-- From this point on, we will need the assumption of dense ordering. A key lemma about it
-- is `exists_between`:
#check exists_between

-- A key lemma in the following is `sInf_eq_of_forall_ge_of_forall_gt_exists_lt`:
#check sInf_eq_of_forall_ge_of_forall_gt_exists_lt

-- (This is not strictly necessary below, but it is an easier version of the key idea.)
-- **EXERCISE:** As a warm-up for the next one, prove that...
lemma sInf_Ioi {α : Type*} [CompleteLattice α] {a : α} [DenselyOrdered α] :
    sInf (Ioi a) = a := by
  -- Hint: Figure out what `sInf_eq_of_forall_ge_of_forall_gt_exists_lt` is saying
  -- and use it and `exists_between` appropriately.
  sorry

-- **EXERCISE:** Prove that...
lemma sInf_setOf_lcInv_ge_le_sSup (x : R) [DenselyOrdered S] :
    sInf {y | x ≤ lcInv F y} ≤ sSup (F '' Iio x) := by
  -- Hint: The key is still `sInf_eq_of_forall_ge_of_forall_gt_exists_lt`, but more thinking
  -- is required for this.
  sorry

-- **EXERCISE:** Prove that...
/-- If `G : S → R` is the left-continuous pseudoinverse of `F : R → S`, then we have
`inf {y ∈ S | G(y) ≥ x} = sup {F(x') | x' < x}`. -/
theorem sInf_setOf_lcInv_ge_eq_sSup [DenselyOrdered S] (x : R) :
    sInf {y | x ≤ lcInv F y} = sSup (F '' Iio x) := by
  -- Hint: This now follows easily by combining the previous results.
  sorry

end left_continuous_inverse

end AaltoFormalMath2025
