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


set_option linter.unusedTactic false

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

  -- ∃ c > 0, ∃ si ∈ SubIoo (Icc a b), ∀ x ∈ si, c ≤ f x
  have ⟨z_ioo, fz_n0⟩  := f_ne_zero.choose_spec
  set z := f_ne_zero.choose
  have fz_pos : 0 < f z := by
    refine lt_of_le_of_ne ?_ ?_
    · exact f_nn z
    · exact fz_n0.symm

  let c := (f z) / 2
  use c, (by positivity)

  -- plan: use
  #check IsOpen.preimage
  -- in a positive neighborhood of (f z)
  -- to get an open set containing z
  -- which must have as subset an open interval containing z (the portion connected to z)
  let c3 := f z * 3 / 2
  let fz_neigh := Ioo c c3
  have fz_neigh_open : IsOpen fz_neigh := isOpen_Ioo
  have wz_open := fz_neigh_open.preimage f_cont
  set wz := f ⁻¹' fz_neigh
  have wz_gt_c : ∀ x ∈ wz, c ≤ f x := by
    unfold wz fz_neigh
    simp only [mem_preimage, mem_Ioo, and_imp]
    intros
    linarith
  have wz_has_z : z ∈ wz := by
    unfold wz fz_neigh c c3
    simp only [mem_preimage, mem_Ioo]
    constructor <;> linarith

  have z_neigh_exists : ∃ a' b', a' ∈ Icc a b ∧ b' ∈ Icc a b ∧  Ioo a' b' ⊆ wz
    ∧ a' < b'
    --∧ z ∈ Ioo a' b'
    := by

    let wz_inside := wz ∩ Ioo a b
    have wz_inside_open : IsOpen wz_inside := by
      unfold wz_inside
      refine IsOpen.inter wz_open ?_
      exact isOpen_Ioo
    have wz_inside_has_z : z ∈ wz_inside := by exact mem_inter wz_has_z z_ioo

    -- have : wz.Nonempty := by exact nonempty_of_mem wz_has_z
    have ioo := wz_inside_open.exists_Ioo_subset (nonempty_of_mem wz_inside_has_z)

    have ⟨ a',b',a'_lt_b',io⟩ := ioo
    use a', b'
    have within : Ioo a' b' ⊆ Ioo a b := by
      trans wz_inside
      exact io
      exact inter_subset_right
    simp only [mem_Icc]

    have ⟨aa, bb⟩  := (Ioo_subset_Ioo_iff a'_lt_b').mp within
    simp [aa,bb, le_trans a'_lt_b'.le bb, le_trans aa a'_lt_b'.le]
    constructor
    · trans wz_inside
      · exact io
      · exact inter_subset_left
    · exact a'_lt_b'



    -- let z_neigh := connectedComponentIn wz z
    -- have z_neigh_open : IsOpen z_neigh := by
    --   exact IsOpen.connectedComponentIn wz_open

    -- #check isOpen_iff_generate_intervals
    -- have openInterval : ∃ a' b', Ioo a' b' = z_neigh := by
    --   unfold z_neigh


    -- -- let a' := (sInf z_neigh) ⊔ a
    -- -- let b' := sSup z_neigh ⊓ b

    -- have ⟨ a',b',io⟩ :=

    -- have a'_lt_b' : a' < b' := sorry
    -- use a', b'
    -- simp only [mem_Icc]
    -- -- constructor
    -- -- · constructor
    -- --   · exact le_max_right (sInf z_neigh) a
    -- --   ·
    -- --   done


    -- sorry

  have ⟨a', b', a'i, b'i, zn_sub, a'_lt_b'⟩ := z_neigh_exists
  use a', a'i, b', b'i, a'_lt_b'
  exact fun x a ↦ wz_gt_c x (zn_sub a)





  -- sorry

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


  have lem := exists_forall_mem_Ioo_gt f a_lt_b f_cont f_nn f_ne_zero
  have ⟨c, c_pos, a', ain,b', bin, a_b, great⟩ := lem
  -- simp only [gt_iff_lt]
  #check setLIntegral_mono

  let zer : ℝ → ENNReal :=
    fun x ↦ Set.indicator (Ioo a' b') (fun _ ↦ ENNReal.ofReal c) x


  -- let f' : ℝ → ENNReal := fun x ↦ ENNReal.ofReal (f x)
  let f' : ℝ → ENNReal := ENNReal.ofReal ∘ f

  have f'_cont : Continuous f' := by
    -- unfold f'
    -- rw [continuous_def] at f_cont ⊢
    -- intros s os
    have := ENNReal.continuous_ofReal
    exact Continuous.comp ENNReal.continuous_ofReal f_cont


  have measurable_f : Measurable f' := by
    exact Continuous.borel_measurable f'_cont

  have f_nn_ioc : ∀ x ∈ Ioc a b, zer x ≤ f' x := by

    intros x ax
    unfold zer
    unfold indicator
    by_cases hx : x ∈ Ioo a' b'

    simp only [hx, ↓reduceIte]
    unfold f'
    simp only [Function.comp_apply]
    exact ENNReal.ofReal_le_ofReal (great x hx)
    simp only [hx, ↓reduceIte, zero_le]




  -- let s := Ioc a b

  have m : Measure ℝ := by exact ProbabilityTheory.gammaMeasure a a

  -- have q : ∫⁻ (x : ℝ) in Ioc a b, zer x ≤ ∫⁻ (x : ℝ) in Ioc a b, f' x --ENNReal.ofReal (f x)
  --   := @setLIntegral_mono _ _ _ _ _ _ measurable_f f_nn_ioc
  have q : ∫⁻ (x : ℝ) in Ioc a b, zer x ≤ ∫⁻ (x : ℝ) in Ioc a b, f' x := setLIntegral_mono measurable_f f_nn_ioc
  -- Okko: why does this need the type hint to work?


  unfold f' at q
  simp only [Function.comp_apply] at q
  refine lt_of_lt_of_le ?_ q

  unfold zer
  simp only [measurableSet_Ioo, lintegral_indicator, Measure.restrict_restrict, lintegral_const,
    MeasurableSet.univ, Measure.restrict_apply, univ_inter, CanonicallyOrderedAdd.mul_pos,
    ENNReal.ofReal_pos]
  simp only [c_pos, true_and]
  have subsetness : Ioo a' b' ⊆ Ioc a b := by
    intro x xa
    simp only [mem_Ioo] at xa
    have ⟨ain1,ain2⟩ := ain
    have ⟨bin1,bin2⟩ := bin
    simp [a_b,bin1,bin2,ain1,ain2,xa]
    constructor
    exact lt_of_le_of_lt ain1 xa.left
    exact le_trans xa.right.le bin2
  have so (s1 s2 : Set ℝ) : s1 ⊆ s2 → s1 ∩ s2 = s1 := by
    intro www
    exact (left_eq_inter.mpr www).symm
  simp [so _ _ subsetness]
  exact a_b


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

  #check intervalIntegral.integral_mono_on

  have lem := main_goal₁ f a_lt_b f_cont f_nn f_ne_zero

  sorry

end nonvanishing_integral

end AaltoFormalMath2025
