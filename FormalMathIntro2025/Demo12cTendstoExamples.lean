import Mathlib

namespace AaltoFormalMath2025



open Filter Set Topology


section pullback_filter

-- Let `f : X → Y` a function and let `G` be a filter on `Y`.
variable {X Y : Type} (f : X → Y) (G : Filter Y)

#check G.comap f -- Pulling back `G` via `f : X → Y` gives a filter on `X`.

-- This is what the pullback means be definition:
example (s : Set X) :
    s ∈ G.comap f ↔ ∃ u ∈ G, f ⁻¹' u ⊆ s := by
  rfl

-- If one thinks of `G` as a generalized set in `Y`, then the pullback `G.comap f` is a
-- generalized set in `X` defined essentially as the preimage of the generalized set `G` under `f`.

end pullback_filter


section pushforward_filter

-- Let `f : X → Y` a function and let `F` be a filter on `X`.
variable {X Y : Type} (f : X → Y) (F : Filter X)

#check F.map f -- Pushing forward `F` via `f : X → Y` gives a filter on `Y`.

-- This is what the pushforward means:
example (u : Set Y) :
    u ∈ F.map f ↔ ∃ s ∈ F, f '' s ⊆ u := by
  exact mem_map_iff_exists_image

-- If one thinks of `F` as a generalized set in `X`, then the pushforward `F.map f` is a
-- generalized set in `Y` defined essentially as the image of the generalized set `F` under `f`.

-- Okko:

example (u : Set Y) :
    u ∈ F.map f ↔ ∃ fs ∈ ((f '' · ) '' F.sets), fs ⊆ u := by
  have : (∃ s ∈ F, f '' s ⊆ u) ↔ ∃ fs ∈ ((f '' · ) '' F.sets), fs ⊆ u := by
    simp only [image_subset_iff, mem_image, Filter.mem_sets, exists_exists_and_eq_and]
  rw [←this]
  exact mem_map_iff_exists_image

-- this is false?
example : F = Filter.principal (⋂₀ F.sets) := by
  ext s
  simp_all only [mem_principal]
  apply Iff.intro
  · intro sF
    apply sInter_subset_of_mem
    exact sF
  · intro a
    have : ⋂₀ F.sets ∈ F := by

      sorry
    sorry


-- proof that the above is false:
example : ∃ (X : Type) (F : Filter X), F ≠ Filter.principal (⋂₀ F.sets) := by
  -- set F : Filter ℕ := atTop
  use ℕ, atTop
  simp only [ne_eq]
  intro cont
  set se := ⋂₀ (atTop : Filter ℕ).sets with se_def
  rw [Set.ext_iff] at se_def
  simp_rw [mem_sInter] at se_def
  have impli (p q : ℕ → Prop) : (∀x, p x ↔ q x) → (∀x, p x → q x) := by
    exact (Iff.mp <| · ·)
    -- exact fun w x ↦ (w x).mp
    -- intro w x px
    -- exact (w x).mp px
  -- apply [forall_imp_iff] at se_def
  apply (impli _ _) at se_def

  -- idea: show that se_def implies se is empty, then note that atTop is not the ⊥

  have nothin (x : ℕ): ∃ t ∈ atTop.sets, x ∉ t := by
    use {y | x+1 ≤ y}
    constructor
    apply mem_atTop
    simp only [mem_setOf_eq, add_le_iff_nonpos_right, nonpos_iff_eq_zero, one_ne_zero,
      not_false_eq_true]
  have se_empty: ∀ x, x ∉ se := by
    intro x xse
    have ⟨t,tin,xnint⟩ := nothin x
    -- have p2 := se_def x xse t tin
    -- have := se_def x (se_def x xse) t tin
    exact xnint (se_def x xse t tin)
  -- clear nothin
  have se_empty2 : se = ∅ := by exact subset_eq_empty se_empty rfl-- sInter_eq_empty_iff.mpr nothin

  rw [se_empty2] at cont
  simp only [principal_empty] at cont

  rw [Filter.ext_iff,←not_exists_not] at cont

  apply cont

  use ∅
  simp only [empty_not_mem, mem_bot, iff_true, not_false_eq_true]

  done

-- example (u : Set Y) :
--     (∃ fs ∈ ((f '' · ) '' F.sets), fs ⊆ u) ↔ u ∈  Filter.principal (⋂₀ ((f '' · ) '' F.sets)) := by
--   have : u ∈ F.map f ↔ ∃ fs ∈ ((f '' · ) '' F.sets), fs ⊆ u := sorry
--   rw [←this]
--   simp only [mem_map, sInter_image, Filter.mem_sets, mem_principal]
--   sorry


end pushforward_filter




section filter_tendsto

-- Let `f : X → Y` a function and let `F` and `G` be filters on `X` and `Y`, respectively.
variable {X Y : Type} (f : X → Y) (F : Filter X) (G : Filter Y)

-- For intuition about the statement "the function `f` tends to `G` along `F`", it may be best
-- to think in terms of generalized sets again.

#check Filter.Tendsto f F G -- the statement "the function `f` tends to `G` along `F`"
#check F.Tendsto f G -- same, but shorter

-- Here is the definition.
example : F.Tendsto f G ↔ F.map f ≤ G := by
  rfl

-- And here is an equivalent condition.
example : F.Tendsto f G ↔ F ≤ G.comap f := by
  exact tendsto_iff_comap

end filter_tendsto

-- Okko
section set_similarities

variable {X : Type} (x y : Set X)
example : x ⊆ y ↔ y ∈ 𝓟 x := by rfl
example : x ⊆ y ↔ 𝓟 x ≤ 𝓟 y := by simp only [le_principal_iff, mem_principal]
example : 𝓟 (x ∩ y) = (𝓟 x) ⊓ (𝓟 y) := by simp only [inf_principal]

-- f ≤ g ↔ ∀ x ∈ g, x ∈ f  -- everything greatere than g is greatere than f

lemma bounding (f g : Filter X) (y): (y ∈ f) → ∀ x ∈ g, y ⊆ x → x ∈ f := by
  intros yf x xg yx
  apply Filter.mem_of_superset yf yx

lemma bounding1 (f g : Filter X) (y) : (y ∈ f) → (f ≤ g ↔ ∀ x ∈ g, ¬(y ⊆ x) → x ∈ f) := by
  intros yf
  have truth := (bounding f g y) yf
  conv => {
    right

    intro x xg
    tactic => {
      have tru := truth x xg
      by_cases h : y ⊆ x
      simp only [h, not_true_eq_false, IsEmpty.forall_iff, eq_iff_iff, true_iff]
      exact tru h
      simp only [h, not_false_eq_true, forall_const]
    }
  }
  exact le_def
lemma bounding11 (f : Filter X) (y) : (y ∈ f) → ∀x, x ∈ f ↔ (x ∩ y) ∈ f := by
  intros yf x
  simp only [inter_mem_iff, iff_self_and]
  intro
  exact yf

lemma bounding2 (f g : Filter X) (y) : (y ∈ f) → (f ≤ g ↔ ∀ x ∈ g, (x ∩ y) ∈ f) := by
  intros yf
  simp_rw [←bounding11 f y yf _]
  exact le_def

lemma bounding21 (f g : Filter X) (y) : (y ∈ f) → (f ≤ g ↔ ∀ xy ∈ ((· ∩ y) '' g.sets), xy ∈ f) := by
  intros yf
  simp only [mem_image, Filter.mem_sets, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
    inter_mem_iff]
  simp only [bounding2 f g y yf, inter_mem_iff]

lemma bounding22 (g : Filter X) (y) : (y ∈ g) → false := by
  intros yg
  simp
  set s := (· ∩ y) '' g.sets with sd
  simp at sd
  simp only [image, Filter.mem_sets] at sd
  apply Set.ext_iff.mp at sd
  have hw : ∀x ∈ g, _ := (imp_intro <| sd ·)
  conv at hw => {
    intro x xg

    simp only [mem_setOf_eq]
    -- x is in g. a = x is sufficient and necessary.
    right

  }
  sorry


-- a filter is closed under intersection and union.

example (f : Filter X) : (y ∈ f) → ¬(x ∈ f) → ¬ (x∩y) ∈ f := by
  intro a a_1
  simp_all only [inter_mem_iff, and_true, not_false_eq_true]

-- is this true even?
example (f g : Filter X) (y) : (y ∈ f) → (f ≤ g ↔ ∀ x ∈ g, x = (x ∩ y) → (x ∩ y) ∈ f) := by
  intros yf

  simp_rw [bounding2 f g y yf]
  constructor
  · intro lft x xg xxy
    exact lft x xg
  · intro rht x xg
    have w := rht x xg
    rw [inter_mem_iff]
    simp only [yf, and_true]
    sorry
    done




end set_similarities


section some_examples

/- The function `x ↦ eˣ` tends to `0` as `x → -∞`. -/
example : Tendsto Real.exp atBot (𝓝 (0 : ℝ)) := by
  exact Real.tendsto_exp_atBot



-- Okko: the one below
example :
    Tendsto (fun (x : ℝ) ↦ 1/x^2) (𝓝[≠] (0 : ℝ)) atTop := by
  rw [tendsto_def]
  intros s sat

  set w := (fun x : ℝ ↦ 1 / x ^ 2)
  have aw (p): w '' p = s → p ⊆  w ⁻¹' s := by
    intro a
    subst a
    exact subset_preimage_image w p
  suffices ∃p ∈ (𝓝[≠] 0), w '' p = s by
    have ⟨p,q1,q2⟩ := this

    -- have := aw p q2
    exact mem_of_superset q1 (aw p q2)

    done



  sorry

/- The function `x ↦ x⁻²` tends to `+∞` as `x → 0` (along the punctured neighborhoods filter). -/
example :
    Tendsto (fun (x : ℝ) ↦ 1/x^2) (𝓝[≠] (0 : ℝ)) atTop := by
  have aux : -- A good strategy is to compose easier pieces.
      (fun (x : ℝ) ↦ 1/x^2)
        = (fun (x : ℝ) ↦ x⁻¹) ∘ (fun (x : ℝ) ↦ x ^ 2) := by
    ext x ; simp
  rw [aux]
  apply Tendsto.comp -- It suffices to prove the convergence of the pieces, and compose limits!
  · exact tendsto_inv_nhdsGT_zero
  · have obs : Tendsto (fun (x : ℝ) ↦ x^2) (𝓝 (0 : ℝ)) (𝓝 (0 : ℝ)) := by
      have sq_cont : Continuous (fun (x : ℝ) ↦ x^2) := by continuity
      simpa [ContinuousAt] using sq_cont.continuousAt (x := 0)
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · exact tendsto_nhdsWithin_of_tendsto_nhds obs
    · have filt : {0}ᶜ ∈ 𝓝[≠] (0 : ℝ) := by exact self_mem_nhdsWithin
      filter_upwards [filt] with x hx
      simp only [mem_Ioi]
      exact lt_of_le_of_ne (sq_nonneg x) (sq_pos_of_ne_zero hx).ne

end some_examples



end AaltoFormalMath2025
