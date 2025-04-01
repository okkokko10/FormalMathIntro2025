import Mathlib

namespace AaltoFormalMath2025

section diagram_chase_exercise
/-!
# Exercise: a small diagram chase

Let U, V, W be vector spaces, and f : U → V an injective linear map,
and g : V → W a surjective linear map, such that the kernel of g coincides
with the range of f. In diagrammatic terms, we have the short exact sequence:

                 f        g
    0 -----> U -----> V -----> W -----> 0 .

(f embeds U into V, and g projects from V to W
and we have "exactness in the middle": ker g = ran f)

Since g is assumed surjective, there exist "sections" σ of the above, i.e.,
linear maps σ : W → V such that g(σ(w)) = w for every w ∈ W, i.e, the following
square commutes (the vertical arrows are identity maps).

                 f        g
    0 -----> U -----> V -----> W -----> 0 .
                      ∧        ∧
                      |        |
                      V <----- W
                           σ

Fix a choice σ of such a section. The goal of this exercise is to do in Lean
the small diagram chase needed to construct a linear map γ : V → U uniquely
determined by the condition that v = σ(g(v)) + f(γ(v)) for any v ∈ V.

                 f        g
    0 -----> U -----> V -----> W -----> 0 .
             ∧        :
             |        :
             U <----- V
                  γ

Let us call that map γ the "corrector (linear) map" for the lack of better
term, because it describes by which embedded element of U in V the vector
v differs from σ(g(v)).
In other words, any v ∈ V gets uniquely decomposed to a vector σ(g(v)) in
the image of the section σ and a "corrector term" f(γ(v)) in the image of
the embedding f. This gives a direct sum decomposition of V (V ≃ U ⊕ W).
One last reinterpretation is that using (id_V - σ ∘ g) : V → V as a map
vertically in the middle ":" would make the completed square commute.

(Situations of this kind appear very frequently in mathematics; this is
essentially the simplest case of "diagram chasing" arguments
<https://en.wikipedia.org/wiki/Commutative_diagram#Diagram_chasing>.)
-/

-- Let `𝕜` be a field.
variable {𝕜 : Type} [Field 𝕜]

-- Let `U`, `V`, and `W` be vector spaces over `𝕜`
variable {U V W : Type}
variable [AddCommGroup U] [Module 𝕜 U]
variable [AddCommGroup V] [Module 𝕜 V]
variable [AddCommGroup W] [Module 𝕜 W]

-- Let f : U → V and g : V → W be linear maps.
variable {f : U →ₗ[𝕜] V} {g : V →ₗ[𝕜] W}

-- (We will assume injectivity of f and surjectivity of g and
-- "exactness in the middle" below separately, as needed. The reason is just
-- to fix the order of some arguments, so that the outline of the exercise
-- does not break depending on what you fill in in the `sorry`es.)

open LinearMap
-- We don't want to write `LinearMap.ker` and `LinearMap.range` all the time.

--variable (hf' : ker f = ⊥)
--variable (g_surj' : range g = ⊤)
--variable (hfg' : range f = ker g)

-- Let σ : W → V be a linear map.
variable {σ : W →ₗ[𝕜] V}

-- (We will assume g ∘ σ = id_W below separately, as needed. Same reason.)
-- variable (hgσ' : g ∘ₗ σ = 1)


/-- Uniqueness of the "corrector" for a given vector. -/
lemma unique_corrector (hf : ker f = ⊥) (v : V) (u₁ u₂ : U)
    (h₁ : v = σ (g v) + f u₁) (h₂ : v = σ (g v) + f u₂) :
    u₁ = u₂ := by

  -- First make sure you know which mathematical assumption guarantees uniqueness here and how.


  -- have hh := Mathlib.Tactic.LinearCombination.add_eq_eq h₁ (congrArg (fun x ↦ -x) h₂)
  -- norm_num at hh
  -- rw [←add_assoc] at hh
  -- rw [neg_add_cancel] at hh
  have hq := Eq.trans (Eq.comm.mp h₁) h₂
  norm_num at hq
  let ud := u₁ - u₂
  let fud := f ud
  have qq : f ud = 0 ↔ ud ∈ (ker f) := by exact Eq.to_iff rfl
  rw [hf] at qq
  simp at qq
  have sub_eq_zero {U1 : Type} [AddCommGroup U1] (a b : U1 ) : a - b = 0 → a = b := by
    intro amb
    apply congrArg (fun x ↦ x + b) at amb
    norm_num at amb
    exact amb
  suffices ud = 0 by
    -- unfold ud at this
    exact sub_eq_zero u₁ u₂ this
  rw [←qq]
  simp [ud]
  rw [hq]
  norm_num


  done

/-- Existence of the "corrector" for a given vector. -/
lemma exists_corrector (hfg : range f = ker g) (hgσ : g ∘ₗ σ = 1) (v : V) :
    ∃ (u : U), v = σ (g v) + f u := by
  -- First make sure you know which mathematical assumption guarantees existence here and how.
  -- When using the hypothesis `hgσ`, you may find `LinearMap.congr_fun` useful.
  have h_1 (x) : (g ∘ₗ σ) x = x := by
    rw [hgσ]
    simp only [one_apply]
  have h_2 (x) : (σ ∘ₗ (g ∘ₗ σ)) x = σ x := by
    suffices (g ∘ₗ σ) x = x by exact Eq.symm (LinearMap.congr_arg (_root_.id (Eq.symm this)))
    exact h_1 x

  have h_3(x) : g v = g (v + σ x) - x  := by
    suffices  g v + x = g (v + σ x) by
      exact (sub_eq_iff_eq_add.mpr this.symm).symm
    simp
    exact (h_1 x).symm

  suffices ∀ (v1 : V), ∃ (u : U), v1 = σ (g v1) + f u by exact this v
  suffices ∀ (v1 : V), ∃ (u : U), v1 - f u = σ (g v1)  by sorry
  save

  have change_of_variable (w : V) ( P : V → Prop) : (∀ v1 : V, P v1) ↔  (∀ v2 : V, P (v2 + w)) := by
    constructor
    · intro l vv
      exact l (vv + w)
    · intro l vv
      have qqq := l (vv - w)
      -- simp only [sub_add_cancel] at qqq
      exact (sub_add_cancel vv w) ▸ qqq



  suffices ∀ (v2 : V), ∃(vv : V), ∃ (u : U), v2 + vv - f u = σ (g (v2 + vv))  by
    intro v1
    have aa := this v1

    done





  -- have h_3 (x) : (σ ∘ₗ g) (σ x) = σ x := by
  --   exact h_2 x
  -- have h_4 (y) : y ∈ range σ → (σ ∘ₗ g) y = y := by
  --   intro ⟨x,y_def⟩
  --   rw [←y_def]
  --   exact h_3 x

  -- suffices ∃ u, v = (σ ∘ₗ g) (σ (g v)) + f u by
  --   rcases this with ⟨u,ww⟩
  --   use u
  --   simp [h_3] at ww
  --   exact ww


  -- use sorry

  -- apply fun x ↦ LinearMap.congr_fun x (σ ∘ₗ g)

  sorry

-- We now use `Exists.choose` with `exists_corrector` to define a
-- "corrector" `γ v : U` for any `v : V`.
/-- The corrector map `γ : V → U` (such that...) -/
noncomputable def corrector (hfg : range f = ker g) (hgσ : g ∘ₗ σ = 1) (v : V) : U :=
  (exists_corrector hfg hgσ v).choose

-- We can use `Exists.choose_spec` to show that the "corrector" thus
-- defined has the desired property.
/-- The corrector map `γ : V → U` satisfies `v = σ(g(v)) + f(γ(v))` for any `v : V`. -/
lemma corrector_spec (hfg : range f = ker g) (hgσ : g ∘ₗ σ = 1) (v : V) :
    v = σ (g v) + f (corrector hfg hgσ v) :=
  (exists_corrector hfg hgσ v).choose_spec

/-
We have defined a function `γ : V → U` which obviously must be linear, because all
conditions involved in its unique construction were linear. But Lean does not know
that; we need to tell it to Lean.

So our goal is to promote the function `γ : V → U` to a linear map `γ : V → U`.
That promoted version of `corrector` will will be `correctorHom` below. The two
properties that we need to prove are that `γ` (i.e., `corrector`) respects addition
and scalar multiplication.
-/

/-- `corrector` respects scalar multiplication. -/
lemma corrector_smul (hf : ker f = ⊥) (hfg : range f = ker g) (hgσ : g ∘ₗ σ = 1) (c : 𝕜) (v : V) :
    corrector hfg hgσ (c • v)
      = c • corrector hfg hgσ v := by
  -- Make sure you know the maths proof first. It uses earlier results.
  sorry

/-- `corrector` respects scalar vector addition. -/
lemma corrector_add (hf : ker f = ⊥) (hfg : range f = ker g) (hgσ : g ∘ₗ σ = 1) (v₁ v₂ : V) :
    corrector hfg hgσ (v₁ + v₂)
      = corrector hfg hgσ v₁ + corrector hfg hgσ v₂ := by
  -- Make sure you know the maths proof first. It uses earlier results.
  sorry

-- This allows us to build a "corrector" linear map.
/-- The corrector *linear map* `γ : V → U` (such that...). -/
noncomputable def correctorHom (hf : ker f = ⊥) (hfg : range f = ker g) (hgσ : g ∘ₗ σ = 1) :
    V →ₗ[𝕜] U where
  toFun := corrector hfg hgσ
  map_add' v₁ v₂ := corrector_add hf hfg hgσ v₁ v₂
  map_smul' c v := corrector_smul hf hfg hgσ c v

-- ...which still satisfies the desired property.
/-- The corrector linear map `γ : V → U` satisfies `v = σ(g(v)) + f(γ(v))` for any `v : V`. -/
lemma correctorHom_spec (hf : ker f = ⊥) (hfg : range f = ker g) (hgσ : g ∘ₗ σ = 1) (v : V) :
    v = σ (g v) + f ((correctorHom hf hfg hgσ) v) :=
  corrector_spec hfg hgσ v

end diagram_chase_exercise

end AaltoFormalMath2025
