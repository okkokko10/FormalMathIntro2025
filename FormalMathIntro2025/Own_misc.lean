import Mathlib.Tactic -- imports all the Lean tactics

section Okko

/-- to show it's not just real numbers -/
def R := ℝ
def N := ℕ

section misc

theorem swap_forall {X Y : Type} {a : X → Prop} {b : Y → Prop}  {f : X → Y → Prop} :
  (∀ x y, a x → b y → f x y) ↔ (∀ x, a x → ∀y, b y → f x y) :=
  by
    -- tauto
    suffices
      ∀ x, ( ∀ y, a x → b y → f x y) ↔ ( a x → ∀y, b y → f x y)
    by exact forall_congr' this
    suffices
      ∀ x, ( a x → ∀ y, b y → f x y) ↔ ( a x → ∀y, b y → f x y)
      by exact fun x ↦ Iff.symm imp_forall_iff
    intro x
    rfl
    done

end misc


def InTail {X : Type} (a : ℕ → X) (B : ℕ) (an : X) : Prop :=
  ∃ n, B ≤ n ∧ (a n = an)
  section
  theorem inTail_def {X : Type} {a : ℕ → X} {B : ℕ} {f : X → Prop} :
    (∀ an, InTail a B an → f an) ↔ ∀ n, B ≤ n → f (a n) :=
    by exact Set.forall_mem_image

  theorem inTail_def' {X : Type} (a : ℕ → X) (B : ℕ) (an : X) :
    InTail a B an ↔ an ∈ a '' {n | B ≤  n} := by rfl

  theorem inTail2 {X : Type} {a : ℕ → X} {B : ℕ} {f : X → X → Prop} :
    (∀ an am, InTail a B an → InTail a B am → f an am) ↔ ∀ n m, B ≤ n → B ≤ m → f (a n) (a m) :=
    by
      -- rw [swap_forall]
      -- simp only [inTail_def]
      -- rw [swap_forall]


      simp [inTail_def,swap_forall]



  end

def InHead {X : Type} (a : ℕ → X) (B : ℕ) (an : X) : Prop :=
  ∃ n, B > n ∧ (a n = an)
section InHead
  theorem inHead_def {X : Type} (a : ℕ → X) (B : ℕ) (an : X) : InHead a B an ↔ ∃ n, B > n ∧ (a n = an) := by rfl

  theorem inHead_def' {X : Type} (a : ℕ → X) (B : ℕ) (an : X) :
    InHead a B an ↔ an ∈ a '' {n | B > n} := by rfl




end InHead


def Tail{X : Type}(a : ℕ → X)(B : ℕ) := a '' {n | B ≤  n} --InTail a B ⁻¹' {True}
  section

  theorem tail_def{X : Type} {a : ℕ → X} {B : ℕ} :
    Tail a B = a '' {n | B ≤ n} := by rfl
      -- simp [tail_def, inTail_def']
  theorem tail_def'{X : Type} {a : ℕ → X} {B : ℕ} :
    Tail a B = InTail a B ⁻¹' {True} := by
      simp [tail_def,inTail_def']
      rfl
  theorem tail_def''{X : Type} {a : ℕ → X} {B : ℕ} :
    Tail a B = {w | InTail a B w} := by
      simp [tail_def']




  end

def Tails{X : Type}(a : ℕ → X) := {Tail a B | B}
  section
  theorem tails_def {a : ℕ → ℝ} :
    Tails a = {Tail a B | B} := by rfl

  theorem tails_def' {a : ℕ → ℝ} :
    Tails a = Set.range (Tail a) := by
      simp only [tails_def]
      rfl
      done
  end


def Head{X : Type}(a : ℕ → X)(B : ℕ) := a '' {n | B >  n}
section

  theorem head_def{X : Type} {a : ℕ → X} {B : ℕ} :
    Head a B = a '' {n | B >  n} := by rfl
  theorem head_def'{X : Type} {a : ℕ → X} {B : ℕ} :
    Head a B = InHead a B ⁻¹' {True} := by
      simp only [Set.preimage_singleton_true]
      rfl

end


def Neighborhood (z) (ε : ℝ) := {w | |w - z| < ε}
  section
  theorem neighborhood_def {z} {ε : ℝ} :
    Neighborhood (z) (ε : ℝ) = {w | |w - z| < ε}
    := by rfl



  theorem neighborhood_contains_le {z} {ε1 ε2 : ℝ} :
    ε1 ≤ ε2 →
    Neighborhood z ε1 ⊆ Neighborhood z ε2 := by
      simp [neighborhood_def]
      intros le w w1
      exact gt_of_ge_of_gt le w1



  end

def Neighborhoods (z) := Neighborhood z '' {ε | ε > 0}
  section
  theorem neighborhoods_def {z} :
    Neighborhoods (z) = Neighborhood z '' {ε | ε > 0}
    := by rfl
  theorem neighborhoods_def'' {z} :
    Neighborhoods (z) = {Neighborhood z ε | ε > 0}
    := by rfl
  theorem neighborhoods_def' {z} :
    Neighborhoods (z) = {{w | |w - z| < ε} | ε > 0}
    := by rfl
  end

def CNeighborhood (z) (ε : ℝ) := {w | |w - z| ≤  ε}
  section
  theorem cneighborhood_def {z} {ε : ℝ} :
    CNeighborhood (z) (ε : ℝ) = {w | |w - z| ≤  ε}
    := by rfl


  theorem cneighborhood_contains_le {z} {ε1 ε2 : ℝ} :
    ε1 ≤ ε2 →
    CNeighborhood z ε1 ⊆ CNeighborhood z ε2 := by
      simp [cneighborhood_def]
      intros le w w1
      exact Preorder.le_trans |w - z| ε1 ε2 w1 le
  theorem cneighborhood_contains_neighborhood {z} {ε : ℝ} :
    Neighborhood z ε ⊆ CNeighborhood z ε := by
      simp [cneighborhood_def,neighborhood_def]
      intros a b
      exact le_of_lt b


  theorem cneighborhood_contains_le_neighborhood {z} {ε1 ε2 : ℝ} :
    ε1 ≤ ε2 →
    Neighborhood z ε1 ⊆ CNeighborhood z ε2 := by
      intro le
      have a: Neighborhood z ε1 ⊆ CNeighborhood z ε1 := cneighborhood_contains_neighborhood
      have b: CNeighborhood z ε1 ⊆ CNeighborhood z ε2 := cneighborhood_contains_le le
      exact fun ⦃a_1⦄ a_2 ↦ b (a a_2)
  theorem neighborhood_contains_lt_cneighborhood {z} {ε1 ε2 : ℝ} :
    ε1 < ε2 →
    CNeighborhood z ε1 ⊆ Neighborhood z ε2 := by
      intro le
      simp [cneighborhood_def,neighborhood_def]
      intros a b
      exact lt_of_le_of_lt b le

  end




def ANeighborhoodContains (z) (s : Set R) := ∃ N ∈ Neighborhoods z, s ⊆ N
section

  theorem aNeighborhoodContains_def {z} {s : Set R} :
    ANeighborhoodContains (z) (s : Set R) ↔ ∃ N ∈ Neighborhoods z, s ⊆ N := by rfl
  theorem aNeighborhoodContains_means_aCNeighContains {z} {s : Set R} :
    ANeighborhoodContains (z) (s : Set R) ↔ ∃ N ∈ CNeighborhood z '' {ε | ε > 0}, s ⊆ N := by

      simp [aNeighborhoodContains_def]
      constructor
      · intro l
        rcases l with ⟨N,N_z,s_N⟩

        simp [neighborhoods_def] at N_z
        rcases N_z with ⟨ε,ε_pos,N_z⟩
        use ε

        have h : Neighborhood z ε ⊆ CNeighborhood z ε := cneighborhood_contains_neighborhood
        rw [N_z] at h
        exact ⟨ε_pos, fun ⦃a⦄ a_1 ↦ h (s_N a_1)⟩
        done
      · intro r
        rcases r with ⟨ε,ε_pos,r⟩
        use Neighborhood z (ε+1)
        constructor
        ·
          use ε+1

          simp [neighborhoods_def,ε_pos]
          positivity
          done
        ·
          have h : CNeighborhood z ε ⊆ Neighborhood z (ε + 1) := neighborhood_contains_lt_cneighborhood (by linarith)
          exact fun ⦃a⦄ a_1 ↦ h (r a_1)
          done




        done


      done


end



section Bounded

theorem _isBounded_def {a : ℕ → ℝ} : IsBounded (a : ℕ → ℝ) ↔ ∃ M, ∀ n, |a n| ≤ M := by rfl

def IsBounded' (s : Set R): Prop := ∃ d, s ⊆ Neighborhood 0 d

theorem isBounded_def{ s : Set R} : IsBounded' (s : Set R) ↔  ∃ d, s ⊆ Neighborhood 0 d := by rfl

theorem isBounded_cneigh { s : Set R} : IsBounded' (s : Set R) ↔  ∃ d, s ⊆ CNeighborhood 0 d := by
  sorry

theorem bounded_seq_bounded_set {a : ℕ → ℝ} : IsBounded a ↔ IsBounded' (Set.range a) := by

  have h123 : IsBounded a ↔ ∃ d, (Set.range a) ⊆ CNeighborhood 0 d :=
    by

    simp only [_isBounded_def, cneighborhood_def, Set.range]
    -- Automatic:
    simp only [sub_zero, Set.setOf_subset_setOf, forall_exists_index, forall_apply_eq_imp_iff]
  rw [h123]
  set s := Set.range a
  simp [isBounded_cneigh]



  -- todo: IsBounded a means there is a closed ball
  -- todo: rename neighborhood to ball.

  -- simp [isBounded_def,_isBounded_def]
  -- simp [Set.range]
  -- simp [neighborhood_def]
  -- simp [Set.subset_def, Set.mem_setOf]

  -- -- suffices (∃ M, ∀ (n : ℕ), |a n| ≤ M) ↔ (∃ d, ∀ (a_1), |a a_1| < d) by exact this


  -- have w(aa ss : ℝ ) : aa ∈ {w | |w| < ss} ↔ |aa| < ss := by exact Set.mem_setOf
  -- simp [w]

  done


-- theorem isBounded_def' {a : ℕ → ℝ} :
--   IsBounded' (a : ℕ → ℝ) ↔  ∃ d , (Set.range a) ⊆ Neighborhood 0 d := by rfl
theorem isBounded_def' {a : ℕ → ℝ} :
  IsBounded (a : ℕ → ℝ) ↔  ∃ d > 0, (Set.range a) ⊆ CNeighborhood 0 d := by

    have hh : IsBounded (a : ℕ → ℝ) ↔ ∃ M > 0, ∀ n, |a n| ≤ M := by
      simp [_isBounded_def]
      constructor
      ·
        intro ⟨M,boundedness⟩
        use max M 1 ---- if M satisfies the left side, then anything larger than M also does.
        simp [boundedness]
        done
      ·
        intro ⟨d,⟨d_pos,boundedness⟩⟩
        use d
        done
      done

    simp [cneighborhood_def,hh,Set.range]
    done
-- theorem isBounded_def'' {a : ℕ → ℝ} :
--   IsBounded (a : ℕ → ℝ) ↔ ANeighborhoodContains 0 (Set.range a) := by
--     simp [aNeighborhoodContains_means_aCNeighContains]
--     rw [isBounded_def']

--     rw [Set.range]

--     simp
--     done







end Bounded




def DiameterUpperBound (s : Set ℝ) (ε : ℝ) := ∀ x∈s, ∀ y∈s, |x-y| < ε
section
theorem diameterUpperBound_def {s : Set ℝ} {ε : ℝ} :
  DiameterUpperBound (s : Set ℝ) (ε : ℝ) ↔ ∀ x∈s, ∀ y∈s, |x-y| < ε := by rfl

theorem diameterUpperBound_def' {s : Set ℝ} {ε : ℝ} :
  DiameterUpperBound (s : Set ℝ) (ε : ℝ) ↔ ∀ x y, x∈s → y∈s → |x-y| < ε :=
  by
    simp [swap_forall]
    rfl

end




section isCauchy

theorem isCauchy_def' {a : ℕ → ℝ} :
    IsCauchy a ↔ ∀ ε > 0, ∃ B : ℕ, ∀ an am, InTail a B an → InTail a B am → |an - am| < ε := by
    simp only [inTail_def, swap_forall, isCauchy_def]

    -- rw [isCauchy_def]
    -- simp [swap_forall]

    -- rfl

    -- suffices
    --   IsCauchy a ↔ ∀ ε > 0, ∃ B : ℕ, ∀ an, ∀ am, InTail a B an → InTail a B am → |an - am| < ε
    --   by exact this

    -- suffices
    --   IsCauchy a ↔ ∀ ε > 0, ∃ B : ℕ, ∀ an, InTail a B an → ∀ am,  InTail a B am → |an - am| < ε
    --   by
    --     have h{X : Type}(f : X → Prop) (p : Prop) : (∀ x, (p → f x)) → (p → ∀ x, ( f x)) :=
    --       by exact fun a_0 a_1 x ↦ a_0 x a_1
    --     conv =>
    --       right
    --       intro ε ε_pos

    --       -- simp [h _ (InTail a _ _)]
    done

lemma isCauchy_def'' {a : ℕ → ℝ} :
    IsCauchy a ↔ ∀ ε > 0,  ∃ T ∈ Tails a, ∀ an ∈ T, ∀ am ∈ T, |an - am| < ε := by
    simp [isCauchy_def,swap_forall, tails_def, tail_def, inTail_def]

    -- simp only [isCauchy_def, gt_iff_lt, swap_forall, tails_def, Set.mem_setOf_eq,
    --   exists_exists_eq_and, inTail_def]




theorem isCauchy_def''' {a : ℕ → ℝ} :
    IsCauchy a ↔ ∀ ε > 0,  ∃ T ∈ Tails a, DiameterUpperBound T ε := by
      simp [diameterUpperBound_def]
      simp [isCauchy_def'']

end isCauchy

section tendsTo


  theorem tendsTo_def' {a : ℕ → ℝ} {t : ℝ} :
      TendsTo a t ↔ ∀ ε, 0 < ε → ∃ B : ℕ, ∀ an, InTail a B an → |an - t| < ε := by
      simp only [inTail_def, swap_forall]
      rfl -- true by definition

  theorem tendsTo_def'' {a : ℕ → ℝ} {t : ℝ} :
      TendsTo a t ↔ ∀ ε, 0 < ε → ∃ B : ℕ, ∀ an ∈ Tail a B, |an - t| < ε := by
      simp only [tail_def', Set.preimage_singleton_true, Set.mem_setOf_eq, inTail_def]
      rfl -- true by definition

  theorem tendsTo_def''' {a : ℕ → ℝ} {t : ℝ} :
      TendsTo a t ↔ ∀ ε, 0 < ε → ∃ B ∈ Tails a, ∀ an ∈ B, |an - t| < ε := by
      simp [tails_def,tail_def, Set.mem_setOf_eq, exists_exists_eq_and, inTail_def]
      rfl -- true by definition


theorem tendsTo_def'4 {a : ℕ → ℝ} {t : ℝ} :
    TendsTo a t ↔ ∀ ε, 0 < ε → ∃ B ∈ Tails a, ∀ an ∈ B, an ∈ Neighborhood t ε := by
    simp only [tails_def, tail_def, Set.mem_setOf_eq, neighborhood_def, exists_exists_eq_and, inTail_def]
    simp only [tendsTo_def]
    simp


    -- rfl -- true by definition

theorem tendsTo_def'5 {a : ℕ → ℝ} {t : ℝ} :
    TendsTo a t ↔ ∀ N ∈ Neighborhoods t, ∃ B ∈ Tails a, ∀ an ∈ B, an ∈ N := by
    simp [neighborhoods_def,neighborhood_def]
    simp [tendsTo_def''']


theorem tendsTo_def'NcT {a : ℕ → ℝ} {t : ℝ} :
    TendsTo a t ↔ ∀ N ∈ Neighborhoods t, ∃ B ∈ Tails a, B ⊆ N := by
    -- have w(B N : Set ℝ) : (∀ an ∈ B, an ∈ N) ↔ B ⊆ N :=
    --   by exact Iff.symm (Eq.to_iff rfl)
    simp [tendsTo_def,tails_def,tail_def,inTail_def,neighborhoods_def,neighborhood_def]

    -- simp [tendsTo_def'5]
    -- rfl

end tendsTo





section Excercises


-- EXERCISE 1
/-- Any convergent real-number sequence is necessarily a Cauchy sequence. -/
theorem isCauchy_of_tendsTo' {a : ℕ → ℝ} {t : ℝ} (a_lim : TendsTo a t) :
    IsCauchy a := by
  -- This is some work --- make sure you know the math proof first!
  -- You may take some inspiration from the uniqueness of limits proof.

  rw [isCauchy_def']
  rw [tendsTo_def'] at a_lim


  -- off topic: I wonder if the limit of a sequence has anything to do with the accummulation points of its set

  -- TendsTo: we can have a tail that is within an arbitriary distance of the limit
  -- IsCauchy: we can have a tail that has arbitrarily small diameter
  -- If all points have at most distance ε/2 to a point `t`, by the triangle inequality they have at most ε distance to any other point
  intro ε ε_pos
  -- ε: diameter

  specialize a_lim (ε/2) (by exact half_pos ε_pos)
  rcases a_lim with ⟨tail, a_lim⟩

  use tail
  intros x y x_tail y_tail
  have x_radius_bounded := a_lim _ x_tail
  have y_radius_bounded := a_lim _ y_tail

  -- apply a_lim at x_tail
  -- apply a_lim at y_tail
  clear * - x_radius_bounded y_radius_bounded

  let diam_bound := |x - t| + |y - t|
  have diam_bounded : diam_bound < ε := by
    suffices diam_bound < ε / 2 + ε / 2 by norm_num at this; exact this
    apply add_lt_add x_radius_bounded y_radius_bounded


  have diam_lt_diam_bound : |x - y| ≤ diam_bound := by
    suffices |x - y| ≤ |x - t| + |y - t| from this
    rw [abs_sub_comm y t]
    exact abs_sub_le x t y
  exact lt_of_le_of_lt diam_lt_diam_bound diam_bounded


theorem isCauchy_of_tendsTo'2 {a : ℕ → ℝ} {t : ℝ} (a_lim : TendsTo a t) :
    IsCauchy a := by
    rw [isCauchy_def''']
    rw [tendsTo_def'NcT] at a_lim




    sorry
    done
end Excercises


end Okko
