import Mathlib.Tactic



namespace AaltoFormalMath2025


section group_element_triviality
/-!
### Another example in the spirit of Section05, sheet 1
-/

-- Let `G` be a group.
variable (G : Type) [Group G]

-- An element `x ∈ G` which satisfies both `x^5 = 1` and `x^8 = 1`
-- must be the neutral element `1`.
example (x : G) (h5 : x ^ 5 = 1) (h8 : x ^ 8 = 1) : x = 1 := by
  -- Idea: Since 5 and 8 are coprime, and the order of x divides both 5 and 8,
  -- the order of x must be 1.
  have h16 : (x ^ 8) ^ 2 = 1 := by
    rw [h8] -- Rewrite with the appropriate hypothesis.
    group -- This is obviously handled by the `group` tactic.
  have h15 : (x ^ 5) ^ 3 = 1 := by
    simp [h5] -- `simp` tactic with the custom rewrite rule `h5`
  rw [← pow_mul] at h16 h15 -- Let's simplify powers.
  norm_num at h16 h15 -- Let's further simplify powers.
  have obs : x ^ 16 = x ^ 15 := by -- This is the key observation.
    simp [h16, h15]
  -- Now just multiply both sides of the bservation by the inverse of x^15 and simplify.
  have key := congrArg (fun g ↦ (x ^ 15)⁻¹ * g) obs
  dsimp at key
  group at key
  exact key

end group_element_triviality


end AaltoFormalMath2025
