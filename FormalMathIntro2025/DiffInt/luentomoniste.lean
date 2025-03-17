
import Mathlib.Tactic -- imports all the Lean tactics
-- import FormalMathIntro2025.ProblemSet1
set_option linter.unusedTactic false
namespace OkkoMath


section MetSp


-- This is the same definition as in *Kevin Buzzard's Section01reals*.
/-- If `n ↦ a(n)` is a sequence of reals and `t` is a real, `TendsTo a t`
is the assertion that the limit of `a(n)` as `n → ∞` is `t`. -/
def TendsTo (a : ℕ → ℝ) (t : ℝ) : Prop :=
  ∀ ε > 0, ∃ B : ℕ, ∀ n, B ≤ n → |a n - t| < ε

theorem tendsTo_def {a : ℕ → ℝ} {t : ℝ} :
    TendsTo a t ↔ ∀ ε, 0 < ε → ∃ B : ℕ, ∀ n, B ≤ n → |a n - t| < ε := by
  rfl -- true by definition




def ContinuousAtPoint {X Y : Type} [mx : MetricSpace X][my : MetricSpace Y] (f : X → Y) (x: X) :=
  ∀ ε > 0, ∃ δ > 0, ∀ x' : X, mx.dist (x) (x') < δ → my.dist (f x) (f x') < ε

def ContinuousAtSet {X Y : Type} [mx : MetricSpace X][my : MetricSpace Y] (f : X → Y) (s: Set X) :=
  ∀ x∈s, ContinuousAtPoint f x




end MetSp

-- #check List

section BasicDefinitions

def Open_Interval (a : ℝ) (b : ℝ) := { x : ℝ  | a < x ∧ x < b}
def Closed_Interval (a : ℝ) (b : ℝ) := { x : ℝ  | a ≤  x ∧ x ≤ b}


section Sum
/-- sum of f from 0 to x -/
def Sum_until (f : ℕ → ℝ) : ℕ → ℝ
| 0 => 0
| Nat.succ x => f (x) + (Sum_until f) (x)

theorem sum_until_zero {f : ℕ → ℝ} :   Sum_until f 0 = 0 :=
  by exact rfl
theorem sum_until_def {f : ℕ → ℝ} {n : ℕ} : n > 0 →  Sum_until f n = f (n-1) + Sum_until f (n-1) :=
  by
    intro n_pos
    rw [Sum_until.eq_def]
    -- have h : n≠0 := by exact Nat.not_eq_zero_of_lt n_pos
    split
    ·
      -- rw [gt_iff_lt, lt_self_iff_false] at n_pos
      contradiction
      done
    · simp only [Nat.succ_eq_add_one, add_tsub_cancel_right]
      done

    done


def R := ℝ

def linear_mult {X R : Type} [Semiring R] (lin : (X → R) → (X → R)) : Prop :=
  ∀ f : X → R, ∀ x : X, ∀ r : R, r * lin f x = lin (fun x' ↦ r * f x') x

def linear_add {X R : Type} [Semiring R] (lin : (X → R) → (X → R)) : Prop :=
  ∀ f g : X → R, ∀ x : X, lin f x + lin g x = lin (fun x' ↦ f x' + g x') x

def linear {X R : Type} [Semiring R] (lin : (X → R) → (X → R)) : Prop :=
  linear_add lin ∧ linear_mult lin


lemma sum_until_linear_mult'  {f : ℕ → ℝ} {n : ℕ} {r : ℝ} :
  r * Sum_until f n = Sum_until (fun x ↦ r * f x) n := by
    induction' n with n previous
    · simp [sum_until_zero]
      done
    simp [sum_until_def]
    rw [←previous]
    ring
    -- simp only [add_right_inj]
    -- exact previous
    done
theorem sum_until_linear_mult : linear_mult (Sum_until ) := by
  simp [linear_mult.eq_def]
  intros f x r
  exact sum_until_linear_mult'
  done

lemma sum_until_linear_add'  {f g : ℕ → ℝ} {n : ℕ} :
  Sum_until f n + Sum_until g n = Sum_until (fun x ↦ f x + g x) n := by
    induction' n with n previous
    · simp [sum_until_zero]
      done
    simp [sum_until_def]
    rw [←previous]
    ring
    done

theorem sum_until_linear_add : linear_add (Sum_until) := by
  simp [linear_add.eq_def]
  intros
  exact sum_until_linear_add'

theorem sum_until_linear : linear Sum_until := by
  unfold linear
  constructor
  · exact sum_until_linear_add
  · exact sum_until_linear_mult
  done

end Sum

-- def FiniteSum (a b : ℤ) (f : ℤ → ℝ) : ℝ :=
--   if (a > 0) then
--     sum_finite (fun n ↦ f n) (a.toNat)
--   else
--     sum_finite (fun n ↦ f (-n)) ((-a).toNat)


def lerp (a b x : ℝ) : ℝ := a + (b - a) * x

/--
  when a=0,b=1, maps 0,1,...,N-1 to 1/N,...,1-1/N
  in other words does not inclide the endpoints
  -/
noncomputable def lerp_nat_open(a b : ℝ)(N n : ℕ) : ℝ :=
  lerp a b ((n+1) / (N+1) )


-- #check Real.instDivInvMonoid

-- #check lerp 1 2 1
-- #eval lerp_nat 1 2 1 2


noncomputable def ApproxIntegral (a b : ℝ) (f : ℝ → ℝ) (N : ℕ) : ℝ :=
  if N = 0 then
    0
  else
    (
      Sum_until (
        f ∘ (lerp_nat_open a b N)
        -- fun n ↦ f (
        --   lerp_nat_open a b N n
        --   )
        ) N
      ) / N

-- theorem ApproxIntegral_linear {a b : ℝ} {N : ℕ} :
--   @linear ℝ ℝ _ (fun f ↦ ApproxIntegral a b f N) := by sorry

/-- limit of sum -/
def RiemannIntegral (a b : ℝ) (f : ℝ → ℝ) (value : ℝ) : Prop :=
  TendsTo (
    ApproxIntegral a b f
    ) value

-- theorem riemann_linear_mult {a b : ℝ} {f : ℝ → ℝ} {mul value : ℝ} :
--   RiemannIntegral a b f value
-- theorem riemann_linear_add {a b : ℝ} :
--   linear_add (RiemannIntegral)



end BasicDefinitions



section S0_Tasointegraali



theorem Lause_0'1 {I : Set ℝ} {a b ia ib : ℝ} {f : ℝ×ℝ → ℝ} :
  I = Open_Interval ia ib →
  ContinuousAtSet f ((Closed_Interval a b).prod I) --→

   := by

  sorry




end S0_Tasointegraali

end OkkoMath
