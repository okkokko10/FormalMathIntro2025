
import Mathlib.Tactic -- imports all the Lean tactics

namespace OkkoMath


-- def Curve (X : Type) := ℝ → X


-- def CurveSet {X : Type} (C : Curve X) := Set.range C

-- def LineIntegral {X : Type} (C : Curve X) (f : X → ℝ) : ℝ := sorry

-- theorem lineIntegral_linearMult {X : Type} {C : Curve X} {f : X → ℝ} {x : ℝ} : x * LineIntegral C f =  LineIntegral C (fun v ↦ x * f v) := by sorry

-- theorem lineIntegral_linearAdd {X : Type} {C : Curve X} {f : X → ℝ} {g : X → ℝ} : LineIntegral C f + LineIntegral C g =  LineIntegral C (fun v ↦ f v + g v) := by sorry




-- lemma task4 (A: Set (Vector ℝ 3)) (C : Curve (Vector ℝ 3)) (R : ℝ) (la : ℝ ) (J_z : ℝ) (m : ℝ) :
--     A = { w | w[0] ^2 + w[1] ^2 = R^2 ∧ w[2] = 0} →
--     J_z = la * (LineIntegral C (fun (v: Vector ℝ 3) ↦ v[0]^2 + v[1]^2)) →
--     m = (LineIntegral C (fun (v: Vector ℝ 3) ↦ 1)) →
--     J_z = R^2 * m
--      := by


--     -- let v := #v[1,2,3]
--     -- have e := v.1
--     -- #check #v[1,2,3].get 1
--     -- #check v[0]



--     sorry
--     done


inductive Indices  :  Type
| x : Indices
| y : Indices

variable [Fintype Indices]

def V : Type := Indices → ℝ

def Vec2 (x y : ℝ) : V :=
  fun (n) ↦ match n with | Indices.x=> x | Indices.y=> y


variable (F : V → V)
variable( v : V) [AddCommGroup V] [Module ℝ V] [TopologicalSpace V] [HMul ℝ V V] [HDiv V ℝ V]


#check dotProduct (Vec2 1 2) (Vec2 1 2)




example : (∀v: V,  (F v) = (Vec2 (- v Indices.y) (v Indices.x)) / (dotProduct v v) ) →
    ∀x y : ℝ ,
      deriv (fun y' ↦ (F (Vec2 x y')) Indices.x ) (y)
    = deriv (fun x' ↦ (F (Vec2 x' y)) Indices.y ) (x)
    := by


  let ww( x' y : ℝ) := deriv (fun (x : ℝ) ↦ x / (x^2 + y^2)) x'
  let ww1 := ww 1 1

  intro F_def
  intro x y
  suffices
    deriv (fun y' ↦ F (Vec2 x y')) y Indices.x = deriv (fun x' ↦ F (Vec2 x' y) ) x Indices.y
    by
    -- have h : deriv (fun y' ↦ F (Vec2 x y') Indices.x ) y = deriv (fun y' ↦ F (Vec2 x y')) y Indices.x
    sorry


  #check deriv_div



  done





inductive Indices3  :  Type
| x : Indices3
| y : Indices3
| z : Indices3


variable [Fintype Indices3]

def V3 : Type := Indices3 → ℝ

def Vec3 (x y z : ℝ) : V3 :=
  fun (n) ↦ match n with | Indices3.x=> x | Indices3.y=> y | Indices3.z=> z

open Indices3

def CrossProduct(a b : V3) : V3 := Vec3 (a y * b z - a z * b y) (a z * b x - a x * b z) (a x * b y - a y * b x)

-- example (sv cv su cu r R : ℝ) (fu fv N : V3) :
--   fu = Vec3 ( - (R + r * cv) * su)  ((R+r*cv) * cu) (r*sv) →
--   fv = Vec3 ( - ( r * sv) * cu) (- r*sv * su) (r*cv) →
--   N = CrossProduct fu fv →
--   (sv ^ 2) = 1 - cv ^ 2 →
--   (su ^ 2) = 1 - cu ^ 2 →
--   (N x)^2 + (N y)^2 + (N z)^2 - (r * (R + r * cv)) ^ 2 = 0 := by
--     intros fu_d fv_d N_d v_1 u_1

--     simp [CrossProduct] at N_d
--     simp [fv_d,fu_d] at N_d
--     ring_nf at N_d
--     simp [N_d]
--     ring_nf
--     save
--     simp [Vec3]
--     norm_num
--     simp [pow_two]
--     norm_num
--     ring_nf!
--     -- simp [pow_two] at v_1 u_1
--     -- have v_2 : 1 - cv ^ 2 = sv ^ 2 := by
--     --   suffices 1 = cv ^ 2 + sv ^ 2   by exact sub_eq_of_eq_add' this
--     --   suffices cv ^ 2 + sv ^ 2 = 1  by exact id (Eq.symm this)
--     --   suffices  sv ^ 2 + cv ^ 2 = 1  by

--     --     exact this
--     --   ring
--     --   exact v_1
--     --   simpa using v_1
--     save
--     have qv : sv ^ 4 = (sv ^ 2) ^ 2 := by sorry
--     have qu : su ^ 4 = (su ^ 2) ^ 2 := by sorry
--     simp_rw [v_1,qv]
--     simp_rw [u_1,qu]

--     ring_nf
--     by_cases h1 : r = 1
--     · rw [h1]
--       ring_nf
--       by_cases h2 : R = 2
--       ·
--         rw [h2]
--         ring_nf
--         norm_num
--         done
--       done


--     done
