import Mathlib



namespace AaltoFormalMath2025

noncomputable section evaluating_finsets
/-!
### An example related to Section08, sheet 1
-/

open Classical

/-- An example finite set of natural numbers. -/
def X : Finset ℕ := if 37 + 5 = 42 then {37,42} else {361}

#check X -- Indeed, a finite set.

#print X -- This is what it is defined to be.

#eval X -- This is what it evaluates to, `X = {37,42}`.

/-- A trickier example of a finite set of natural numbers. -/
def Y : Finset ℕ := if RiemannHypothesis then {37,42} else {361}

#check Y -- Indeed, a finite set.

#print Y -- This is what it is defined to be.

--#eval Y -- ERROR!

end evaluating_finsets


end AaltoFormalMath2025
