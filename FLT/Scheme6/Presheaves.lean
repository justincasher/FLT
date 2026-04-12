/-
Copyright (c) 2026 Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina
-/
import Mathlib

/-!
# Presheaves and Sheaves

This file develops properties of presheaves and sheaves on topological spaces,
corresponding to §1 of the Scheme 6 blueprint.

## Main definitions

* `Scheme6.Presheaf` — A presheaf on a topological space `X` valued in a category `C`.
* `Scheme6.IsSheaf` — The sheaf condition (locality + gluing) for a presheaf.

## References

* Blueprint: `def:presheaf`, `def:sheaf`
-/

noncomputable section

open CategoryTheory TopologicalSpace AlgebraicGeometry

namespace Scheme6

/-- A presheaf of types on a topological space `X` is a contravariant functor
from the category of open sets of `X` to a target category. -/
def Presheaf' (C : Type*) [Category C] (X : TopCat) :=
  TopCat.Presheaf C X

/-- A presheaf on `X` is a sheaf when it satisfies the locality and gluing
axioms with respect to all open covers. -/
def IsSheaf' {X : TopCat} (F : TopCat.Presheaf (Type _) X) : Prop :=
  TopCat.Presheaf.IsSheaf F

-- TODO: Add further lemmas about presheaves and sheaves here.
-- For example:
--   • restriction maps compose correctly
--   • the sheaf condition implies locality
--   • pushforward of a sheaf is a sheaf

end Scheme6

end
