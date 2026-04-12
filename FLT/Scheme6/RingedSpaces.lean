/-
Copyright (c) 2026 Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina
-/
import Mathlib

/-!
# Ringed Spaces and Locally Ringed Spaces

This file develops ringed spaces, stalks, and locally ringed spaces,
corresponding to §2 of the Scheme 6 blueprint.

## Main definitions

* `Scheme6.SheafedSpace'` — A topological space equipped with a sheaf of commutative rings.
* `Scheme6.stalk'` — The stalk of a presheaf at a point (colimit over open neighbourhoods).
* `Scheme6.LocallyRingedSpace'` — A ringed space whose stalks are all local rings.

## References

* Blueprint: `def:ringed_space`, `def:stalk`, `def:locally_ringed_space`
-/

noncomputable section

open CategoryTheory TopologicalSpace AlgebraicGeometry

namespace Scheme6

/-- A ringed space (sheafed space) is a topological space equipped with a
sheaf of commutative rings. -/
def SheafedSpace' : Type _ :=
  AlgebraicGeometry.SheafedSpace CommRingCat

/-- The stalk of a presheaf at a point is the colimit over all open
neighbourhoods of that point. -/
def stalk' {X : TopCat} (F : TopCat.Presheaf CommRingCat X) (x : X) :=
  TopCat.Presheaf.stalk F x

/-- A locally ringed space is a ringed space whose stalks are all local rings. -/
def LocallyRingedSpace' : Type _ :=
  AlgebraicGeometry.LocallyRingedSpace

-- TODO: Add further lemmas about ringed spaces here.
-- For example:
--   • the stalk of a sheaf of rings is a ring
--   • stalk maps induced by morphisms of ringed spaces
--   • a morphism of locally ringed spaces induces local ring maps on stalks

end Scheme6

end
