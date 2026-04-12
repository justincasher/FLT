/-
Copyright (c) 2026 Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina
-/
import Mathlib

/-!
# The Prime Spectrum and the Structure Sheaf

This file develops the prime spectrum and structure sheaf of a commutative ring,
corresponding to §3 of the Scheme 6 blueprint.

## Main definitions

* `Scheme6.PrimeSpectrum'` — The set of prime ideals with the Zariski topology.
* `Scheme6.structureSheaf'` — The structure sheaf on `Spec R` with sections `R_f` on `D(f)`.

## References

* Blueprint: `def:spectrum`, `def:structure_sheaf`
-/

noncomputable section

open CategoryTheory TopologicalSpace AlgebraicGeometry

namespace Scheme6

/-- The prime spectrum of a commutative ring `R` is the set of prime ideals
of `R`, equipped with the Zariski topology. -/
abbrev PrimeSpectrum' (R : Type*) [CommRing R] : Type _ :=
  PrimeSpectrum R

/-- The structure sheaf on `Spec R` is the sheaf of commutative rings whose
sections on basic opens `D(f)` are the localizations `R_f`. -/
def structureSheaf' (R : Type*) [CommRing R] :=
  Spec.structureSheaf R

-- TODO: Add further lemmas about the spectrum and structure sheaf here.
-- For example:
--   • Spec is a contravariant functor from CommRing to Scheme
--   • the stalk of the structure sheaf at 𝔭 is the localization R_𝔭
--   • basic opens D(f) form a basis for the Zariski topology
--   • Spec R is quasi-compact

end Scheme6

end
