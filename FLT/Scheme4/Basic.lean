import Mathlib.Topology.Sheaves.Sheaf
import Mathlib.Topology.Sheaves.Presheaf
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.Spec

/-!
# Schemes (blueprint Scheme 4)

This file provides thin FLT-side wrappers for the blueprint definitions
of presheaves and sheaves of commutative rings on a topological space,
and of affine schemes. The remaining blueprint definitions
(ringed spaces, stalks, locally ringed spaces, prime spectrum,
structure sheaf, schemes, scheme morphisms) are taken directly from
Mathlib without redefinition.
-/

namespace FLT.Scheme4

open CategoryTheory TopologicalSpace AlgebraicGeometry

/-- A presheaf of commutative rings on a topological space `X`,
    i.e. a `TopCat.Presheaf` with values in `CommRingCat`. -/
abbrev RingPresheaf (X : TopCat) : Type _ :=
  TopCat.Presheaf CommRingCat X

/-- A sheaf of commutative rings on a topological space `X`. -/
abbrev RingSheaf (X : TopCat) : Type _ :=
  TopCat.Sheaf CommRingCat X

/-- A locally ringed space is an affine scheme if it is isomorphic
    (in `LocallyRingedSpace`) to `Spec.locallyRingedSpaceObj` of some
    commutative ring. -/
def IsAffineScheme (X : LocallyRingedSpace) : Prop :=
  ∃ (R : CommRingCat),
    Nonempty (X ≅ Spec.locallyRingedSpaceObj R)

end FLT.Scheme4
