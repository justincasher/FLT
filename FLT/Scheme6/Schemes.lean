/-
Copyright (c) 2026 Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina
-/
import Mathlib

/-!
# Schemes and Morphisms of Schemes

This file develops schemes, affine schemes, and morphisms of schemes,
corresponding to §4 of the Scheme 6 blueprint.

## Main definitions

* `Scheme6.IsAffine'` — A scheme is affine when it is isomorphic to `Spec R`.
* `Scheme6.Scheme'` — A locally ringed space locally isomorphic to affine schemes.
* `Scheme6.Hom'` — A morphism of schemes (= morphism of locally ringed spaces).

## Main results

* `Scheme6.specIsAffine'` — `Spec R` is an affine scheme.
* `Scheme6.scheme_id'` — The identity morphism of a scheme.
* `Scheme6.scheme_comp'` — Composition of scheme morphisms.
* `Scheme6.scheme_comp_id'` — Right identity law.
* `Scheme6.scheme_id_comp'` — Left identity law.
* `Scheme6.scheme_comp_assoc'` — Associativity of composition.

## References

* Blueprint: `def:affine_scheme`, `def:scheme`, `def:morphism_of_schemes`
-/

noncomputable section

open CategoryTheory TopologicalSpace AlgebraicGeometry

namespace Scheme6

/-- A scheme is affine when it is isomorphic to `Spec R` for some commutative
ring `R`. -/
def IsAffine' (X : AlgebraicGeometry.Scheme) : Prop :=
  AlgebraicGeometry.IsAffine X

/-- A scheme is a locally ringed space that is locally isomorphic to affine
schemes. -/
def Scheme' : Type _ :=
  AlgebraicGeometry.Scheme

/-- A morphism of schemes is a morphism of their underlying locally ringed
spaces. -/
def Hom' (X Y : AlgebraicGeometry.Scheme) :=
  AlgebraicGeometry.Scheme.Hom X Y

/-! ### Basic properties -/

/-- The spectrum of any commutative ring is an affine scheme. -/
theorem specIsAffine' (R : CommRingCat) : IsAffine' (Spec R) :=
  AlgebraicGeometry.isAffine_Spec R

/-- Every scheme has an identity morphism. -/
def scheme_id' (X : AlgebraicGeometry.Scheme) : Hom' X X :=
  𝟙 X

/-- Morphisms of schemes can be composed. -/
def scheme_comp' {X Y Z : AlgebraicGeometry.Scheme}
    (f : Hom' X Y) (g : Hom' Y Z) : Hom' X Z :=
  show X ⟶ Z from f ≫ g

/-- Composing with the identity morphism on the right is a no-op. -/
theorem scheme_comp_id' {X Y : AlgebraicGeometry.Scheme} (f : Hom' X Y) :
    scheme_comp' f (scheme_id' Y) = f := by
  unfold scheme_comp' scheme_id'
  simp

/-- Composing with the identity morphism on the left is a no-op. -/
theorem scheme_id_comp' {X Y : AlgebraicGeometry.Scheme} (f : Hom' X Y) :
    scheme_comp' (scheme_id' X) f = f := by
  unfold scheme_comp' scheme_id'
  simp

/-- Composition of scheme morphisms is associative. -/
theorem scheme_comp_assoc' {W X Y Z : AlgebraicGeometry.Scheme}
    (f : Hom' W X) (g : Hom' X Y) (h : Hom' Y Z) :
    scheme_comp' (scheme_comp' f g) h = scheme_comp' f (scheme_comp' g h) := by
  unfold scheme_comp'
  simp [Category.assoc]

-- TODO: Add further lemmas about schemes here.
-- For example:
--   • every affine scheme is a scheme (tautological but good to state)
--   • open immersions, closed immersions
--   • fibre products of schemes
--   • Spec is fully faithful on affine schemes

end Scheme6

end
