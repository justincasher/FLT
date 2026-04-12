/-
Copyright (c) 2026 Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina
-/
import Mathlib

/-!
# Scheme 6 --- Blueprint

This file provides sorry'd declarations corresponding to the 10 definitions
in the Scheme 6 blueprint. All 10 already exist in Mathlib; each declaration
here is an alias that witnesses the correspondence.
-/

noncomputable section

open CategoryTheory TopologicalSpace AlgebraicGeometry

/-! ## Presheaves and Sheaves -/

/-- **Blueprint def:presheaf** A presheaf of types on a topological space `X` is a
contravariant functor from the category of open sets of `X` to a target category. -/
def Scheme6.Presheaf (C : Type*) [Category C] (X : TopCat) :=
  TopCat.Presheaf C X

/-- **Blueprint def:sheaf** A presheaf on `X` is a sheaf when it satisfies the
locality and gluing axioms with respect to all open covers. -/
def Scheme6.IsSheaf {X : TopCat}
    (F : TopCat.Presheaf (Type _) X) : Prop :=
  TopCat.Presheaf.IsSheaf F

/-- **Blueprint def:ringed_space** A ringed space (here, a sheafed space) is a
topological space equipped with a sheaf of commutative rings. -/
def Scheme6.SheafedSpace : Type _ :=
  AlgebraicGeometry.SheafedSpace CommRingCat

/-- **Blueprint def:stalk** The stalk of a presheaf at a point is the colimit
over all open neighbourhoods of that point. -/
def Scheme6.stalk {X : TopCat} (F : TopCat.Presheaf CommRingCat X) (x : X) :=
  TopCat.Presheaf.stalk F x

/-- **Blueprint def:locally_ringed_space** A locally ringed space is a ringed
space whose stalks are all local rings. -/
def Scheme6.LocallyRingedSpace : Type _ :=
  AlgebraicGeometry.LocallyRingedSpace

/-! ## The Spectrum and Structure Sheaf -/

/-- **Blueprint def:spectrum** The prime spectrum of a commutative ring `R` is
the set of prime ideals of `R`, equipped with the Zariski topology. -/
abbrev Scheme6.PrimeSpectrum (R : Type*) [CommRing R] : Type _ :=
  _root_.PrimeSpectrum R

/-- **Blueprint def:structure_sheaf** The structure sheaf on `Spec R` is the
sheaf of commutative rings whose sections on basic opens `D(f)` are the
localizations `R_f`. -/
def Scheme6.structureSheaf (R : Type*) [CommRing R] :=
  Spec.structureSheaf R

/-! ## Schemes -/

/-- **Blueprint def:affine_scheme** A scheme is affine when it is isomorphic
to `Spec R` for some commutative ring `R`. -/
def Scheme6.IsAffine (X : AlgebraicGeometry.Scheme) : Prop :=
  AlgebraicGeometry.IsAffine X

/-- **Blueprint def:scheme** A scheme is a locally ringed space that is locally
isomorphic to affine schemes. -/
def Scheme6.Scheme : Type _ :=
  AlgebraicGeometry.Scheme

/-- **Blueprint def:morphism_of_schemes** A morphism of schemes is a morphism
of their underlying locally ringed spaces. -/
def Scheme6.Hom (X Y : AlgebraicGeometry.Scheme) :=
  AlgebraicGeometry.Scheme.Hom X Y

/-! ## Simple proofs using our definitions -/

/-- The spectrum of any commutative ring is an affine scheme. -/
theorem Scheme6.specIsAffine (R : CommRingCat) :
    Scheme6.IsAffine (Spec R) :=
  AlgebraicGeometry.isAffine_Spec R

/-- Every scheme has an identity morphism. -/
def Scheme6.idHom (X : AlgebraicGeometry.Scheme) : Scheme6.Hom X X :=
  𝟙 X

/-- Morphisms of schemes can be composed. -/
def Scheme6.compHom {X Y Z : AlgebraicGeometry.Scheme}
    (f : Scheme6.Hom X Y) (g : Scheme6.Hom Y Z) : Scheme6.Hom X Z :=
  show X ⟶ Z from f ≫ g

/-- Composing with the identity morphism on the right is a no-op. -/
theorem Scheme6.comp_id {X Y : AlgebraicGeometry.Scheme} (f : Scheme6.Hom X Y) :
    Scheme6.compHom f (Scheme6.idHom Y) = f := by
  unfold Scheme6.compHom Scheme6.idHom
  simp

/-- Composing with the identity morphism on the left is a no-op. -/
theorem Scheme6.id_comp {X Y : AlgebraicGeometry.Scheme} (f : Scheme6.Hom X Y) :
    Scheme6.compHom (Scheme6.idHom X) f = f := by
  unfold Scheme6.compHom Scheme6.idHom
  simp

/-- Composition of scheme morphisms is associative. -/
theorem Scheme6.comp_assoc {W X Y Z : AlgebraicGeometry.Scheme}
    (f : Scheme6.Hom W X) (g : Scheme6.Hom X Y) (h : Scheme6.Hom Y Z) :
    Scheme6.compHom (Scheme6.compHom f g) h = Scheme6.compHom f (Scheme6.compHom g h) := by
  unfold Scheme6.compHom
  simp [Category.assoc]

end
