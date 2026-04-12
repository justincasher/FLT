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
def Scheme6.PrimeSpectrum (R : Type*) [CommRing R] :=
  PrimeSpectrum R

/-- **Blueprint def:structure_sheaf** The structure sheaf on `Spec R` is the
sheaf of commutative rings whose sections on basic opens `D(f)` are the
localizations `R_f`. -/
def Scheme6.structureSheaf (R : Type*) [CommRing R] :=
  AlgebraicGeometry.structureSheaf R

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

end
