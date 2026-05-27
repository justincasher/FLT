/-
Copyright (c) 2026 Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.GroupTheory.Exponent
import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.Trace
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic

/-!
# Character values of finite groups lie in cyclotomic fields, II
-/

namespace FLT.CharacterValuesCyclotomic

open Polynomial

/-! ### The embedding `φ : CyclotomicField n ℚ →+* ℂ` -/

lemma cyclotomicField_isAlgebraic (n : ℕ) :
    Algebra.IsAlgebraic ℚ (CyclotomicField n ℚ) := by
  sorry

noncomputable def cyclotomicEmbeddingAlgHom (n : ℕ) :
    CyclotomicField n ℚ →ₐ[ℚ] ℂ :=
  sorry

noncomputable def cyclotomicEmbedding (n : ℕ) : CyclotomicField n ℚ →+* ℂ :=
  (cyclotomicEmbeddingAlgHom n).toRingHom

lemma mem_range_of_pow_eq_one {n : ℕ} (hn : n ≠ 0)
    (φ : CyclotomicField n ℚ →+* ℂ) {ξ : ℂ} (hξ : ξ ^ n = 1) :
    ξ ∈ φ.range := by
  sorry

/-! ### Eigenvalues of finite-order endomorphisms are roots of unity -/

lemma representation_pow_exponent_eq_one
    {G : Type*} [Group G]
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : G →* (V →ₗ[ℂ] V)) (g : G) :
    (ρ g) ^ Monoid.exponent G = 1 := by
  sorry

lemma eigenvalue_pow_eq_one
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    {n : ℕ} (hn : n ≠ 0) {f : V →ₗ[ℂ] V} (hf : f ^ n = 1)
    {μ : ℂ} (hμ : Module.End.HasEigenvalue f μ) :
    μ ^ n = 1 := by
  sorry

/-- Over `ℂ` (an algebraically closed field of characteristic zero, in particular an
integral domain), every root of the characteristic polynomial of a linear
endomorphism of a finite-dimensional vector space is an eigenvalue. -/
lemma hasEigenvalue_of_mem_charpoly_roots
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (f : V →ₗ[ℂ] V) {μ : ℂ} (hμ : μ ∈ f.charpoly.roots) :
    Module.End.HasEigenvalue f μ :=
  Module.End.hasEigenvalue_iff_isRoot_charpoly f μ |>.mpr
    ((Polynomial.mem_roots f.charpoly_monic.ne_zero).mp hμ)

lemma charpoly_roots_pow_eq_one
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    {n : ℕ} (hn : n ≠ 0) {f : V →ₗ[ℂ] V} (hf : f ^ n = 1)
    {μ : ℂ} (hμ : μ ∈ f.charpoly.roots) :
    μ ^ n = 1 := by
  sorry

lemma trace_eq_charpoly_roots_sum
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (f : V →ₗ[ℂ] V) :
    LinearMap.trace ℂ V f = f.charpoly.roots.sum := by
  sorry

lemma multiset_sum_mem_subring {R : Type*} [Ring R] (S : Subring R) (m : Multiset R)
    (hm : ∀ a ∈ m, a ∈ S) :
    m.sum ∈ S := by
  sorry

lemma trace_mem_range
    {G : Type*} [Group G] [Finite G]
    (φ : CyclotomicField (Monoid.exponent G) ℚ →+* ℂ)
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : G →* (V →ₗ[ℂ] V)) (g : G) :
    LinearMap.trace ℂ V (ρ g) ∈ φ.range := by
  sorry

theorem character_values_in_cyclotomic_field
    (G : Type*) [Group G] [Finite G] :
    ∃ φ : CyclotomicField (Monoid.exponent G) ℚ →+* ℂ,
      ∀ {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
        (ρ : G →* (V →ₗ[ℂ] V)) (g : G),
        LinearMap.trace ℂ V (ρ g) ∈ φ.range := by
  sorry

end FLT.CharacterValuesCyclotomic
