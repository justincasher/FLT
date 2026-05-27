/-
Copyright (c) 2026 Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.GroupTheory.Exponent
import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
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

/-- The cyclotomic field `CyclotomicField n ℚ` is algebraic over `ℚ`. -/
lemma cyclotomicField_isAlgebraic (n : ℕ) :
    Algebra.IsAlgebraic ℚ (CyclotomicField n ℚ) :=
  Algebra.IsAlgebraic.of_finite ℚ (CyclotomicField n ℚ)

/-- The range of any ring homomorphism `φ : CyclotomicField n ℚ → ℂ` contains every
`n`-th root of unity in `ℂ`, provided `n ≠ 0`. -/
lemma mem_range_of_pow_eq_one {n : ℕ} (hn : n ≠ 0)
    (φ : CyclotomicField n ℚ →+* ℂ) {ξ : ℂ} (hξ : ξ ^ n = 1) :
    ξ ∈ φ.range := by
  haveI : NeZero n := ⟨hn⟩
  set ζ := IsCyclotomicExtension.zeta n ℚ (CyclotomicField n ℚ)
  have hζ : IsPrimitiveRoot ζ n := IsCyclotomicExtension.zeta_spec n ℚ _
  have hφζ : IsPrimitiveRoot (φ ζ) n := hζ.map_of_injective φ.injective
  obtain ⟨k, _, hk⟩ := hφζ.eq_pow_of_pow_eq_one hξ
  refine ⟨ζ ^ k, ?_⟩
  rw [map_pow]
  exact hk

lemma representation_pow_exponent_eq_one
    {G : Type*} [Group G]
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : G →* (V →ₗ[ℂ] V)) (g : G) :
    (ρ g) ^ Monoid.exponent G = 1 := by
  rw [← map_pow, Monoid.pow_exponent_eq_one, map_one]

lemma eigenvalue_pow_eq_one
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    {n : ℕ} (_hn : n ≠ 0) {f : V →ₗ[ℂ] V} (hf : f ^ n = 1)
    {μ : ℂ} (hμ : Module.End.HasEigenvalue f μ) :
    μ ^ n = 1 := by
  have h : Module.End.HasEigenvalue (f ^ n) (μ ^ n) := hμ.pow n
  rw [hf] at h
  obtain ⟨v, hv_mem, hv_ne⟩ := h.exists_hasEigenvector
  have hv_eq : (1 : V →ₗ[ℂ] V) v = μ ^ n • v :=
    Module.End.HasEigenvector.apply_eq_smul ⟨hv_mem, hv_ne⟩
  rw [Module.End.one_apply] at hv_eq
  have h_sub : (1 - μ ^ n) • v = 0 := by
    rw [sub_smul, one_smul, ← hv_eq, sub_self]
  rcases smul_eq_zero.mp h_sub with h1 | h2
  · exact (sub_eq_zero.mp h1).symm
  · exact absurd h2 hv_ne

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
    μ ^ n = 1 :=
  eigenvalue_pow_eq_one hn hf (hasEigenvalue_of_mem_charpoly_roots f hμ)

lemma trace_eq_charpoly_roots_sum
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (f : V →ₗ[ℂ] V) :
    LinearMap.trace ℂ V f = f.charpoly.roots.sum := by
  let b := Module.Free.chooseBasis ℂ V
  rw [LinearMap.trace_eq_matrix_trace ℂ b,
    Matrix.trace_eq_sum_roots_charpoly_of_splits
      (by simpa using (IsAlgClosed.splits f.charpoly : f.charpoly.Splits)),
    LinearMap.charpoly_toMatrix]

lemma multiset_sum_mem_subring {R : Type*} [Ring R] (S : Subring R) (m : Multiset R)
    (hm : ∀ a ∈ m, a ∈ S) :
    m.sum ∈ S :=
  S.multiset_sum_mem m hm

/-- For a finite group `G` of exponent `n`, every character value of a
finite-dimensional complex representation `ρ : G →* (V →ₗ[ℂ] V)` lies in the range
of any chosen ring homomorphism `φ : CyclotomicField n ℚ → ℂ`. -/
lemma trace_mem_range
    {G : Type*} [Group G] [Finite G]
    (φ : CyclotomicField (Monoid.exponent G) ℚ →+* ℂ)
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : G →* (V →ₗ[ℂ] V)) (g : G) :
    LinearMap.trace ℂ V (ρ g) ∈ φ.range := by
  have hn : Monoid.exponent G ≠ 0 := Monoid.exponent_ne_zero_of_finite
  have hρ : (ρ g) ^ Monoid.exponent G = 1 := representation_pow_exponent_eq_one ρ g
  rw [trace_eq_charpoly_roots_sum]
  refine multiset_sum_mem_subring φ.range _ ?_
  intro μ hμ
  exact mem_range_of_pow_eq_one hn φ (charpoly_roots_pow_eq_one hn hρ hμ)

end FLT.CharacterValuesCyclotomic
