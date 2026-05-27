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

For a finite group `G` of exponent `n`, every character value of a finite-dimensional
complex representation `ρ : G →* (V →ₗ[ℂ] V)` lies in the image of a (single,
`G`-uniform) ring embedding `CyclotomicField n ℚ →+* ℂ`.

This file formalizes the elementary route to the conclusion: the eigenvalues of
`ρ g` are `n`-th roots of unity (because `ρ(g)^n = id`), hence they each lie in
the range of any embedding of `CyclotomicField n ℚ` into `ℂ`; the trace is the
sum of these eigenvalues, so it too lies in the range.

This corresponds to part II of the blueprint
"Character values of finite groups lie in cyclotomic fields".
-/

namespace FLT.CharacterValuesCyclotomic

open Polynomial

/-! ### The embedding `φ : CyclotomicField n ℚ →+* ℂ` -/

/-- The cyclotomic field `CyclotomicField n ℚ` is algebraic over `ℚ`. -/
lemma cyclotomicField_isAlgebraic (n : ℕ) :
    Algebra.IsAlgebraic ℚ (CyclotomicField n ℚ) :=
  Algebra.IsAlgebraic.of_finite ℚ (CyclotomicField n ℚ)

/-- For every `n : ℕ` there is a `ℚ`-algebra homomorphism from `CyclotomicField n ℚ`
to `ℂ`. -/
noncomputable def cyclotomicEmbeddingAlgHom (n : ℕ) :
    CyclotomicField n ℚ →ₐ[ℚ] ℂ :=
  sorry

/-- For every `n : ℕ` there is a ring homomorphism from `CyclotomicField n ℚ` to `ℂ`.
This is the underlying ring homomorphism of `cyclotomicEmbeddingAlgHom n`. -/
noncomputable def cyclotomicEmbedding (n : ℕ) : CyclotomicField n ℚ →+* ℂ :=
  (cyclotomicEmbeddingAlgHom n).toRingHom

/-- The range of any ring homomorphism `φ : CyclotomicField n ℚ → ℂ` contains every
`n`-th root of unity in `ℂ`, provided `n ≠ 0`. -/
lemma mem_range_of_pow_eq_one {n : ℕ} (hn : n ≠ 0)
    (φ : CyclotomicField n ℚ →+* ℂ) {ξ : ℂ} (hξ : ξ ^ n = 1) :
    ξ ∈ φ.range := by
  sorry

/-! ### Eigenvalues of finite-order endomorphisms are roots of unity -/

/-- A monoid homomorphism `ρ : G →* (V →ₗ[ℂ] V)` sends every `g` to a linear
endomorphism whose `Monoid.exponent G`-th power is the identity. When `G` is finite
the exponent is positive, giving the usual "roots of unity" statement; when the
exponent is zero the statement is `(ρ g) ^ 0 = 1`, which is also true. -/
lemma representation_pow_exponent_eq_one
    {G : Type*} [Group G]
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : G →* (V →ₗ[ℂ] V)) (g : G) :
    (ρ g) ^ Monoid.exponent G = 1 := by
  rw [← map_pow, Monoid.pow_exponent_eq_one, map_one]

/-- Eigenvalues of a finite-order endomorphism are `n`-th roots of unity. -/
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

/-- Over `ℂ` (an algebraically closed field of characteristic zero, in particular an
integral domain), every root of the characteristic polynomial of a linear
endomorphism of a finite-dimensional vector space is an eigenvalue. -/
lemma hasEigenvalue_of_mem_charpoly_roots
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (f : V →ₗ[ℂ] V) {μ : ℂ} (hμ : μ ∈ f.charpoly.roots) :
    Module.End.HasEigenvalue f μ :=
  Module.End.hasEigenvalue_iff_isRoot_charpoly f μ |>.mpr
    ((Polynomial.mem_roots f.charpoly_monic.ne_zero).mp hμ)

/-- Roots of the characteristic polynomial of a finite-order endomorphism over `ℂ`
are `n`-th roots of unity. -/
lemma charpoly_roots_pow_eq_one
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    {n : ℕ} (hn : n ≠ 0) {f : V →ₗ[ℂ] V} (hf : f ^ n = 1)
    {μ : ℂ} (hμ : μ ∈ f.charpoly.roots) :
    μ ^ n = 1 := by
  sorry

/-- Over `ℂ`, the trace of a linear endomorphism of a finite-dimensional vector space
equals the sum (with multiplicity) of the roots of its characteristic polynomial. -/
lemma trace_eq_charpoly_roots_sum
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (f : V →ₗ[ℂ] V) :
    LinearMap.trace ℂ V f = f.charpoly.roots.sum := by
  let b := Module.Free.chooseBasis ℂ V
  rw [LinearMap.trace_eq_matrix_trace ℂ b,
    Matrix.trace_eq_sum_roots_charpoly_of_splits
      (by simpa using (IsAlgClosed.splits f.charpoly : f.charpoly.Splits)),
    LinearMap.charpoly_toMatrix]

/-- A multiset of elements of a ring `R`, all lying in a subring `S`, has sum
in `S`. -/
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
  sorry

/-! ### Main theorem -/

/-- **Character values of finite groups lie in cyclotomic fields, II**:
For every finite group `G` there exists a ring homomorphism
`φ : CyclotomicField (Monoid.exponent G) ℚ →+* ℂ` such that, for every
finite-dimensional complex vector space `V` and every representation
`ρ : G →* (V →ₗ[ℂ] V)`, every character value `trace (ρ g)` lies in the
range of `φ`. -/
theorem character_values_in_cyclotomic_field
    (G : Type*) [Group G] [Finite G] :
    ∃ φ : CyclotomicField (Monoid.exponent G) ℚ →+* ℂ,
      ∀ {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
        (ρ : G →* (V →ₗ[ℂ] V)) (g : G),
        LinearMap.trace ℂ V (ρ g) ∈ φ.range := by
  sorry

end FLT.CharacterValuesCyclotomic
