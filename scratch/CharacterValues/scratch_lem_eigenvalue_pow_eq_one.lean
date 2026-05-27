/-
Copyright (c) 2026 Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.GroupTheory.Exponent
import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.Trace
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic

namespace FLT.CharacterValuesCyclotomic

open Polynomial

/-- Eigenvalues of a finite-order endomorphism are `n`-th roots of unity. -/
lemma eigenvalue_pow_eq_one
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    {n : ℕ} (hn : n ≠ 0) {f : V →ₗ[ℂ] V} (hf : f ^ n = 1)
    {μ : ℂ} (hμ : Module.End.HasEigenvalue f μ) :
    μ ^ n = 1 := by
  have h : Module.End.HasEigenvalue (f ^ n) (μ ^ n) := hμ.pow n
  rw [hf] at h
  obtain ⟨v, hv_mem, hv_ne⟩ := h.exists_hasEigenvector
  have hv_eq : (1 : V →ₗ[ℂ] V) v = μ ^ n • v :=
    Module.End.HasEigenvector.apply_eq_smul ⟨hv_mem, hv_ne⟩
  rw [Module.End.one_apply] at hv_eq
  -- hv_eq : v = μ ^ n • v
  have h_sub : (1 - μ ^ n) • v = 0 := by
    rw [sub_smul, one_smul, ← hv_eq, sub_self]
  rcases smul_eq_zero.mp h_sub with h1 | h2
  · exact (sub_eq_zero.mp h1).symm
  · exact absurd h2 hv_ne

end FLT.CharacterValuesCyclotomic
