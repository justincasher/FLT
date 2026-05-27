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
import Mathlib.Algebra.Ring.Subring.Basic

/-!
# Character values of finite groups lie in cyclotomic fields, II
-/

namespace FLT.CharacterValuesCyclotomic

open Polynomial

/-- A multiset of elements of a ring `R`, all lying in a subring `S`, has sum
in `S`. -/
lemma multiset_sum_mem_subring {R : Type*} [Ring R] (S : Subring R) (m : Multiset R)
    (hm : ∀ a ∈ m, a ∈ S) :
    m.sum ∈ S :=
  S.multiset_sum_mem m hm

end FLT.CharacterValuesCyclotomic
