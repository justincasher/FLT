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

/-!
# Character values of finite groups lie in cyclotomic fields, II
-/

namespace FLT.CharacterValuesCyclotomic

open Polynomial

/-- The cyclotomic field `CyclotomicField n ℚ` is algebraic over `ℚ`. -/
lemma cyclotomicField_isAlgebraic (n : ℕ) :
    Algebra.IsAlgebraic ℚ (CyclotomicField n ℚ) :=
  Algebra.IsAlgebraic.of_finite ℚ (CyclotomicField n ℚ)

end FLT.CharacterValuesCyclotomic
