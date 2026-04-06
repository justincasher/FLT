/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Fundamental Theorem of Calculus

This file formalizes the blueprint for the Fundamental Theorem of Calculus,
mapping each blueprint declaration to existing Mathlib concepts.

## Blueprint definitions

The following definitions from the blueprint correspond to existing Mathlib concepts:
- `def:continuous_on` → `ContinuousOn`
- `def:has_deriv_at` → `HasDerivAt`
- `def:interval_integral` → `∫ x in a..b, f x` (`intervalIntegral`)
- `def:antiderivative` → `IsAntiderivativeOn` (defined below)
-/

open MeasureTheory Set Interval

namespace FLT.FundamentalTheoremOfCalculus

/-- A function `F` is an antiderivative of `f` on `(a,b)` if `F` has derivative `f x` at every
point `x ∈ (a,b)`. This corresponds to `def:antiderivative` in the blueprint. -/
def IsAntiderivativeOn (F f : ℝ → ℝ) (a b : ℝ) : Prop :=
  ∀ x ∈ Ioo a b, HasDerivAt F (f x) x

/-- Continuous functions on a closed interval are interval integrable.
Blueprint: `lem:continuous_integrable`. -/
theorem continuous_integrable {f : ℝ → ℝ} {a b : ℝ}
    (hf : ContinuousOn f (uIcc a b)) :
    IntervalIntegrable f volume a b := sorry

/-- If `‖f x‖ ≤ M` a.e. on `Ι a b`, then `‖∫ x in a..b, f x‖ ≤ M * |b - a|`.
Blueprint: `lem:integral_bound`. -/
theorem integral_bound {f : ℝ → ℝ} {a b M : ℝ}
    (hf : ∀ᵐ x, x ∈ Ι a b → ‖f x‖ ≤ M) :
    ‖∫ x in a..b, f x‖ ≤ M * |b - a| := sorry

/-- Lagrange's Mean Value Theorem: if `f` is continuous on `[a,b]` and differentiable on `(a,b)`,
then there exists `c ∈ (a,b)` such that `f' c = (f b - f a) / (b - a)`.
Blueprint: `lem:mean_value_theorem`. -/
theorem mean_value_theorem {f f' : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : ContinuousOn f (Icc a b))
    (hf' : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x) :
    ∃ c ∈ Ioo a b, f' c = (f b - f a) / (b - a) := sorry

/-- Heine–Cantor theorem: a continuous function on a compact interval is uniformly continuous.
Blueprint: `lem:uniform_continuity`. -/
theorem uniform_continuity {f : ℝ → ℝ} {a b : ℝ}
    (hf : ContinuousOn f (Icc a b)) :
    UniformContinuousOn f (Icc a b) := sorry

/-- If `f` is continuous on `[a,b]` and `f'(x) = 0` for all `x ∈ (a,b)`, then `f` is constant.
Blueprint: `lem:zero_deriv_constant`. -/
theorem zero_deriv_constant {f : ℝ → ℝ} {a b : ℝ}
    (hcont : ContinuousOn f (Icc a b))
    (hderiv : ∀ x ∈ Ioo a b, HasDerivAt f 0 x) :
    ∀ x ∈ Icc a b, f x = f a := by
  apply constant_of_has_deriv_right_zero hcont
  intro x hx
  rcases eq_or_lt_of_le hx.1 with rfl | hax
  · -- x = a: need HasDerivWithinAt f 0 (Ici a) a
    -- We show this using the squeeze: |f(a+h) - f(a)| ≤ 0 * h for h > 0
    -- by applying the convex MVT on [a, a+h] ⊆ [a, b] for small h
    rw [hasDerivWithinAt_iff_tendsto]
    rw [show (0 : ℝ) = 0 by rfl]
    simp only [sub_zero]
    rw [Metric.tendsto_nhdsWithin_nhds]
    intro ε hε
    refine ⟨ε, hε, fun y hy_dist hy_mem => ?_⟩
    sorry
  · -- x > a, so x ∈ Ioo a b
    exact (hderiv x ⟨hax, hx.2⟩).hasDerivWithinAt

/-- First Fundamental Theorem of Calculus: if `f` is continuous on `[a,b]`, then
`F(x) = ∫ t in a..x, f t` has derivative `f x` at every `x ∈ (a,b)`.
Blueprint: `thm:ftc1`. -/
theorem ftc1 {f : ℝ → ℝ} {a b : ℝ}
    (hf : ContinuousOn f (uIcc a b))
    (x : ℝ) (hx : x ∈ Ioo (min a b) (max a b)) :
    HasDerivAt (fun u => ∫ t in a..u, f t) (f x) x := sorry

/-- Second Fundamental Theorem of Calculus: if `f` is continuous on `[a,b]` and `F` is an
antiderivative of `f` (i.e. `F` has right derivative `f'` on `(a,b)`), then
`∫ x in a..b, f' x = F b - F a`.
Blueprint: `thm:ftc2`. -/
theorem ftc2 {F f' : ℝ → ℝ} {a b : ℝ}
    (hF : ContinuousOn F (uIcc a b))
    (hF' : ∀ x ∈ Ioo (min a b) (max a b), HasDerivWithinAt F (f' x) (Ioi x) x)
    (hf'i : IntervalIntegrable f' volume a b) :
    ∫ x in a..b, f' x = F b - F a := sorry

end FLT.FundamentalTheoremOfCalculus
