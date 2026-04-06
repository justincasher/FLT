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
  -- Show f is constant on Ioo a b using the convex MVT
  have hIoo : ∀ x ∈ Ioo a b, DifferentiableAt ℝ f x :=
    fun x hx => (hderiv x hx).differentiableAt
  have hconst_Ioo : ∀ x ∈ Ioo a b, ∀ y ∈ Ioo a b, f x = f y := by
    intro x hx y hy
    have key := convex_Ioo a b |>.norm_image_sub_le_of_norm_deriv_le hIoo
      (fun z hz => ?_) hx hy
    · simp only [zero_mul, norm_le_zero_iff, sub_eq_zero] at key; exact key.symm
    · have := (hderiv z hz).deriv
      rw [this]
      simp
  -- Extend to Icc a b by continuity
  intro x hx
  by_cases hab : a < b
  · -- There exist sequences in Ioo converging to a and x
    have ha_mem : a ∈ Icc a b := left_mem_Icc.mpr hab.le
    -- Use density of Ioo in Icc
    have hdense : closure (Ioo a b) = Icc a b := closure_Ioo hab.ne
    rw [← hdense] at hx ha_mem
    obtain ⟨sx, hsx_mem, hsx_lim⟩ := mem_closure_iff_seq_limit.mp hx
    obtain ⟨sa, hsa_mem, hsa_lim⟩ := mem_closure_iff_seq_limit.mp ha_mem
    have hsx_Icc : ∀ n, sx n ∈ Icc a b := fun n => by
      rw [← hdense]; exact subset_closure (hsx_mem n)
    have hsa_Icc : ∀ n, sa n ∈ Icc a b := fun n => by
      rw [← hdense]; exact subset_closure (hsa_mem n)
    have hf_sx : Filter.Tendsto (f ∘ sx) Filter.atTop (nhds (f x)) :=
      (hcont.continuousAt (by rw [hdense]; exact hx) |>.tendsto).comp hsx_lim
    sorry
  · -- a ≥ b, so Icc a b is trivial
    push_neg at hab
    interval_cases x <;> simp_all [le_antisymm hx.2 (hab.trans hx.1)]

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
