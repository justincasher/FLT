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

open MeasureTheory Set Interval Topology

namespace FLT.FundamentalTheoremOfCalculus

/-- A function `F` is an antiderivative of `f` on `(a,b)` if `F` has derivative `f x` at every
point `x ∈ (a,b)`. This corresponds to `def:antiderivative` in the blueprint. -/
def IsAntiderivativeOn (F f : ℝ → ℝ) (a b : ℝ) : Prop :=
  ∀ x ∈ Ioo a b, HasDerivAt F (f x) x

/-- Continuous functions on a closed interval are interval integrable.
Blueprint: `lem:continuous_integrable`. -/
theorem continuous_integrable {f : ℝ → ℝ} {a b : ℝ}
    (hf : ContinuousOn f (uIcc a b)) :
    IntervalIntegrable f volume a b := hf.intervalIntegrable

/-- If `‖f x‖ ≤ M` a.e. on `Ι a b`, then `‖∫ x in a..b, f x‖ ≤ M * |b - a|`.
Blueprint: `lem:integral_bound`. -/
theorem integral_bound {f : ℝ → ℝ} {a b M : ℝ}
    (hf : ∀ᵐ x, x ∈ Ι a b → ‖f x‖ ≤ M) :
    ‖∫ x in a..b, f x‖ ≤ M * |b - a| :=
  intervalIntegral.norm_integral_le_of_norm_le_const_ae hf

/-- Lagrange's Mean Value Theorem: if `f` is continuous on `[a,b]` and differentiable on `(a,b)`,
then there exists `c ∈ (a,b)` such that `f' c = (f b - f a) / (b - a)`.
Blueprint: `lem:mean_value_theorem`. -/
theorem mean_value_theorem {f f' : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : ContinuousOn f (Icc a b))
    (hf' : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x) :
    ∃ c ∈ Ioo a b, f' c = (f b - f a) / (b - a) :=
  exists_hasDerivAt_eq_slope f f' hab hf hf'

/-- Heine–Cantor theorem: a continuous function on a compact interval is uniformly continuous.
Blueprint: `lem:uniform_continuity`. -/
theorem uniform_continuity {f : ℝ → ℝ} {a b : ℝ}
    (hf : ContinuousOn f (Icc a b)) :
    UniformContinuousOn f (Icc a b) :=
  isCompact_Icc.uniformContinuousOn_of_continuous hf

/-- If `f` is continuous on `[a,b]` and `f'(x) = 0` for all `x ∈ (a,b)`, then `f` is constant.
Blueprint: `lem:zero_deriv_constant`. -/
theorem zero_deriv_constant {f : ℝ → ℝ} {a b : ℝ}
    (hcont : ContinuousOn f (Icc a b))
    (hderiv : ∀ x ∈ Ioo a b, HasDerivAt f 0 x) :
    ∀ x ∈ Icc a b, f x = f a := by
  intro x hx
  rcases eq_or_lt_of_le hx.1 with rfl | hax'
  · rfl
  · have hcont' : ContinuousOn f (Icc a x) :=
      hcont.mono (Icc_subset_Icc_right hx.2)
    have hderiv' : ∀ y ∈ Ioo a x, HasDerivAt f 0 y := fun y hy =>
      hderiv y ⟨hy.1, lt_of_lt_of_le hy.2 hx.2⟩
    obtain ⟨c, _, hc'⟩ := exists_hasDerivAt_eq_slope f (fun _ => (0 : ℝ)) hax' hcont' hderiv'
    have hne : x - a ≠ 0 := sub_ne_zero.mpr (ne_of_gt hax')
    rw [eq_comm, div_eq_zero_iff] at hc'
    rcases hc' with h | h
    · linarith
    · exact absurd h hne

/-- First Fundamental Theorem of Calculus: if `f` is continuous on `[a,b]`, then
`F(x) = ∫ t in a..x, f t` has derivative `f x` at every `x ∈ (a,b)`.
Blueprint: `thm:ftc1`. -/
theorem ftc1 {f : ℝ → ℝ} {a b : ℝ}
    (hf : ContinuousOn f (uIcc a b))
    (x : ℝ) (hx : x ∈ Ioo (min a b) (max a b)) :
    HasDerivAt (fun u => ∫ t in a..u, f t) (f x) x := by
  have hx_mem : x ∈ uIcc a b := by
    change x ∈ Icc (min a b) (max a b)
    exact Ioo_subset_Icc_self hx
  have hx_nhds : uIcc a b ∈ 𝓝 x := by
    change Icc (min a b) (max a b) ∈ 𝓝 x
    exact Icc_mem_nhds hx.1 hx.2
  have hcont_x : ContinuousAt f x := (hf x hx_mem).continuousAt hx_nhds
  have hint : IntervalIntegrable f volume a x :=
    hf.intervalIntegrable.mono_set (uIcc_subset_uIcc_left hx_mem)
  have hf_ioo : ContinuousOn f (Ioo (min a b) (max a b)) :=
    hf.mono Ioo_subset_Icc_self
  have hmeas : StronglyMeasurableAtFilter f (𝓝 x) volume :=
    hf_ioo.stronglyMeasurableAtFilter isOpen_Ioo x hx
  exact intervalIntegral.integral_hasDerivAt_right hint hmeas hcont_x

/-- Second Fundamental Theorem of Calculus: if `f` is continuous on `[a,b]` and `F` is an
antiderivative of `f` (i.e. `F` has right derivative `f'` on `(a,b)`), then
`∫ x in a..b, f' x = F b - F a`.
Blueprint: `thm:ftc2`. -/
theorem ftc2 {F f' : ℝ → ℝ} {a b : ℝ}
    (hF : ContinuousOn F (uIcc a b))
    (hF' : ∀ x ∈ Ioo (min a b) (max a b), HasDerivWithinAt F (f' x) (Ioi x) x)
    (hf'i : IntervalIntegrable f' volume a b) :
    ∫ x in a..b, f' x = F b - F a :=
  intervalIntegral.integral_eq_sub_of_hasDeriv_right hF hF' hf'i

end FLT.FundamentalTheoremOfCalculus
