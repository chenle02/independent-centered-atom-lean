/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

A bounded measurable coefficient multiplying independent centered noise.
-/
import Mathlib.Probability.ConditionalExpectation
import Mathlib.Probability.Independence.Integration
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic.NormNum
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal
namespace ProbabilityCore.IndependentCenteredAtom

/-- A bounded past coefficient times independent centered L2 noise.
Noise moments and independence are hypotheses. The conclusion supplies product
integrability, conditional mean zero and the factored second moment. -/
theorem bounded_mul_independent_centered
    {Ω : Type*} [m₀ : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (noise F : MeasurableSpace Ω) (hnoise : noise ≤ m₀) (hF : F ≤ m₀)
    (hind : Indep noise F μ) (Z : Ω → ℝ) (hZ : StronglyMeasurable[noise] Z)
    (hZ₂ : MemLp Z 2 μ) (hmean : (∫ ω, Z ω ∂μ) = 0)
    (V : ℝ) (hvariance : (∫ ω, (Z ω)^2 ∂μ) = V)
    (ξ : Ω → ℝ) (hξ : StronglyMeasurable[F] ξ)
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ ω, |ξ ω| ≤ C) :
    Integrable (fun ω => ξ ω * Z ω) μ ∧
    Integrable (fun ω => (ξ ω * Z ω)^2) μ ∧
    μ[(fun ω => ξ ω * Z ω) | F] =ᵐ[μ] 0 ∧
    (∫ ω, (ξ ω * Z ω)^2 ∂μ) = V * (∫ ω, (ξ ω)^2 ∂μ) := by
  have hξa : StronglyMeasurable[m₀] ξ := hξ.mono hF
  have hZI : Integrable Z μ := MemLp.integrable (by norm_num : (1:ℝ≥0∞) ≤ 2) hZ₂
  have hξsquareI : Integrable (fun ω => (ξ ω)^2) μ := by
    refine (integrable_const (C^2:ℝ)).mono' (hξa.pow 2).aestronglyMeasurable (ae_of_all _ ?_)
    intro ω
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hC).mpr (hbound ω)
  have hZX : IndepFun Z ξ μ := by
    rw [IndepFun_iff_Indep, Indep_iff]
    intro A B hA hB
    exact (Indep_iff _ _ _).mp hind A B
      (hZ.measurable.comap_le A hA) (hξ.measurable.comap_le B hB)
  have hI : Integrable (fun ω => ξ ω * Z ω) μ :=
    hZI.bdd_mul hξa.aestronglyMeasurable
      (ae_of_all _ (fun ω => by simpa only [Real.norm_eq_abs] using hbound ω))
  have hI₂ : Integrable (fun ω => (ξ ω * Z ω)^2) μ := by
    have hmul := (hZX.symm.comp (measurable_id.pow_const 2)
      (measurable_id.pow_const 2)).integrable_mul hξsquareI hZ₂.integrable_sq
    change Integrable (fun ω => (ξ ω)^2 * (Z ω)^2) μ at hmul
    simpa only [mul_pow] using hmul
  have hCE : μ[(fun ω => ξ ω * Z ω) | F] =ᵐ[μ] (0 : Ω → ℝ) := by
    letI : IsFiniteMeasure (μ.trim hF) := isFiniteMeasure_trim hF
    have hZCE : μ[Z | F] =ᵐ[μ] (0 : Ω → ℝ) := by
      have hh := condExp_indep_eq (μ:=μ) hnoise hF hZ hind
      filter_upwards [hh] with ω hω
      change μ[Z | F] ω = (∫ ζ, Z ζ ∂μ) at hω
      change μ[Z | F] ω = 0
      exact hω.trans hmean
    have hpull := condExp_mul_of_stronglyMeasurable_left (μ:=μ) (m:=F) hξ hI hZI
    change μ[(fun ω => ξ ω * Z ω) | F] =ᵐ[μ]
      (fun ω => ξ ω * μ[Z | F] ω) at hpull
    filter_upwards [hpull, hZCE] with ω hpullω hzeroω
    change μ[Z | F] ω = 0 at hzeroω
    change μ[(fun ω => ξ ω * Z ω) | F] ω = 0
    exact hpullω.trans (by rw [hzeroω, mul_zero])
  have hvarianceAtom : (∫ ω, (ξ ω * Z ω)^2 ∂μ) =
      V * (∫ ω, (ξ ω)^2 ∂μ) := by
    have hξsquare : AEStronglyMeasurable[m₀] ((fun y : ℝ => y^2) ∘ ξ) μ := by
      change AEStronglyMeasurable[m₀] (fun ω => (ξ ω)^2) μ
      exact hξsquareI.aestronglyMeasurable
    have hZsquare : AEStronglyMeasurable[m₀] ((fun y : ℝ => y^2) ∘ Z) μ := by
      change AEStronglyMeasurable[m₀] (fun ω => (Z ω)^2) μ
      exact hZ₂.integrable_sq.aestronglyMeasurable
    have hsquare := (hZX.symm.comp (measurable_id.pow_const 2)
      (measurable_id.pow_const 2)).integral_mul_eq_mul_integral hξsquare hZsquare
    change (∫ ω, (ξ ω)^2 * (Z ω)^2 ∂μ) =
      (∫ ω, (ξ ω)^2 ∂μ) * (∫ ω, (Z ω)^2 ∂μ) at hsquare
    calc
      _ = (∫ ω, (ξ ω)^2 ∂μ) * (∫ ω, (Z ω)^2 ∂μ) := by
        simpa only [mul_pow] using hsquare
      _ = V * (∫ ω, (ξ ω)^2 ∂μ) := by
        rw [hvariance]
        exact mul_comm _ _
  exact ⟨hI, hI₂, hCE, hvarianceAtom⟩
end ProbabilityCore.IndependentCenteredAtom
