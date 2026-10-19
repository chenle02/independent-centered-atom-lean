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
  sorry
end ProbabilityCore.IndependentCenteredAtom
