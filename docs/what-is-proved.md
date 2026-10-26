# What is proved

<!-- Hand-written. Lean statement copied verbatim from ProbabilityCore/IndependentCenteredAtom.lean at commit 0fdcdc039eebe632581e1d92cb6068d989cbc9a0 (the commit the build receipt binds). Re-copy it when the receipts move. -->

`independent-centered-atom-lean` proves one theorem: a bounded coefficient measurable with respect to
the past, multiplied by noise that is independent of the past, centered and square-integrable, has
conditional mean zero given the past, and the second moment of the product factors into the noise
variance times the second moment of the coefficient. This is the elementary step used when computing
second moments of stochastic sums against independent centered noise. The typeset statement is the
author's transcription of the Lean statement; Lean checks only the Lean statement, which is folded
under the card and linked to its source line.

## Notation

- $`(\Omega,\mathcal{F}_0,\mu)`$: a probability space (`μ : Measure Ω` with `IsProbabilityMeasure μ`;
  $`\mathcal{F}_0`$ is the ambient σ-algebra `m₀`).
- $`\mathcal{N},\mathcal{F}\subseteq\mathcal{F}_0`$: two sub-σ-algebras, the noise and the past
  (`noise`, `F`, with `noise ≤ m₀` and `F ≤ m₀`).
- $`\mathbb{E}_\mu[\,\cdot\mid\mathcal{F}]`$: conditional expectation, Lean's `μ[· | F]`.
- "Measurable" means strongly measurable with respect to the stated σ-algebra (`StronglyMeasurable[noise]`,
  `StronglyMeasurable[F]`), which for real-valued functions is ordinary measurability.

## Main results

| # | Result | Reference | Lean | Status |
|---|---|---|---|---|
| 1 | [Bounded coefficient times independent centered noise](#1-bounded-coefficient-times-independent-centered-noise) | standard; Mathlib lemmas below | `bounded_mul_independent_centered` | proved |

### 1. Bounded coefficient times independent centered noise

A bounded past coefficient times independent centered $`L^2`$ noise is integrable, has conditional mean
zero given the past, and its second moment factors.

**Statement.** Let $`(\Omega,\mathcal{F}_0,\mu)`$ be a probability space and let
$`\mathcal{N},\mathcal{F}\subseteq\mathcal{F}_0`$ be independent sub-σ-algebras. Let $`Z`$ be
$`\mathcal{N}`$-measurable with $`Z\in L^2(\mu)`$, $`\int Z\,d\mu=0`$ and $`\int Z^2\,d\mu=V`$, and let
$`\xi`$ be $`\mathcal{F}`$-measurable with $`|\xi(\omega)|\le C`$ for every $`\omega`$, where $`C\ge0`$.
Then $`\xi Z`$ and $`(\xi Z)^2`$ are $`\mu`$-integrable, and

```math
\mathbb{E}_\mu[\xi Z\mid\mathcal{F}]=0\quad\mu\text{-a.e.},\qquad
\int(\xi Z)^2\,d\mu=V\int\xi^2\,d\mu .
```

**Reference.** A standard identity with no single source; the Lean proof assembles three Mathlib
results: independence of a conditional expectation
([`condExp_indep_eq`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=MeasureTheory.condExp_indep_eq#doc)),
pulling a measurable factor out of a conditional expectation
([`condExp_mul_of_stronglyMeasurable_left`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=MeasureTheory.condExp_mul_of_stronglyMeasurable_left#doc)),
and the product rule for integrals of independent functions
([`IndepFun.integral_mul_eq_mul_integral`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=ProbabilityTheory.IndepFun.integral_mul_eq_mul_integral#doc)),
at the pinned Mathlib commit `56a005855ea17e0b0958f73ec801ae140b0a1679`.

**Compared with the reference.** The coefficient is bounded everywhere ($`|\xi|\le C`$), not merely
square-integrable; this gives the integrability of $`\xi Z`$ and $`(\xi Z)^2`$ as conclusions. The
variance $`V`$ is named by the hypothesis $`\int Z^2\,d\mu=V`$; no sign condition on $`V`$ is assumed or
needed. The conditional mean is stated $`\mu`$-almost everywhere.

**Lean.** [`ProbabilityCore.IndependentCenteredAtom.bounded_mul_independent_centered`](https://github.com/chenle02/independent-centered-atom-lean/blob/0fdcdc039eebe632581e1d92cb6068d989cbc9a0/ProbabilityCore/IndependentCenteredAtom.lean#L20)

<details markdown="1">
<summary>Lean statement (copy with the button on the code block)</summary>

```lean
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
    (∫ ω, (ξ ω * Z ω)^2 ∂μ) = V * (∫ ω, (ξ ω)^2 ∂μ)
```

</details>

<details markdown="1">
<summary>Sign-off</summary>

| Field | Value |
|---|---|
| Status | proved |
| Sorry count | 0 (build receipt `.lean-receipts/0fdcdc039eeb-systemd-user-independent-centered-atom-lower001.service-17ad8834031e464eb7e50bb963f1c6c4-h-24e00fc5da6c.json`) |
| Axioms | `propext`, `Classical.choice`, `Quot.sound` (build receipt, at commit `0fdcdc039eeb`; 1 of 1 claim checked, none nonstandard) |
| Statement comparison | comparator receipt `.lean-receipts/0fdcdc039eeb-comparator.json`: result pass; the Challenge statement in `ProbabilityCore/Challenge.lean` = this statement |
| Definitions judged by a person | none recorded |
| Evidence commit | `0fdcdc039eeb` (receipts in `.lean-receipts/`) |
| Human review | unchecked: no independent human review asserted |
| Not covered | no Poisson random measure, stochastic integral or particle model; no unbounded coefficient |
| Signed off | lean-pkg `gate` + `comparator`, 2026-10-19 (mechanical checks only) |

</details>

## Not proved here

- No Poisson random measure, stochastic integral or particle model is constructed.
- No version for an unbounded (merely square-integrable) coefficient.
- No new mathematics is claimed: this is a standard identity, packaged for reuse.

## How this was checked

The [verification page](verification.html) and the [coverage page](coverage.html) are generated by
lean-pkg from the receipts in `.lean-receipts/`. The comparator checks the proof against the trusted
statement in `ProbabilityCore/Challenge.lean` (whose `sorry` is intentional), and `ProbabilityCore/Axioms.lean`
prints the axioms of the theorem. To reproduce, run `lake exe cache get` and `lake build`.
