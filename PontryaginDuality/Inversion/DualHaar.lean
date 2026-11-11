/-
Copyright (c) 2026 Wenrong Zou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wenrong Zou
-/
module

public import PontryaginDuality.PositiveDefinite.Bochner

/-!
# The dual Haar measure and the Fourier inversion theorem

Let `G` be a locally compact abelian group with a regular Haar measure `μ`. In this file we define
the dual Haar measure `μ.dualAddHaar` on the Pontryagin dual of `G`: it is the unique regular Haar
measure for which the Fourier inversion formula holds.

## Main definitions

* `MeasureTheory.Measure.dualAddHaar μ`: the Haar measure on `AddPontryaginDual G` dual to `μ`.

## Main statements

Let `f : G → ℂ` be a continuous, integrable and positive definite function.

* `AddPontryaginDual.fourierIntegral_nonneg`: the Fourier transform of `f` is nonnegative.
* `AddPontryaginDual.withDensity_dualAddHaar_enorm_fourierIntegral`: the measure associated with
  `f` by Bochner's theorem is the measure with density `fourierIntegral μ f` with respect to
  `μ.dualAddHaar`.
* `AddPontryaginDual.integrable_fourierIntegral`,
  `AddPontryaginDual.fourierIntegralInv_fourierIntegral`: the **Fourier inversion theorem**:
  the Fourier transform of `f` is integrable and
  `f x = ∫ χ, χ x • fourierIntegral μ f χ ∂μ.dualAddHaar`.

## Implementation notes

The textbooks state the inversion theorem for the linear span of the continuous positive definite
functions which are integrable. We only state it for positive definite functions, in order to
avoid complex measures; the general case follows by linearity.

## References

* [G. B. Folland, *A Course in Abstract Harmonic Analysis*, Section 4.2][folland2016]
* [W. Rudin, *Fourier Analysis on Groups*, Section 1.5][rudin1962]
-/

@[expose] public section

open MeasureTheory Measure Filter Topology
open scoped ComplexOrder ENNReal

namespace AddPontryaginDual

variable {G : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [MeasurableSpace (AddPontryaginDual G)] [BorelSpace (AddPontryaginDual G)]
  (μ : Measure G) [μ.IsAddHaarMeasure] [μ.Regular]

/-- If `f` and `g` are continuous, integrable and positive definite, then the measures
`fourierIntegral μ f • bochnerMeasure g` and `fourierIntegral μ g • bochnerMeasure f` are
equal. -/
theorem integral_mul_fourierIntegral_bochnerMeasure_comm {f g : G → ℂ}
    (hf : Continuous f) (hfi : Integrable f μ) (hfp : IsPositiveDefinite f)
    (hg : Continuous g) (hgi : Integrable g μ) (hgp : IsPositiveDefinite g)
    {Ψ : AddPontryaginDual G → ℂ} (hΨ : Continuous Ψ) (hΨ' : HasCompactSupport Ψ) :
    ∫ χ, Ψ χ * fourierIntegral μ f χ ∂bochnerMeasure g =
      ∫ χ, Ψ χ * fourierIntegral μ g χ ∂bochnerMeasure f := by
  -- For `h : Lp ℂ 1 μ`, `integral_mul_eq_integral_fourierIntegral_neg` gives
  -- `∫ χ, fourierL1 μ h χ ∂bochnerMeasure f = ∫ x, h x * f (-x) ∂μ`. Applying this to `h * g`
  -- and `h * f` and using the commutativity of the convolution, we get
  -- `∫ χ, fourierL1 μ h χ * fourierIntegral μ g χ ∂bochnerMeasure f
  --   = ∫ χ, fourierL1 μ h χ * fourierIntegral μ f χ ∂bochnerMeasure g`.
  -- Conclude by `denseRange_fourierL1`.
  sorry

/-- There is a regular Haar measure `ν` on the Pontryagin dual such that, for every continuous,
integrable and positive definite function `f`, the Fourier transform of `f` is nonnegative and the
measure associated with `f` by Bochner's theorem has density `fourierIntegral μ f` with respect to
`ν`. -/
theorem exists_isAddHaarMeasure_withDensity_eq_bochnerMeasure :
    ∃ ν : Measure (AddPontryaginDual G), ν.IsAddHaarMeasure ∧ ν.Regular ∧
      ∀ f : G → ℂ, Continuous f → Integrable f μ → IsPositiveDefinite f →
        (∀ χ, 0 ≤ fourierIntegral μ f χ) ∧
          ν.withDensity (fun χ ↦ ‖fourierIntegral μ f χ‖ₑ) = bochnerMeasure f := by
  -- For `Ψ` continuous with compact support, choose `f` continuous, integrable and positive
  -- definite such that `fourierIntegral μ f` does not vanish on the support of `Ψ` (take
  -- `f x = ∫ y, g y * conj (g (-x + y)) ∂μ`, whose Fourier transform is
  -- `‖fourierIntegral μ g‖ ^ 2`, and use `exists_fourierL1_ne_zero` and compactness), and set
  -- `Λ Ψ = ∫ χ, Ψ χ / fourierIntegral μ f χ ∂bochnerMeasure f`. This does not depend on `f` by
  -- `integral_mul_fourierIntegral_bochnerMeasure_comm`. Then `Λ` is a nonzero positive linear
  -- functional, and it is translation invariant since
  -- `bochnerMeasure (fun x ↦ η x * f x)` is the translate of `bochnerMeasure f` by `η`. The
  -- measure `ν` is given by the Riesz–Markov–Kakutani theorem (`RealRMK.rieszMeasure`).
  sorry

/-- The Haar measure on the Pontryagin dual of `G` which is dual to the Haar measure `μ` on `G`:
the unique regular Haar measure for which the Fourier inversion formula holds (see
`AddPontryaginDual.fourierIntegralInv_fourierIntegral` and `AddPontryaginDual.eq_dualAddHaar`). -/
noncomputable def _root_.MeasureTheory.Measure.dualAddHaar : Measure (AddPontryaginDual G) :=
  (exists_isAddHaarMeasure_withDensity_eq_bochnerMeasure μ).choose

instance : (μ.dualAddHaar).IsAddHaarMeasure :=
  (exists_isAddHaarMeasure_withDensity_eq_bochnerMeasure μ).choose_spec.1

instance : (μ.dualAddHaar).Regular :=
  (exists_isAddHaarMeasure_withDensity_eq_bochnerMeasure μ).choose_spec.2.1

variable {μ} {f : G → ℂ}

/-- The Fourier transform of a continuous, integrable and positive definite function is
nonnegative. -/
theorem fourierIntegral_nonneg (hf : Continuous f) (hfi : Integrable f μ)
    (hfp : IsPositiveDefinite f) (χ : AddPontryaginDual G) : 0 ≤ fourierIntegral μ f χ :=
  ((exists_isAddHaarMeasure_withDensity_eq_bochnerMeasure μ).choose_spec.2.2 f hf hfi hfp).1 χ

/-- The measure associated by Bochner's theorem with a continuous, integrable and positive
definite function `f` has density `fourierIntegral μ f` with respect to the dual Haar measure. -/
theorem withDensity_dualAddHaar_enorm_fourierIntegral (hf : Continuous f) (hfi : Integrable f μ)
    (hfp : IsPositiveDefinite f) :
    μ.dualAddHaar.withDensity (fun χ ↦ ‖fourierIntegral μ f χ‖ₑ) = bochnerMeasure f :=
  ((exists_isAddHaarMeasure_withDensity_eq_bochnerMeasure μ).choose_spec.2.2 f hf hfi hfp).2

/-- The Fourier transform of a continuous, integrable and positive definite function is
integrable with respect to the dual Haar measure. -/
theorem integrable_fourierIntegral (hf : Continuous f) (hfi : Integrable f μ)
    (hfp : IsPositiveDefinite f) : Integrable (fourierIntegral μ f) μ.dualAddHaar := by
  -- `∫⁻ χ, ‖fourierIntegral μ f χ‖ₑ ∂μ.dualAddHaar = bochnerMeasure f univ < ∞`.
  sorry

/-- The **Fourier inversion theorem** for continuous, integrable and positive definite
functions. -/
theorem fourierIntegralInv_fourierIntegral (hf : Continuous f) (hfi : Integrable f μ)
    (hfp : IsPositiveDefinite f) :
    fourierIntegralInv μ.dualAddHaar (fourierIntegral μ f) = f := by
  -- `integral_toAddChar_bochnerMeasure`, `withDensity_dualAddHaar_enorm_fourierIntegral` and
  -- `fourierIntegral_nonneg`.
  sorry

/-- The dual Haar measure is the only regular Haar measure for which the Fourier inversion
formula holds at `0`. -/
theorem eq_dualAddHaar {ν : Measure (AddPontryaginDual G)} [ν.IsAddHaarMeasure] [ν.Regular]
    (h : ∀ f : G → ℂ, Continuous f → Integrable f μ → IsPositiveDefinite f →
      fourierIntegralInv ν (fourierIntegral μ f) 0 = f 0) : ν = μ.dualAddHaar := by
  -- `ν = c • μ.dualAddHaar` by uniqueness of the Haar measure, and `c = 1` by applying the
  -- assumption to a function `f` with `f 0 ≠ 0` (`exists_isPositiveDefinite_hasCompactSupport`).
  sorry

end AddPontryaginDual
