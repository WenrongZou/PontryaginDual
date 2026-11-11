/-
Copyright (c) 2026 Wenrong Zou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wenrong Zou
-/
module

public import PontryaginDuality.Fourier.L1
public import PontryaginDuality.PositiveDefinite.Basic

/-!
# Bochner's theorem

Let `G` be a locally compact abelian group. Bochner's theorem states that the continuous positive
definite functions on `G` are exactly the functions of the form `x ↦ ∫ χ, χ x ∂ν`, where `ν` is a
finite regular measure on the Pontryagin dual of `G`, and that `ν` is unique.

## Main definitions

* `AddPontryaginDual.bochnerMeasure φ`: the finite regular measure on `AddPontryaginDual G`
  associated with a continuous positive definite function `φ : G → ℂ`. It is `0` if `φ` is not
  continuous and positive definite.

## Main statements

* `IsPositiveDefinite.norm_integral_mul_le`: the key estimate
  `‖∫ x, f x * φ x ∂μ‖ ≤ ‖φ 0‖ * ‖fourierL1 μ f‖`.
* `IsPositiveDefinite.exists_measure_integral_toAddChar`: **Bochner's theorem** (existence).
* `AddPontryaginDual.measure_ext_of_integral_toAddChar`: a finite regular measure `ν` on the
  Pontryagin dual is determined by the function `x ↦ ∫ χ, χ x ∂ν` (uniqueness in Bochner's
  theorem).
* `AddPontryaginDual.ae_eq_zero_of_fourierIntegralInv_eq_zero`: the inverse Fourier transform is
  injective on `L¹` of the Pontryagin dual.

## Implementation notes

We follow the proof of [W. Rudin, *Fourier Analysis on Groups*, Section 1.4][rudin1962], which
only uses the Gelfand theory of `L¹(G)` (and neither the Gelfand–Naimark–Segal construction nor
the Krein–Milman theorem).

## References

* [W. Rudin, *Fourier Analysis on Groups*, Section 1.4][rudin1962]
* [G. B. Folland, *A Course in Abstract Harmonic Analysis*, Section 4.2][folland2016]
-/

@[expose] public section

open MeasureTheory Measure Filter Topology
open scoped ComplexOrder ComplexConjugate

variable {G : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
  [LocallyCompactSpace G]

section Estimate

variable [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsAddHaarMeasure] [μ.Regular]

open AddPontryaginDual in
/-- The key estimate in the proof of Bochner's theorem: the linear functional
`f ↦ ∫ x, f x * φ x ∂μ` on `L¹(G)` associated with a continuous positive definite function `φ`
is bounded with respect to the uniform norm of the Fourier transform. -/
theorem IsPositiveDefinite.norm_integral_mul_le {φ : G → ℂ} (hφ : IsPositiveDefinite φ)
    (hφc : Continuous φ) (f : Lp ℂ 1 μ) :
    ‖∫ x, f x * φ x ∂μ‖ ≤ ‖φ 0‖ * ‖fourierL1 μ f‖ := by
  -- Write `T f = ∫ x, f x * φ x ∂μ` and `f⋆ = L1.involution f`. By
  -- `IsPositiveDefinite.integral_integral_nonneg` and a density argument, `(f, g) ↦ T (f * g⋆)`
  -- is a positive semidefinite Hermitian form on `L¹(G)`. The Cauchy–Schwarz inequality and
  -- approximate units (`L1.exists_nhds_zero_norm_mul_sub_lt`) give `‖T f‖ ^ 2 ≤ φ 0 * T (f * f⋆)`.
  -- Iterating this inequality with `h = f * f⋆` in place of `f` gives
  -- `‖T f‖ ^ 2 ≤ φ 0 ^ (2 - 2⁻¹ ^ n) * ‖h ^ (2 ^ n)‖ ^ (2⁻¹ ^ n)`, and the right-hand side tends to
  -- `φ 0 ^ 2 * ‖fourierL1 μ h‖ = (φ 0 * ‖fourierL1 μ f‖) ^ 2` by Gelfand's formula and
  -- `spectralRadius_inr_eq_nnnorm_fourierL1`.
  sorry

end Estimate

namespace AddPontryaginDual

variable [MeasurableSpace (AddPontryaginDual G)] [BorelSpace (AddPontryaginDual G)]

section FourierStieltjes

omit [IsTopologicalAddGroup G] [LocallyCompactSpace G] [MeasurableSpace (AddPontryaginDual G)]
  [BorelSpace (AddPontryaginDual G)] in
/-- The elements of the Pontryagin dual are positive definite functions. -/
theorem isPositiveDefinite_toAddChar (χ : AddPontryaginDual G) :
    IsPositiveDefinite fun x ↦ (χ.toAddChar x : ℂ) :=
  χ.toAddChar.isPositiveDefinite

/-- The function `x ↦ ∫ χ, χ x ∂ν` is positive definite for every finite measure `ν` on the
Pontryagin dual. -/
theorem isPositiveDefinite_integral_toAddChar (ν : Measure (AddPontryaginDual G))
    [IsFiniteMeasure ν] : IsPositiveDefinite fun x : G ↦ ∫ χ, (χ.toAddChar x : ℂ) ∂ν := by
  sorry

/-- The function `x ↦ ∫ χ, χ x ∂ν` is continuous for every finite regular measure `ν` on the
Pontryagin dual. -/
theorem continuous_integral_toAddChar (ν : Measure (AddPontryaginDual G)) [IsFiniteMeasure ν]
    [ν.Regular] : Continuous fun x : G ↦ ∫ χ, (χ.toAddChar x : ℂ) ∂ν := by
  -- This is `continuous_fourierIntegralInv` applied to the constant function `1`.
  sorry

/-- A finite regular measure `ν` on the Pontryagin dual is determined by the function
`x ↦ ∫ χ, χ x ∂ν`. This is the uniqueness part of Bochner's theorem. -/
theorem measure_ext_of_integral_toAddChar {ν₁ ν₂ : Measure (AddPontryaginDual G)}
    [IsFiniteMeasure ν₁] [IsFiniteMeasure ν₂] [ν₁.Regular] [ν₂.Regular]
    (h : ∀ x : G, ∫ χ, (χ.toAddChar x : ℂ) ∂ν₁ = ∫ χ, (χ.toAddChar x : ℂ) ∂ν₂) : ν₁ = ν₂ := by
  -- Let `μ` be a Haar measure on `G`. Integrating the assumption against `f : Lp ℂ 1 μ` gives
  -- `∫ χ, fourierL1 μ f (-χ) ∂ν₁ = ∫ χ, fourierL1 μ f (-χ) ∂ν₂`. Since `fourierL1 μ` has dense
  -- range (`denseRange_fourierL1`), the two measures have the same integrals against all
  -- continuous functions vanishing at infinity, so they are equal by
  -- `Measure.ext_of_integral_eq_on_compactlySupported`.
  sorry

/-- The inverse Fourier transform is injective on `L¹` of the Pontryagin dual. -/
theorem ae_eq_zero_of_fourierIntegralInv_eq_zero {ν : Measure (AddPontryaginDual G)} [ν.Regular]
    {F : AddPontryaginDual G → ℂ} (hF : Integrable F ν) (h : fourierIntegralInv ν F = 0) :
    F =ᵐ[ν] 0 := by
  -- Same proof as `measure_ext_of_integral_toAddChar`: `∫ χ, Φ χ * F χ ∂ν = 0` for all `Φ` in the
  -- range of `fourierL1 μ`, hence for all continuous functions `Φ` vanishing at infinity.
  sorry

end FourierStieltjes

section Bochner

/-- **Bochner's theorem**: every continuous positive definite function on a locally compact
abelian group is of the form `x ↦ ∫ χ, χ x ∂ν` for a finite regular measure `ν` on the Pontryagin
dual. -/
theorem _root_.IsPositiveDefinite.exists_measure_integral_toAddChar {φ : G → ℂ}
    (hφ : IsPositiveDefinite φ) (hφc : Continuous φ) :
    ∃ ν : Measure (AddPontryaginDual G), IsFiniteMeasure ν ∧ ν.Regular ∧
      ∀ x, φ x = ∫ χ, (χ.toAddChar x : ℂ) ∂ν := by
  -- Let `μ` be a Haar measure on `G`. By `IsPositiveDefinite.norm_integral_mul_le`, the linear
  -- functional `fourierL1 μ f ↦ ∫ x, f x * φ x ∂μ` is well defined and bounded on the range of
  -- `fourierL1 μ`, which is dense in `C₀(AddPontryaginDual G, ℂ)` (`denseRange_fourierL1`). Extend
  -- it to a bounded linear functional `Λ` with `‖Λ‖ ≤ φ 0`. Using approximate units one gets
  -- `φ 0 ≤ ‖Λ‖` and that `Λ` attains its norm "at the constant function `1`", which implies that
  -- `Λ` is positive. The Riesz–Markov–Kakutani theorem (`RealRMK.rieszMeasure`) gives a finite
  -- regular measure `ν` with `∫ x, f x * φ x ∂μ = ∫ χ, fourierL1 μ f (-χ) ∂ν` for all `f`, and
  -- then `φ x = ∫ χ, χ x ∂ν` for all `x` since both sides are continuous.
  sorry

open Classical in
/-- The finite regular measure on the Pontryagin dual associated with a continuous positive
definite function `φ` by Bochner's theorem. It is defined to be `0` if `φ` is not continuous and
positive definite. -/
noncomputable def bochnerMeasure (φ : G → ℂ) : Measure (AddPontryaginDual G) :=
  if h : IsPositiveDefinite φ ∧ Continuous φ then
    (h.1.exists_measure_integral_toAddChar h.2).choose
  else 0

variable {φ : G → ℂ}

instance : IsFiniteMeasure (bochnerMeasure φ) := by
  unfold bochnerMeasure
  split_ifs with h
  · exact (h.1.exists_measure_integral_toAddChar h.2).choose_spec.1
  · infer_instance

instance : (bochnerMeasure φ).Regular := by
  unfold bochnerMeasure
  split_ifs with h
  · exact (h.1.exists_measure_integral_toAddChar h.2).choose_spec.2.1
  · infer_instance

theorem integral_toAddChar_bochnerMeasure (hφ : IsPositiveDefinite φ) (hφc : Continuous φ)
    (x : G) : ∫ χ, (χ.toAddChar x : ℂ) ∂bochnerMeasure φ = φ x := by
  unfold bochnerMeasure
  split_ifs with h
  · exact ((h.1.exists_measure_integral_toAddChar h.2).choose_spec.2.2 x).symm
  · exact absurd ⟨hφ, hφc⟩ h

/-- The measure given by Bochner's theorem is unique. -/
theorem eq_bochnerMeasure {ν : Measure (AddPontryaginDual G)} [IsFiniteMeasure ν] [ν.Regular]
    (h : ∀ x, φ x = ∫ χ, (χ.toAddChar x : ℂ) ∂ν) : ν = bochnerMeasure φ := by
  have hφ : IsPositiveDefinite φ := by
    convert isPositiveDefinite_integral_toAddChar ν using 1
    exact funext h
  have hφc : Continuous φ := by
    convert continuous_integral_toAddChar ν using 1
    exact funext h
  refine measure_ext_of_integral_toAddChar fun x ↦ ?_
  rw [integral_toAddChar_bochnerMeasure hφ hφc, h x]

@[simp]
theorem bochnerMeasure_integral_toAddChar (ν : Measure (AddPontryaginDual G)) [IsFiniteMeasure ν]
    [ν.Regular] : bochnerMeasure (fun x : G ↦ ∫ χ, (χ.toAddChar x : ℂ) ∂ν) = ν :=
  (eq_bochnerMeasure fun _ ↦ rfl).symm

end Bochner

section Parseval

variable [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsAddHaarMeasure] [μ.Regular]

/-- A Parseval-type formula: the integral of an integrable function `f` against a continuous
positive definite function `φ` is the integral of the Fourier transform of `f` against the measure
associated with `φ`. -/
theorem integral_mul_eq_integral_fourierIntegral_neg {φ : G → ℂ} (hφ : IsPositiveDefinite φ)
    (hφc : Continuous φ) {f : G → ℂ} (hf : Integrable f μ) :
    ∫ x, f x * φ x ∂μ = ∫ χ, fourierIntegral μ f (-χ) ∂bochnerMeasure φ := by
  -- Replace `φ x` by `∫ χ, χ x ∂bochnerMeasure φ` and exchange the two integrals.
  sorry

end Parseval

end AddPontryaginDual
