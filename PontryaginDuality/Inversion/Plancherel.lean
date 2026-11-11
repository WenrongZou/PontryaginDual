/-
Copyright (c) 2026 Wenrong Zou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wenrong Zou
-/
module

public import Mathlib.Analysis.Normed.Operator.Extend
public import PontryaginDuality.Inversion.DualHaar

/-!
# The Plancherel theorem

Let `G` be a locally compact abelian group with a regular Haar measure `μ`. The Plancherel theorem
states that the Fourier transform on `L¹(G) ∩ L²(G)` extends to a unitary operator from `L²(G)` to
`L²` of the Pontryagin dual, with respect to the dual Haar measure.

## Main definitions

* `MeasureTheory.Lp.integrableSubmodule μ`: the subspace `L¹ ∩ L²` of `L²`.
* `AddPontryaginDual.fourierL2 μ`: the Fourier transform as a linear isometry equivalence
  `Lp ℂ 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 μ.dualAddHaar`.

## Main statements

* `AddPontryaginDual.eLpNorm_two_fourierIntegral`: the Fourier transform preserves the `L²` norm
  of functions in `L¹ ∩ L²`.
* `AddPontryaginDual.fourierL2_toLp`: `fourierL2 μ` is given by `fourierIntegral μ` on `L¹ ∩ L²`.
* `AddPontryaginDual.coeFn_fourierL2_symm`: the inverse of `fourierL2 μ` is given by
  `fourierIntegralInv μ.dualAddHaar` on `L¹ ∩ L²`.
* `AddPontryaginDual.fourierIntegral_fourierIntegralInv_mul`: the Fourier transform turns the
  pointwise product of inverse Fourier transforms into the convolution.
* `AddPontryaginDual.exists_integrable_fourierIntegral_ne_zero`: for every nonempty open subset
  `U` of the Pontryagin dual, there is an integrable function on `G` whose Fourier transform is
  nonzero and vanishes outside `U`.

## References

* [G. B. Folland, *A Course in Abstract Harmonic Analysis*, Sections 4.2 and 4.3][folland2016]
-/

@[expose] public section

open MeasureTheory Measure Filter Topology
open scoped ENNReal Convolution

/-- The subspace `L¹ ∩ L²` of `L²`. -/
def MeasureTheory.Lp.integrableSubmodule {α : Type*} [MeasurableSpace α] (μ : Measure α) :
    Submodule ℂ (Lp ℂ 2 μ) where
  carrier := {f | Integrable f μ}
  add_mem' hf hg := (hf.add hg).congr (Lp.coeFn_add _ _).symm
  zero_mem' := (integrable_zero _ _ _).congr (Lp.coeFn_zero _ _ _).symm
  smul_mem' c _ hf := (hf.smul c).congr (Lp.coeFn_smul c _).symm

namespace AddPontryaginDual

variable {G : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [MeasurableSpace (AddPontryaginDual G)] [BorelSpace (AddPontryaginDual G)]
  (μ : Measure G) [μ.IsAddHaarMeasure] [μ.Regular]

section L1L2

variable {f : G → ℂ}

/-- The Fourier transform of a function in `L¹ ∩ L²` is in `L²`. -/
theorem memLp_two_fourierIntegral (hf : Integrable f μ) (hf2 : MemLp f 2 μ) :
    MemLp (fourierIntegral μ f) 2 μ.dualAddHaar := by
  sorry

/-- The Fourier transform preserves the `L²` norm of functions in `L¹ ∩ L²`. -/
theorem eLpNorm_two_fourierIntegral (hf : Integrable f μ) (hf2 : MemLp f 2 μ) :
    eLpNorm (fourierIntegral μ f) 2 μ.dualAddHaar = eLpNorm f 2 μ := by
  -- Let `g x = ∫ y, f y * conj (f (-x + y)) ∂μ`. Then `g` is continuous, integrable and positive
  -- definite (`isPositiveDefinite_integral_mul_conj`), `g 0 = ∫ y, ‖f y‖ ^ 2 ∂μ` and
  -- `fourierIntegral μ g χ = ‖fourierIntegral μ f χ‖ ^ 2`. Apply the inversion theorem
  -- `fourierIntegralInv_fourierIntegral` to `g` at `0`.
  sorry

end L1L2

section L2

/-- The Fourier transform on `L¹ ∩ L²`, with values in `L²` of the Pontryagin dual. Use
`AddPontryaginDual.fourierL2` instead. -/
noncomputable def fourierL2Fun (f : Lp.integrableSubmodule μ) : Lp ℂ 2 μ.dualAddHaar :=
  (memLp_two_fourierIntegral μ f.2 (Lp.memLp f.1)).toLp (fourierIntegral μ f.1)

theorem fourierL2Fun_add (f g : Lp.integrableSubmodule μ) :
    fourierL2Fun μ (f + g) = fourierL2Fun μ f + fourierL2Fun μ g := by
  sorry

theorem fourierL2Fun_smul (c : ℂ) (f : Lp.integrableSubmodule μ) :
    fourierL2Fun μ (c • f) = c • fourierL2Fun μ f := by
  sorry

theorem norm_fourierL2Fun (f : Lp.integrableSubmodule μ) : ‖fourierL2Fun μ f‖ = ‖f‖ := by
  -- This is `eLpNorm_two_fourierIntegral`.
  sorry

/-- The Fourier transform on `L¹ ∩ L²` as a linear map. Use `AddPontryaginDual.fourierL2`
instead. -/
noncomputable def fourierL2Aux : Lp.integrableSubmodule μ →ₗ[ℂ] Lp ℂ 2 μ.dualAddHaar where
  toFun := fourierL2Fun μ
  map_add' := fourierL2Fun_add μ
  map_smul' := fourierL2Fun_smul μ

/-- The extension of the Fourier transform to a continuous linear map on `L²`. Use
`AddPontryaginDual.fourierL2` instead. -/
noncomputable def fourierL2CLM : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ.dualAddHaar :=
  (fourierL2Aux μ).extendOfNorm (Lp.integrableSubmodule μ).subtype

/-- `L¹ ∩ L²` is dense in `L²`. -/
theorem dense_integrableSubmodule : Dense (Lp.integrableSubmodule μ : Set (Lp ℂ 2 μ)) := by
  -- It contains the continuous functions with compact support.
  sorry

theorem fourierL2CLM_apply (f : Lp.integrableSubmodule μ) :
    fourierL2CLM μ f = fourierL2Fun μ f := by
  -- `LinearMap.extendOfNorm_eq`, `dense_integrableSubmodule` and `norm_fourierL2Fun`.
  sorry

theorem norm_fourierL2CLM (f : Lp ℂ 2 μ) : ‖fourierL2CLM μ f‖ = ‖f‖ := by
  -- By density, from `fourierL2CLM_apply` and `norm_fourierL2Fun`.
  sorry

theorem fourierL2CLM_surjective : Function.Surjective (fourierL2CLM μ) := by
  -- The range is closed, since `fourierL2CLM μ` is an isometry. Let `Ψ` be orthogonal to the
  -- range. The range is stable under multiplication by `χ ↦ χ x` for all `x : G` (by
  -- `fourierIntegral_comp_add_left`), hence for all `f` in `L¹ ∩ L²` the integrable function
  -- `F = conj (fourierIntegral μ f) * Ψ` satisfies `fourierIntegralInv μ.dualAddHaar F = 0`.
  -- By `ae_eq_zero_of_fourierIntegralInv_eq_zero`, `F = 0` almost everywhere, and `Ψ = 0` by
  -- `exists_fourierL1_ne_zero`.
  sorry

/-- The **Plancherel theorem**: the Fourier transform as a linear isometry equivalence between
`L²(G)` and `L²` of the Pontryagin dual of `G`, with respect to the dual Haar measure. -/
noncomputable def fourierL2 : Lp ℂ 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 μ.dualAddHaar :=
  LinearIsometryEquiv.ofSurjective
    { toLinearMap := (fourierL2CLM μ).toLinearMap
      norm_map' := norm_fourierL2CLM μ }
    (fourierL2CLM_surjective μ)

variable {μ} in
/-- On `L¹ ∩ L²`, the Fourier transform `fourierL2 μ` is given by `fourierIntegral μ`. -/
theorem fourierL2_toLp {f : G → ℂ} (hf : Integrable f μ) (hf2 : MemLp f 2 μ) :
    fourierL2 μ (hf2.toLp f) = (memLp_two_fourierIntegral μ hf hf2).toLp (fourierIntegral μ f) := by
  sorry

variable {μ} in
/-- On `L¹ ∩ L²`, the inverse of the Fourier transform `fourierL2 μ` is given by
`fourierIntegralInv μ.dualAddHaar`. -/
theorem coeFn_fourierL2_symm {F : AddPontryaginDual G → ℂ} (hF : Integrable F μ.dualAddHaar)
    (hF2 : MemLp F 2 μ.dualAddHaar) :
    (fourierL2 μ).symm (hF2.toLp F) =ᵐ[μ] fourierIntegralInv μ.dualAddHaar F := by
  -- The inverse of a unitary operator is its adjoint. For `f` in `L¹ ∩ L²`, exchanging the two
  -- integrals gives
  -- `⟪fourierL2 μ f, F⟫ = ∫ x, conj (f x) * fourierIntegralInv μ.dualAddHaar F x ∂μ`.
  sorry

end L2

section Convolution

variable {μ} {Φ Ψ : AddPontryaginDual G → ℂ}

theorem integrable_fourierIntegralInv_mul (hΦ : Continuous Φ) (hΦ' : HasCompactSupport Φ)
    (hΨ : Continuous Ψ) (hΨ' : HasCompactSupport Ψ) :
    Integrable (fourierIntegralInv μ.dualAddHaar Φ * fourierIntegralInv μ.dualAddHaar Ψ) μ := by
  -- Both factors are in `L²` by `coeFn_fourierL2_symm`.
  sorry

/-- The Fourier transform turns the pointwise product of the inverse Fourier transforms of two
continuous functions with compact support into their convolution. -/
theorem fourierIntegral_fourierIntegralInv_mul (hΦ : Continuous Φ) (hΦ' : HasCompactSupport Φ)
    (hΨ : Continuous Ψ) (hΨ' : HasCompactSupport Ψ) :
    fourierIntegral μ (fourierIntegralInv μ.dualAddHaar Φ * fourierIntegralInv μ.dualAddHaar Ψ) =
      Φ ⋆[.mul ℂ ℂ, μ.dualAddHaar] Ψ := by
  -- Write `f = fourierIntegralInv μ.dualAddHaar Φ` and `g = fourierIntegralInv μ.dualAddHaar Ψ`.
  -- Then `fourierIntegral μ (f * g) χ = ⟪conj g * χ, f⟫` is the inner product in `L²(G)`. Apply
  -- `fourierL2 μ`, which preserves inner products and maps `f` to `Φ` and `conj g * χ` to
  -- `η ↦ conj (Ψ (χ - η))` by `coeFn_fourierL2_symm`.
  sorry

variable (μ) in
/-- For every nonempty open subset `U` of the Pontryagin dual, there is an integrable function on
`G` whose Fourier transform is nonzero and vanishes outside `U`. -/
theorem exists_integrable_fourierIntegral_ne_zero {U : Set (AddPontryaginDual G)} (hU : IsOpen U)
    (hne : U.Nonempty) :
    ∃ f : G → ℂ, Integrable f μ ∧ fourierIntegral μ f ≠ 0 ∧
      ∀ χ ∉ U, fourierIntegral μ f χ = 0 := by
  -- Let `χ₀ ∈ U` and let `V` be a symmetric neighborhood of `0` with `χ₀ + V + V ⊆ U`. Let `Φ ≥ 0`
  -- be a nonzero continuous function with compact support contained in `V` such that
  -- `Φ (-χ) = Φ χ`, and let `Ψ χ = Φ (χ - χ₀)`. Then `Φ ⋆ Ψ` is supported in `χ₀ + V + V` and it is
  -- nonzero at `χ₀`. Conclude by `fourierIntegral_fourierIntegralInv_mul`.
  sorry

end Convolution

end AddPontryaginDual
