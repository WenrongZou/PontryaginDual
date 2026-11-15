/-
Copyright (c) 2026 Wenrong Zou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wenrong Zou
-/
module

public import Mathlib.Analysis.Normed.Operator.Extend
public import PontryaginDuality.Inversion.DualHaar

import PontryaginDuality.Mathlib.MeasureTheory.Function.ContinuousMapDense
import PontryaginDuality.Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.WithDensity

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
open scoped ENNReal NNReal Convolution ComplexConjugate

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

/-- Hölder's inequality for the integral of a product of two functions in `L²`. -/
private theorem enorm_integral_mul_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g : α → ℂ} (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) :
    ‖∫ x, f x * g x ∂μ‖ₑ ≤ eLpNorm f 2 μ * eLpNorm g 2 μ :=
  calc ‖∫ x, f x * g x ∂μ‖ₑ
    _ ≤ ∫⁻ x, ‖f x * g x‖ₑ ∂μ := enorm_integral_le_lintegral_enorm _
    _ = eLpNorm (f • g) 1 μ := (eLpNorm_one_eq_lintegral_enorm (hf.smul hg)).symm
    _ ≤ eLpNorm f 2 μ * eLpNorm g 2 μ := eLpNorm_smul_le_mul_eLpNorm hf hg

/-- The Fourier transform preserves the `L²` norm of continuous functions with compact support. -/
private theorem eLpNorm_two_fourierIntegral_of_hasCompactSupport {u : G → ℂ} (hu : Continuous u)
    (huc : HasCompactSupport u) :
    eLpNorm (fourierIntegral μ u) 2 μ.dualAddHaar = eLpNorm u 2 μ := by
  -- Let `g x = ∫ y, u y * conj (u (-x + y)) ∂μ`. Then `g` is continuous, integrable and positive
  -- definite, `g 0 = ∫ y, ‖u y‖ ^ 2 ∂μ` and `fourierIntegral μ g χ = ‖fourierIntegral μ u χ‖ ^ 2`.
  -- The total mass of `bochnerMeasure g` is `g 0`, and it is the integral of its density
  -- `fourierIntegral μ g` with respect to the dual Haar measure.
  have hu2 : MemLp u 2 μ := hu.memLp_of_hasCompactSupport huc
  have hgc : Continuous fun x ↦ ∫ y, u y * conj (u (-x + y)) ∂μ := continuous_integral_mul_conj hu2
  have hgp : IsPositiveDefinite fun x ↦ ∫ y, u y * conj (u (-x + y)) ∂μ :=
    isPositiveDefinite_integral_mul_conj hu2
  have hgi : Integrable (fun x ↦ ∫ y, u y * conj (u (-x + y)) ∂μ) μ :=
    hgc.integrable_of_hasCompactSupport (hasCompactSupport_integral_mul_conj huc)
  have hg0 : ∫ y, u y * conj (u (-0 + y)) ∂μ = ((∫ y, ‖u y‖ ^ 2 ∂μ : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine integral_congr_ae (.of_forall fun y ↦ ?_)
    simp only [neg_zero, zero_add, Complex.ofReal_pow, Complex.mul_conj']
  have hmass : bochnerMeasure (fun x ↦ ∫ y, u y * conj (u (-x + y)) ∂μ) Set.univ =
      ENNReal.ofReal (∫ y, ‖u y‖ ^ 2 ∂μ) := by
    have h := integral_toAddChar_bochnerMeasure hgp hgc 0
    rw [hg0] at h
    have h' : (bochnerMeasure fun x ↦ ∫ y, u y * conj (u (-x + y)) ∂μ).real Set.univ =
        ∫ y, ‖u y‖ ^ 2 ∂μ := by
      apply Complex.ofReal_injective
      rw [← h]
      simp
    rw [← h', measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
  have h1 : ∫⁻ χ, ‖fourierIntegral μ u χ‖ₑ ^ 2 ∂μ.dualAddHaar =
      ENNReal.ofReal (∫ y, ‖u y‖ ^ 2 ∂μ) := by
    rw [← hmass, ← withDensity_dualAddHaar_enorm_fourierIntegral hgc hgi hgp,
      withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    refine lintegral_congr fun χ ↦ ?_
    rw [fourierIntegral_integral_mul_conj μ hu huc, enorm_mul, sq]
    simp only [enorm_eq_nnnorm, RCLike.nnnorm_conj]
  have h2 : ∫⁻ y, ‖u y‖ₑ ^ 2 ∂μ = ENNReal.ofReal (∫ y, ‖u y‖ ^ 2 ∂μ) := by
    rw [ofReal_integral_eq_lintegral_ofReal
      ((memLp_two_iff_integrable_sq_norm hu.aestronglyMeasurable).1 hu2)
      (.of_forall fun y ↦ sq_nonneg _)]
    refine lintegral_congr fun y ↦ ?_
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  have hsq : eLpNorm (fourierIntegral μ u) 2 μ.dualAddHaar ^ 2 = eLpNorm u 2 μ ^ 2 := by
    rw [sq_eLpNorm_two (continuous_fourierIntegral
      (hu.integrable_of_hasCompactSupport huc)).aestronglyMeasurable,
      sq_eLpNorm_two hu.aestronglyMeasurable, h1, h2]
  exact le_antisymm ((ENNReal.pow_le_pow_left_iff two_ne_zero).1 hsq.le)
    ((ENNReal.pow_le_pow_left_iff two_ne_zero).1 hsq.ge)

/-- The inverse Fourier transform is a contraction for the `L²` norms. -/
private theorem eLpNorm_two_fourierIntegralInv_neg_le {F : AddPontryaginDual G → ℂ}
    (hF : Integrable F μ.dualAddHaar) :
    eLpNorm (fun x ↦ fourierIntegralInv μ.dualAddHaar F (-x)) 2 μ ≤
      eLpNorm F 2 μ.dualAddHaar := by
  -- By the multiplication formula and the case of continuous functions with compact support,
  -- `u ↦ ∫ x, u x * fourierIntegralInv μ.dualAddHaar F (-x) ∂μ` is bounded for the `L²` norm.
  refine eLpNorm_two_le_of_forall_enorm_integral_mul_le
    (h := fun x ↦ fourierIntegralInv μ.dualAddHaar F (-x))
    ((continuous_fourierIntegralInv hF).comp continuous_neg) (M := ∫ χ, ‖F χ‖ ∂μ.dualAddHaar)
    (fun x ↦ ?_) fun u hu huc ↦ ?_
  · exact (norm_integral_le_integral_norm _).trans_eq (by simp only [Circle.norm_smul])
  · have hui : Integrable u μ := hu.integrable_of_hasCompactSupport huc
    rw [← integral_fourierIntegral_mul hui hF, mul_comm,
      ← eLpNorm_two_fourierIntegral_of_hasCompactSupport μ hu huc]
    exact enorm_integral_mul_le (continuous_fourierIntegral hui).aestronglyMeasurable hF.1

private theorem memLp_two_fourierIntegralInv {F : AddPontryaginDual G → ℂ}
    (hF : Integrable F μ.dualAddHaar) (hF2 : MemLp F 2 μ.dualAddHaar) :
    MemLp (fourierIntegralInv μ.dualAddHaar F) 2 μ := by
  have h : MemLp (fun x ↦ fourierIntegralInv μ.dualAddHaar F (-x)) 2 μ :=
    (eLpNorm_two_fourierIntegralInv_neg_le μ hF).trans_lt hF2.eLpNorm_lt_top
  simpa [Function.comp_def] using h.comp_measurePreserving (measurePreserving_neg μ)

/-- The Fourier transform is a contraction for the `L²` norms. -/
private theorem eLpNorm_two_fourierIntegral_le {f : G → ℂ} (hf : Integrable f μ) :
    eLpNorm (fourierIntegral μ f) 2 μ.dualAddHaar ≤ eLpNorm f 2 μ := by
  -- By the multiplication formula and `eLpNorm_two_fourierIntegralInv_neg_le`,
  -- `Ψ ↦ ∫ χ, Ψ χ * fourierIntegral μ f χ ∂μ.dualAddHaar` is bounded for the `L²` norm.
  refine eLpNorm_two_le_of_forall_enorm_integral_mul_le (continuous_fourierIntegral hf)
    (M := ∫ x, ‖f x‖ ∂μ) (norm_fourierIntegral_le_integral_norm μ f) fun Ψ hΨ hΨc ↦ ?_
  have hΨi : Integrable Ψ μ.dualAddHaar := hΨ.integrable_of_hasCompactSupport hΨc
  simp_rw [mul_comm (Ψ _)]
  rw [integral_fourierIntegral_mul hf hΨi]
  exact (enorm_integral_mul_le hf.1
    ((continuous_fourierIntegralInv hΨi).comp continuous_neg).aestronglyMeasurable).trans
    (mul_le_mul_right (eLpNorm_two_fourierIntegralInv_neg_le μ hΨi) _)

variable {f : G → ℂ}

/-- The Fourier transform of a function in `L¹ ∩ L²` is in `L²`. -/
theorem memLp_two_fourierIntegral (hf : Integrable f μ) (hf2 : MemLp f 2 μ) :
    MemLp (fourierIntegral μ f) 2 μ.dualAddHaar :=
  (eLpNorm_two_fourierIntegral_le μ hf).trans_lt hf2.eLpNorm_lt_top

/-- The Fourier transform preserves the `L²` norm of functions in `L¹ ∩ L²`. -/
theorem eLpNorm_two_fourierIntegral (hf : Integrable f μ) (hf2 : MemLp f 2 μ) :
    eLpNorm (fourierIntegral μ f) 2 μ.dualAddHaar = eLpNorm f 2 μ := by
  -- This holds for continuous functions with compact support: if
  -- `g x = ∫ y, u y * conj (u (-x + y)) ∂μ`, then `g` is continuous, integrable and positive
  -- definite, and we apply the inversion theorem to `g` at `0`. The general case follows by
  -- density, since the Fourier transform is a contraction for the `L²` norms.
  refine le_antisymm (eLpNorm_two_fourierIntegral_le μ hf) ?_
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ ↦ ?_
  obtain ⟨u, huc, hfu, hu, hu2⟩ := hf2.exists_hasCompactSupport_eLpNorm_sub_le'
    (by norm_num : (2 : ℝ≥0∞) ≠ ∞) (ε := ((ε / 2 : ℝ≥0) : ℝ≥0∞)) (by positivity)
  have hui : Integrable u μ := hu.integrable_of_hasCompactSupport huc
  have h1 : fourierIntegral μ u = fourierIntegral μ f + fourierIntegral μ (u - f) := by
    rw [← fourierIntegral_add hf (hui.sub hf), add_sub_cancel]
  have h2 : eLpNorm (fourierIntegral μ (u - f)) 2 μ.dualAddHaar ≤ ((ε / 2 : ℝ≥0) : ℝ≥0∞) :=
    (eLpNorm_two_fourierIntegral_le μ (hui.sub hf)).trans (eLpNorm_sub_comm u f 2 μ ▸ hfu)
  calc eLpNorm f 2 μ
    _ = eLpNorm (u + (f - u)) 2 μ := by rw [add_sub_cancel]
    _ ≤ eLpNorm u 2 μ + eLpNorm (f - u) 2 μ := eLpNorm_add_le one_le_two
    _ = eLpNorm (fourierIntegral μ f + fourierIntegral μ (u - f)) 2 μ.dualAddHaar +
        eLpNorm (f - u) 2 μ := by
      rw [← h1, eLpNorm_two_fourierIntegral_of_hasCompactSupport μ hu huc]
    _ ≤ eLpNorm (fourierIntegral μ f) 2 μ.dualAddHaar + ((ε / 2 : ℝ≥0) : ℝ≥0∞) +
        ((ε / 2 : ℝ≥0) : ℝ≥0∞) :=
      add_le_add ((eLpNorm_add_le one_le_two).trans (add_le_add le_rfl h2)) hfu
    _ = eLpNorm (fourierIntegral μ f) 2 μ.dualAddHaar + ε := by
      rw [add_assoc, ← ENNReal.coe_add, add_halves]

end L1L2

section L2

/-- The Fourier transform on `L¹ ∩ L²`, with values in `L²` of the Pontryagin dual. Use
`AddPontryaginDual.fourierL2` instead. -/
noncomputable def fourierL2Fun (f : Lp.integrableSubmodule μ) : Lp ℂ 2 μ.dualAddHaar :=
  (memLp_two_fourierIntegral μ f.2 (Lp.memLp f.1)).toLp (fourierIntegral μ f.1)

theorem fourierL2Fun_add (f g : Lp.integrableSubmodule μ) :
    fourierL2Fun μ (f + g) = fourierL2Fun μ f + fourierL2Fun μ g := by
  have h : fourierIntegral μ ((f + g : Lp.integrableSubmodule μ) : Lp ℂ 2 μ) =
      fourierIntegral μ f.1 + fourierIntegral μ g.1 := by
    rw [Submodule.coe_add, fourierIntegral_congr_ae (Lp.coeFn_add _ _),
      fourierIntegral_add f.2 g.2]
  unfold fourierL2Fun
  exact (MemLp.toLp_congr _ _ (.of_eq h)).trans (MemLp.toLp_add _ _)

theorem fourierL2Fun_smul (c : ℂ) (f : Lp.integrableSubmodule μ) :
    fourierL2Fun μ (c • f) = c • fourierL2Fun μ f := by
  have h : fourierIntegral μ ((c • f : Lp.integrableSubmodule μ) : Lp ℂ 2 μ) =
      c • fourierIntegral μ f.1 := by
    rw [Submodule.coe_smul, fourierIntegral_congr_ae (Lp.coeFn_smul _ _),
      fourierIntegral_const_smul]
  unfold fourierL2Fun
  exact (MemLp.toLp_congr _ _ (.of_eq h)).trans (MemLp.toLp_const_smul _ _)

theorem norm_fourierL2Fun (f : Lp.integrableSubmodule μ) : ‖fourierL2Fun μ f‖ = ‖f‖ := by
  -- This is `eLpNorm_two_fourierIntegral`.
  rw [fourierL2Fun, Lp.norm_toLp, eLpNorm_two_fourierIntegral μ f.2 (Lp.memLp f.1),
    ← Submodule.norm_coe, Lp.norm_def]

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

omit [MeasurableSpace (AddPontryaginDual G)] [BorelSpace (AddPontryaginDual G)] in
/-- `L¹ ∩ L²` is dense in `L²`. -/
theorem dense_integrableSubmodule : Dense (Lp.integrableSubmodule μ : Set (Lp ℂ 2 μ)) := by
  -- It contains the continuous functions with compact support.
  refine (Lp.dense_hasCompactSupport_continuous (E := ℂ) (μ := μ) (p := 2) (by norm_num)).mono ?_
  rintro f ⟨g, hfg, hgc, hg⟩
  exact (hg.integrable_of_hasCompactSupport hgc).congr hfg.symm

theorem fourierL2CLM_apply (f : Lp.integrableSubmodule μ) :
    fourierL2CLM μ f = fourierL2Fun μ f :=
  -- `LinearMap.extendOfNorm_eq`, `dense_integrableSubmodule` and `norm_fourierL2Fun`.
  LinearMap.extendOfNorm_eq (dense_integrableSubmodule μ).denseRange_val
    ⟨1, fun g ↦ by rw [one_mul]; exact (norm_fourierL2Fun μ g).le⟩ f

variable {μ} in
theorem fourierL2CLM_toLp {f : G → ℂ} (hf : Integrable f μ) (hf2 : MemLp f 2 μ) :
    fourierL2CLM μ (hf2.toLp f) =
      (memLp_two_fourierIntegral μ hf hf2).toLp (fourierIntegral μ f) := by
  have hmem : Integrable (hf2.toLp f) μ := hf.congr hf2.coeFn_toLp.symm
  rw [show hf2.toLp f = ((⟨hf2.toLp f, hmem⟩ : Lp.integrableSubmodule μ) : Lp ℂ 2 μ) from rfl,
    fourierL2CLM_apply]
  exact MemLp.toLp_congr _ _ (.of_eq (fourierIntegral_congr_ae hf2.coeFn_toLp))

theorem norm_fourierL2CLM (f : Lp ℂ 2 μ) : ‖fourierL2CLM μ f‖ = ‖f‖ :=
  -- By density, from `fourierL2CLM_apply` and `norm_fourierL2Fun`.
  (dense_integrableSubmodule μ).induction (P := fun f ↦ ‖fourierL2CLM μ f‖ = ‖f‖)
    (fun g hg ↦ (congrArg norm (fourierL2CLM_apply μ ⟨g, hg⟩)).trans
      (norm_fourierL2Fun μ ⟨g, hg⟩))
    (isClosed_eq (fourierL2CLM μ).continuous.norm continuous_norm) f

private theorem inner_toLp_left {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℂ}
    (hf : MemLp f 2 μ) (g : Lp ℂ 2 μ) :
    inner ℂ (hf.toLp f) g = ∫ x, conj (f x) * g x ∂μ := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp] with x hx
  rw [hx, RCLike.inner_apply, mul_comm]

private theorem inner_toLp {α : Type*} [MeasurableSpace α] {μ : Measure α} {f g : α → ℂ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    inner ℂ (hf.toLp f) (hg.toLp g) = ∫ x, conj (f x) * g x ∂μ := by
  rw [inner_toLp_left]
  refine integral_congr_ae ?_
  filter_upwards [hg.coeFn_toLp] with x hx
  rw [hx]

private theorem eq_zero_of_forall_inner_eq_zero {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] {s : Set E} (hs : Dense s) {a : E}
    (h : ∀ w ∈ s, inner ℂ w a = 0) : a = 0 :=
  inner_self_eq_zero.1 (hs.induction (P := fun w ↦ inner ℂ w a = 0) h
    (isClosed_eq (continuous_id.inner continuous_const) continuous_const) a)

theorem fourierL2CLM_surjective : Function.Surjective (fourierL2CLM μ) := by
  -- The range is closed, since `fourierL2CLM μ` is an isometry. Let `Ψ` be orthogonal to the
  -- range. The range is stable under multiplication by `χ ↦ χ x` for all `x : G` (by
  -- `fourierIntegral_comp_add_left`), hence for all `u` in `L¹ ∩ L²` the integrable function
  -- `F = conj (fourierIntegral μ u) * Ψ` satisfies `fourierIntegralInv μ.dualAddHaar F = 0`.
  -- By `ae_eq_zero_of_fourierIntegralInv_eq_zero`, `F = 0` almost everywhere. Hence `Ψ` is
  -- orthogonal to the continuous functions with compact support, by
  -- `exists_fourierIntegral_ne_zero_of_isCompact`, and `Ψ = 0`.
  have hiso : Isometry (fourierL2CLM μ) := Isometry.of_dist_eq fun f g ↦ by
    rw [dist_eq_norm, dist_eq_norm, ← map_sub, norm_fourierL2CLM]
  have hKc : IsClosed (LinearMap.range (fourierL2CLM μ).toLinearMap :
      Set (Lp ℂ 2 μ.dualAddHaar)) := by
    rw [LinearMap.coe_range]
    exact hiso.isClosedEmbedding.isClosed_range
  have : CompleteSpace (LinearMap.range (fourierL2CLM μ).toLinearMap) := hKc.completeSpace_coe
  suffices hK : (LinearMap.range (fourierL2CLM μ).toLinearMap)ᗮ = ⊥ from
    LinearMap.range_eq_top.1 (Submodule.orthogonal_eq_bot_iff.1 hK)
  refine (Submodule.eq_bot_iff _).2 fun Ψ hΨ ↦ ?_
  have key {u : G → ℂ} (hu : Integrable u μ) (hu2 : MemLp u 2 μ) :
      (fun χ ↦ conj (fourierIntegral μ u χ) * Ψ χ) =ᵐ[μ.dualAddHaar] 0 := by
    have hF : Integrable (fun χ ↦ conj (fourierIntegral μ u χ) * Ψ χ) μ.dualAddHaar :=
      (memLp_two_fourierIntegral μ hu hu2).star.integrable_mul (Lp.memLp Ψ)
    refine ae_eq_zero_of_fourierIntegralInv_eq_zero hF (funext fun x ↦ ?_)
    have hv : Integrable (fun y ↦ u (-x + y)) μ := hu.comp_add_left (-x)
    have hv2 : MemLp (fun y ↦ u (-x + y)) 2 μ :=
      hu2.comp_measurePreserving (measurePreserving_add_left μ (-x))
    have h0 : inner ℂ (fourierL2CLM μ (hv2.toLp _)) Ψ = 0 :=
      (Submodule.mem_orthogonal _ Ψ).1 hΨ _
        (LinearMap.mem_range_self (fourierL2CLM μ).toLinearMap (hv2.toLp _))
    rw [fourierL2CLM_toLp hv hv2, inner_toLp_left] at h0
    rw [Pi.zero_apply, fourierIntegralInv_apply, ← h0]
    refine integral_congr_ae (.of_forall fun χ ↦ ?_)
    simp only [fourierIntegral_comp_add_left, Circle.smul_def, smul_eq_mul, map_mul,
      AddChar.map_neg_eq_inv, ← Circle.coe_inv_eq_conj, inv_inv]
    ring
  refine eq_zero_of_forall_inner_eq_zero (Lp.dense_hasCompactSupport_continuous (E := ℂ)
    (μ := μ.dualAddHaar) (p := 2) (by norm_num)) ?_
  rintro Θ ⟨θ, hΘθ, hθc, hθ⟩
  obtain ⟨g, hg, hgi, hgp, hg0⟩ := exists_fourierIntegral_ne_zero_of_isCompact μ hθc.isCompact
  have hg2 : MemLp g 2 μ := (memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).2
    ((hgi.norm.const_mul ‖g 0‖).mono' (hg.norm.pow 2).aestronglyMeasurable
      (.of_forall fun x ↦ by
        rw [Real.norm_of_nonneg (sq_nonneg _), sq]
        exact mul_le_mul_of_nonneg_right (hgp.norm_apply_le x) (norm_nonneg _)))
  rw [L2.inner_def]
  refine integral_eq_zero_of_ae ?_
  filter_upwards [hΘθ, key hgi hg2] with χ h1 h2
  rw [RCLike.inner_apply, h1]
  by_cases h0 : fourierIntegral μ g χ = 0
  · rw [image_eq_zero_of_notMem_tsupport fun h ↦ hg0 χ h h0]
    simp
  · have : Ψ χ = 0 := by simpa [h0] using h2
    rw [this]
    simp

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
    fourierL2 μ (hf2.toLp f) = (memLp_two_fourierIntegral μ hf hf2).toLp (fourierIntegral μ f) :=
  fourierL2CLM_toLp hf hf2

omit [IsTopologicalAddGroup G] [LocallyCompactSpace G] [BorelSpace G]
  [MeasurableSpace (AddPontryaginDual G)] [BorelSpace (AddPontryaginDual G)] [μ.IsAddHaarMeasure]
  [μ.Regular] in
private theorem fourierIntegral_conj_apply_neg (f : G → ℂ) (χ : AddPontryaginDual G) :
    fourierIntegral μ (fun x ↦ conj (f x)) (-χ) = conj (fourierIntegral μ f χ) := by
  rw [fourierIntegral, fourierIntegral, ← integral_conj]
  refine integral_congr_ae (.of_forall fun x ↦ ?_)
  simp [Circle.smul_def, AddChar.map_neg_eq_inv, ← Circle.coe_inv_eq_conj]

variable {μ} in
/-- On `L¹ ∩ L²`, the inverse of the Fourier transform `fourierL2 μ` is given by
`fourierIntegralInv μ.dualAddHaar`. -/
theorem coeFn_fourierL2_symm {F : AddPontryaginDual G → ℂ} (hF : Integrable F μ.dualAddHaar)
    (hF2 : MemLp F 2 μ.dualAddHaar) :
    (fourierL2 μ).symm (hF2.toLp F) =ᵐ[μ] fourierIntegralInv μ.dualAddHaar F := by
  -- The inverse of a unitary operator is its adjoint. For `u` continuous with compact support,
  -- exchanging the two integrals gives
  -- `⟪fourierL2 μ u, F⟫ = ∫ x, conj (u x) * fourierIntegralInv μ.dualAddHaar F x ∂μ`.
  have hh2 : MemLp (fourierIntegralInv μ.dualAddHaar F) 2 μ :=
    memLp_two_fourierIntegralInv μ hF hF2
  suffices h : (fourierL2 μ).symm (hF2.toLp F) = hh2.toLp _ from h ▸ hh2.coeFn_toLp
  rw [← sub_eq_zero]
  refine eq_zero_of_forall_inner_eq_zero (Lp.dense_hasCompactSupport_continuous (E := ℂ)
    (μ := μ) (p := 2) (by norm_num)) ?_
  rintro w ⟨u, hwu, huc, hu⟩
  have hui : Integrable u μ := hu.integrable_of_hasCompactSupport huc
  have hu2 : MemLp u 2 μ := hu.memLp_of_hasCompactSupport huc
  obtain rfl : w = hu2.toLp u := Lp.ext (hwu.trans hu2.coeFn_toLp.symm)
  rw [inner_sub_right, sub_eq_zero, ← LinearIsometryEquiv.inner_map_eq_flip,
    fourierL2_toLp hui hu2, inner_toLp, inner_toLp,
    integral_mul_fourierIntegralInv (f := fun x ↦ conj (u x))
      ((Complex.continuous_conj.comp hu).integrable_of_hasCompactSupport
        (huc.comp_left (map_zero _))) hF]
  simp_rw [fourierIntegral_conj_apply_neg]

end L2

section Convolution

variable {μ} {Φ Ψ : AddPontryaginDual G → ℂ}

theorem integrable_fourierIntegralInv_mul (hΦ : Continuous Φ) (hΦ' : HasCompactSupport Φ)
    (hΨ : Continuous Ψ) (hΨ' : HasCompactSupport Ψ) :
    Integrable (fourierIntegralInv μ.dualAddHaar Φ * fourierIntegralInv μ.dualAddHaar Ψ) μ :=
  -- Both factors are in `L²`.
  (memLp_two_fourierIntegralInv μ (hΦ.integrable_of_hasCompactSupport hΦ')
    (hΦ.memLp_of_hasCompactSupport hΦ')).integrable_mul
    (memLp_two_fourierIntegralInv μ (hΨ.integrable_of_hasCompactSupport hΨ')
      (hΨ.memLp_of_hasCompactSupport hΨ'))

/-- The Fourier transform turns the pointwise product of the inverse Fourier transforms of two
continuous functions with compact support into their convolution. -/
theorem fourierIntegral_fourierIntegralInv_mul (hΦ : Continuous Φ) (hΦ' : HasCompactSupport Φ)
    (hΨ : Continuous Ψ) (hΨ' : HasCompactSupport Ψ) :
    fourierIntegral μ (fourierIntegralInv μ.dualAddHaar Φ * fourierIntegralInv μ.dualAddHaar Ψ) =
      Φ ⋆[.mul ℂ ℂ, μ.dualAddHaar] Ψ := by
  -- Write `f = fourierIntegralInv μ.dualAddHaar Φ` and `g = fourierIntegralInv μ.dualAddHaar Ψ`.
  -- Then `fourierIntegral μ (f * g) χ = ⟪conj g * χ, f⟫` is the inner product in `L²(G)`. Apply
  -- `fourierL2 μ`, which preserves inner products and maps `f` to `Φ` and `conj g * χ` to
  -- `ξ ↦ conj (Ψ (χ - ξ))` by `coeFn_fourierL2_symm`.
  ext χ
  have hΦi : Integrable Φ μ.dualAddHaar := hΦ.integrable_of_hasCompactSupport hΦ'
  have hΦ2 : MemLp Φ 2 μ.dualAddHaar := hΦ.memLp_of_hasCompactSupport hΦ'
  have hΨχ : Continuous fun ξ ↦ conj (Ψ (χ - ξ)) :=
    Complex.continuous_conj.comp (hΨ.comp (continuous_const.sub continuous_id))
  have hΨχ' : HasCompactSupport fun ξ ↦ conj (Ψ (χ - ξ)) :=
    (hΨ'.comp_homeomorph (Homeomorph.subLeft χ)).comp_left (g := conj) (map_zero _)
  have hΨχi : Integrable (fun ξ ↦ conj (Ψ (χ - ξ))) μ.dualAddHaar :=
    hΨχ.integrable_of_hasCompactSupport hΨχ'
  have hΨχ2 : MemLp (fun ξ ↦ conj (Ψ (χ - ξ))) 2 μ.dualAddHaar :=
    hΨχ.memLp_of_hasCompactSupport hΨχ'
  have hinv (x : G) : fourierIntegralInv μ.dualAddHaar (fun ξ ↦ conj (Ψ (χ - ξ))) x =
      conj (fourierIntegralInv μ.dualAddHaar Ψ x) * χ.toAddChar x :=
    calc ∫ ξ, ξ.toAddChar x • conj (Ψ (χ - ξ)) ∂μ.dualAddHaar
      _ = ∫ ξ, conj ((χ - ξ).toAddChar x • Ψ (χ - ξ)) * (χ.toAddChar x : ℂ) ∂μ.dualAddHaar := by
        refine integral_congr_ae (.of_forall fun ξ ↦ ?_)
        simp only [toAddChar_sub_apply, Circle.smul_def, smul_eq_mul, map_mul,
          ← Circle.coe_inv_eq_conj, inv_div]
        rw [mul_right_comm, ← Circle.coe_mul, div_mul_cancel]
      _ = ∫ ξ, conj (ξ.toAddChar x • Ψ ξ) * (χ.toAddChar x : ℂ) ∂μ.dualAddHaar :=
        integral_sub_left_eq_self
          (fun ξ ↦ conj (ξ.toAddChar x • Ψ ξ) * (χ.toAddChar x : ℂ)) μ.dualAddHaar χ
      _ = conj (∫ ξ, ξ.toAddChar x • Ψ ξ ∂μ.dualAddHaar) * χ.toAddChar x := by
        rw [integral_mul_const, integral_conj]
  have hf2 : MemLp (fourierIntegralInv μ.dualAddHaar Φ) 2 μ :=
    memLp_two_fourierIntegralInv μ hΦi hΦ2
  have ha2 : MemLp (fourierIntegralInv μ.dualAddHaar fun ξ ↦ conj (Ψ (χ - ξ))) 2 μ :=
    memLp_two_fourierIntegralInv μ hΨχi hΨχ2
  have e1 : (fourierL2 μ).symm (hΦ2.toLp Φ) = hf2.toLp _ :=
    Lp.ext ((coeFn_fourierL2_symm hΦi hΦ2).trans hf2.coeFn_toLp.symm)
  have e2 : (fourierL2 μ).symm (hΨχ2.toLp _) = ha2.toLp _ :=
    Lp.ext ((coeFn_fourierL2_symm hΨχi hΨχ2).trans ha2.coeFn_toLp.symm)
  calc fourierIntegral μ
        (fourierIntegralInv μ.dualAddHaar Φ * fourierIntegralInv μ.dualAddHaar Ψ) χ
    _ = ∫ x, conj (fourierIntegralInv μ.dualAddHaar (fun ξ ↦ conj (Ψ (χ - ξ))) x) *
          fourierIntegralInv μ.dualAddHaar Φ x ∂μ := by
      refine integral_congr_ae (.of_forall fun x ↦ ?_)
      simp only [hinv, Pi.mul_apply, Circle.smul_def, smul_eq_mul, map_mul, Complex.conj_conj,
        AddChar.map_neg_eq_inv, ← Circle.coe_inv_eq_conj]
      ring
    _ = inner ℂ (ha2.toLp _) (hf2.toLp _) := (inner_toLp ha2 hf2).symm
    _ = inner ℂ (hΨχ2.toLp _) (hΦ2.toLp Φ) := by
      rw [← e1, ← e2, LinearIsometryEquiv.inner_map_map]
    _ = ∫ ξ, conj (conj (Ψ (χ - ξ))) * Φ ξ ∂μ.dualAddHaar := inner_toLp hΨχ2 hΦ2
    _ = (Φ ⋆[.mul ℂ ℂ, μ.dualAddHaar] Ψ) χ := by
      rw [convolution_def]
      refine integral_congr_ae (.of_forall fun ξ ↦ ?_)
      simp only [Complex.conj_conj, ContinuousLinearMap.mul_apply', mul_comm]

variable (μ) in
/-- For every nonempty open subset `U` of the Pontryagin dual, there is an integrable function on
`G` whose Fourier transform is nonzero and vanishes outside `U`. -/
theorem exists_integrable_fourierIntegral_ne_zero {U : Set (AddPontryaginDual G)} (hU : IsOpen U)
    (hne : U.Nonempty) :
    ∃ f : G → ℂ, Integrable f μ ∧ fourierIntegral μ f ≠ 0 ∧
      ∀ χ ∉ U, fourierIntegral μ f χ = 0 := by
  -- Let `χ₀ ∈ U` and let `V` be a neighborhood of `0` with `χ₀ + V - V ⊆ U`. Let `φ ≥ 0` be a
  -- nonzero continuous function with compact support contained in `V`, and let
  -- `ψ ξ = φ (χ₀ - ξ)`. Then `φ ⋆ ψ` vanishes outside `χ₀ + V - V` and it is nonzero at `χ₀`.
  -- Conclude by `fourierIntegral_fourierIntegralInv_mul`.
  obtain ⟨χ₀, hχ₀⟩ := hne
  have hU₀ : (fun χ ↦ χ₀ + χ) ⁻¹' U ∈ 𝓝 (0 : AddPontryaginDual G) :=
    (hU.preimage (continuous_const.add continuous_id)).mem_nhds (by simpa using hχ₀)
  obtain ⟨V, hV, hVU⟩ := exists_nhds_half_neg hU₀
  obtain ⟨θ, hθ1, hθ0, hθc, -⟩ := exists_continuous_one_zero_of_isCompact
    (isCompact_singleton (x := (0 : AddPontryaginDual G))) (isOpen_interior (s := V)).isClosed_compl
    (Set.disjoint_singleton_left.2 fun h ↦ h (mem_interior_iff_mem_nhds.2 hV))
  have hφ : Continuous fun ξ ↦ (θ ξ : ℂ) := Complex.continuous_ofReal.comp θ.continuous
  have hφ' : HasCompactSupport fun ξ ↦ (θ ξ : ℂ) := hθc.comp_left Complex.ofReal_zero
  have hψ : Continuous fun ξ ↦ (θ (χ₀ - ξ) : ℂ) :=
    hφ.comp (continuous_const.sub continuous_id)
  have hψ' : HasCompactSupport fun ξ ↦ (θ (χ₀ - ξ) : ℂ) :=
    hφ'.comp_homeomorph (Homeomorph.subLeft χ₀)
  have hθV (ξ : AddPontryaginDual G) (h : (θ ξ : ℂ) ≠ 0) : ξ ∈ V := by
    by_contra hξ
    exact h (by simp [hθ0 fun h' ↦ hξ (interior_subset h')])
  have hconv := fourierIntegral_fourierIntegralInv_mul (μ := μ) hφ hφ' hψ hψ'
  refine ⟨_, integrable_fourierIntegralInv_mul hφ hφ' hψ hψ', fun h ↦ ?_, fun χ hχ ↦ ?_⟩
  · have hpos : 0 < ∫ ξ, θ ξ * θ ξ ∂μ.dualAddHaar :=
      Continuous.integral_pos_of_hasCompactSupport_nonneg_ne_zero (x := 0)
        (θ.continuous.mul θ.continuous) hθc.mul_left (fun ξ ↦ mul_self_nonneg _)
        (by simp [hθ1 (Set.mem_singleton 0)])
    have h1 := congr_fun (hconv.symm.trans h) χ₀
    rw [convolution_def, Pi.zero_apply] at h1
    have h2 : ∫ ξ, (ContinuousLinearMap.mul ℂ ℂ) (θ ξ : ℂ) (θ (χ₀ - (χ₀ - ξ)) : ℂ)
        ∂μ.dualAddHaar = ((∫ ξ, θ ξ * θ ξ ∂μ.dualAddHaar : ℝ) : ℂ) := by
      rw [← integral_complex_ofReal]
      refine integral_congr_ae (.of_forall fun ξ ↦ ?_)
      simp
    rw [h2] at h1
    exact hpos.ne' (by exact_mod_cast h1)
  · rw [hconv, convolution_def]
    refine integral_eq_zero_of_ae (.of_forall fun ξ ↦ ?_)
    by_contra h
    simp only [ContinuousLinearMap.mul_apply', Pi.zero_apply] at h
    obtain ⟨h1, h2⟩ := mul_ne_zero_iff.1 h
    have h3 : χ₀ + (ξ - (χ₀ - (χ - ξ))) ∈ U := hVU ξ (hθV ξ h1) _ (hθV _ h2)
    exact hχ (by rwa [show χ₀ + (ξ - (χ₀ - (χ - ξ))) = χ by abel] at h3)

end Convolution

end AddPontryaginDual
