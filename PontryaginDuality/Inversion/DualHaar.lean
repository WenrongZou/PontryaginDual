/-
Copyright (c) 2026 Wenrong Zou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wenrong Zou
-/
module

public import PontryaginDuality.Fourier.CStar

import PontryaginDuality.Mathlib.MeasureTheory.Function.ContinuousMapDense
import PontryaginDuality.Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.WithDensity

/-!
# The dual Haar measure

Let `G` be a locally compact abelian group with a regular Haar measure `μ`. In this file we define
the dual Haar measure `μ.dualAddHaar` on the Pontryagin dual of `G`: it is the regular Haar
measure for which the Fourier transform preserves the `L²` norm.

## Main definitions

* `MeasureTheory.Measure.dualAddHaar μ`: the Haar measure on `AddPontryaginDual G` dual to `μ`.

## Main statements

Let `f` and `g` be in `L¹ ∩ L²`.

* `AddPontryaginDual.integral_mul_sq_fourierIntegral_spectralMeasure_comm`: the measures
  `‖fourierIntegral μ f‖ ^ 2 • spectralMeasure μ g` and
  `‖fourierIntegral μ g‖ ^ 2 • spectralMeasure μ f` are equal.
* `AddPontryaginDual.withDensity_dualAddHaar_sq_enorm_fourierIntegral`: the spectral measure of
  `f` has density `‖fourierIntegral μ f‖ ^ 2` with respect to `μ.dualAddHaar`.
* `AddPontryaginDual.eLpNorm_two_fourierIntegral`: the Fourier transform preserves the `L²` norm
  of `f`.

## Implementation notes

We follow [bourbaki1967], Chap. II, §1, n°3. For `f ∈ A(G)`, Bourbaki restricts the bounded
measure `μ_f` to the open set `Ω_f` where the Fourier transform `Ff` does not vanish. The measures
`(Ff)⁻¹ • μ_f` on `Ω_f` are compatible and define a measure `ν` on the Pontryagin dual, which is
invariant under translations; it is positive by the uniqueness of the Haar measure. A measure in
the sense of Mathlib is positive from the start, hence we only use the functions `f = g * g⋆`,
for which `μ_f = spectralMeasure μ g` is positive and `Ff = ‖Fg‖ ^ 2`.

As on the `main` branch, the measure is defined by the Riesz–Markov–Kakutani theorem
(`RealRMK.rieszMeasure`), applied to the positive linear functional
`ψ ↦ ∫ χ, ψ χ / ‖fourierIntegral μ g χ‖ ^ 2 ∂spectralMeasure μ g`, where `g` is any continuous
function with compact support whose Fourier transform does not vanish on the support of `ψ`.

## References

* [N. Bourbaki, *Théories spectrales*, Chap. II, §1, n°3][bourbaki1967]
-/

@[expose] public section

open MeasureTheory Measure Filter Topology
open scoped ComplexConjugate ENNReal NNReal ZeroAtInfty CompactlySupported

namespace AddPontryaginDual

variable {G : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [MeasurableSpace (AddPontryaginDual G)] [BorelSpace (AddPontryaginDual G)]
  (μ : Measure G) [μ.IsAddHaarMeasure] [μ.Regular]

omit [MeasurableSpace (AddPontryaginDual G)] [BorelSpace (AddPontryaginDual G)] in
/-- For every compact subset `K` of the Pontryagin dual, there is a continuous function with
compact support whose Fourier transform does not vanish on `K`. -/
theorem exists_hasCompactSupport_fourierIntegral_ne_zero {K : Set (AddPontryaginDual G)}
    (hK : IsCompact K) :
    ∃ g : G → ℂ, Continuous g ∧ HasCompactSupport g ∧ ∀ χ ∈ K, fourierIntegral μ g χ ≠ 0 := by
  -- TS II §1 n°3, Lemme 1 (ii): there is `φ ∈ L¹(G)` such that `‖fourierL1 μ φ χ - 1‖ < 1 / 2` for
  -- all `χ ∈ K`. Approximate `φ` in `L¹(G)` by a continuous function with compact support.
  obtain ⟨φ, -, hφ, -⟩ := exists_fourierL1_sub_one_lt_convL2_sub_lt μ hK 0 (half_pos one_pos)
  obtain ⟨g, hgc, hφg, hg, hg1⟩ := MemLp.exists_hasCompactSupport_eLpNorm_sub_le'
    ENNReal.one_ne_top (Lp.memLp φ) (ε := ENNReal.ofReal (1 / 2)) (by simp)
  have hgi : Integrable g μ := memLp_one_iff_integrable.1 hg1
  have hi : Integrable (⇑φ - g) μ := (L1.integrable_coeFn φ).sub hgi
  refine ⟨g, hg, hgc, fun χ hχ h0 ↦ ?_⟩
  have h1 : ‖fourierL1 μ φ χ - fourierIntegral μ g χ‖ ≤ 1 / 2 := by
    have e : fourierL1 μ φ χ - fourierIntegral μ g χ = fourierIntegral μ (⇑φ - g) χ := by
      rw [fourierL1_apply, fourierIntegral_apply, fourierIntegral_apply, fourierIntegral_apply,
        ← integral_sub ((fourierIntegral_convergent_iff χ).2 (L1.integrable_coeFn φ))
          ((fourierIntegral_convergent_iff χ).2 hgi)]
      simp only [Pi.sub_apply, smul_sub]
    rw [e]
    refine (norm_fourierIntegral_le_integral_norm μ _ χ).trans ?_
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hφg
    rwa [eLpNorm_one_eq_lintegral_enorm hi.1, ← integral_norm_eq_lintegral_enorm hi.1,
      ENNReal.toReal_ofReal (by norm_num)] at h
  have h2 := hφ χ hχ
  rw [h0, sub_zero] at h1
  have := norm_sub_norm_le (1 : ℂ) (1 - fourierL1 μ φ χ)
  rw [sub_sub_cancel, norm_one, norm_sub_rev] at this
  linarith

/-- For `f` and `g` in `L¹ ∩ L²`, the measures `‖fourierIntegral μ f‖ ^ 2 • spectralMeasure μ g` and
`‖fourierIntegral μ g‖ ^ 2 • spectralMeasure μ f` are equal. -/
theorem integral_mul_sq_fourierIntegral_spectralMeasure_comm {f g : G → ℂ} (hf : Integrable f μ)
    (hf2 : MemLp f 2 μ) (hg : Integrable g μ) (hg2 : MemLp g 2 μ)
    (Φ : C₀(AddPontryaginDual G, ℂ)) :
    ∫ χ, Φ χ * ‖fourierIntegral μ f χ‖ ^ 2 ∂spectralMeasure μ (hg2.toLp g) =
      ∫ χ, Φ χ * ‖fourierIntegral μ g χ‖ ^ 2 ∂spectralMeasure μ (hf2.toLp f) := by
  -- TS II §1 n°3, (15): `Ff • μ_g = Fg • μ_f`. Both sides are the integral of `Φ` against the
  -- spectral measure of `f ⋆ g = g ⋆ f`.
  have e {h : G → ℂ} (hh : Integrable h μ) (χ : AddPontryaginDual G) :
      fourierL1 μ (hh.toL1 h) χ = fourierIntegral μ h χ :=
    congr_fun (fourierIntegral_congr_ae hh.coeFn_toL1) χ
  have h1 := integral_spectralMeasure_convL2 μ (hf.toL1 f) (hg2.toLp g) Φ
  have h2 := integral_spectralMeasure_convL2 μ (hg.toL1 g) (hf2.toLp f) Φ
  simp_rw [e] at h1 h2
  rw [← h1, ← h2, L1.convL2_toL1_toLp_comm hf hf2 hg hg2]

private theorem tsupport_div_subset {X : Type*} [TopologicalSpace X] (ψ d : X → ℝ) :
    tsupport (fun x ↦ ψ x / d x) ⊆ tsupport ψ := by
  simp_rw [div_eq_mul_inv]
  exact tsupport_mul_subset_left

private theorem hasCompactSupport_div {X : Type*} [TopologicalSpace X] {ψ : X → ℝ}
    (hψ : HasCompactSupport ψ) (d : X → ℝ) : HasCompactSupport fun x ↦ ψ x / d x :=
  hψ.mono fun x hx h0 ↦ hx (by simp [h0])

section

variable {μ} {f g : G → ℂ} {ψ : AddPontryaginDual G → ℝ}

omit [MeasurableSpace (AddPontryaginDual G)] [BorelSpace (AddPontryaginDual G)]
  [μ.IsAddHaarMeasure] in
private theorem continuous_div_sq_norm_fourierIntegral (hg : Integrable g μ) (hψ : Continuous ψ)
    (hgψ : ∀ χ ∈ tsupport ψ, fourierIntegral μ g χ ≠ 0) :
    Continuous fun χ ↦ ψ χ / ‖fourierIntegral μ g χ‖ ^ 2 :=
  continuous_of_tsupport fun χ hχ ↦
    hψ.continuousAt.div ((continuous_fourierIntegral hg).norm.pow 2).continuousAt
      (pow_ne_zero 2 (norm_ne_zero_iff.2 (hgψ χ (tsupport_div_subset _ _ hχ))))

omit [IsTopologicalAddGroup G] [LocallyCompactSpace G] [BorelSpace G]
  [MeasurableSpace (AddPontryaginDual G)] [BorelSpace (AddPontryaginDual G)] [μ.IsAddHaarMeasure]
  [μ.Regular] in
private theorem ofReal_div_sq_mul_sq (hgψ : ∀ χ ∈ tsupport ψ, fourierIntegral μ g χ ≠ 0)
    (χ : AddPontryaginDual G) :
    ((ψ χ / ‖fourierIntegral μ g χ‖ ^ 2 : ℝ) : ℂ) * ‖fourierIntegral μ g χ‖ ^ 2 = ψ χ := by
  by_cases h0 : fourierIntegral μ g χ = 0
  · have : ψ χ = 0 := image_eq_zero_of_notMem_tsupport fun h ↦ hgψ χ h h0
    simp [this]
  · have : (‖fourierIntegral μ g χ‖ : ℂ) ^ 2 ≠ 0 := pow_ne_zero 2 (by simpa using h0)
    rw [Complex.ofReal_div, Complex.ofReal_pow, div_mul_cancel₀ _ this]

/-- The measures `(Ff)⁻¹ • μ_f` and `(Fg)⁻¹ • μ_g` of Bourbaki coincide on `Ω_f ∩ Ω_g`. -/
private theorem integral_div_sq_spectralMeasure_eq (hf : Integrable f μ) (hf2 : MemLp f 2 μ)
    (hg : Integrable g μ) (hg2 : MemLp g 2 μ) (hψ : Continuous ψ) (hψc : HasCompactSupport ψ)
    (hfψ : ∀ χ ∈ tsupport ψ, fourierIntegral μ f χ ≠ 0)
    (hgψ : ∀ χ ∈ tsupport ψ, fourierIntegral μ g χ ≠ 0) :
    ∫ χ, ψ χ / ‖fourierIntegral μ f χ‖ ^ 2 ∂spectralMeasure μ (hf2.toLp f) =
      ∫ χ, ψ χ / ‖fourierIntegral μ g χ‖ ^ 2 ∂spectralMeasure μ (hg2.toLp g) := by
  -- Apply `integral_mul_sq_fourierIntegral_spectralMeasure_comm` to
  -- `Φ = ψ / (‖Ff‖ ^ 2 * ‖Fg‖ ^ 2)`.
  have hK₁ : ∀ χ ∈ tsupport (fun χ ↦ ψ χ / ‖fourierIntegral μ f χ‖ ^ 2),
      fourierIntegral μ g χ ≠ 0 := fun χ hχ ↦ hgψ χ (tsupport_div_subset _ _ hχ)
  have hK₂ : ∀ χ ∈ tsupport (fun χ ↦ ψ χ / ‖fourierIntegral μ g χ‖ ^ 2),
      fourierIntegral μ f χ ≠ 0 := fun χ hχ ↦ hfψ χ (tsupport_div_subset _ _ hχ)
  have hΨ : Continuous fun χ ↦
      ((ψ χ / ‖fourierIntegral μ f χ‖ ^ 2 / ‖fourierIntegral μ g χ‖ ^ 2 : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (continuous_div_sq_norm_fourierIntegral hg
      (continuous_div_sq_norm_fourierIntegral hf hψ hfψ) hK₁)
  have hΨc : HasCompactSupport fun χ ↦
      ((ψ χ / ‖fourierIntegral μ f χ‖ ^ 2 / ‖fourierIntegral μ g χ‖ ^ 2 : ℝ) : ℂ) :=
    (hasCompactSupport_div (hasCompactSupport_div hψc _) _).comp_left Complex.ofReal_zero
  refine Complex.ofReal_injective ?_
  rw [← integral_complex_ofReal, ← integral_complex_ofReal]
  calc ∫ χ, ((ψ χ / ‖fourierIntegral μ f χ‖ ^ 2 : ℝ) : ℂ) ∂spectralMeasure μ (hf2.toLp f)
    _ = ∫ χ, ((ψ χ / ‖fourierIntegral μ f χ‖ ^ 2 / ‖fourierIntegral μ g χ‖ ^ 2 : ℝ) : ℂ) *
          ‖fourierIntegral μ g χ‖ ^ 2 ∂spectralMeasure μ (hf2.toLp f) :=
      integral_congr_ae (.of_forall fun χ ↦ (ofReal_div_sq_mul_sq hK₁ χ).symm)
    _ = ∫ χ, ((ψ χ / ‖fourierIntegral μ f χ‖ ^ 2 / ‖fourierIntegral μ g χ‖ ^ 2 : ℝ) : ℂ) *
          ‖fourierIntegral μ f χ‖ ^ 2 ∂spectralMeasure μ (hg2.toLp g) :=
      integral_mul_sq_fourierIntegral_spectralMeasure_comm μ hg hg2 hf hf2
        ⟨⟨_, hΨ⟩, hΨc.is_zero_at_infty⟩
    _ = ∫ χ, ((ψ χ / ‖fourierIntegral μ g χ‖ ^ 2 : ℝ) : ℂ) ∂spectralMeasure μ (hg2.toLp g) :=
      integral_congr_ae (.of_forall fun χ ↦ by
        beta_reduce
        rw [div_right_comm]
        exact ofReal_div_sq_mul_sq hK₂ χ)

end

/-! ### The dual Haar measure -/

/-- A continuous function with compact support whose Fourier transform does not vanish on the
support of `ψ`. -/
private noncomputable def auxFun (ψ : C_c(AddPontryaginDual G, ℝ)) : G → ℂ :=
  (exists_hasCompactSupport_fourierIntegral_ne_zero μ ψ.hasCompactSupport.isCompact).choose

omit [MeasurableSpace (AddPontryaginDual G)] [BorelSpace (AddPontryaginDual G)] in
private theorem memLp_auxFun (ψ : C_c(AddPontryaginDual G, ℝ)) : MemLp (auxFun μ ψ) 2 μ :=
  have h := (exists_hasCompactSupport_fourierIntegral_ne_zero μ
    ψ.hasCompactSupport.isCompact).choose_spec
  h.1.memLp_of_hasCompactSupport h.2.1

omit [MeasurableSpace (AddPontryaginDual G)] [BorelSpace (AddPontryaginDual G)] in
private theorem integrable_auxFun (ψ : C_c(AddPontryaginDual G, ℝ)) :
    Integrable (auxFun μ ψ) μ :=
  have h := (exists_hasCompactSupport_fourierIntegral_ne_zero μ
    ψ.hasCompactSupport.isCompact).choose_spec
  h.1.integrable_of_hasCompactSupport h.2.1

omit [MeasurableSpace (AddPontryaginDual G)] [BorelSpace (AddPontryaginDual G)] in
private theorem fourierIntegral_auxFun_ne_zero (ψ : C_c(AddPontryaginDual G, ℝ)) :
    ∀ χ ∈ tsupport ψ, fourierIntegral μ (auxFun μ ψ) χ ≠ 0 :=
  (exists_hasCompactSupport_fourierIntegral_ne_zero μ
    ψ.hasCompactSupport.isCompact).choose_spec.2.2

/-- The integral of `ψ` against the measure `(Ff)⁻¹ • μ_f` of Bourbaki, where `f = g * g⋆` and
`g = auxFun μ ψ`. -/
private noncomputable def dualHaarFun (ψ : C_c(AddPontryaginDual G, ℝ)) : ℝ :=
  ∫ χ, ψ χ / ‖fourierIntegral μ (auxFun μ ψ) χ‖ ^ 2
    ∂spectralMeasure μ ((memLp_auxFun μ ψ).toLp _)

private theorem dualHaarFun_eq (ψ : C_c(AddPontryaginDual G, ℝ)) {g : G → ℂ}
    (hg : Integrable g μ) (hg2 : MemLp g 2 μ)
    (hgψ : ∀ χ ∈ tsupport ψ, fourierIntegral μ g χ ≠ 0) :
    dualHaarFun μ ψ =
      ∫ χ, ψ χ / ‖fourierIntegral μ g χ‖ ^ 2 ∂spectralMeasure μ (hg2.toLp g) :=
  integral_div_sq_spectralMeasure_eq (integrable_auxFun μ ψ) (memLp_auxFun μ ψ) hg hg2
    (map_continuous ψ) ψ.hasCompactSupport (fourierIntegral_auxFun_ne_zero μ ψ) hgψ

private theorem dualHaarFun_add (ψ₁ ψ₂ : C_c(AddPontryaginDual G, ℝ)) :
    dualHaarFun μ (ψ₁ + ψ₂) = dualHaarFun μ ψ₁ + dualHaarFun μ ψ₂ := by
  -- By `dualHaarFun_eq`, applied to a function `g` whose Fourier transform does not vanish on
  -- the union of the supports of `ψ₁` and `ψ₂`.
  obtain ⟨g, hg, hgc, hg0⟩ := exists_hasCompactSupport_fourierIntegral_ne_zero μ
    (ψ₁.hasCompactSupport.isCompact.union ψ₂.hasCompactSupport.isCompact)
  have hgi : Integrable g μ := hg.integrable_of_hasCompactSupport hgc
  have hg2 : MemLp g 2 μ := hg.memLp_of_hasCompactSupport hgc
  have h₁ : ∀ χ ∈ tsupport ψ₁, fourierIntegral μ g χ ≠ 0 := fun χ hχ ↦ hg0 χ (.inl hχ)
  have h₂ : ∀ χ ∈ tsupport ψ₂, fourierIntegral μ g χ ≠ 0 := fun χ hχ ↦ hg0 χ (.inr hχ)
  rw [dualHaarFun_eq μ _ hgi hg2 fun χ hχ ↦ hg0 χ (tsupport_add ψ₁ ψ₂ hχ),
    dualHaarFun_eq μ _ hgi hg2 h₁, dualHaarFun_eq μ _ hgi hg2 h₂,
    ← integral_add
      ((continuous_div_sq_norm_fourierIntegral hgi (map_continuous ψ₁)
        h₁).integrable_of_hasCompactSupport (hasCompactSupport_div ψ₁.hasCompactSupport _))
      ((continuous_div_sq_norm_fourierIntegral hgi (map_continuous ψ₂)
        h₂).integrable_of_hasCompactSupport (hasCompactSupport_div ψ₂.hasCompactSupport _))]
  simp only [CompactlySupportedContinuousMap.coe_add, Pi.add_apply, add_div]

private theorem dualHaarFun_smul (c : ℝ) (ψ : C_c(AddPontryaginDual G, ℝ)) :
    dualHaarFun μ (c • ψ) = c • dualHaarFun μ ψ := by
  -- By `dualHaarFun_eq`, applied to `g = auxFun μ ψ`.
  have hc : tsupport (c • ψ : C_c(AddPontryaginDual G, ℝ)) ⊆ tsupport ψ :=
    closure_mono fun χ hχ h0 ↦ hχ (by simp [h0])
  rw [dualHaarFun_eq μ _ (integrable_auxFun μ ψ) (memLp_auxFun μ ψ) fun χ hχ ↦
    fourierIntegral_auxFun_ne_zero μ ψ χ (hc hχ), smul_eq_mul, dualHaarFun, ← integral_const_mul]
  simp only [CompactlySupportedContinuousMap.coe_smul, Pi.smul_apply, smul_eq_mul, mul_div_assoc]

/-- The positive linear functional
`ψ ↦ ∫ χ, ψ χ / ‖fourierIntegral μ g χ‖ ^ 2 ∂spectralMeasure μ g`, where `g` is any function in
`L¹ ∩ L²` whose Fourier transform does not vanish on the support of `ψ` (see
`AddPontryaginDual.dualHaarFun_eq`). -/
private noncomputable def dualHaarFunctional : C_c(AddPontryaginDual G, ℝ) →ₚ[ℝ] ℝ :=
  PositiveLinearMap.mk₀
    { toFun := dualHaarFun μ
      map_add' := dualHaarFun_add μ
      map_smul' := dualHaarFun_smul μ }
    fun _ hψ ↦ integral_nonneg fun χ ↦ div_nonneg (hψ χ) (sq_nonneg _)

/-- The Haar measure on the Pontryagin dual of `G` which is dual to the Haar measure `μ` on `G`:
the regular Haar measure for which the Fourier transform preserves the `L²` norm (see
`AddPontryaginDual.eLpNorm_two_fourierIntegral`).

It is the measure associated by the Riesz–Markov–Kakutani theorem with the positive linear
functional `ψ ↦ ∫ χ, ψ χ / ‖fourierIntegral μ g χ‖ ^ 2 ∂spectralMeasure μ g`, where `g` is any
function in `L¹ ∩ L²` whose Fourier transform does not vanish on the support of `ψ`. -/
@[no_expose]
noncomputable def _root_.MeasureTheory.Measure.dualAddHaar : Measure (AddPontryaginDual G) :=
  RealRMK.rieszMeasure (dualHaarFunctional μ)

instance : (μ.dualAddHaar).Regular :=
  RealRMK.regular_rieszMeasure _

private theorem integral_dualAddHaar {ψ : AddPontryaginDual G → ℝ} (hψ : Continuous ψ)
    (hψc : HasCompactSupport ψ) {g : G → ℂ} (hg : Integrable g μ) (hg2 : MemLp g 2 μ)
    (hgψ : ∀ χ ∈ tsupport ψ, fourierIntegral μ g χ ≠ 0) :
    ∫ χ, ψ χ ∂μ.dualAddHaar =
      ∫ χ, ψ χ / ‖fourierIntegral μ g χ‖ ^ 2 ∂spectralMeasure μ (hg2.toLp g) :=
  (RealRMK.integral_rieszMeasure (dualHaarFunctional μ) ⟨⟨ψ, hψ⟩, hψc⟩).trans
    (dualHaarFun_eq μ ⟨⟨ψ, hψ⟩, hψc⟩ hg hg2 hgψ)

/-- The spectral measure of `f ∈ L¹ ∩ L²` has density `‖fourierIntegral μ f‖ ^ 2` with respect to
the dual Haar measure. -/
theorem withDensity_dualAddHaar_sq_enorm_fourierIntegral {f : G → ℂ} (hf : Integrable f μ)
    (hf2 : MemLp f 2 μ) :
    μ.dualAddHaar.withDensity (fun χ ↦ ‖fourierIntegral μ f χ‖ₑ ^ 2) =
      spectralMeasure μ (hf2.toLp f) := by
  -- TS II §1 n°3, (16): `μ_f = Ff • ν`. By `Measure.withDensity_eq_of_forall_integral_mul_eq`, it
  -- suffices to prove that `∫ χ, ψ χ * ‖Ff χ‖ ^ 2 ∂μ.dualAddHaar = ∫ χ, ψ χ ∂spectralMeasure μ f`
  -- for `ψ` continuous with compact support. This follows from `integral_dualAddHaar` and
  -- `integral_mul_sq_fourierIntegral_spectralMeasure_comm`.
  have hfc : Continuous (fourierIntegral μ f) := continuous_fourierIntegral hf
  simp_rw [enorm_eq_nnnorm, ← ENNReal.coe_pow]
  refine Measure.withDensity_eq_of_forall_integral_mul_eq
    (ρ := fun χ ↦ ‖fourierIntegral μ f χ‖₊ ^ 2) (hfc.nnnorm.pow 2)
    (C := (∫ x, ‖f x‖ ∂μ).toNNReal ^ 2) (fun χ ↦ ?_) fun ψ ↦ ?_
  · have h : ‖fourierIntegral μ f χ‖₊ ≤ (∫ x, ‖f x‖ ∂μ).toNNReal :=
      (Real.le_toNNReal_iff_coe_le (integral_nonneg fun _ ↦ norm_nonneg _)).2
        (norm_fourierIntegral_le_integral_norm μ f χ)
    exact pow_le_pow_left₀ zero_le h 2
  obtain ⟨g, hg, hgc, hg0⟩ :=
    exists_hasCompactSupport_fourierIntegral_ne_zero μ ψ.hasCompactSupport.isCompact
  have hgi : Integrable g μ := hg.integrable_of_hasCompactSupport hgc
  have hg2 : MemLp g 2 μ := hg.memLp_of_hasCompactSupport hgc
  have hΨ : Continuous fun χ ↦ ((ψ χ / ‖fourierIntegral μ g χ‖ ^ 2 : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp
      (continuous_div_sq_norm_fourierIntegral hgi (map_continuous ψ) hg0)
  have hΨc : HasCompactSupport fun χ ↦ ((ψ χ / ‖fourierIntegral μ g χ‖ ^ 2 : ℝ) : ℂ) :=
    (hasCompactSupport_div ψ.hasCompactSupport _).comp_left Complex.ofReal_zero
  refine Complex.ofReal_injective ?_
  calc ((∫ χ, ψ χ * ((‖fourierIntegral μ f χ‖₊ ^ 2 : ℝ≥0) : ℝ) ∂μ.dualAddHaar : ℝ) : ℂ)
    _ = ((∫ χ, ψ χ * ‖fourierIntegral μ f χ‖ ^ 2 / ‖fourierIntegral μ g χ‖ ^ 2
          ∂spectralMeasure μ (hg2.toLp g) : ℝ) : ℂ) := by
      rw [← integral_dualAddHaar μ (ψ := fun χ ↦ ψ χ * ‖fourierIntegral μ f χ‖ ^ 2)
        ((map_continuous ψ).mul (hfc.norm.pow 2)) ψ.hasCompactSupport.mul_right hgi hg2
        fun χ hχ ↦ hg0 χ (tsupport_mul_subset_left hχ)]
      simp
    _ = ∫ χ, ((ψ χ / ‖fourierIntegral μ g χ‖ ^ 2 : ℝ) : ℂ) * ‖fourierIntegral μ f χ‖ ^ 2
          ∂spectralMeasure μ (hg2.toLp g) := by
      rw [← integral_complex_ofReal]
      refine integral_congr_ae (.of_forall fun χ ↦ ?_)
      push_cast
      ring
    _ = ∫ χ, ((ψ χ / ‖fourierIntegral μ g χ‖ ^ 2 : ℝ) : ℂ) * ‖fourierIntegral μ g χ‖ ^ 2
          ∂spectralMeasure μ (hf2.toLp f) :=
      integral_mul_sq_fourierIntegral_spectralMeasure_comm μ hf hf2 hgi hg2
        ⟨⟨_, hΨ⟩, hΨc.is_zero_at_infty⟩
    _ = ((∫ χ, ψ χ ∂spectralMeasure μ (hf2.toLp f) : ℝ) : ℂ) := by
      rw [← integral_complex_ofReal]
      exact integral_congr_ae (.of_forall fun χ ↦ ofReal_div_sq_mul_sq hg0 χ)

/-- The Fourier transform preserves the `L²` norm of functions in `L¹ ∩ L²`. -/
theorem eLpNorm_two_fourierIntegral {f : G → ℂ} (hf : Integrable f μ) (hf2 : MemLp f 2 μ) :
    eLpNorm (fourierIntegral μ f) 2 μ.dualAddHaar = eLpNorm f 2 μ := by
  -- TS II §1 n°3, (19). Bourbaki proves this for `f ∈ A(G)` and extends it by density.
  have hsq : eLpNorm (fourierIntegral μ f) 2 μ.dualAddHaar ^ 2 = eLpNorm f 2 μ ^ 2 := by
    rw [sq_eLpNorm_two (continuous_fourierIntegral hf).aestronglyMeasurable, ← setLIntegral_univ,
      ← withDensity_apply _ MeasurableSet.univ,
      withDensity_dualAddHaar_sq_enorm_fourierIntegral μ hf hf2, spectralMeasure_univ,
      enorm_eq_nnnorm, Lp.nnnorm_toLp, ENNReal.coe_toNNReal hf2.eLpNorm_lt_top.ne]
  exact le_antisymm ((ENNReal.pow_le_pow_left_iff two_ne_zero).1 hsq.le)
    ((ENNReal.pow_le_pow_left_iff two_ne_zero).1 hsq.ge)

/-! ### Invariance under translations -/

section Translation

variable {μ} {g : G → ℂ} (η : AddPontryaginDual G)

omit [IsTopologicalAddGroup G] [LocallyCompactSpace G] [MeasurableSpace (AddPontryaginDual G)]
  [BorelSpace (AddPontryaginDual G)] [μ.IsAddHaarMeasure] [μ.Regular] in
private theorem integrable_toAddChar_smul (hg : Integrable g μ) :
    Integrable (fun x ↦ η.toAddChar x • g x) μ :=
  hg.mono (η.continuous_toAddChar.aestronglyMeasurable.fun_smul hg.1)
    (.of_forall fun x ↦ by rw [Circle.norm_smul])

omit [IsTopologicalAddGroup G] [LocallyCompactSpace G] [MeasurableSpace (AddPontryaginDual G)]
  [BorelSpace (AddPontryaginDual G)] [μ.IsAddHaarMeasure] [μ.Regular] in
private theorem memLp_toAddChar_smul (hg2 : MemLp g 2 μ) :
    MemLp (fun x ↦ η.toAddChar x • g x) 2 μ :=
  MemLp.of_le hg2
    (η.continuous_toAddChar.aestronglyMeasurable.fun_smul (MemLp.aestronglyMeasurable hg2))
    (.of_forall fun x ↦ by rw [Circle.norm_smul])

omit [LocallyCompactSpace G] [MeasurableSpace (AddPontryaginDual G)]
  [BorelSpace (AddPontryaginDual G)] [μ.Regular] in
private theorem inner_toLp_vadd_toLp (hg2 : MemLp g 2 μ) (y : G) :
    inner ℂ (hg2.toLp g) (DomAddAct.mk y +ᵥ hg2.toLp g) = ∫ x, conj (g x) * g (y + x) ∂μ := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hg2.coeFn_toLp, DomAddAct.vadd_Lp_ae_eq (DomAddAct.mk y) (hg2.toLp g),
    (measurePreserving_add_left μ y).quasiMeasurePreserving.tendsto_ae.eventually
      hg2.coeFn_toLp] with x hx hx' hx''
  rw [hx, hx', Equiv.symm_apply_apply, vadd_eq_add, hx'', RCLike.inner_apply, mul_comm]

omit [LocallyCompactSpace G] [MeasurableSpace (AddPontryaginDual G)]
  [BorelSpace (AddPontryaginDual G)] [μ.Regular] in
/-- Multiplication by a character is a unitary operator on `L²(G)` which commutes with
translations up to a scalar. -/
private theorem inner_toLp_vadd_toAddChar_smul (hg2 : MemLp g 2 μ) (y : G) :
    inner ℂ ((memLp_toAddChar_smul η hg2).toLp _)
        (DomAddAct.mk y +ᵥ (memLp_toAddChar_smul η hg2).toLp _) =
      η.toAddChar y • inner ℂ (hg2.toLp g) (DomAddAct.mk y +ᵥ hg2.toLp g) := by
  rw [inner_toLp_vadd_toLp, inner_toLp_vadd_toLp, Circle.smul_def, smul_eq_mul,
    ← integral_const_mul]
  refine integral_congr_ae (.of_forall fun x ↦ ?_)
  have h1 : conj (η.toAddChar x : ℂ) * η.toAddChar x = 1 := by
    rw [Complex.conj_mul', Circle.norm_coe]
    simp
  simp only [Circle.smul_def, smul_eq_mul, map_mul, AddChar.map_add_eq_mul, Circle.coe_mul]
  linear_combination (η.toAddChar y * conj (g x) * g (y + x)) * h1

omit [IsTopologicalAddGroup G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G] in
private theorem continuous_integral_zeroAtInfty (ν : Measure (AddPontryaginDual G))
    [IsFiniteMeasure ν] : Continuous fun Φ : C₀(AddPontryaginDual G, ℂ) ↦ ∫ χ, Φ χ ∂ν := by
  simpa using ZeroAtInftyContinuousMap.continuous_integral_mul (ν := ν) (integrable_const (1 : ℂ))

/-- Multiplying `g` by a character `η` translates the spectral measure of `g` by `η`. -/
private theorem spectralMeasure_toAddChar_smul (hg2 : MemLp g 2 μ) :
    spectralMeasure μ ((memLp_toAddChar_smul η hg2).toLp _) =
      Measure.map (η + ·) (spectralMeasure μ (hg2.toLp g)) := by
  -- For `φ ∈ L¹(G)`, the integrals of `fourierL1 μ φ` against both measures are equal to
  -- `∫ y, φ y * η (-y) * ⟪g, g (-y + ·)⟫ ∂μ`. Conclude by `denseRange_fourierL1`.
  have : (Measure.map (η + ·) (spectralMeasure μ (hg2.toLp g))).Regular :=
    Regular.map (Homeomorph.addLeft η)
  have : IsFiniteMeasure (Measure.map (η + ·) (spectralMeasure μ (hg2.toLp g))) :=
    isFiniteMeasure_map _ _
  have key (Φ : C₀(AddPontryaginDual G, ℂ)) :
      ∫ χ, Φ χ ∂spectralMeasure μ ((memLp_toAddChar_smul η hg2).toLp _) =
        ∫ χ, Φ χ ∂Measure.map (η + ·) (spectralMeasure μ (hg2.toLp g)) := by
    refine (denseRange_fourierL1 μ).induction_on Φ (isClosed_eq
      (continuous_integral_zeroAtInfty _) (continuous_integral_zeroAtInfty _)) fun φ ↦ ?_
    have hφ' : Integrable (fun x ↦ (-η).toAddChar x • φ x) μ :=
      integrable_toAddChar_smul (-η) (L1.integrable_coeFn φ)
    have e (χ : AddPontryaginDual G) : fourierL1 μ φ (η + χ) = fourierL1 μ (hφ'.toL1 _) χ := by
      rw [fourierL1_apply, fourierL1_apply, fourierIntegral_congr_ae hφ'.coeFn_toL1,
        fourierIntegral_toAddChar_smul, sub_neg_eq_add, add_comm]
    rw [(measurableEmbedding_addLeft η).integral_map]
    simp_rw [e]
    rw [integral_spectralMeasure, integral_spectralMeasure, fourierMultiplier_fourierL1,
      fourierMultiplier_fourierL1, L1.regularRep_apply, L1.regularRep_apply, L1.inner_convL2,
      L1.inner_convL2]
    refine integral_congr_ae ?_
    filter_upwards [hφ'.coeFn_toL1] with y hy
    rw [hy, inner_toLp_vadd_toAddChar_smul η hg2]
    simp only [toAddChar_neg_apply, AddChar.map_neg_eq_inv, Circle.smul_def, smul_eq_mul]
    ring
  refine Measure.ext_of_integral_eq_on_compactlySupported fun ψ ↦ ?_
  have h := key ⟨⟨fun χ ↦ (ψ χ : ℂ), Complex.continuous_ofReal.comp (map_continuous ψ)⟩,
    (ψ.hasCompactSupport.comp_left Complex.ofReal_zero).is_zero_at_infty⟩
  simp only [ZeroAtInftyContinuousMap.coe_mk, integral_complex_ofReal] at h
  exact_mod_cast h

end Translation

private theorem map_add_left_dualAddHaar (η : AddPontryaginDual G) :
    Measure.map (η + ·) μ.dualAddHaar = μ.dualAddHaar := by
  -- Multiplying `g` by the character `-η` translates both `fourierIntegral μ g` and
  -- `spectralMeasure μ g` by `-η`.
  have : (Measure.map (η + ·) μ.dualAddHaar).Regular := Regular.map (Homeomorph.addLeft η)
  refine Measure.ext_of_integral_eq_on_compactlySupported fun ψ ↦ ?_
  rw [(measurableEmbedding_addLeft η).integral_map]
  obtain ⟨g, hg, hgc, hg0⟩ :=
    exists_hasCompactSupport_fourierIntegral_ne_zero μ ψ.hasCompactSupport.isCompact
  have hgi : Integrable g μ := hg.integrable_of_hasCompactSupport hgc
  have hg2 : MemLp g 2 μ := hg.memLp_of_hasCompactSupport hgc
  have hψ' : Continuous fun χ ↦ ψ (η + χ) :=
    (map_continuous ψ).comp (continuous_const.add continuous_id)
  have hψ'c : HasCompactSupport fun χ ↦ ψ (η + χ) :=
    ψ.hasCompactSupport.comp_homeomorph (Homeomorph.addLeft η)
  have hg' : ∀ χ ∈ tsupport fun χ ↦ ψ (η + χ),
      fourierIntegral μ (fun x ↦ (-η).toAddChar x • g x) χ ≠ 0 := by
    intro χ hχ
    rw [show (fun χ ↦ ψ (η + χ)) = ψ ∘ Homeomorph.addLeft η from rfl,
      tsupport_comp_eq_preimage] at hχ
    rw [fourierIntegral_toAddChar_smul, sub_neg_eq_add, add_comm]
    exact hg0 _ hχ
  rw [integral_dualAddHaar μ hψ' hψ'c (integrable_toAddChar_smul (-η) hgi)
      (memLp_toAddChar_smul (-η) hg2) hg',
    integral_dualAddHaar μ (map_continuous ψ) ψ.hasCompactSupport hgi hg2 hg0,
    spectralMeasure_toAddChar_smul (-η) hg2, (measurableEmbedding_addLeft (-η)).integral_map]
  refine integral_congr_ae (.of_forall fun χ ↦ ?_)
  simp only [fourierIntegral_toAddChar_smul, add_neg_cancel_left, sub_neg_eq_add,
    neg_add_cancel_comm]

private theorem dualAddHaar_ne_zero : μ.dualAddHaar ≠ 0 := by
  -- By `eLpNorm_two_fourierIntegral`, applied to a nonzero continuous function with compact
  -- support.
  intro h
  obtain ⟨θ, hθ1, -, hθc, -⟩ := exists_continuous_one_zero_of_isCompact
    (isCompact_singleton (x := (0 : G))) isClosed_empty (Set.disjoint_empty _)
  have hg : Continuous fun x ↦ (θ x : ℂ) := Complex.continuous_ofReal.comp θ.continuous
  have hgc : HasCompactSupport fun x ↦ (θ x : ℂ) := hθc.comp_left Complex.ofReal_zero
  have h2 := eLpNorm_two_fourierIntegral μ (hg.integrable_of_hasCompactSupport hgc)
    (hg.memLp_of_hasCompactSupport hgc)
  rw [h, eLpNorm_measure_zero] at h2
  have h3 := congr_fun ((hg.ae_eq_iff_eq μ continuous_zero).1
    ((eLpNorm_eq_zero_iff two_ne_zero).1 h2.symm)) 0
  simp [hθ1 (Set.mem_singleton 0)] at h3

instance : (μ.dualAddHaar).IsAddHaarMeasure :=
  have : (μ.dualAddHaar).IsAddLeftInvariant := ⟨map_add_left_dualAddHaar μ⟩
  have : NeZero μ.dualAddHaar := ⟨dualAddHaar_ne_zero μ⟩
  {}

end AddPontryaginDual
