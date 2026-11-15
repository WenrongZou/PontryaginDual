/-
Copyright (c) 2026 Wenrong Zou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wenrong Zou
-/
module

public import PontryaginDuality.PositiveDefinite.Bochner

import PontryaginDuality.Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.WithDensity

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

The dual Haar measure is defined as the measure associated by the Riesz–Markov–Kakutani theorem
(`RealRMK.rieszMeasure`) with the positive linear functional
`ψ ↦ ∫ χ, ψ χ / fourierIntegral μ f χ ∂bochnerMeasure f`, where `f` is any continuous, integrable
and positive definite function whose Fourier transform is nonnegative and does not vanish on the
support of `ψ`. The value does not depend on `f`, by
`AddPontryaginDual.integral_mul_fourierIntegral_bochnerMeasure_comm`.

## References

* [G. B. Folland, *A Course in Abstract Harmonic Analysis*, Section 4.2][folland2016]
* [W. Rudin, *Fourier Analysis on Groups*, Section 1.5][rudin1962]
-/

@[expose] public section

open MeasureTheory Measure Filter Topology
open scoped ComplexOrder ComplexConjugate ENNReal NNReal ZeroAtInfty CompactlySupported Convolution

namespace AddPontryaginDual

variable {G : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [MeasurableSpace (AddPontryaginDual G)] [BorelSpace (AddPontryaginDual G)]
  (μ : Measure G) [μ.IsAddHaarMeasure] [μ.Regular]

omit [μ.IsAddHaarMeasure] in
private theorem integrable_fourierIntegral_of_isFiniteMeasure {f : G → ℂ} (hf : Integrable f μ)
    (ν : Measure (AddPontryaginDual G)) [IsFiniteMeasure ν] : Integrable (fourierIntegral μ f) ν :=
  .of_bound (continuous_fourierIntegral hf).aestronglyMeasurable (∫ x, ‖f x‖ ∂μ)
    (.of_forall (norm_fourierIntegral_le_integral_norm μ f))

omit [μ.IsAddHaarMeasure] in
/-- The integral of the Fourier transform of `h` against the measure associated with `φ`. -/
private theorem integral_fourierIntegral_bochnerMeasure {φ h : G → ℂ} (hφ : IsPositiveDefinite φ)
    (hφc : Continuous φ) (hh : Integrable h μ) :
    ∫ χ, fourierIntegral μ h χ ∂bochnerMeasure φ = ∫ x, h x * φ (-x) ∂μ := by
  simpa [fourierIntegralInv, Circle.smul_def, integral_toAddChar_bochnerMeasure hφ hφc] using
    integral_fourierIntegral_mul (ν := bochnerMeasure φ) hh (integrable_const (1 : ℂ))

private theorem integral_fourierIntegral_mul_fourierIntegral_bochnerMeasure {φ ψ h : G → ℂ}
    (hφ : IsPositiveDefinite φ) (hφc : Continuous φ) (hψ : Integrable ψ μ) (hh : Integrable h μ) :
    ∫ χ, fourierIntegral μ h χ * fourierIntegral μ ψ χ ∂bochnerMeasure φ =
      ∫ x, h x * ∫ y, ψ (-x + y) * φ (-y) ∂μ ∂μ := by
  rw [integral_fourierIntegral_mul hh (integrable_fourierIntegral_of_isFiniteMeasure μ hψ _)]
  refine integral_congr_ae (.of_forall fun x ↦ ?_)
  have := integral_fourierIntegral_bochnerMeasure μ hφ hφc (hψ.comp_add_left (-x))
  beta_reduce
  rw [fourierIntegralInv_apply, ← this]
  simp_rw [fourierIntegral_comp_add_left]

/-- If `f` and `g` are continuous, integrable and positive definite, then the measures
`fourierIntegral μ f • bochnerMeasure g` and `fourierIntegral μ g • bochnerMeasure f` are
equal. -/
theorem integral_mul_fourierIntegral_bochnerMeasure_comm {f g : G → ℂ}
    (hf : Continuous f) (hfi : Integrable f μ) (hfp : IsPositiveDefinite f)
    (hg : Continuous g) (hgi : Integrable g μ) (hgp : IsPositiveDefinite g)
    {Ψ : AddPontryaginDual G → ℂ} (hΨ : Continuous Ψ) (hΨ' : HasCompactSupport Ψ) :
    ∫ χ, Ψ χ * fourierIntegral μ f χ ∂bochnerMeasure g =
      ∫ χ, Ψ χ * fourierIntegral μ g χ ∂bochnerMeasure f := by
  -- For `h` integrable, both `∫ χ, fourierIntegral μ h χ * fourierIntegral μ f χ ∂bochnerMeasure g`
  -- and the same expression with `f` and `g` exchanged are equal to
  -- `∫ x, h x * ∫ y, f (-x + y) * g (-y) ∂μ ∂μ`, by the commutativity of the convolution.
  have hconv (x : G) : ∫ y, f (-x + y) * g (-y) ∂μ = ∫ y, g (-x + y) * f (-y) ∂μ := by
    rw [← integral_add_left_eq_self (fun y ↦ g (-x + y) * f (-y)) x,
      ← integral_neg_eq_self (fun y ↦ g (-x + (x + y)) * f (-(x + y))) μ]
    refine integral_congr_ae (.of_forall fun y ↦ ?_)
    beta_reduce
    rw [neg_add_cancel_left, neg_add, neg_neg, mul_comm]
  have key (h : G → ℂ) (hh : Integrable h μ) :
      ∫ χ, fourierIntegral μ h χ * fourierIntegral μ f χ ∂bochnerMeasure g =
        ∫ χ, fourierIntegral μ h χ * fourierIntegral μ g χ ∂bochnerMeasure f := by
    rw [integral_fourierIntegral_mul_fourierIntegral_bochnerMeasure μ hgp hg hfi hh,
      integral_fourierIntegral_mul_fourierIntegral_bochnerMeasure μ hfp hf hgi hh]
    simp_rw [hconv]
  -- Conclude by `denseRange_fourierL1`.
  have key' (Φ : C₀(AddPontryaginDual G, ℂ)) :
      ∫ χ, Φ χ * fourierIntegral μ f χ ∂bochnerMeasure g =
        ∫ χ, Φ χ * fourierIntegral μ g χ ∂bochnerMeasure f :=
    (denseRange_fourierL1 μ).induction_on Φ (isClosed_eq
      (ZeroAtInftyContinuousMap.continuous_integral_mul
        (integrable_fourierIntegral_of_isFiniteMeasure μ hfi _))
      (ZeroAtInftyContinuousMap.continuous_integral_mul
        (integrable_fourierIntegral_of_isFiniteMeasure μ hgi _)))
      fun h ↦ key h (L1.integrable_coeFn h)
  exact key' ⟨⟨Ψ, hΨ⟩, hΨ'.is_zero_at_infty⟩

/-! ### Auxiliary functions

To construct the dual Haar measure, we use the continuous, integrable and positive definite
functions whose Fourier transform is nonnegative and does not vanish on a given compact set. -/

private theorem tsupport_div_subset {X : Type*} [TopologicalSpace X] (ψ d : X → ℝ) :
    tsupport (fun x ↦ ψ x / d x) ⊆ tsupport ψ := by
  simp_rw [div_eq_mul_inv]
  exact tsupport_mul_subset_left

private theorem hasCompactSupport_div {X : Type*} [TopologicalSpace X] {ψ : X → ℝ}
    (hψ : HasCompactSupport ψ) (d : X → ℝ) : HasCompactSupport fun x ↦ ψ x / d x :=
  hψ.mono fun x hx h0 ↦ hx (by simp [h0])

/-- A continuous, integrable and positive definite function `f` whose Fourier transform is
nonnegative and does not vanish on the set `K`. -/
private structure IsGood (f : G → ℂ) (K : Set (AddPontryaginDual G)) : Prop where
  continuous : Continuous f
  integrable : Integrable f μ
  isPositiveDefinite : IsPositiveDefinite f
  nonneg : ∀ χ, 0 ≤ fourierIntegral μ f χ
  ne_zero : ∀ χ ∈ K, fourierIntegral μ f χ ≠ 0

namespace IsGood

variable {μ} {f g : G → ℂ} {K L : Set (AddPontryaginDual G)}

omit [IsTopologicalAddGroup G] [LocallyCompactSpace G] [BorelSpace G]
  [MeasurableSpace (AddPontryaginDual G)] [BorelSpace (AddPontryaginDual G)] [μ.IsAddHaarMeasure]
  [μ.Regular] in
private theorem mono (hf : IsGood μ f K) (h : L ⊆ K) : IsGood μ f L :=
  { hf with ne_zero := fun χ hχ ↦ hf.ne_zero χ (h hχ) }

omit [IsTopologicalAddGroup G] [LocallyCompactSpace G] [BorelSpace G]
  [MeasurableSpace (AddPontryaginDual G)] [BorelSpace (AddPontryaginDual G)] [μ.IsAddHaarMeasure]
  [μ.Regular] in
private theorem zero : IsGood μ (0 : G → ℂ) ∅ where
  continuous := continuous_zero
  integrable := integrable_zero _ _ _
  isPositiveDefinite := .zero
  nonneg χ := by simp [fourierIntegral]
  ne_zero χ hχ := hχ.elim

omit [LocallyCompactSpace G] [MeasurableSpace (AddPontryaginDual G)]
  [BorelSpace (AddPontryaginDual G)] [μ.IsAddHaarMeasure] [μ.Regular] in
private theorem add (hf : IsGood μ f K) (hg : IsGood μ g L) : IsGood μ (f + g) (K ∪ L) where
  continuous := hf.continuous.add hg.continuous
  integrable := hf.integrable.add hg.integrable
  isPositiveDefinite := hf.isPositiveDefinite.add hg.isPositiveDefinite
  nonneg χ := by
    rw [fourierIntegral_add hf.integrable hg.integrable]
    exact add_nonneg (hf.nonneg χ) (hg.nonneg χ)
  ne_zero χ hχ := by
    rw [fourierIntegral_add hf.integrable hg.integrable]
    rcases hχ with hχ | hχ
    · exact (add_pos_of_pos_of_nonneg ((hf.nonneg χ).lt_of_ne' (hf.ne_zero χ hχ))
        (hg.nonneg χ)).ne'
    · exact (add_pos_of_nonneg_of_pos (hf.nonneg χ)
        ((hg.nonneg χ).lt_of_ne' (hg.ne_zero χ hχ))).ne'

omit [IsTopologicalAddGroup G] [LocallyCompactSpace G] [MeasurableSpace (AddPontryaginDual G)]
  [BorelSpace (AddPontryaginDual G)] [μ.IsAddHaarMeasure] [μ.Regular] in
/-- Multiplying by a character translates the Fourier transform. -/
private theorem toAddChar_smul (hf : IsGood μ f K) (η : AddPontryaginDual G) :
    IsGood μ (fun x ↦ η.toAddChar x • f x) {χ | χ - η ∈ K} where
  continuous := η.continuous_toAddChar.smul hf.continuous
  integrable := by
    have hc : Continuous fun x ↦ η.toAddChar x := η.continuous_toAddChar
    simp_rw [← integrable_norm_iff (hc.aestronglyMeasurable.fun_smul hf.integrable.1),
      Circle.norm_smul]
    exact hf.integrable.norm
  isPositiveDefinite := (isPositiveDefinite_toAddChar η).mul hf.isPositiveDefinite
  nonneg χ := by
    rw [fourierIntegral_toAddChar_smul]
    exact hf.nonneg _
  ne_zero χ hχ := by
    rw [fourierIntegral_toAddChar_smul]
    exact hf.ne_zero _ hχ

omit [MeasurableSpace (AddPontryaginDual G)] [BorelSpace (AddPontryaginDual G)]
  [μ.IsAddHaarMeasure] in
private theorem continuous_div (hf : IsGood μ f K) {ψ : AddPontryaginDual G → ℝ}
    (hψ : Continuous ψ) (hψK : tsupport ψ ⊆ K) :
    Continuous fun χ ↦ ψ χ / ‖fourierIntegral μ f χ‖ :=
  continuous_of_tsupport fun χ hχ ↦
    hψ.continuousAt.div (continuous_fourierIntegral hf.integrable).norm.continuousAt
      (norm_ne_zero_iff.2 (hf.ne_zero χ (hψK (tsupport_div_subset _ _ hχ))))

omit [μ.IsAddHaarMeasure] in
private theorem integrable_div (hf : IsGood μ f K) {ψ : AddPontryaginDual G → ℝ}
    (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) (hψK : tsupport ψ ⊆ K) :
    Integrable (fun χ ↦ ψ χ / ‖fourierIntegral μ f χ‖) (bochnerMeasure f) :=
  (hf.continuous_div hψ hψK).integrable_of_hasCompactSupport (hasCompactSupport_div hψc _)

omit [IsTopologicalAddGroup G] [LocallyCompactSpace G] [BorelSpace G]
  [MeasurableSpace (AddPontryaginDual G)] [BorelSpace (AddPontryaginDual G)] [μ.IsAddHaarMeasure]
  [μ.Regular] in
private theorem ofReal_div_mul (hf : IsGood μ f K) {ψ : AddPontryaginDual G → ℝ}
    (hψK : tsupport ψ ⊆ K) (χ : AddPontryaginDual G) :
    ((ψ χ / ‖fourierIntegral μ f χ‖ : ℝ) : ℂ) * fourierIntegral μ f χ = ψ χ := by
  by_cases h0 : fourierIntegral μ f χ = 0
  · have : ψ χ = 0 := image_eq_zero_of_notMem_tsupport fun h ↦ hf.ne_zero χ (hψK h) h0
    simp [this]
  · rw [Complex.ofReal_div, ← Complex.eq_coe_norm_of_nonneg (hf.nonneg χ), div_mul_cancel₀ _ h0]

/-- The integral of `ψ / fourierIntegral μ f` against `bochnerMeasure f` does not depend on `f`. -/
private theorem integral_div_eq (hf : IsGood μ f K) (hg : IsGood μ g K)
    {ψ : AddPontryaginDual G → ℝ} (hψ : Continuous ψ) (hψc : HasCompactSupport ψ)
    (hψK : tsupport ψ ⊆ K) :
    ∫ χ, ψ χ / ‖fourierIntegral μ f χ‖ ∂bochnerMeasure f =
      ∫ χ, ψ χ / ‖fourierIntegral μ g χ‖ ∂bochnerMeasure g := by
  have hK₁ : tsupport (fun χ ↦ ψ χ / ‖fourierIntegral μ f χ‖) ⊆ K :=
    (tsupport_div_subset _ _).trans hψK
  have hK₂ : tsupport (fun χ ↦ ψ χ / ‖fourierIntegral μ g χ‖) ⊆ K :=
    (tsupport_div_subset _ _).trans hψK
  have hΨ : Continuous fun χ ↦
      ((ψ χ / ‖fourierIntegral μ f χ‖ / ‖fourierIntegral μ g χ‖ : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (hg.continuous_div (hf.continuous_div hψ hψK) hK₁)
  have hΨc : HasCompactSupport fun χ ↦
      ((ψ χ / ‖fourierIntegral μ f χ‖ / ‖fourierIntegral μ g χ‖ : ℝ) : ℂ) :=
    (hasCompactSupport_div (hasCompactSupport_div hψc _) _).comp_left Complex.ofReal_zero
  refine Complex.ofReal_injective ?_
  rw [← integral_complex_ofReal, ← integral_complex_ofReal]
  calc ∫ χ, ((ψ χ / ‖fourierIntegral μ f χ‖ : ℝ) : ℂ) ∂bochnerMeasure f
    _ = ∫ χ, ((ψ χ / ‖fourierIntegral μ f χ‖ / ‖fourierIntegral μ g χ‖ : ℝ) : ℂ) *
          fourierIntegral μ g χ ∂bochnerMeasure f :=
      integral_congr_ae (.of_forall fun χ ↦ (hg.ofReal_div_mul hK₁ χ).symm)
    _ = ∫ χ, ((ψ χ / ‖fourierIntegral μ f χ‖ / ‖fourierIntegral μ g χ‖ : ℝ) : ℂ) *
          fourierIntegral μ f χ ∂bochnerMeasure g :=
      integral_mul_fourierIntegral_bochnerMeasure_comm μ hg.continuous hg.integrable
        hg.isPositiveDefinite hf.continuous hf.integrable hf.isPositiveDefinite hΨ hΨc
    _ = ∫ χ, ((ψ χ / ‖fourierIntegral μ g χ‖ : ℝ) : ℂ) ∂bochnerMeasure g :=
      integral_congr_ae (.of_forall fun χ ↦ by
        beta_reduce
        rw [div_right_comm]
        exact hf.ofReal_div_mul hK₂ χ)

end IsGood

omit [MeasurableSpace (AddPontryaginDual G)] [BorelSpace (AddPontryaginDual G)] in
/-- If `u` is continuous with compact support, then the Fourier transform of
`x ↦ ∫ y, u y * conj (u (-x + y)) ∂μ` is `χ ↦ fourierIntegral μ u χ * conj (fourierIntegral μ u χ)`.
This is the Fourier transform of the convolution of `u` and `x ↦ conj (u (-x))`. -/
theorem fourierIntegral_integral_mul_conj {u : G → ℂ} (hu : Continuous u)
    (huc : HasCompactSupport u) (χ : AddPontryaginDual G) :
    fourierIntegral μ (fun x ↦ ∫ y, u y * conj (u (-x + y)) ∂μ) χ =
      fourierIntegral μ u χ * conj (fourierIntegral μ u χ) := by
  -- The function is the convolution of `u` and `x ↦ conj (u (-x))`.
  have hv : Continuous fun x ↦ conj (u (-x)) :=
    Complex.continuous_conj.comp (hu.comp continuous_neg)
  have hvc : HasCompactSupport fun x ↦ conj (u (-x)) :=
    (huc.comp_homeomorph (Homeomorph.neg G)).comp_left (g := conj) (map_zero _)
  have hae := L1.coeFn_mul_of_hasCompactSupport (μ := μ) hu huc hv hvc
  have hconv : (u ⋆[.mul ℂ ℂ, μ] fun x ↦ conj (u (-x))) =
      fun x ↦ ∫ y, u y * conj (u (-x + y)) ∂μ := by
    ext x
    simp only [convolution_def, ContinuousLinearMap.mul_apply', sub_eq_neg_add, neg_add_rev,
      neg_neg]
  rw [hconv] at hae
  rw [← fourierIntegral_congr_ae hae, fourierIntegral_mul,
    fourierIntegral_congr_ae (Integrable.coeFn_toL1 _),
    fourierIntegral_congr_ae (Integrable.coeFn_toL1 _), fourierIntegral_conj_neg]

omit [MeasurableSpace (AddPontryaginDual G)] [BorelSpace (AddPontryaginDual G)] in
private theorem exists_isGood_fourierIntegral_ne_zero (χ₀ : AddPontryaginDual G) :
    ∃ f : G → ℂ, IsGood μ f ∅ ∧ fourierIntegral μ f χ₀ ≠ 0 := by
  -- Take `f x = ∫ y, u y * conj (u (-x + y)) ∂μ`, where `u = χ₀ • θ` and `θ` is a nonzero
  -- nonnegative continuous function with compact support.
  obtain ⟨θ, hθ1, -, hθc, hθ01⟩ := exists_continuous_one_zero_of_isCompact
    (isCompact_singleton (x := (0 : G))) isClosed_empty (Set.disjoint_empty _)
  have hpos : 0 < ∫ x, θ x ∂μ :=
    Continuous.integral_pos_of_hasCompactSupport_nonneg_ne_zero (x := 0) θ.continuous hθc
      (fun x ↦ (hθ01 x).1) (by simp [hθ1 (Set.mem_singleton 0)])
  have hu : Continuous fun x ↦ χ₀.toAddChar x • (θ x : ℂ) :=
    χ₀.continuous_toAddChar.smul (Complex.continuous_ofReal.comp θ.continuous)
  have huc : HasCompactSupport fun x ↦ χ₀.toAddChar x • (θ x : ℂ) :=
    (hθc.comp_left Complex.ofReal_zero).smul_left
  have hu0 : fourierIntegral μ (fun x ↦ χ₀.toAddChar x • (θ x : ℂ)) χ₀ ≠ 0 := by
    have : fourierIntegral μ (fun x ↦ (θ x : ℂ)) 0 = ((∫ x, θ x ∂μ : ℝ) : ℂ) := by
      simp [fourierIntegral, integral_complex_ofReal]
    rw [fourierIntegral_toAddChar_smul, sub_self, this]
    exact_mod_cast hpos.ne'
  have hu2 : MemLp (fun x ↦ χ₀.toAddChar x • (θ x : ℂ)) 2 μ := hu.memLp_of_hasCompactSupport huc
  refine ⟨_, ⟨continuous_integral_mul_conj hu2,
    (continuous_integral_mul_conj hu2).integrable_of_hasCompactSupport
      (hasCompactSupport_integral_mul_conj huc),
    isPositiveDefinite_integral_mul_conj hu2, fun χ ↦ ?_, fun χ hχ ↦ hχ.elim⟩, ?_⟩
  · rw [fourierIntegral_integral_mul_conj μ hu huc]
    exact mul_star_self_nonneg _
  · rw [fourierIntegral_integral_mul_conj μ hu huc]
    exact mul_ne_zero hu0 ((map_ne_zero _).2 hu0)

omit [MeasurableSpace (AddPontryaginDual G)] [BorelSpace (AddPontryaginDual G)] in
private theorem exists_isGood {K : Set (AddPontryaginDual G)} (hK : IsCompact K) :
    ∃ f : G → ℂ, IsGood μ f K := by
  refine hK.induction_on (p := fun K ↦ ∃ f : G → ℂ, IsGood μ f K) ⟨0, .zero⟩
    (fun s t hst ⟨f, hf⟩ ↦ ⟨f, hf.mono hst⟩) (fun s t ⟨f, hf⟩ ⟨g, hg⟩ ↦ ⟨f + g, hf.add hg⟩)
    fun χ₀ _ ↦ ?_
  obtain ⟨f, hf, hfχ⟩ := exists_isGood_fourierIntegral_ne_zero μ χ₀
  exact ⟨{χ | fourierIntegral μ f χ ≠ 0}, mem_nhdsWithin_of_mem_nhds
    ((isOpen_ne_fun (continuous_fourierIntegral hf.integrable) continuous_const).mem_nhds hfχ),
    f, { hf with ne_zero := fun χ hχ ↦ hχ }⟩

omit [MeasurableSpace (AddPontryaginDual G)] [BorelSpace (AddPontryaginDual G)] in
/-- For every compact subset `K` of the Pontryagin dual, there is a continuous, integrable and
positive definite function whose Fourier transform does not vanish on `K`. -/
theorem exists_fourierIntegral_ne_zero_of_isCompact {K : Set (AddPontryaginDual G)}
    (hK : IsCompact K) :
    ∃ f : G → ℂ, Continuous f ∧ Integrable f μ ∧ IsPositiveDefinite f ∧
      ∀ χ ∈ K, fourierIntegral μ f χ ≠ 0 :=
  let ⟨f, hf⟩ := exists_isGood μ hK
  ⟨f, hf.continuous, hf.integrable, hf.isPositiveDefinite, hf.ne_zero⟩

omit [MeasurableSpace G] [BorelSpace G] in
/-- Multiplying a positive definite function by a character translates the associated measure. -/
private theorem bochnerMeasure_toAddChar_smul {f : G → ℂ} (hfp : IsPositiveDefinite f)
    (hf : Continuous f) (η : AddPontryaginDual G) :
    bochnerMeasure (fun x ↦ η.toAddChar x • f x) = Measure.map (η + ·) (bochnerMeasure f) := by
  have : (Measure.map (η + ·) (bochnerMeasure f)).Regular := Regular.map (Homeomorph.addLeft η)
  refine (eq_bochnerMeasure fun x ↦ ?_).symm
  rw [(measurableEmbedding_addLeft η).integral_map]
  simp_rw [toAddChar_add_apply, Circle.coe_mul, integral_const_mul,
    integral_toAddChar_bochnerMeasure hfp hf, Circle.smul_def, smul_eq_mul]

/-- If `∫ x, ψ x * s x ∂ν` is nonnegative for all nonnegative continuous functions `ψ` with
compact support, then the continuous function `s` is nonnegative. -/
private theorem nonneg_of_forall_integral_mul_nonneg {X : Type*} [TopologicalSpace X] [T2Space X]
    [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X] {ν : Measure X}
    [IsFiniteMeasureOnCompacts ν] [ν.IsOpenPosMeasure] {s : X → ℝ} (hs : Continuous s)
    (h : ∀ ψ : X → ℝ, Continuous ψ → HasCompactSupport ψ → (∀ x, 0 ≤ ψ x) →
      0 ≤ ∫ x, ψ x * s x ∂ν) (x : X) : 0 ≤ s x := by
  by_contra! hx
  obtain ⟨θ, hθ1, hθ0, hθc, hθ01⟩ := exists_continuous_one_zero_of_isCompact
    (isCompact_singleton (x := x)) (isOpen_lt hs continuous_const).isClosed_compl
    (Set.disjoint_singleton_left.2 fun h ↦ h hx)
  have hle (y : X) : 0 ≤ θ y * -s y := by
    by_cases hy : s y < 0
    · exact mul_nonneg (hθ01 y).1 (neg_nonneg.2 hy.le)
    · simp [hθ0 hy]
  have hpos : 0 < ∫ y, θ y * -s y ∂ν :=
    Continuous.integral_pos_of_hasCompactSupport_nonneg_ne_zero (x := x)
      (θ.continuous.mul hs.neg) hθc.mul_right hle
      (by simpa [hθ1 (Set.mem_singleton x)] using hx.ne)
  have := h θ θ.continuous hθc fun y ↦ (hθ01 y).1
  simp only [mul_neg, integral_neg] at hpos
  linarith

/-! ### The dual Haar measure -/

/-- A continuous, integrable and positive definite function whose Fourier transform is nonnegative
and does not vanish on the support of `ψ`. -/
private noncomputable def auxFun (ψ : C_c(AddPontryaginDual G, ℝ)) : G → ℂ :=
  (exists_isGood μ ψ.hasCompactSupport.isCompact).choose

omit [MeasurableSpace (AddPontryaginDual G)] [BorelSpace (AddPontryaginDual G)] in
private theorem isGood_auxFun (ψ : C_c(AddPontryaginDual G, ℝ)) :
    IsGood μ (auxFun μ ψ) (tsupport ψ) :=
  (exists_isGood μ ψ.hasCompactSupport.isCompact).choose_spec

private theorem integral_div_auxFun (ψ : C_c(AddPontryaginDual G, ℝ)) {f : G → ℂ}
    (hf : IsGood μ f (tsupport ψ)) :
    ∫ χ, ψ χ / ‖fourierIntegral μ (auxFun μ ψ) χ‖ ∂bochnerMeasure (auxFun μ ψ) =
      ∫ χ, ψ χ / ‖fourierIntegral μ f χ‖ ∂bochnerMeasure f :=
  (isGood_auxFun μ ψ).integral_div_eq hf (map_continuous ψ) ψ.hasCompactSupport subset_rfl

/-- The positive linear functional `ψ ↦ ∫ χ, ψ χ / fourierIntegral μ f χ ∂bochnerMeasure f`, where
`f` is any continuous, integrable and positive definite function whose Fourier transform is
nonnegative and does not vanish on the support of `ψ`
(see `AddPontryaginDual.dualHaarFunctional_apply`). -/
private noncomputable def dualHaarFunctional : C_c(AddPontryaginDual G, ℝ) →ₚ[ℝ] ℝ :=
  PositiveLinearMap.mk₀
    { toFun := fun ψ ↦
        ∫ χ, ψ χ / ‖fourierIntegral μ (auxFun μ ψ) χ‖ ∂bochnerMeasure (auxFun μ ψ)
      map_add' := fun ψ₁ ψ₂ ↦ by
        obtain ⟨f, hf⟩ := exists_isGood μ
          (ψ₁.hasCompactSupport.isCompact.union ψ₂.hasCompactSupport.isCompact)
        have h₁ : IsGood μ f (tsupport ψ₁) := hf.mono Set.subset_union_left
        have h₂ : IsGood μ f (tsupport ψ₂) := hf.mono Set.subset_union_right
        rw [integral_div_auxFun μ _ (hf.mono (tsupport_add ψ₁ ψ₂)), integral_div_auxFun μ _ h₁,
          integral_div_auxFun μ _ h₂,
          ← integral_add (h₁.integrable_div (map_continuous ψ₁) ψ₁.hasCompactSupport subset_rfl)
            (h₂.integrable_div (map_continuous ψ₂) ψ₂.hasCompactSupport subset_rfl)]
        simp only [CompactlySupportedContinuousMap.coe_add, Pi.add_apply, add_div]
      map_smul' := fun c ψ ↦ by
        have hc : tsupport (c • ψ : C_c(AddPontryaginDual G, ℝ)) ⊆ tsupport ψ :=
          closure_mono fun χ hχ h0 ↦ hχ (by simp [h0])
        rw [integral_div_auxFun μ _ ((isGood_auxFun μ ψ).mono hc), RingHom.id_apply, smul_eq_mul,
          ← integral_const_mul]
        simp only [CompactlySupportedContinuousMap.coe_smul, Pi.smul_apply, smul_eq_mul,
          mul_div_assoc] }
    fun ψ hψ ↦ integral_nonneg fun χ ↦ div_nonneg (hψ χ) (norm_nonneg _)

/-- The Haar measure on the Pontryagin dual of `G` which is dual to the Haar measure `μ` on `G`:
the unique regular Haar measure for which the Fourier inversion formula holds (see
`AddPontryaginDual.fourierIntegralInv_fourierIntegral` and `AddPontryaginDual.eq_dualAddHaar`).

It is the measure associated by the Riesz–Markov–Kakutani theorem with the positive linear
functional `ψ ↦ ∫ χ, ψ χ / fourierIntegral μ f χ ∂bochnerMeasure f`, where `f` is any continuous,
integrable and positive definite function whose Fourier transform is nonnegative and does not
vanish on the support of `ψ`. -/
@[no_expose]
noncomputable def _root_.MeasureTheory.Measure.dualAddHaar : Measure (AddPontryaginDual G) :=
  RealRMK.rieszMeasure (dualHaarFunctional μ)

instance : (μ.dualAddHaar).Regular :=
  RealRMK.regular_rieszMeasure _

private theorem integral_dualAddHaar {ψ : AddPontryaginDual G → ℝ} (hψ : Continuous ψ)
    (hψc : HasCompactSupport ψ) {f : G → ℂ} (hf : IsGood μ f (tsupport ψ)) :
    ∫ χ, ψ χ ∂μ.dualAddHaar = ∫ χ, ψ χ / ‖fourierIntegral μ f χ‖ ∂bochnerMeasure f :=
  (RealRMK.integral_rieszMeasure (dualHaarFunctional μ) ⟨⟨ψ, hψ⟩, hψc⟩).trans
    (integral_div_auxFun μ ⟨⟨ψ, hψ⟩, hψc⟩ hf)

/-- The measure `bochnerMeasure f` has density `fourierIntegral μ f` with respect to the dual Haar
measure, in terms of integrals of continuous functions with compact support. -/
private theorem integral_mul_clm_fourierIntegral {f : G → ℂ} (hf : Continuous f)
    (hfi : Integrable f μ) (hfp : IsPositiveDefinite f) {ψ : AddPontryaginDual G → ℝ}
    (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) (ℓ : ℂ →L[ℝ] ℝ) :
    ∫ χ, ψ χ * ℓ (fourierIntegral μ f χ) ∂μ.dualAddHaar =
      ℓ (∫ χ, (ψ χ : ℂ) ∂bochnerMeasure f) := by
  obtain ⟨g, hg⟩ := exists_isGood μ hψc.isCompact
  have hfc : Continuous (fourierIntegral μ f) := continuous_fourierIntegral hfi
  have hΨ : Continuous fun χ ↦ ((ψ χ / ‖fourierIntegral μ g χ‖ : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (hg.continuous_div hψ subset_rfl)
  have hΨc : HasCompactSupport fun χ ↦ ((ψ χ / ‖fourierIntegral μ g χ‖ : ℝ) : ℂ) :=
    (hasCompactSupport_div hψc _).comp_left Complex.ofReal_zero
  calc ∫ χ, ψ χ * ℓ (fourierIntegral μ f χ) ∂μ.dualAddHaar
    _ = ∫ χ, ψ χ * ℓ (fourierIntegral μ f χ) / ‖fourierIntegral μ g χ‖ ∂bochnerMeasure g :=
      integral_dualAddHaar μ (hψ.mul (ℓ.continuous.comp hfc)) hψc.mul_right
        (hg.mono tsupport_mul_subset_left)
    _ = ∫ χ, ℓ (((ψ χ / ‖fourierIntegral μ g χ‖ : ℝ) : ℂ) * fourierIntegral μ f χ)
          ∂bochnerMeasure g := by
      refine integral_congr_ae (.of_forall fun χ ↦ ?_)
      beta_reduce
      rw [← Complex.real_smul, map_smul, smul_eq_mul, mul_div_right_comm]
    _ = ℓ (∫ χ, ((ψ χ / ‖fourierIntegral μ g χ‖ : ℝ) : ℂ) * fourierIntegral μ f χ
          ∂bochnerMeasure g) :=
      ℓ.integral_comp_comm ((hΨ.mul hfc).integrable_of_hasCompactSupport hΨc.mul_right)
    _ = ℓ (∫ χ, ((ψ χ / ‖fourierIntegral μ g χ‖ : ℝ) : ℂ) * fourierIntegral μ g χ
          ∂bochnerMeasure f) := by
      rw [integral_mul_fourierIntegral_bochnerMeasure_comm μ hf hfi hfp hg.continuous
        hg.integrable hg.isPositiveDefinite hΨ hΨc]
    _ = ℓ (∫ χ, (ψ χ : ℂ) ∂bochnerMeasure f) := by simp_rw [hg.ofReal_div_mul subset_rfl]

private theorem integral_mul_re_fourierIntegral {f : G → ℂ} (hf : Continuous f)
    (hfi : Integrable f μ) (hfp : IsPositiveDefinite f) {ψ : AddPontryaginDual G → ℝ}
    (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) :
    ∫ χ, ψ χ * (fourierIntegral μ f χ).re ∂μ.dualAddHaar = ∫ χ, ψ χ ∂bochnerMeasure f := by
  simpa [integral_complex_ofReal] using
    integral_mul_clm_fourierIntegral μ hf hfi hfp hψ hψc Complex.reCLM

private theorem integral_mul_im_fourierIntegral {f : G → ℂ} (hf : Continuous f)
    (hfi : Integrable f μ) (hfp : IsPositiveDefinite f) {ψ : AddPontryaginDual G → ℝ}
    (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) :
    ∫ χ, ψ χ * (fourierIntegral μ f χ).im ∂μ.dualAddHaar = 0 := by
  simpa [integral_complex_ofReal] using
    integral_mul_clm_fourierIntegral μ hf hfi hfp hψ hψc Complex.imCLM

private theorem map_add_left_dualAddHaar (η : AddPontryaginDual G) :
    Measure.map (η + ·) μ.dualAddHaar = μ.dualAddHaar := by
  -- Multiplying `g` by the character `-η` translates both `fourierIntegral μ g` and
  -- `bochnerMeasure g` by `η`.
  have : (Measure.map (η + ·) μ.dualAddHaar).Regular := Regular.map (Homeomorph.addLeft η)
  refine Measure.ext_of_integral_eq_on_compactlySupported fun ψ ↦ ?_
  rw [(measurableEmbedding_addLeft η).integral_map]
  obtain ⟨g, hg⟩ := exists_isGood μ ψ.hasCompactSupport.isCompact
  have hψ' : Continuous fun χ ↦ ψ (η + χ) :=
    (map_continuous ψ).comp (continuous_const.add continuous_id)
  have hψ'c : HasCompactSupport fun χ ↦ ψ (η + χ) :=
    ψ.hasCompactSupport.comp_homeomorph (Homeomorph.addLeft η)
  have hg' : IsGood μ (fun x ↦ (-η).toAddChar x • g x) (tsupport fun χ ↦ ψ (η + χ)) := by
    refine (hg.toAddChar_smul (-η)).mono fun χ hχ ↦ ?_
    rw [show (fun χ ↦ ψ (η + χ)) = ψ ∘ Homeomorph.addLeft η from rfl,
      tsupport_comp_eq_preimage] at hχ
    change χ - -η ∈ tsupport ψ
    rwa [sub_neg_eq_add, add_comm]
  rw [integral_dualAddHaar μ hψ' hψ'c hg',
    integral_dualAddHaar μ (map_continuous ψ) ψ.hasCompactSupport hg,
    bochnerMeasure_toAddChar_smul hg.isPositiveDefinite hg.continuous,
    (measurableEmbedding_addLeft (-η)).integral_map]
  refine integral_congr_ae (.of_forall fun χ ↦ ?_)
  simp only [fourierIntegral_toAddChar_smul, add_neg_cancel_left, sub_neg_eq_add,
    neg_add_cancel_comm]

private theorem dualAddHaar_ne_zero : μ.dualAddHaar ≠ 0 := by
  -- Otherwise `bochnerMeasure φ = 0` for all `φ`, hence `φ 0 = 0`.
  intro h
  obtain ⟨φ, hφ, hφc, hφp, -, hφ0⟩ :=
    exists_isPositiveDefinite_hasCompactSupport (G := G) (U := Set.univ) Filter.univ_mem
  have h0 : bochnerMeasure φ = 0 := by
    refine Measure.ext_of_integral_eq_on_compactlySupported fun ψ ↦ ?_
    rw [← integral_mul_re_fourierIntegral μ hφ (hφ.integrable_of_hasCompactSupport hφc) hφp
      (map_continuous ψ) ψ.hasCompactSupport, h]
    simp
  have := integral_toAddChar_bochnerMeasure hφp hφ 0
  rw [h0] at this
  exact hφ0 (by simpa using this.symm)

instance : (μ.dualAddHaar).IsAddHaarMeasure :=
  have : (μ.dualAddHaar).IsAddLeftInvariant := ⟨map_add_left_dualAddHaar μ⟩
  have : NeZero μ.dualAddHaar := ⟨dualAddHaar_ne_zero μ⟩
  {}

variable {μ} {f : G → ℂ}

/-- The Fourier transform of a continuous, integrable and positive definite function is
nonnegative. -/
theorem fourierIntegral_nonneg (hf : Continuous f) (hfi : Integrable f μ)
    (hfp : IsPositiveDefinite f) (χ : AddPontryaginDual G) : 0 ≤ fourierIntegral μ f χ := by
  -- The measure `bochnerMeasure f` has density `fourierIntegral μ f` with respect to
  -- `μ.dualAddHaar`, which is positive on nonempty open sets.
  have hfc : Continuous (fourierIntegral μ f) := continuous_fourierIntegral hfi
  have hre := nonneg_of_forall_integral_mul_nonneg (ν := μ.dualAddHaar)
    (s := fun χ ↦ (fourierIntegral μ f χ).re) (Complex.continuous_re.comp hfc)
    (fun ψ hψ hψc hψ0 ↦ by
      rw [integral_mul_re_fourierIntegral μ hf hfi hfp hψ hψc]
      exact integral_nonneg hψ0) χ
  have him := nonneg_of_forall_integral_mul_nonneg (ν := μ.dualAddHaar)
    (s := fun χ ↦ (fourierIntegral μ f χ).im) (Complex.continuous_im.comp hfc)
    (fun ψ hψ hψc _ ↦ (integral_mul_im_fourierIntegral μ hf hfi hfp hψ hψc).ge) χ
  have him' := nonneg_of_forall_integral_mul_nonneg (ν := μ.dualAddHaar)
    (s := fun χ ↦ -(fourierIntegral μ f χ).im) (Complex.continuous_im.comp hfc).neg
    (fun ψ hψ hψc _ ↦ by
      simp [mul_neg, integral_neg, integral_mul_im_fourierIntegral μ hf hfi hfp hψ hψc]) χ
  exact Complex.nonneg_iff.2 ⟨hre, le_antisymm him (neg_nonneg.1 him')⟩

/-- The measure associated by Bochner's theorem with a continuous, integrable and positive
definite function `f` has density `fourierIntegral μ f` with respect to the dual Haar measure. -/
theorem withDensity_dualAddHaar_enorm_fourierIntegral (hf : Continuous f) (hfi : Integrable f μ)
    (hfp : IsPositiveDefinite f) :
    μ.dualAddHaar.withDensity (fun χ ↦ ‖fourierIntegral μ f χ‖ₑ) = bochnerMeasure f := by
  simp_rw [enorm_eq_nnnorm]
  refine Measure.withDensity_eq_of_forall_integral_mul_eq
    (ρ := fun χ ↦ ‖fourierIntegral μ f χ‖₊) (continuous_fourierIntegral hfi).nnnorm
    (C := (∫ x, ‖f x‖ ∂μ).toNNReal) (fun χ ↦ ?_) fun ψ ↦ ?_
  · exact (Real.le_toNNReal_iff_coe_le (integral_nonneg fun _ ↦ norm_nonneg _)).2
      (norm_fourierIntegral_le_integral_norm μ f χ)
  · rw [← integral_mul_re_fourierIntegral μ hf hfi hfp (map_continuous ψ) ψ.hasCompactSupport]
    refine integral_congr_ae (.of_forall fun χ ↦ ?_)
    beta_reduce
    rw [coe_nnnorm, Complex.re_eq_norm.2 (fourierIntegral_nonneg hf hfi hfp χ)]

/-- The Fourier transform of a continuous, integrable and positive definite function is
integrable with respect to the dual Haar measure. -/
theorem integrable_fourierIntegral (hf : Continuous f) (hfi : Integrable f μ)
    (hfp : IsPositiveDefinite f) : Integrable (fourierIntegral μ f) μ.dualAddHaar := by
  -- `∫⁻ χ, ‖fourierIntegral μ f χ‖ₑ ∂μ.dualAddHaar = bochnerMeasure f univ < ∞`.
  refine ⟨(continuous_fourierIntegral hfi).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm, ← setLIntegral_univ, ← withDensity_apply _ MeasurableSet.univ,
    withDensity_dualAddHaar_enorm_fourierIntegral hf hfi hfp]
  exact measure_lt_top _ _

/-- The **Fourier inversion theorem** for continuous, integrable and positive definite
functions. -/
theorem fourierIntegralInv_fourierIntegral (hf : Continuous f) (hfi : Integrable f μ)
    (hfp : IsPositiveDefinite f) :
    fourierIntegralInv μ.dualAddHaar (fourierIntegral μ f) = f := by
  -- `integral_toAddChar_bochnerMeasure`, `withDensity_dualAddHaar_enorm_fourierIntegral` and
  -- `fourierIntegral_nonneg`.
  ext x
  rw [fourierIntegralInv_apply, ← integral_toAddChar_bochnerMeasure hfp hf x,
    ← withDensity_dualAddHaar_enorm_fourierIntegral hf hfi hfp,
    integral_withDensity_eq_integral_toReal_smul
      (continuous_fourierIntegral hfi).enorm.measurable (.of_forall fun _ ↦ enorm_lt_top)]
  refine integral_congr_ae (.of_forall fun χ ↦ ?_)
  beta_reduce
  rw [toReal_enorm, Complex.real_smul, ← Complex.eq_coe_norm_of_nonneg
    (fourierIntegral_nonneg hf hfi hfp χ), Circle.smul_def, smul_eq_mul, mul_comm]

/-- The dual Haar measure is the only regular Haar measure for which the Fourier inversion
formula holds at `0`. -/
theorem eq_dualAddHaar {ν : Measure (AddPontryaginDual G)} [ν.IsAddHaarMeasure] [ν.Regular]
    (h : ∀ f : G → ℂ, Continuous f → Integrable f μ → IsPositiveDefinite f →
      fourierIntegralInv ν (fourierIntegral μ f) 0 = f 0) : ν = μ.dualAddHaar := by
  -- `ν = c • μ.dualAddHaar` by uniqueness of the Haar measure, and `c = 1` by applying the
  -- assumption to a function `f` with `f 0 ≠ 0` (`exists_isPositiveDefinite_hasCompactSupport`).
  obtain ⟨c, rfl⟩ : ∃ c : ℝ≥0, ν = c • μ.dualAddHaar :=
    ⟨_, isAddLeftInvariant_eq_smul_of_regular ν μ.dualAddHaar⟩
  obtain ⟨f, hf, hfc, hfp, -, hf0⟩ :=
    exists_isPositiveDefinite_hasCompactSupport (G := G) (U := Set.univ) Filter.univ_mem
  have hfi : Integrable f μ := hf.integrable_of_hasCompactSupport hfc
  have h1 := h f hf hfi hfp
  rw [fourierIntegralInv_apply, integral_smul_nnreal_measure, ← fourierIntegralInv_apply,
    fourierIntegralInv_fourierIntegral hf hfi hfp, NNReal.smul_def, Complex.real_smul,
    mul_eq_right₀ hf0] at h1
  rw [show c = 1 by exact_mod_cast h1, one_smul]

end AddPontryaginDual
