/-
Copyright (c) 2026 Wenrong Zou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wenrong Zou
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.MeasureTheory.Function.L2Space
public import PontryaginDuality.Convolution.L1Algebra

import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lp
import PontryaginDuality.Mathlib.MeasureTheory.Function.ContinuousMapDense

/-!
# The regular representation of `L¹(G)` on `L²(G)`

For a locally compact abelian group `G` with Haar measure `μ`, the convolution
`f ⋆ g = ∫ y, f y • τ_y g ∂μ` of `f ∈ L¹(G)` and `g ∈ L²(G)` is in `L²(G)`, and `f ↦ (g ↦ f ⋆ g)`
is an injective homomorphism of involutive algebras from `L¹(G)` to the bounded operators on
`L²(G)`.

## Main definitions

* `MeasureTheory.L1.convL2 f g`: the convolution of `f ∈ L¹(G)` and `g ∈ L²(G)`.
* `MeasureTheory.L1.regularRep μ`: the regular representation, as a homomorphism of non-unital
  algebras `L¹(G) →ₙₐ[𝕜] L²(G) →L[𝕜] L²(G)`.

## Main statements

* `MeasureTheory.L1.coeFn_convL2_toLp`: on `L¹ ∩ L²`, the convolution `L¹ × L² → L²` is the
  product of `L¹(G)`.
* `MeasureTheory.L1.regularRep_involution`: the regular representation turns the involution of
  `L¹(G)` into the adjoint.
* `MeasureTheory.L1.regularRep_injective`: the regular representation is injective.
* `MeasureTheory.L1.exists_nhds_zero_norm_convL2_sub_lt`: approximate units.

## References

* [N. Bourbaki, *Théories spectrales*, Chap. I, §6, n°7][bourbaki1967]
-/

@[expose] public section

open MeasureTheory Measure Filter Topology
open scoped ENNReal ComplexConjugate

namespace MeasureTheory.L1

variable {G 𝕜 : Type*} [RCLike 𝕜] [MeasurableSpace G] [AddCommGroup G] [TopologicalSpace G]
  [IsTopologicalAddGroup G] [LocallyCompactSpace G] [BorelSpace G] {μ : Measure G}
  [μ.IsAddHaarMeasure] [μ.Regular]

/-- The convolution `f ⋆ g = ∫ y, f y • τ_y g ∂μ` of `f ∈ L¹(G)` and `g ∈ L²(G)`, where
`τ_y g = (x ↦ g (-y + x))`. -/
noncomputable def convL2 (f : Lp 𝕜 1 μ) (g : Lp 𝕜 2 μ) : Lp 𝕜 2 μ :=
  ∫ y, f y • (DomAddAct.mk (-y) +ᵥ g) ∂μ

theorem continuous_translateL2 (g : Lp 𝕜 2 μ) :
    Continuous fun y : G ↦ DomAddAct.mk (-y) +ᵥ g :=
  have : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨ENNReal.ofNat_ne_top⟩
  (DomAddAct.continuous_mk.comp continuous_neg).vadd continuous_const

theorem integrable_smul_translateL2 (f : Lp 𝕜 1 μ) (g : Lp 𝕜 2 μ) :
    Integrable (fun y ↦ f y • (DomAddAct.mk (-y) +ᵥ g)) μ := by
  refine ⟨?_, ((L1.integrable_coeFn f).norm.mul_const ‖g‖).hasFiniteIntegral.mono
    (.of_forall fun y ↦ by simp [norm_smul])⟩
  -- `f` is an a.e. limit of continuous functions with compact support.
  have (n : ℕ) : ∃ φ : G → 𝕜, HasCompactSupport φ ∧ eLpNorm (⇑f - φ) 1 μ ≤ (n : ℝ≥0∞)⁻¹ ∧
      Continuous φ ∧ MemLp φ 1 μ :=
    (Lp.memLp f).exists_hasCompactSupport_eLpNorm_sub_le' ENNReal.one_ne_top (by simp)
  choose φ hφ hfφ hφ' _ using this
  have : TendstoInMeasure μ φ atTop f :=
    tendstoInMeasure_of_tendsto_eLpNorm one_ne_zero <|
      tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
        ENNReal.tendsto_inv_nat_nhds_zero (fun _ ↦ zero_le)
        fun n ↦ eLpNorm_sub_comm (φ n) f 1 μ ▸ hfφ n
  obtain ⟨ns, -, hns⟩ := this.exists_seq_tendsto_ae
  refine aestronglyMeasurable_of_tendsto_ae atTop (fun n ↦ ?_) (hns.mono fun y hy ↦ hy.smul_const _)
  exact (((hφ' (ns n)).smul (continuous_translateL2 g)).stronglyMeasurable_of_hasCompactSupport
    (hφ (ns n)).smul_right).aestronglyMeasurable

omit [LocallyCompactSpace G] [μ.Regular] in
private theorem translate_smulL2 (c : G) (a : 𝕜) (g : Lp 𝕜 2 μ) :
    DomAddAct.mk c +ᵥ a • g = a • (DomAddAct.mk c +ᵥ g) :=
  (Lp.compMeasurePreservingₗ 𝕜 _ _).map_smul a g

theorem convL2_add_right (f : Lp 𝕜 1 μ) (g h : Lp 𝕜 2 μ) :
    convL2 f (g + h) = convL2 f g + convL2 f h := by
  simp only [convL2, DomAddAct.vadd_Lp_add, smul_add]
  exact MeasureTheory.integral_add (integrable_smul_translateL2 f g)
    (integrable_smul_translateL2 f h)

omit [LocallyCompactSpace G] [μ.Regular] in
theorem convL2_smul_right (c : 𝕜) (f : Lp 𝕜 1 μ) (g : Lp 𝕜 2 μ) :
    convL2 f (c • g) = c • convL2 f g := by
  simp only [convL2, translate_smulL2, smul_comm _ c, MeasureTheory.integral_smul]

theorem convL2_add_left (f g : Lp 𝕜 1 μ) (h : Lp 𝕜 2 μ) :
    convL2 (f + g) h = convL2 f h + convL2 g h := by
  rw [convL2, convL2, convL2, ← MeasureTheory.integral_add (integrable_smul_translateL2 f h)
    (integrable_smul_translateL2 g h)]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_add f g] with y hy
  rw [hy, Pi.add_apply, add_smul]

omit [LocallyCompactSpace G] [μ.Regular] in
theorem convL2_smul_left (c : 𝕜) (f : Lp 𝕜 1 μ) (g : Lp 𝕜 2 μ) :
    convL2 (c • f) g = c • convL2 f g := by
  rw [convL2, convL2, ← MeasureTheory.integral_smul]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_smul c f] with y hy
  rw [hy, Pi.smul_apply, smul_assoc]

omit [LocallyCompactSpace G] [μ.Regular] in
theorem convL2_zero_left (g : Lp 𝕜 2 μ) : convL2 (0 : Lp 𝕜 1 μ) g = 0 := by
  simpa using convL2_smul_left (0 : 𝕜) (0 : Lp 𝕜 1 μ) g

omit [LocallyCompactSpace G] [μ.Regular] in
theorem norm_convL2_le (f : Lp 𝕜 1 μ) (g : Lp 𝕜 2 μ) : ‖convL2 f g‖ ≤ ‖f‖ * ‖g‖ := by
  rw [L1.norm_eq_integral_norm f, ← integral_mul_const]
  exact (norm_integral_le_integral_norm _).trans_eq (by simp [norm_smul])

omit [LocallyCompactSpace G] [μ.Regular] in
theorem translate_convL2 (c : G) (f : Lp 𝕜 1 μ) (g : Lp 𝕜 2 μ) :
    DomAddAct.mk c +ᵥ convL2 f g = convL2 (DomAddAct.mk c +ᵥ f) g := by
  let L : Lp 𝕜 2 μ →ₗᵢ[𝕜] Lp 𝕜 2 μ :=
    Lp.compMeasurePreservingₗᵢ 𝕜 (c + ·) (measurePreserving_add_left μ c)
  calc DomAddAct.mk c +ᵥ convL2 f g
    _ = ∫ y, DomAddAct.mk c +ᵥ f y • (DomAddAct.mk (-y) +ᵥ g) ∂μ :=
      (L.integral_comp_comm _).symm
    _ = ∫ y, f y • (DomAddAct.mk (-y + c) +ᵥ g) ∂μ := by
      simp only [translate_smulL2, vadd_vadd, ← DomAddAct.mk_add]
    _ = ∫ y, f (c + y) • (DomAddAct.mk (-(c + y) + c) +ᵥ g) ∂μ :=
      (integral_add_left_eq_self (fun y ↦ f y • (DomAddAct.mk (-y + c) +ᵥ g)) c).symm
    _ = convL2 (DomAddAct.mk c +ᵥ f) g := by
      refine integral_congr_ae ?_
      filter_upwards [DomAddAct.vadd_Lp_ae_eq (DomAddAct.mk c) f] with y hy
      rw [hy]
      simp

theorem convL2_mul (f g : Lp 𝕜 1 μ) (h : Lp 𝕜 2 μ) :
    convL2 (f * g) h = convL2 f (convL2 g h) := by
  -- `convL2 · h` is continuous linear, so it commutes with the integral.
  let R : Lp 𝕜 1 μ →L[𝕜] Lp 𝕜 2 μ := LinearMap.mkContinuous
    { toFun := (convL2 · h), map_add' := (convL2_add_left · · h),
      map_smul' := (convL2_smul_left · · h) } ‖h‖
    fun k ↦ (norm_convL2_le k h).trans_eq (mul_comm _ _)
  calc convL2 (f * g) h
    _ = ∫ y, convL2 (f y • (DomAddAct.mk (-y) +ᵥ g)) h ∂μ :=
      (R.integral_comp_comm (integrable_smul_translate f g)).symm
    _ = convL2 f (convL2 g h) := by
      simp only [convL2_smul_left, ← translate_convL2]
      rfl

/-- The inner product with a convolution. -/
theorem inner_convL2 (h : Lp 𝕜 2 μ) (f : Lp 𝕜 1 μ) (g : Lp 𝕜 2 μ) :
    inner 𝕜 h (convL2 f g) = ∫ y, f y * inner 𝕜 h (DomAddAct.mk (-y) +ᵥ g) ∂μ := by
  rw [convL2, ← integral_inner (integrable_smul_translateL2 f g)]
  simp only [inner_smul_right]

omit [LocallyCompactSpace G] [μ.Regular] in
/-- Translations are unitary operators on `L²(G)`. -/
theorem inner_translate (c : G) (g h : Lp 𝕜 2 μ) :
    inner 𝕜 (DomAddAct.mk c +ᵥ g) h = inner 𝕜 g (DomAddAct.mk (-c) +ᵥ h) := by
  have e : h = DomAddAct.mk c +ᵥ (DomAddAct.mk (-c) +ᵥ h) := by
    rw [vadd_vadd, ← DomAddAct.mk_add, neg_add_cancel, DomAddAct.mk_zero, zero_vadd]
  conv_lhs => rw [e]
  exact (Lp.compMeasurePreservingₗᵢ 𝕜 (c + ·) (measurePreserving_add_left μ c)).inner_map_map g _

/-- On `L¹ ∩ L²`, the convolution `L¹ × L² → L²` is the product of `L¹(G)`. -/
theorem coeFn_convL2_toLp (f : Lp 𝕜 1 μ) {g : G → 𝕜} (hg : Integrable g μ) (hg2 : MemLp g 2 μ) :
    convL2 f (hg2.toLp g) =ᵐ[μ] (f * hg.toL1 g : Lp 𝕜 1 μ) := by
  -- Compare the integrals over sets of finite measure: both are
  -- `∫ y, f y * ∫ x in s, g (-y + x) ∂μ ∂μ`.
  have htr (y : G) {p : ℝ≥0∞} (K : Lp 𝕜 p μ) (hK : K =ᵐ[μ] g) (s : Set G) :
      ∫ x in s, (DomAddAct.mk (-y) +ᵥ K : Lp 𝕜 p μ) x ∂μ = ∫ x in s, g (-y + x) ∂μ := by
    refine integral_congr_ae (ae_restrict_of_ae ?_)
    filter_upwards [DomAddAct.vadd_Lp_ae_eq (DomAddAct.mk (-y)) K,
      (measurePreserving_add_left μ (-y)).quasiMeasurePreserving.tendsto_ae.eventually hK]
      with x hx hx'
    rw [hx, Equiv.symm_apply_apply, vadd_eq_add, hx']
  refine AEFinStronglyMeasurable.ae_eq_of_forall_setIntegral_eq
    (fun s _ hμs ↦ integrableOn_Lp_of_measure_ne_top _ one_le_two hμs.ne)
    (fun s _ _ ↦ (L1.integrable_coeFn _).integrableOn) (fun s hs hμs ↦ ?_)
    (MemLp.aefinStronglyMeasurable (Lp.memLp _) two_ne_zero ENNReal.ofNat_ne_top)
    (Integrable.aefinStronglyMeasurable (L1.integrable_coeFn _))
  have : Fact (μ s < ∞) := ⟨hμs⟩
  let T : Lp 𝕜 1 μ →L[𝕜] 𝕜 := (L1.integralCLM' 𝕜).comp (LpToLpRestrictCLM G 𝕜 𝕜 μ 1 s)
  have hT (h : Lp 𝕜 1 μ) : T h = ∫ x in s, h x ∂μ := by
    rw [ContinuousLinearMap.comp_apply, ← L1.integral_eq', L1.integral_eq_integral,
      integral_congr_ae (LpToLpRestrictCLM_coeFn 𝕜 s h)]
  calc ∫ x in s, convL2 f (hg2.toLp g) x ∂μ
    _ = ∫ y, f y * ∫ x in s, g (-y + x) ∂μ ∂μ := by
      rw [← L2.inner_indicatorConstLp_one hs hμs.ne, inner_convL2]
      simp_rw [L2.inner_indicatorConstLp_one hs hμs.ne, htr _ _ hg2.coeFn_toLp]
    _ = ∫ y, T (f y • (DomAddAct.mk (-y) +ᵥ hg.toL1 g)) ∂μ := by
      simp_rw [map_smul, hT, smul_eq_mul, htr _ _ hg.coeFn_toL1]
    _ = ∫ x in s, (f * hg.toL1 g : Lp 𝕜 1 μ) x ∂μ := by
      rw [← hT, mul_def, T.integral_comp_comm (integrable_smul_translate f _)]

theorem convL2_toL1_toLp_comm {f g : G → 𝕜} (hf : Integrable f μ) (hf2 : MemLp f 2 μ)
    (hg : Integrable g μ) (hg2 : MemLp g 2 μ) :
    convL2 (hf.toL1 f) (hg2.toLp g) = convL2 (hg.toL1 g) (hf2.toLp f) := by
  refine Lp.ext ((coeFn_convL2_toLp _ hg hg2).trans ?_)
  rw [mul_comm]
  exact (coeFn_convL2_toLp _ hf hf2).symm

variable (μ) in
/-- The regular representation of `L¹(G)` on `L²(G)`. -/
noncomputable def regularRep : Lp 𝕜 1 μ →ₙₐ[𝕜] Lp 𝕜 2 μ →L[𝕜] Lp 𝕜 2 μ where
  toFun f := LinearMap.mkContinuous
    { toFun := convL2 f
      map_add' := convL2_add_right f
      map_smul' := fun c g ↦ convL2_smul_right c f g } ‖f‖ (norm_convL2_le f)
  map_smul' c f := ContinuousLinearMap.ext fun g ↦ convL2_smul_left c f g
  map_zero' := ContinuousLinearMap.ext fun g ↦ convL2_zero_left g
  map_add' f g := ContinuousLinearMap.ext fun h ↦ convL2_add_left f g h
  map_mul' f g := ContinuousLinearMap.ext fun h ↦ convL2_mul f g h

@[simp]
theorem regularRep_apply (f : Lp 𝕜 1 μ) (g : Lp 𝕜 2 μ) : regularRep μ f g = convL2 f g :=
  rfl

variable (μ) in
/-- The regular representation turns the involution of `L¹(G)` into the adjoint. -/
theorem regularRep_involution (f : Lp 𝕜 1 μ) :
    regularRep μ (involution f) = star (regularRep μ f) := by
  -- `τ_y` is unitary with adjoint `τ_{-y}`, hence
  -- `⟪f ⋆ g, h⟫ = ∫ y, conj (f y) * ⟪g, τ_{-y} h⟫ ∂μ = ⟪g, involution f ⋆ h⟫`.
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.eq_adjoint_iff]
  intro g h
  rw [regularRep_apply, regularRep_apply, inner_convL2, ← inner_conj_symm, inner_convL2,
    ← integral_conj, ← integral_neg_eq_self (fun y ↦ f y * inner 𝕜 g (DomAddAct.mk (-y) +ᵥ h)) μ]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_involution f] with y hy
  rw [hy, map_mul, starRingEnd_self_apply, inner_conj_symm, inner_translate, neg_neg]

variable (μ) in
/-- The regular representation of `L¹(G)` is injective. -/
theorem regularRep_injective :
    Function.Injective (regularRep μ : Lp 𝕜 1 μ → Lp 𝕜 2 μ →L[𝕜] Lp 𝕜 2 μ) := by
  -- If `f ⋆ g = 0` for all `g ∈ L²`, then `f * u = 0` in `L¹` for all `u ∈ L¹ ∩ L²`
  -- (`coeFn_convL2_toLp`), hence `f = 0` by `exists_nhds_zero_norm_mul_sub_lt`.
  refine (injective_iff_map_eq_zero (regularRep μ)).2 fun f hf ↦ ?_
  refine norm_le_zero_iff.1 (le_of_forall_pos_lt_add fun ε hε ↦ ?_)
  rw [zero_add]
  obtain ⟨U, hU, h⟩ := exists_nhds_zero_norm_mul_sub_lt f hε
  obtain ⟨K, ⟨hK0, hK, hK'⟩, hKU⟩ := (isCompact_isClosed_basis_nhds (0 : G)).mem_iff.1 hU
  have hμK : μ K ≠ ∞ := hK.measure_lt_top.ne
  have hμK0 : 0 < μ.real K := ENNReal.toReal_pos (measure_pos_of_mem_nhds μ hK0).ne' hμK
  have hu1 : Integrable (K.indicator fun _ ↦ ((μ.real K)⁻¹ : 𝕜)) μ :=
    (integrableOn_const hμK).integrable_indicator hK'.measurableSet
  have hu2 : MemLp (K.indicator fun _ ↦ ((μ.real K)⁻¹ : 𝕜)) 2 μ :=
    memLp_indicator_const 2 hK'.nullMeasurableSet _ (Or.inr hμK)
  have hu : hu1.toL1 _ =ᵐ[μ] K.indicator fun _ ↦ ((μ.real K)⁻¹ : 𝕜) := hu1.coeFn_toL1
  have h0 : f * hu1.toL1 _ = 0 := by
    refine Lp.ext ((coeFn_convL2_toLp f hu1 hu2).symm.trans ?_)
    rw [← regularRep_apply, hf, zero_apply]
    exact (Lp.coeFn_zero 𝕜 2 μ).trans (Lp.coeFn_zero 𝕜 1 μ).symm
  have hn : ‖hu1.toL1 (K.indicator fun _ ↦ ((μ.real K)⁻¹ : 𝕜))‖ = 1 := by
    rw [L1.norm_eq_integral_norm, integral_congr_ae (hu.mono fun x hx ↦ by rw [hx]),
      integral_congr_ae (.of_forall fun x ↦ norm_indicator_eq_indicator_norm _ _),
      integral_indicator_const _ hK'.measurableSet]
    simp [hμK0.ne', abs_of_pos hμK0]
  have := h (hu1.toL1 _) ?_ hn ?_
  · rwa [mul_comm, h0, zero_sub, norm_neg] at this
  · filter_upwards [hu] with x hx
    rw [hx]
    by_cases hxK : x ∈ K <;> simp [hxK, abs_of_pos hμK0]
  · filter_upwards [hu] with x hx hxU
    rw [hx, Set.indicator_of_notMem fun hxK ↦ hxU (hKU hxK)]

/-- **Approximate units**: `u ⋆ g` is close to `g` in `L²` if `u ≥ 0` has integral `1` and is
supported near `0`. -/
theorem exists_nhds_zero_norm_convL2_sub_lt (g : Lp 𝕜 2 μ) {ε : ℝ} (hε : 0 < ε) :
    ∃ U ∈ 𝓝 (0 : G), ∀ u : Lp 𝕜 1 μ, (∀ᵐ x ∂μ, u x = (‖u x‖ : 𝕜)) → ‖u‖ = 1 →
      (∀ᵐ x ∂μ, x ∉ U → u x = 0) → ‖convL2 u g - g‖ < ε := by
  have hg : Continuous fun y : G ↦ ‖(DomAddAct.mk (-y) +ᵥ g) - g‖ :=
    ((continuous_translateL2 g).sub continuous_const).norm
  refine ⟨{y | ‖(DomAddAct.mk (-y) +ᵥ g) - g‖ < ε / 2},
    (hg.tendsto 0).eventually (gt_mem_nhds (by simpa using half_pos hε)), fun u hu hu1 huU ↦ ?_⟩
  have hu' : ∫ y, u y ∂μ = 1 := by
    rw [integral_congr_ae hu, integral_ofReal, ← L1.norm_eq_integral_norm, hu1, RCLike.ofReal_one]
  have key : convL2 u g - g = ∫ y, u y • ((DomAddAct.mk (-y) +ᵥ g) - g) ∂μ := by
    simp only [smul_sub]
    rw [MeasureTheory.integral_sub (integrable_smul_translateL2 u g)
      ((L1.integrable_coeFn u).smul_const g), integral_smul_const, hu', one_smul, convL2]
  calc ‖convL2 u g - g‖
    _ ≤ ∫ y, ‖u y • ((DomAddAct.mk (-y) +ᵥ g) - g)‖ ∂μ := key ▸ norm_integral_le_integral_norm _
    _ ≤ ∫ y, ‖u y‖ * (ε / 2) ∂μ := by
      refine integral_mono_of_nonneg (.of_forall fun _ ↦ norm_nonneg _)
        ((L1.integrable_coeFn u).norm.mul_const _) ?_
      filter_upwards [huU] with y hy
      by_cases hyU : ‖(DomAddAct.mk (-y) +ᵥ g) - g‖ < ε / 2
      · rw [norm_smul]
        gcongr
      · simp [hy hyU]
    _ < ε := by
      rw [integral_mul_const, ← L1.norm_eq_integral_norm, hu1, one_mul]
      exact half_lt_self hε

end MeasureTheory.L1
