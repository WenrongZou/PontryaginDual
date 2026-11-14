/-
Copyright (c) 2026 Wenrong Zou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wenrong Zou
-/
module

public import Mathlib.Analysis.Convolution
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.MeasureTheory.Function.LpSpace.DomAct.Continuous
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.Unique

import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import PontryaginDuality.Mathlib.MeasureTheory.Function.ContinuousMapDense

/-!
# The convolution algebra `L¹(G)`

For a locally compact additive group `G` with Haar measure `μ`, we make `L¹(G) = Lp 𝕜 1 μ` a
non-unital normed ring under convolution `f * g = ∫ y, f y • τ_y g ∂μ`, commutative if `G` is,
and define the involution `f ↦ (x ↦ conj (f (-x)))` for commutative `G`.

## Implementation notes

The product is an `L¹(G)`-valued Bochner integral rather than `MeasureTheory.convolution`, whose
integrability and associativity lemmas need `[SFinite μ]` and `[MeasurableAdd₂ G]`; these fail for
general locally compact groups. `coeFn_mul_of_hasCompactSupport` relates the two.

The existing `Star (Lp 𝕜 1 μ)` is pointwise conjugation, so `involution` is a plain function.

## TODO

* Make the involution a `StarRing` (probably needs a type synonym, and the modular function in the
  non-unimodular case).
* The multiplicative version.
-/

@[expose] public section

open MeasureTheory Measure Filter Topology
open scoped ENNReal ComplexConjugate Convolution

namespace MeasureTheory.L1

variable {G 𝕜 : Type*} [RCLike 𝕜] [MeasurableSpace G]

section AddGroup

variable [AddGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [LocallyCompactSpace G]
  [BorelSpace G] {μ : Measure G} [μ.IsAddHaarMeasure] [μ.Regular]

/-- Convolution `f * g = ∫ y, f y • τ_y g ∂μ`, where `τ_y g = (x ↦ g (-y + x))`. -/
noncomputable instance instMul : Mul (Lp 𝕜 1 μ) where
  mul f g := ∫ y, f y • (DomAddAct.mk (-y) +ᵥ g) ∂μ

omit [LocallyCompactSpace G] [μ.Regular] in
theorem mul_def (f g : Lp 𝕜 1 μ) : f * g = ∫ y, f y • (DomAddAct.mk (-y) +ᵥ g) ∂μ :=
  rfl

theorem continuous_translate (g : Lp 𝕜 1 μ) : Continuous fun y : G ↦ DomAddAct.mk (-y) +ᵥ g :=
  have : Fact ((1 : ℝ≥0∞) ≠ ∞) := ⟨ENNReal.one_ne_top⟩
  (DomAddAct.continuous_mk.comp continuous_neg).vadd continuous_const

theorem integrable_smul_translate (f g : Lp 𝕜 1 μ) :
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
  exact (((hφ' (ns n)).smul (continuous_translate g)).stronglyMeasurable_of_hasCompactSupport
    (hφ (ns n)).smul_right).aestronglyMeasurable

omit [LocallyCompactSpace G] [μ.Regular] in
protected theorem norm_mul_le (f g : Lp 𝕜 1 μ) : ‖f * g‖ ≤ ‖f‖ * ‖g‖ := by
  rw [L1.norm_eq_integral_norm f, ← integral_mul_const]
  exact (norm_integral_le_integral_norm _).trans_eq (by simp [norm_smul])

omit [LocallyCompactSpace G] [μ.Regular] in
theorem translate_smul (c : G) (a : 𝕜) (f : Lp 𝕜 1 μ) :
    DomAddAct.mk c +ᵥ a • f = a • (DomAddAct.mk c +ᵥ f) :=
  (Lp.compMeasurePreservingₗ 𝕜 _ _).map_smul a f

omit [LocallyCompactSpace G] [μ.Regular] in
theorem translate_mul (c : G) (f g : Lp 𝕜 1 μ) :
    DomAddAct.mk c +ᵥ (f * g) = (DomAddAct.mk c +ᵥ f) * g := by
  let L : Lp 𝕜 1 μ →ₗᵢ[𝕜] Lp 𝕜 1 μ :=
    Lp.compMeasurePreservingₗᵢ 𝕜 (c + ·) (measurePreserving_add_left μ c)
  calc DomAddAct.mk c +ᵥ (f * g)
    _ = ∫ y, DomAddAct.mk c +ᵥ f y • (DomAddAct.mk (-y) +ᵥ g) ∂μ :=
      (L.integral_comp_comm _).symm
    _ = ∫ y, f y • (DomAddAct.mk (-y + c) +ᵥ g) ∂μ := by
      simp only [translate_smul, vadd_vadd, ← DomAddAct.mk_add]
    _ = ∫ y, f (c + y) • (DomAddAct.mk (-(c + y) + c) +ᵥ g) ∂μ :=
      (integral_add_left_eq_self (fun y ↦ f y • (DomAddAct.mk (-y + c) +ᵥ g)) c).symm
    _ = (DomAddAct.mk c +ᵥ f) * g := by
      refine integral_congr_ae ?_
      filter_upwards [DomAddAct.vadd_Lp_ae_eq (DomAddAct.mk c) f] with y hy
      rw [hy]
      simp

protected theorem mul_add (f g h : Lp 𝕜 1 μ) : f * (g + h) = f * g + f * h := by
  simp only [mul_def, DomAddAct.vadd_Lp_add, smul_add]
  exact MeasureTheory.integral_add (integrable_smul_translate f g)
    (integrable_smul_translate f h)

protected theorem add_mul (f g h : Lp 𝕜 1 μ) : (f + g) * h = f * h + g * h := by
  rw [mul_def, mul_def, mul_def,
    ← MeasureTheory.integral_add (integrable_smul_translate f h) (integrable_smul_translate g h)]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_add f g] with y hy
  rw [hy, Pi.add_apply, add_smul]

omit [LocallyCompactSpace G] [μ.Regular] in
protected theorem zero_mul (f : Lp 𝕜 1 μ) : 0 * f = 0 := by
  refine (integral_congr_ae ?_).trans (MeasureTheory.integral_zero _ _)
  filter_upwards [Lp.coeFn_zero 𝕜 1 μ] with y hy
  rw [hy, Pi.zero_apply, zero_smul]

omit [LocallyCompactSpace G] [μ.Regular] in
protected theorem mul_zero (f : Lp 𝕜 1 μ) : f * 0 = 0 := by
  simp [mul_def]

omit [LocallyCompactSpace G] [μ.Regular] in
protected theorem smul_mul (c : 𝕜) (f g : Lp 𝕜 1 μ) : (c • f) * g = c • (f * g) := by
  rw [mul_def, mul_def, ← MeasureTheory.integral_smul]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_smul c f] with y hy
  rw [hy, Pi.smul_apply, smul_assoc]

omit [LocallyCompactSpace G] [μ.Regular] in
protected theorem mul_smul (c : 𝕜) (f g : Lp 𝕜 1 μ) : f * (c • g) = c • (f * g) := by
  simp only [mul_def, translate_smul, smul_comm _ c, MeasureTheory.integral_smul]

protected theorem mul_assoc (f g h : Lp 𝕜 1 μ) : f * g * h = f * (g * h) := by
  -- `· * h` is continuous linear, so it commutes with the integral.
  let R : Lp 𝕜 1 μ →L[𝕜] Lp 𝕜 1 μ := LinearMap.mkContinuous
    { toFun := (· * h), map_add' := (L1.add_mul · · h), map_smul' := (L1.smul_mul · · h) } ‖h‖
    fun k ↦ (L1.norm_mul_le k h).trans_eq (mul_comm _ _)
  calc f * g * h
    _ = ∫ y, f y • (DomAddAct.mk (-y) +ᵥ g) * h ∂μ :=
      (R.integral_comp_comm (integrable_smul_translate f g)).symm
    _ = f * (g * h) := by
      simp only [L1.smul_mul, ← translate_mul]
      rfl

noncomputable instance instNonUnitalNormedRing : NonUnitalNormedRing (Lp 𝕜 1 μ) where
  __ := (inferInstance : NormedAddCommGroup (Lp 𝕜 1 μ))
  left_distrib := L1.mul_add
  right_distrib := L1.add_mul
  zero_mul := L1.zero_mul
  mul_zero := L1.mul_zero
  mul_assoc := L1.mul_assoc
  norm_mul_le := L1.norm_mul_le

instance instIsScalarTower : IsScalarTower 𝕜 (Lp 𝕜 1 μ) (Lp 𝕜 1 μ) where
  smul_assoc := L1.smul_mul

instance instSMulCommClass : SMulCommClass 𝕜 (Lp 𝕜 1 μ) (Lp 𝕜 1 μ) where
  smul_comm c f g := (L1.mul_smul c f g).symm

/-- **Approximate units**: `u * f` is close to `f` if `u ≥ 0` has integral `1` and is supported
near `0`. -/
theorem exists_nhds_zero_norm_mul_sub_lt (f : Lp 𝕜 1 μ) {ε : ℝ} (hε : 0 < ε) :
    ∃ U ∈ 𝓝 (0 : G), ∀ u : Lp 𝕜 1 μ, (∀ᵐ x ∂μ, u x = (‖u x‖ : 𝕜)) → ‖u‖ = 1 →
      (∀ᵐ x ∂μ, x ∉ U → u x = 0) → ‖u * f - f‖ < ε := by
  have hf : Continuous fun y : G ↦ ‖(DomAddAct.mk (-y) +ᵥ f) - f‖ :=
    ((continuous_translate f).sub continuous_const).norm
  refine ⟨{y | ‖(DomAddAct.mk (-y) +ᵥ f) - f‖ < ε / 2},
    (hf.tendsto 0).eventually (gt_mem_nhds (by simpa using half_pos hε)), fun u hu hu1 huU ↦ ?_⟩
  have hu' : ∫ y, u y ∂μ = 1 := by
    rw [integral_congr_ae hu, integral_ofReal, ← L1.norm_eq_integral_norm, hu1, RCLike.ofReal_one]
  have key : u * f - f = ∫ y, u y • ((DomAddAct.mk (-y) +ᵥ f) - f) ∂μ := by
    simp only [smul_sub]
    rw [MeasureTheory.integral_sub (integrable_smul_translate u f)
      ((L1.integrable_coeFn u).smul_const f), integral_smul_const, hu', one_smul, mul_def]
  calc ‖u * f - f‖
    _ ≤ ∫ y, ‖u y • ((DomAddAct.mk (-y) +ᵥ f) - f)‖ ∂μ := key ▸ norm_integral_le_integral_norm _
    _ ≤ ∫ y, ‖u y‖ * (ε / 2) ∂μ := by
      refine integral_mono_of_nonneg (.of_forall fun _ ↦ norm_nonneg _)
        ((L1.integrable_coeFn u).norm.mul_const _) ?_
      filter_upwards [huU] with y hy
      by_cases hyU : ‖(DomAddAct.mk (-y) +ᵥ f) - f‖ < ε / 2
      · rw [norm_smul]
        gcongr
      · simp [hy hyU]
    _ < ε := by
      rw [integral_mul_const, ← L1.norm_eq_integral_norm, hu1, one_mul]
      exact half_lt_self hε

/-- **Approximate units**: for every `f` and `ε > 0`, there is `u` with `‖u‖ = 1` and
`‖u * f - f‖ < ε`. -/
theorem exists_norm_eq_one_norm_mul_sub_lt (f : Lp 𝕜 1 μ) {ε : ℝ} (hε : 0 < ε) :
    ∃ u : Lp 𝕜 1 μ, ‖u‖ = 1 ∧ ‖u * f - f‖ < ε := by
  -- Take the normalized indicator function of a small compact neighborhood of `0`.
  obtain ⟨U, hU, h⟩ := exists_nhds_zero_norm_mul_sub_lt f hε
  obtain ⟨K, ⟨hK0, hK, hK'⟩, hKU⟩ := (isCompact_isClosed_basis_nhds (0 : G)).mem_iff.1 hU
  have hμK : μ K ≠ ∞ := hK.measure_lt_top.ne
  have hμK0 : 0 < μ.real K := ENNReal.toReal_pos (measure_pos_of_mem_nhds μ hK0).ne' hμK
  let u : Lp 𝕜 1 μ := indicatorConstLp 1 hK'.measurableSet hμK ((μ.real K)⁻¹ : 𝕜)
  have hu : u =ᵐ[μ] K.indicator fun _ ↦ ((μ.real K)⁻¹ : 𝕜) := indicatorConstLp_coeFn
  have hu1 : ‖u‖ = 1 := by
    simp [u, norm_indicatorConstLp one_ne_zero ENNReal.one_ne_top, hμK0.ne', abs_of_pos hμK0]
  refine ⟨u, hu1, h u ?_ hu1 ?_⟩
  · filter_upwards [hu] with x hx
    rw [hx]
    by_cases hxK : x ∈ K <;> simp [hxK, abs_of_pos hμK0]
  · filter_upwards [hu] with x hx hxU
    rw [hx, Set.indicator_of_notMem fun hxK ↦ hxU (hKU hxK)]

end AddGroup

section AddCommGroup

variable [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [LocallyCompactSpace G]
  [BorelSpace G] {μ : Measure G} [μ.IsAddHaarMeasure] [μ.Regular]

/-- On continuous compactly supported functions, the product is `MeasureTheory.convolution`. -/
theorem coeFn_mul_of_hasCompactSupport {f g : G → 𝕜} (hf : Continuous f)
    (hf' : HasCompactSupport f) (hg : Continuous g) (hg' : HasCompactSupport g) :
    ((hf.integrable_of_hasCompactSupport hf').toL1 f *
      (hg.integrable_of_hasCompactSupport hg').toL1 g : Lp 𝕜 1 μ) =ᵐ[μ]
      f ⋆[.mul 𝕜 𝕜, μ] g := by
  set F : Lp 𝕜 1 μ := (hf.integrable_of_hasCompactSupport hf').toL1 f
  set K : Lp 𝕜 1 μ := (hg.integrable_of_hasCompactSupport hg').toL1 g
  have hF : F =ᵐ[μ] f := Integrable.coeFn_toL1 _
  have hK : K =ᵐ[μ] g := Integrable.coeFn_toL1 _
  let k (x y : G) : 𝕜 := f y * g (x - y)
  have hk : Continuous (Function.uncurry k) := by fun_prop
  have hk' : HasCompactSupport (Function.uncurry k) := by
    refine .intro ((hg'.isCompact.add hf'.isCompact).prod hf'.isCompact) fun p hp ↦ ?_
    by_contra h
    obtain ⟨h1, h2⟩ := mul_ne_zero_iff.1 h
    exact hp ⟨⟨_, subset_tsupport _ h2, _, subset_tsupport _ h1, sub_add_cancel _ _⟩,
      subset_tsupport _ h1⟩
  have hfg : Integrable (f ⋆[.mul 𝕜 𝕜, μ] g) μ := by
    refine (hg'.continuous_convolution_right _ hf.locallyIntegrable
      hg).integrable_of_hasCompactSupport (.intro (hg'.isCompact.add hf'.isCompact) fun x hx ↦ ?_)
    by_contra h
    exact hx (Set.add_subset_add (subset_tsupport g) (subset_tsupport f)
      (support_convolution_subset_swap _ h))
  -- Compare the integrals over sets of finite measure, using Fubini for `k`.
  refine Integrable.ae_eq_of_forall_setIntegral_eq _ _ (L1.integrable_coeFn _) hfg
    fun s hs hμs ↦ ?_
  have : Fact (μ s < ∞) := ⟨hμs⟩
  let T : Lp 𝕜 1 μ →L[𝕜] 𝕜 := (L1.integralCLM' 𝕜).comp (LpToLpRestrictCLM G 𝕜 𝕜 μ 1 s)
  have hT (h : Lp 𝕜 1 μ) : T h = ∫ x in s, h x ∂μ := by
    rw [ContinuousLinearMap.comp_apply, ← L1.integral_eq', L1.integral_eq_integral,
      integral_congr_ae (LpToLpRestrictCLM_coeFn 𝕜 s h)]
  calc ∫ x in s, (F * K : Lp 𝕜 1 μ) x ∂μ
    _ = ∫ y, T (F y • (DomAddAct.mk (-y) +ᵥ K)) ∂μ := by
      rw [← hT, mul_def, T.integral_comp_comm (integrable_smul_translate F K)]
    _ = ∫ y, ∫ x in s, k x y ∂μ ∂μ := by
      refine integral_congr_ae ?_
      filter_upwards [hF] with y hy
      rw [map_smul, hT, smul_eq_mul, hy, ← integral_const_mul]
      refine integral_congr_ae (ae_restrict_of_ae ?_)
      filter_upwards [DomAddAct.vadd_Lp_ae_eq (DomAddAct.mk (-y)) K,
        (measurePreserving_add_left μ (-y)).quasiMeasurePreserving.tendsto_ae.eventually hK]
        with x hx hx'
      rw [hx, Equiv.symm_apply_apply, vadd_eq_add, hx', neg_add_eq_sub]
    _ = ∫ x in s, ∫ y, k x y ∂μ ∂μ := (integral_integral_swap_of_hasCompactSupport hk hk').symm

protected theorem mul_comm (f g : Lp 𝕜 1 μ) : f * g = g * f := by
  -- By density, we may assume that `f` and `g` are continuous with compact support.
  refine (Lp.dense_hasCompactSupport_continuous ENNReal.one_ne_top).denseRange_val.induction_on₂
    (isClosed_eq (continuous_fst.mul continuous_snd) (continuous_snd.mul continuous_fst))
    ?_ f g
  rintro ⟨f, φ, hf, hφ', hφ⟩ ⟨g, ψ, hg, hψ', hψ⟩
  obtain rfl : f = (hφ.integrable_of_hasCompactSupport hφ').toL1 φ :=
    Lp.ext (hf.trans (Integrable.coeFn_toL1 _).symm)
  obtain rfl : g = (hψ.integrable_of_hasCompactSupport hψ').toL1 ψ :=
    Lp.ext (hg.trans (Integrable.coeFn_toL1 _).symm)
  refine Lp.ext ((coeFn_mul_of_hasCompactSupport hφ hφ' hψ hψ').trans ?_)
  rw [← convolution_flip, ContinuousLinearMap.flip_mul]
  exact (coeFn_mul_of_hasCompactSupport hψ hψ' hφ hφ').symm

noncomputable instance instNonUnitalNormedCommRing : NonUnitalNormedCommRing (Lp 𝕜 1 μ) where
  __ := (inferInstance : NonUnitalNormedRing (Lp 𝕜 1 μ))
  mul_comm := L1.mul_comm

/-- The involution `f ↦ (x ↦ conj (f (-x)))` of `L¹(G)`. -/
noncomputable def involution (f : Lp 𝕜 1 μ) : Lp 𝕜 1 μ :=
  Lp.compMeasurePreserving Neg.neg (measurePreserving_neg μ) (star f)

theorem coeFn_involution (f : Lp 𝕜 1 μ) : involution f =ᵐ[μ] fun x ↦ conj (f (-x)) :=
  (Lp.coeFn_compMeasurePreserving _ _).trans
    ((Lp.coeFn_star f).comp_tendsto (measurePreserving_neg μ).quasiMeasurePreserving.tendsto_ae)

private theorem tendsto_neg_ae : Tendsto (Neg.neg : G → G) (ae μ) (ae μ) :=
  (measurePreserving_neg μ).quasiMeasurePreserving.tendsto_ae

@[simp]
theorem involution_involution (f : Lp 𝕜 1 μ) : involution (involution f) = f := by
  ext1
  filter_upwards [coeFn_involution (involution f),
    tendsto_neg_ae.eventually (coeFn_involution f)] with x h1 h2
  simp only [h1, h2, neg_neg, starRingEnd_self_apply]

@[simp]
theorem norm_involution (f : Lp 𝕜 1 μ) : ‖involution f‖ = ‖f‖ := by
  rw [involution, Lp.norm_compMeasurePreserving, Lp.norm_def, Lp.norm_def,
    eLpNorm_congr_ae (Lp.coeFn_star f), eLpNorm_star]

@[simp]
theorem involution_add (f g : Lp 𝕜 1 μ) : involution (f + g) = involution f + involution g := by
  ext1
  filter_upwards [coeFn_involution (f + g), coeFn_involution f, coeFn_involution g,
    Lp.coeFn_add (involution f) (involution g),
    tendsto_neg_ae.eventually (Lp.coeFn_add f g)] with x h1 h2 h3 h4 h5
  rw [h1, h4, Pi.add_apply, h2, h3, h5, Pi.add_apply, map_add]

@[simp]
theorem involution_smul (c : 𝕜) (f : Lp 𝕜 1 μ) : involution (c • f) = conj c • involution f := by
  ext1
  filter_upwards [coeFn_involution (c • f), coeFn_involution f,
    Lp.coeFn_smul (conj c) (involution f),
    tendsto_neg_ae.eventually (Lp.coeFn_smul c f)] with x h1 h2 h3 h4
  rw [h1, h3, Pi.smul_apply, h2, h4, Pi.smul_apply, smul_eq_mul, smul_eq_mul, map_mul]

@[simp]
theorem involution_sub (f g : Lp 𝕜 1 μ) : involution (f - g) = involution f - involution g := by
  have h : involution (-g) = -involution g := by simpa using involution_smul (-1 : 𝕜) g
  rw [sub_eq_add_neg, involution_add, h, sub_eq_add_neg]

theorem continuous_involution : Continuous (involution : Lp 𝕜 1 μ → Lp 𝕜 1 μ) :=
  (Isometry.of_dist_eq fun f g ↦ by
    rw [dist_eq_norm, dist_eq_norm, ← involution_sub, norm_involution]).continuous

theorem involution_translate (c : G) (f : Lp 𝕜 1 μ) :
    involution (DomAddAct.mk c +ᵥ f) = DomAddAct.mk (-c) +ᵥ involution f := by
  ext1
  filter_upwards [coeFn_involution (DomAddAct.mk c +ᵥ f),
    tendsto_neg_ae.eventually (DomAddAct.vadd_Lp_ae_eq (DomAddAct.mk c) f),
    DomAddAct.vadd_Lp_ae_eq (DomAddAct.mk (-c)) (involution f),
    (measurePreserving_add_left μ (-c)).quasiMeasurePreserving.tendsto_ae.eventually
      (coeFn_involution f)] with x h1 h2 h3 h4
  simp only [Equiv.symm_apply_apply, vadd_eq_add] at h2 h3
  rw [h1, h2, h3, h4, neg_add_rev, neg_neg, add_comm]

@[simp]
theorem involution_mul (f g : Lp 𝕜 1 μ) : involution (f * g) = involution f * involution g := by
  let L : Lp 𝕜 1 μ →SL[starRingEnd 𝕜] Lp 𝕜 1 μ := LinearMap.mkContinuous
    { toFun := involution, map_add' := involution_add, map_smul' := involution_smul } 1
    fun h ↦ (norm_involution h).le.trans_eq (one_mul _).symm
  calc involution (f * g)
    _ = ∫ y, involution (f y • (DomAddAct.mk (-y) +ᵥ g)) ∂μ :=
      (L.integral_comp_commSL RCLike.conj_smul (integrable_smul_translate f g)).symm
    _ = ∫ y, conj (f y) • (DomAddAct.mk y +ᵥ involution g) ∂μ := by
      simp only [involution_smul, involution_translate, neg_neg]
    _ = ∫ y, conj (f (-y)) • (DomAddAct.mk (-y) +ᵥ involution g) ∂μ :=
      (integral_neg_eq_self (fun y ↦ conj (f y) • (DomAddAct.mk y +ᵥ involution g)) μ).symm
    _ = involution f * involution g := by
      refine integral_congr_ae ?_
      filter_upwards [coeFn_involution f] with y hy
      rw [hy]

end AddCommGroup

end MeasureTheory.L1
