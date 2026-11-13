/-
Copyright (c) 2026 Wenrong Zou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wenrong Zou
-/
module

public import PontryaginDuality.Convolution.L1Algebra
public import PontryaginDuality.Fourier.AddChar

import PontryaginDuality.Mathlib.MeasureTheory.Function.ContinuousMapDense

/-!
# The Fourier transform on a locally compact abelian group

Let `G` be a locally compact abelian group with a Haar measure `μ`. The Fourier transform of
`f : G → E` is the function on the Pontryagin dual of `G` given by
`χ ↦ ∫ x, χ (-x) • f x ∂μ`.

## Main definitions

* `AddPontryaginDual.fourierIntegral μ f`: the Fourier transform of `f : G → E` with respect to
  the measure `μ`, as a function `AddPontryaginDual G → E`.
* `AddPontryaginDual.fourierIntegralInv ν F`: the inverse Fourier transform of
  `F : AddPontryaginDual G → E` with respect to the measure `ν` on `AddPontryaginDual G`, as a
  function `G → E`. It is given by `x ↦ ∫ χ, χ x • F χ ∂ν`.

## Main statements

* `AddPontryaginDual.continuous_fourierIntegral`: the Fourier transform of an integrable function
  is continuous.
* `AddPontryaginDual.fourierIntegral_mul`: the Fourier transform turns the convolution product of
  `L¹(G)` into the pointwise product.

## Implementation notes

`VectorFourier.fourierIntegral e μ L f w = ∫ v, e (-L v w) • f v ∂μ` is the special case where `G`
is a module `V` and the character is `v ↦ e (L v w)`.
-/

@[expose] public section

open MeasureTheory Measure Filter Topology
open scoped ComplexConjugate

namespace AddPontryaginDual

variable {G E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [MeasurableSpace G]
  [AddCommGroup G] [TopologicalSpace G]

section Defs

variable {μ : Measure G} {f g : G → E} {χ : AddPontryaginDual G}

/-- The Fourier transform of `f : G → E` with respect to the measure `μ`, as a function on the
Pontryagin dual of `G`. It sends a character `χ` to `∫ x, χ (-x) • f x ∂μ`. -/
noncomputable def fourierIntegral (μ : Measure G) (f : G → E) (χ : AddPontryaginDual G) : E :=
  ∫ x, χ.toAddChar (-x) • f x ∂μ

/-- The inverse Fourier transform of `F : AddPontryaginDual G → E` with respect to the measure `ν`
on the Pontryagin dual of `G`. It sends `x : G` to `∫ χ, χ x • F χ ∂ν`. -/
noncomputable def fourierIntegralInv [MeasurableSpace (AddPontryaginDual G)]
    (ν : Measure (AddPontryaginDual G)) (F : AddPontryaginDual G → E) (x : G) : E :=
  ∫ χ, χ.toAddChar x • F χ ∂ν

theorem fourierIntegral_apply : fourierIntegral μ f χ = ∫ x, χ.toAddChar (-x) • f x ∂μ :=
  rfl

omit [MeasurableSpace G] in
theorem fourierIntegralInv_apply [MeasurableSpace (AddPontryaginDual G)]
    {ν : Measure (AddPontryaginDual G)} {F : AddPontryaginDual G → E} {x : G} :
    fourierIntegralInv ν F x = ∫ χ, χ.toAddChar x • F χ ∂ν :=
  rfl

theorem fourierIntegral_congr_ae (h : f =ᵐ[μ] g) : fourierIntegral μ f = fourierIntegral μ g := by
  ext χ
  refine integral_congr_ae ?_
  filter_upwards [h] with x hx
  rw [hx]

/-- The uniform norm of the Fourier transform of `f` is bounded by the `L¹` norm of `f`. -/
theorem norm_fourierIntegral_le_integral_norm (μ : Measure G) (f : G → E)
    (χ : AddPontryaginDual G) : ‖fourierIntegral μ f χ‖ ≤ ∫ x, ‖f x‖ ∂μ := by
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  simp_rw [Circle.norm_smul]

theorem fourierIntegral_const_smul (μ : Measure G) (c : ℂ) (f : G → E) :
    fourierIntegral μ (c • f) = c • fourierIntegral μ f := by
  ext χ
  simp only [fourierIntegral, Pi.smul_apply, smul_comm _ c, integral_smul]

theorem fourierIntegral_smul_const [CompleteSpace E] (μ : Measure G) (f : G → ℂ) (c : E) :
    fourierIntegral μ (fun x ↦ f x • c) = fun χ ↦ fourierIntegral μ f χ • c := by
  ext χ
  simp only [fourierIntegral]
  rw [← integral_smul_const]
  simp only [smul_assoc]

/-- The Fourier transform turns multiplication by a character into translation. -/
theorem fourierIntegral_toAddChar_smul (μ : Measure G) (η : AddPontryaginDual G) (f : G → E)
    (χ : AddPontryaginDual G) :
    fourierIntegral μ (fun x ↦ η.toAddChar x • f x) χ = fourierIntegral μ f (χ - η) := by
  simp only [fourierIntegral, toAddChar_sub_apply, AddChar.map_neg_eq_inv, smul_smul,
    div_eq_mul_inv, mul_inv, inv_inv]

end Defs

/-- If `c : X → Y → Circle` is jointly continuous and `F` is integrable, then
`x ↦ ∫ y, c x y • F y ∂ν` is continuous. -/
private theorem continuous_integral_circle_smul {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [WeaklyLocallyCompactSpace Y] [R1Space Y] [MeasurableSpace Y]
    [BorelSpace Y] {ν : Measure Y} [ν.Regular] {c : X → Y → Circle}
    (hc : Continuous (Function.uncurry c)) {F : Y → E} (hF : Integrable F ν) :
    Continuous fun x ↦ ∫ y, c x y • F y ∂ν := by
  have hcF {F : Y → E} (hF : Integrable F ν) (x : X) : Integrable (fun y ↦ c x y • F y) ν := by
    have hcx : Continuous (c x) := hc.comp (.prodMk_right x)
    simp_rw [← integrable_norm_iff (hcx.aestronglyMeasurable.fun_smul hF.1), Circle.norm_smul]
    exact hF.norm
  -- Approximate `F` in `L¹` by a continuous function `Φ` with compact support.
  refine continuous_of_uniform_approx_of_continuous fun u hu ↦ ?_
  obtain ⟨ε, hε, hεu⟩ := Metric.mem_uniformity_dist.1 hu
  obtain ⟨Φ, hΦ, hFΦ, hΦc, hΦi⟩ :=
    (memLp_one_iff_integrable.2 hF).exists_hasCompactSupport_eLpNorm_sub_le' ENNReal.one_ne_top
      (ε := ENNReal.ofReal (ε / 2)) (by positivity)
  rw [memLp_one_iff_integrable] at hΦi
  refine ⟨fun x ↦ ∫ y, c x y • Φ y ∂ν, ?_, fun x ↦ hεu ?_⟩
  · refine continuousOn_univ.1 (continuousOn_integral_of_compact_support hΦ.isCompact
      (hc.smul (hΦc.comp continuous_snd)).continuousOn fun x y _ hy ↦ ?_)
    rw [image_eq_zero_of_notMem_tsupport hy, smul_zero]
  · rw [dist_eq_norm, ← integral_sub (hcF hF x) (hcF hΦi x)]
    calc ‖∫ y, (c x y • F y - c x y • Φ y) ∂ν‖
      _ ≤ ∫ y, ‖(F - Φ) y‖ ∂ν :=
        (norm_integral_le_integral_norm _).trans_eq
          (by simp only [← smul_sub, Circle.norm_smul, Pi.sub_apply])
      _ ≤ ε / 2 := by
        rw [← ENNReal.ofReal_le_ofReal_iff (half_pos hε).le,
          ofReal_integral_norm_eq_lintegral_enorm (hF.sub hΦi),
          ← eLpNorm_one_eq_lintegral_enorm (hF.sub hΦi).aestronglyMeasurable]
        exact hFΦ
      _ < ε := half_lt_self hε

section AddGroup

variable [IsTopologicalAddGroup G] [LocallyCompactSpace G] [BorelSpace G]
  {μ : Measure G} [μ.IsAddHaarMeasure] [μ.Regular] {f : G → E}

omit [LocallyCompactSpace G] [μ.IsAddHaarMeasure] [μ.Regular] in
theorem fourierIntegral_convergent_iff (χ : AddPontryaginDual G) :
    Integrable (fun x ↦ χ.toAddChar (-x) • f x) μ ↔ Integrable f μ := by
  have aux {g : G → E} (hg : Integrable g μ) (η : AddPontryaginDual G) :
      Integrable (fun x ↦ η.toAddChar (-x) • g x) μ := by
    have c : Continuous fun x ↦ η.toAddChar (-x) := η.continuous_toAddChar.comp continuous_neg
    simp_rw [← integrable_norm_iff (c.aestronglyMeasurable.fun_smul hg.1), Circle.norm_smul]
    exact hg.norm
  refine ⟨fun hf ↦ ?_, fun hf ↦ aux hf χ⟩
  simpa [smul_smul] using aux hf (-χ)

omit [LocallyCompactSpace G] [μ.IsAddHaarMeasure] [μ.Regular] in
theorem fourierIntegral_add {g : G → E} (hf : Integrable f μ) (hg : Integrable g μ) :
    fourierIntegral μ (f + g) = fourierIntegral μ f + fourierIntegral μ g := by
  ext χ
  simp only [fourierIntegral, Pi.add_apply, smul_add]
  exact integral_add ((fourierIntegral_convergent_iff χ).2 hf)
    ((fourierIntegral_convergent_iff χ).2 hg)

omit [LocallyCompactSpace G] [μ.Regular] in
/-- The Fourier transform turns translation into multiplication by a character. -/
theorem fourierIntegral_comp_add_left (f : G → E) (a : G) (χ : AddPontryaginDual G) :
    fourierIntegral μ (fun x ↦ f (a + x)) χ = χ.toAddChar a • fourierIntegral μ f χ := by
  calc fourierIntegral μ (fun x ↦ f (a + x)) χ
    _ = ∫ x, χ.toAddChar a • χ.toAddChar (-(a + x)) • f (a + x) ∂μ := by
      refine integral_congr_ae (.of_forall fun x ↦ ?_)
      simp only [smul_smul, ← AddChar.map_add_eq_mul, neg_add_rev, add_neg_cancel_comm_assoc]
    _ = ∫ x, χ.toAddChar a • χ.toAddChar (-x) • f x ∂μ :=
      integral_add_left_eq_self (fun x ↦ χ.toAddChar a • χ.toAddChar (-x) • f x) a
    _ = χ.toAddChar a • fourierIntegral μ f χ := by
      simp only [Circle.smul_def (χ.toAddChar a), integral_smul, fourierIntegral]

/-- The Fourier transform turns the involution `f ↦ (x ↦ conj (f (-x)))` into the complex
conjugation. -/
theorem fourierIntegral_conj_neg (f : G → ℂ) (χ : AddPontryaginDual G) :
    fourierIntegral μ (fun x ↦ conj (f (-x))) χ = conj (fourierIntegral μ f χ) := by
  rw [fourierIntegral, fourierIntegral, ← integral_conj,
    ← integral_neg_eq_self (fun x ↦ conj (χ.toAddChar (-x) • f x)) μ]
  simp [Circle.smul_def, AddChar.map_neg_eq_inv, ← Circle.coe_inv_eq_conj]

omit [μ.IsAddHaarMeasure] in
/-- The Fourier transform of an integrable function is continuous. -/
theorem continuous_fourierIntegral (hf : Integrable f μ) : Continuous (fourierIntegral μ f) :=
  continuous_integral_circle_smul (c := fun (χ : AddPontryaginDual G) x ↦ χ.toAddChar (-x))
    (continuous_toAddChar_uncurry.comp (continuous_fst.prodMk continuous_snd.neg)) hf

omit [MeasurableSpace G] [BorelSpace G] in
/-- The inverse Fourier transform of an integrable function is continuous. -/
theorem continuous_fourierIntegralInv [MeasurableSpace (AddPontryaginDual G)]
    [BorelSpace (AddPontryaginDual G)] {ν : Measure (AddPontryaginDual G)} [ν.Regular]
    {F : AddPontryaginDual G → E} (hF : Integrable F ν) :
    Continuous (fourierIntegralInv ν F) :=
  continuous_integral_circle_smul (c := fun x (χ : AddPontryaginDual G) ↦ χ.toAddChar x)
    (continuous_toAddChar_uncurry.comp continuous_swap) hF

section Lp

/-! ### The Fourier transform of elements of `L¹(G)` -/

omit [IsTopologicalAddGroup G] [LocallyCompactSpace G] [BorelSpace G] [μ.IsAddHaarMeasure]
  [μ.Regular] in
theorem fourierIntegral_coeFn_zero (χ : AddPontryaginDual G) :
    fourierIntegral μ (0 : Lp E 1 μ) χ = 0 := by
  rw [fourierIntegral_congr_ae (Lp.coeFn_zero E 1 μ)]
  simp [fourierIntegral]

omit [LocallyCompactSpace G] [μ.IsAddHaarMeasure] [μ.Regular] in
theorem fourierIntegral_coeFn_add (f g : Lp E 1 μ) (χ : AddPontryaginDual G) :
    fourierIntegral μ (f + g : Lp E 1 μ) χ = fourierIntegral μ f χ + fourierIntegral μ g χ := by
  rw [fourierIntegral_congr_ae (Lp.coeFn_add f g),
    fourierIntegral_add (L1.integrable_coeFn f) (L1.integrable_coeFn g), Pi.add_apply]

omit [IsTopologicalAddGroup G] [LocallyCompactSpace G] [BorelSpace G] [μ.IsAddHaarMeasure]
  [μ.Regular] in
theorem fourierIntegral_coeFn_smul (c : ℂ) (f : Lp E 1 μ) (χ : AddPontryaginDual G) :
    fourierIntegral μ (c • f : Lp E 1 μ) χ = c • fourierIntegral μ f χ := by
  rw [fourierIntegral_congr_ae (Lp.coeFn_smul c f), fourierIntegral_const_smul, Pi.smul_apply]

omit [IsTopologicalAddGroup G] [LocallyCompactSpace G] [BorelSpace G] [μ.IsAddHaarMeasure]
  [μ.Regular] in
theorem norm_fourierIntegral_coeFn_le (f : Lp E 1 μ) (χ : AddPontryaginDual G) :
    ‖fourierIntegral μ f χ‖ ≤ ‖f‖ :=
  (norm_fourierIntegral_le_integral_norm μ f χ).trans_eq (L1.norm_eq_integral_norm f).symm

omit [LocallyCompactSpace G] [μ.Regular] in
theorem fourierIntegral_coeFn_vadd (a : G) (f : Lp E 1 μ) (χ : AddPontryaginDual G) :
    fourierIntegral μ (DomAddAct.mk a +ᵥ f : Lp E 1 μ) χ =
      χ.toAddChar a • fourierIntegral μ f χ := by
  rw [← fourierIntegral_comp_add_left]
  exact congr_fun (fourierIntegral_congr_ae (DomAddAct.vadd_Lp_ae_eq (DomAddAct.mk a) f)) χ

end Lp

/-- The Fourier transform turns the convolution product of `L¹(G)` into the pointwise product. -/
theorem fourierIntegral_mul (f g : Lp ℂ 1 μ) (χ : AddPontryaginDual G) :
    fourierIntegral μ (f * g : Lp ℂ 1 μ) χ = fourierIntegral μ f χ * fourierIntegral μ g χ := by
  -- `fourierIntegral μ · χ` is continuous linear, so it commutes with the integral.
  let T : Lp ℂ 1 μ →L[ℂ] ℂ := LinearMap.mkContinuous
    { toFun := fun h ↦ fourierIntegral μ h χ
      map_add' := fun h k ↦ fourierIntegral_coeFn_add h k χ
      map_smul' := fun c h ↦ fourierIntegral_coeFn_smul c h χ } 1
    fun h ↦ (norm_fourierIntegral_coeFn_le h χ).trans_eq (one_mul _).symm
  have hT (y : G) : T (DomAddAct.mk (-y) +ᵥ g) = χ.toAddChar (-y) • fourierIntegral μ g χ :=
    fourierIntegral_coeFn_vadd (-y) g χ
  calc fourierIntegral μ (f * g : Lp ℂ 1 μ) χ
    _ = ∫ y, T (f y • (DomAddAct.mk (-y) +ᵥ g)) ∂μ :=
      (T.integral_comp_comm (L1.integrable_smul_translate f g)).symm
    _ = ∫ y, χ.toAddChar (-y) • f y * fourierIntegral μ g χ ∂μ := by
      simp only [map_smul, hT, smul_eq_mul, Circle.smul_def, mul_left_comm, mul_assoc]
    _ = fourierIntegral μ f χ * fourierIntegral μ g χ := integral_mul_const _ _

theorem fourierIntegral_involution (f : Lp ℂ 1 μ) (χ : AddPontryaginDual G) :
    fourierIntegral μ (L1.involution f) χ = conj (fourierIntegral μ f χ) := by
  rw [fourierIntegral_congr_ae (L1.coeFn_involution f), fourierIntegral_conj_neg]

end AddGroup

end AddPontryaginDual
