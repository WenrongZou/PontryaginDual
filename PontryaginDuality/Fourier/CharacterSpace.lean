/-
Copyright (c) 2026 Wenrong Zou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wenrong Zou
-/
module

public import Mathlib.Topology.Algebra.Module.Spaces.CharacterSpace
public import PontryaginDuality.Fourier.Basic

/-!
# The Pontryagin dual as the character space of `L¹(G)`

Let `G` be a locally compact abelian group with a regular Haar measure `μ`. Every
`χ : AddPontryaginDual G` defines a character of the commutative Banach algebra `L¹(G)`, namely
`f ↦ fourierIntegral μ f χ`. We state that this gives a homeomorphism between
`AddPontryaginDual G` and the character space of `L¹(G)` (i.e. its Gelfand spectrum): the Fourier
transform is the Gelfand transform of `L¹(G)`.

## Main definitions

* `AddPontryaginDual.fourierIntegralCLM μ χ`: the continuous linear map
  `f ↦ fourierIntegral μ f χ` on `L¹(G; E)`.
* `AddPontryaginDual.toCharacterSpace μ χ`: the character of `L¹(G)` associated with `χ`.
* `AddPontryaginDual.characterSpaceHomeomorph μ`: the homeomorphism
  `AddPontryaginDual G ≃ₜ characterSpace ℂ (Lp ℂ 1 μ)`.

## Main statements

* `AddPontryaginDual.toCharacterSpace_surjective`: every character of `L¹(G)` comes from a unique
  element of `AddPontryaginDual G`.
* `AddPontryaginDual.isHomeomorph_toCharacterSpace`: the compact-open topology on
  `AddPontryaginDual G` agrees with the weak-* topology on the character space.

## References

* [G. B. Folland, *A Course in Abstract Harmonic Analysis*, Section 4.1][folland2016]
-/

@[expose] public section

open MeasureTheory Measure Filter Topology WeakDual
open scoped ENNReal

namespace AddPontryaginDual

variable {G E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [LocallyCompactSpace G]
  [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsAddHaarMeasure] [μ.Regular]

/-- The Fourier transform at `χ : AddPontryaginDual G`, as a continuous linear map on
`L¹(G; E)`. -/
noncomputable def fourierIntegralCLM (χ : AddPontryaginDual G) : Lp E 1 μ →L[ℂ] E :=
  LinearMap.mkContinuous
    { toFun := fun f ↦ fourierIntegral μ f χ
      map_add' := fun f g ↦ fourierIntegral_coeFn_add f g χ
      map_smul' := fun c f ↦ fourierIntegral_coeFn_smul c f χ } 1
    fun f ↦ (norm_fourierIntegral_coeFn_le f χ).trans_eq (one_mul _).symm

omit [LocallyCompactSpace G] [μ.IsAddHaarMeasure] [μ.Regular] in
@[simp]
theorem fourierIntegralCLM_apply (χ : AddPontryaginDual G) (f : Lp E 1 μ) :
    fourierIntegralCLM μ χ f = fourierIntegral μ f χ :=
  rfl

omit [LocallyCompactSpace G] [μ.IsAddHaarMeasure] [μ.Regular] in
theorem norm_fourierIntegralCLM_le (χ : AddPontryaginDual G) :
    ‖(fourierIntegralCLM μ χ : Lp E 1 μ →L[ℂ] E)‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

/-- The linear functional `f ↦ fourierIntegral μ f χ` is a character of the Banach algebra
`L¹(G)`. -/
theorem toWeakDual_fourierIntegralCLM_mem_characterSpace (χ : AddPontryaginDual G) :
    StrongDual.toWeakDual (fourierIntegralCLM μ χ) ∈ characterSpace ℂ (Lp ℂ 1 μ) := by
  refine ⟨fun h ↦ ?_, fun f g ↦ fourierIntegral_mul f g χ⟩
  -- If `K` is a compact neighborhood of `0`, the Fourier transform of `χ • 1_K` at `χ` is `μ K`.
  obtain ⟨K, hK0, hK, hK'⟩ := exists_mem_nhds_isCompact_isClosed (0 : G)
  have hg : Integrable (K.indicator fun _ ↦ (1 : ℂ)) μ :=
    (integrableOn_const hK.measure_lt_top.ne).integrable_indicator hK'.measurableSet
  have hf : Integrable (fun x ↦ χ.toAddChar x • K.indicator (fun _ ↦ (1 : ℂ)) x) μ := by
    simpa [AddChar.map_neg_eq_inv] using (fourierIntegral_convergent_iff (-χ)).2 hg
  have h0 : fourierIntegral μ (hf.toL1 _) χ = 0 := DFunLike.congr_fun h (hf.toL1 _)
  rw [fourierIntegral_congr_ae hf.coeFn_toL1, fourierIntegral_toAddChar_smul, sub_self] at h0
  simp only [fourierIntegral, toAddChar_zero_apply, one_smul,
    integral_indicator_const _ hK'.measurableSet, smul_eq_zero, one_ne_zero, or_false] at h0
  exact (ENNReal.toReal_pos (measure_pos_of_mem_nhds μ hK0).ne' hK.measure_lt_top.ne).ne' h0

/-- The character of the Banach algebra `L¹(G)` associated with `χ : AddPontryaginDual G`,
namely `f ↦ fourierIntegral μ f χ`. -/
noncomputable def toCharacterSpace (χ : AddPontryaginDual G) : characterSpace ℂ (Lp ℂ 1 μ) :=
  ⟨StrongDual.toWeakDual (fourierIntegralCLM μ χ),
    toWeakDual_fourierIntegralCLM_mem_characterSpace μ χ⟩

@[simp]
theorem toCharacterSpace_apply (χ : AddPontryaginDual G) (f : Lp ℂ 1 μ) :
    toCharacterSpace μ χ f = fourierIntegral μ f χ :=
  rfl

private theorem exists_apply_ne_zero (Φ : characterSpace ℂ (Lp ℂ 1 μ)) : ∃ f, Φ f ≠ 0 := by
  by_contra! h
  exact Φ.2.1 (ContinuousLinearMap.ext h)

private theorem continuous_mk_vadd (f : Lp ℂ 1 μ) :
    Continuous fun a : G ↦ DomAddAct.mk a +ᵥ f :=
  have : Fact ((1 : ℝ≥0∞) ≠ ∞) := ⟨ENNReal.one_ne_top⟩
  DomAddAct.continuous_mk.vadd continuous_const

/-- A bounded additive character with values in `ℂ` has norm one. -/
private theorem norm_addChar_eq_one {H : Type*} [AddGroup H] {ψ : AddChar H ℂ} {C : ℝ}
    (hC : ∀ x, ‖ψ x‖ ≤ C) (x : H) : ‖ψ x‖ = 1 := by
  have h (y : H) : ‖ψ y‖ ≤ 1 := by
    by_contra! hy
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt C hy
    exact (hC (n • y)).not_gt (by rwa [AddChar.map_nsmul_eq_pow, norm_pow])
  refine (h x).antisymm ?_
  calc 1 = ‖ψ x‖ * ‖ψ (-x)‖ := by
        rw [← norm_mul, ← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one,
          norm_one]
    _ ≤ ‖ψ x‖ * 1 := by gcongr; exact h (-x)
    _ = ‖ψ x‖ := mul_one _

/-- Different characters of `G` define different characters of `L¹(G)`. -/
theorem toCharacterSpace_injective : Function.Injective (toCharacterSpace μ) := by
  -- If `fourierIntegral μ f χ ≠ 0`, then `χ a` is the quotient of the Fourier transforms at `χ`
  -- of the translate `τ_a f` and of `f`.
  intro χ η h
  obtain ⟨f, hf⟩ := exists_apply_ne_zero μ (toCharacterSpace μ χ)
  refine toAddChar_injective (DFunLike.ext _ _ fun a ↦ Circle.ext ?_)
  have h1 := DFunLike.congr_fun h (DomAddAct.mk a +ᵥ f)
  have h2 := DFunLike.congr_fun h f
  simp only [toCharacterSpace_apply, fourierIntegral_coeFn_vadd, Circle.smul_def,
    smul_eq_mul] at h1 h2 hf
  rw [← h2] at h1
  exact mul_right_cancel₀ hf h1

/-- Every character of `L¹(G)` is of the form `f ↦ fourierIntegral μ f χ`. -/
theorem toCharacterSpace_surjective : Function.Surjective (toCharacterSpace μ) := by
  intro Φ
  obtain ⟨f, hf⟩ := exists_apply_ne_zero μ Φ
  -- Set `ψ a = Φ (τ_a f) / Φ f`. Then `Φ (τ_a g) = ψ a * Φ g` for all `g`, by `L1.translate_mul`.
  have key (a : G) (g : Lp ℂ 1 μ) :
      Φ (DomAddAct.mk a +ᵥ g) = Φ (DomAddAct.mk a +ᵥ f) / Φ f * Φ g := by
    rw [div_mul_eq_mul_div, eq_div_iff hf, ← map_mul, ← map_mul, ← L1.translate_mul,
      ← L1.translate_mul, mul_comm]
  -- Hence `ψ` is an additive character. It is bounded, hence it has values in the unit circle.
  let ψ : AddChar G ℂ :=
    { toFun := fun a ↦ Φ (DomAddAct.mk a +ᵥ f) / Φ f
      map_zero_eq_one' := by simp [div_self hf]
      map_add_eq_mul' := fun a b ↦ by
        simp only [DomAddAct.mk_add, ← vadd_vadd]
        rw [key b, mul_div_assoc, mul_comm] }
  have hψ (a : G) : ‖ψ a‖ = 1 := by
    refine norm_addChar_eq_one (C := ‖CharacterSpace.toCLM Φ‖ * ‖f‖ / ‖Φ f‖) (fun x ↦ ?_) a
    rw [show ψ x = Φ (DomAddAct.mk x +ᵥ f) / Φ f from rfl, norm_div]
    gcongr
    exact ((CharacterSpace.toCLM Φ).le_opNorm _).trans_eq (by rw [DomAddAct.norm_vadd_Lp])
  have hψc : Continuous ψ := ((map_continuous Φ).comp (continuous_mk_vadd μ f)).div_const _
  let ψ' : AddChar G Circle :=
    { toFun := fun a ↦ ⟨ψ a, mem_sphere_zero_iff_norm.2 (hψ a)⟩
      map_zero_eq_one' := Circle.ext ψ.map_zero_eq_one
      map_add_eq_mul' := fun a b ↦ Circle.ext (ψ.map_add_eq_mul a b) }
  refine ⟨ofAddChar ψ' (hψc.subtype_mk _), CharacterSpace.ext fun g ↦ mul_right_cancel₀ hf ?_⟩
  -- Apply `Φ` to the Bochner integral `g * f = ∫ y, g y • τ_{-y} f ∂μ`.
  calc toCharacterSpace μ (ofAddChar ψ' (hψc.subtype_mk _)) g * Φ f
    _ = ∫ y, ψ (-y) * g y * Φ f ∂μ := (integral_mul_const _ _).symm
    _ = ∫ y, Φ (g y • (DomAddAct.mk (-y) +ᵥ f)) ∂μ := by
      refine integral_congr_ae (.of_forall fun y ↦ ?_)
      simp only [map_smul, smul_eq_mul]
      rw [show ψ (-y) = Φ (DomAddAct.mk (-y) +ᵥ f) / Φ f from rfl, mul_right_comm,
        div_mul_cancel₀ _ hf, mul_comm]
    _ = Φ (g * f) :=
      (CharacterSpace.toCLM Φ).integral_comp_comm (L1.integrable_smul_translate g f)
    _ = Φ g * Φ f := map_mul Φ g f

theorem continuous_toCharacterSpace : Continuous (toCharacterSpace μ) :=
  -- This amounts to the continuity of `fourierIntegral μ f` for all `f : Lp ℂ 1 μ`.
  (continuous_of_continuous_eval fun f ↦
    continuous_fourierIntegral (L1.integrable_coeFn f)).subtype_mk _

/-- The evaluation map is jointly continuous on the character space of `L¹(G)`. -/
private theorem continuous_eval_characterSpace :
    Continuous fun p : characterSpace ℂ (Lp ℂ 1 μ) × Lp ℂ 1 μ ↦ p.1 p.2 := by
  -- The characters are equicontinuous: `‖Φ g‖ ≤ ‖g‖`.
  have hΦ (Φ : characterSpace ℂ (Lp ℂ 1 μ)) (g : Lp ℂ 1 μ) : ‖Φ g‖ ≤ ‖g‖ := by
    obtain ⟨χ, rfl⟩ := toCharacterSpace_surjective μ Φ
    exact norm_fourierIntegral_coeFn_le g χ
  refine continuous_iff_continuousAt.2 fun ⟨Φ₀, g₀⟩ ↦ ?_
  have h0 : Continuous fun p : characterSpace ℂ (Lp ℂ 1 μ) × Lp ℂ 1 μ ↦
      ‖p.2 - g₀‖ + ‖p.1 g₀ - Φ₀ g₀‖ :=
    ((continuous_snd.sub continuous_const).norm).add
      ((((eval_continuous g₀).comp continuous_subtype_val).comp continuous_fst).sub
        continuous_const).norm
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ ↦ norm_nonneg _) (fun p ↦ ?_) (by simpa using h0.tendsto (Φ₀, g₀))
  calc ‖p.1 p.2 - Φ₀ g₀‖
    _ = ‖p.1 (p.2 - g₀) + (p.1 g₀ - Φ₀ g₀)‖ := by rw [map_sub, sub_add_sub_cancel]
    _ ≤ ‖p.1 (p.2 - g₀)‖ + ‖p.1 g₀ - Φ₀ g₀‖ := norm_add_le _ _
    _ ≤ ‖p.2 - g₀‖ + ‖p.1 g₀ - Φ₀ g₀‖ := by gcongr; exact hΦ _ _

/-- The compact-open topology on the Pontryagin dual agrees with the weak-* topology on the
character space of `L¹(G)`. -/
theorem isHomeomorph_toCharacterSpace : IsHomeomorph (toCharacterSpace μ) := by
  -- It remains to prove that the inverse map is continuous. If `Φ₀ f ≠ 0`, then the character
  -- of `G` associated with `Φ` close to `Φ₀` is `x ↦ Φ (τ_x f) / Φ f`, which is jointly
  -- continuous in `(Φ, x)` since `x ↦ τ_x f` is continuous and the characters are equicontinuous.
  let e := Equiv.ofBijective _ ⟨toCharacterSpace_injective μ, toCharacterSpace_surjective μ⟩
  have he (Φ : characterSpace ℂ (Lp ℂ 1 μ)) (g : Lp ℂ 1 μ) :
      fourierIntegral μ g (e.symm Φ) = Φ g :=
    DFunLike.congr_fun (e.apply_symm_apply Φ) g
  suffices h : Continuous fun p : characterSpace ℂ (Lp ℂ 1 μ) × G ↦
      ((e.symm p.1).toAddChar p.2 : ℂ) from
    isHomeomorph_iff_exists_inverse.2 ⟨continuous_toCharacterSpace μ, e.symm,
      e.symm_apply_apply, e.apply_symm_apply, continuous_of_continuous_uncurry _
        (h.subtype_mk fun p ↦ ((e.symm p.1).toAddChar p.2).2)⟩
  refine continuous_iff_continuousAt.2 fun ⟨Φ₀, x₀⟩ ↦ ?_
  obtain ⟨f, hf⟩ := exists_apply_ne_zero μ Φ₀
  have hf' : Continuous fun p : characterSpace ℂ (Lp ℂ 1 μ) × G ↦ p.1 f :=
    ((eval_continuous f).comp continuous_subtype_val).comp continuous_fst
  have hc : ContinuousAt (fun p : characterSpace ℂ (Lp ℂ 1 μ) × G ↦
      p.1 (DomAddAct.mk p.2 +ᵥ f) / p.1 f) (Φ₀, x₀) :=
    ((continuous_eval_characterSpace μ).comp (continuous_fst.prodMk
      ((continuous_mk_vadd μ f).comp continuous_snd))).continuousAt.div hf'.continuousAt hf
  refine hc.congr ?_
  filter_upwards [hf'.continuousAt.eventually_ne hf] with p hp
  rw [div_eq_iff hp, ← he, ← he, fourierIntegral_coeFn_vadd, Circle.smul_def, smul_eq_mul]

/-- The Pontryagin dual of `G` is homeomorphic to the character space of `L¹(G)`. -/
noncomputable def characterSpaceHomeomorph :
    AddPontryaginDual G ≃ₜ characterSpace ℂ (Lp ℂ 1 μ) :=
  IsHomeomorph.homeomorph _ (isHomeomorph_toCharacterSpace μ)

@[simp]
theorem characterSpaceHomeomorph_apply (χ : AddPontryaginDual G) :
    characterSpaceHomeomorph μ χ = toCharacterSpace μ χ :=
  rfl

end AddPontryaginDual
