/-
Copyright (c) 2026 Wenrong Zou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wenrong Zou
-/
module

public import Mathlib.Algebra.Algebra.Spectrum.Quasispectrum
public import Mathlib.Analysis.Normed.Algebra.Spectrum
public import Mathlib.Topology.ContinuousMap.ZeroAtInfty
public import PontryaginDuality.Fourier.CharacterSpace

import Mathlib.Analysis.CStarAlgebra.GelfandDuality
import Mathlib.Analysis.Normed.Algebra.UnitizationL1
import Mathlib.Analysis.Normed.Module.WeakDual
import PontryaginDuality.Mathlib.Topology.ContinuousMap.StoneWeierstrass

/-!
# The Fourier transform on `L¹(G)`

Let `G` be a locally compact abelian group with a regular Haar measure `μ`. In this file we bundle
the Fourier transform as a homomorphism of non-unital algebras from `L¹(G)` to the continuous
functions on `AddPontryaginDual G` vanishing at infinity, and we state its main properties. They
all follow from the identification of `AddPontryaginDual G` with the character space of `L¹(G)`
(see `AddPontryaginDual.characterSpaceHomeomorph`).

## Main definitions

* `AddPontryaginDual.fourierL1 μ`: the Fourier transform as a non-unital algebra homomorphism
  `L¹(G) →ₙₐ[ℂ] C₀(AddPontryaginDual G, ℂ)`.

## Main statements

* `AddPontryaginDual.tendsto_fourierIntegral_cocompact`: the Riemann–Lebesgue lemma.
* `AddPontryaginDual.denseRange_fourierL1`: the range of the Fourier transform is dense in
  `C₀(AddPontryaginDual G, ℂ)`.
* `AddPontryaginDual.quasispectrum_eq_insert_zero_range_fourierL1`,
  `AddPontryaginDual.spectralRadius_inr_eq_nnnorm_fourierL1`: the (quasi)spectrum of `f : L¹(G)` is
  the range of its Fourier transform together with `0`. Combined with Gelfand's formula, this
  expresses `‖fourierL1 μ f‖` as the limit of `‖f ^ n‖ ^ (1 / n)`.
-/

@[expose] public section

open MeasureTheory Measure Filter Topology WeakDual
open scoped ZeroAtInfty ENNReal

namespace AddPontryaginDual

variable {G E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [LocallyCompactSpace G]
  [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsAddHaarMeasure] [μ.Regular]

/-- For `f : L¹(G)` and `ε > 0`, the set of `χ` such that `ε ≤ ‖fourierIntegral μ f χ‖` is
compact. -/
private theorem isCompact_setOf_le_norm_fourierIntegral (f : Lp ℂ 1 μ) {ε : ℝ} (hε : 0 < ε) :
    IsCompact {χ : AddPontryaginDual G | ε ≤ ‖fourierIntegral μ f χ‖} := by
  -- `characterSpace ℂ (Lp ℂ 1 μ) ∪ {0}` is weak-* closed and contained in the unit ball, hence
  -- it is weak-* compact by the Banach–Alaoglu theorem.
  have hK : IsCompact (characterSpace ℂ (Lp ℂ 1 μ) ∪ {0}) := by
    refine (WeakDual.isCompact_closedBall (0 : StrongDual ℂ (Lp ℂ 1 μ)) 1).of_isClosed_subset
      (CharacterSpace.union_zero_isClosed ℂ _) ?_
    rintro Φ (hΦ | rfl)
    · obtain ⟨χ, hχ⟩ := toCharacterSpace_surjective μ ⟨Φ, hΦ⟩
      obtain rfl : StrongDual.toWeakDual (fourierIntegralCLM μ χ) = Φ := congrArg Subtype.val hχ
      simpa using norm_fourierIntegralCLM_le μ χ
    · simp
  -- The set `{Φ | ε ≤ ‖Φ f‖}` is weak-* closed and does not contain `0`.
  have he : IsEmbedding fun χ : AddPontryaginDual G ↦
      (toCharacterSpace μ χ : WeakDual ℂ (Lp ℂ 1 μ)) :=
    IsEmbedding.subtypeVal.comp (characterSpaceHomeomorph μ).isEmbedding
  refine (he.isCompact_preimage_iff (K := (characterSpace ℂ (Lp ℂ 1 μ) ∪ {0}) ∩
    {Φ | ε ≤ ‖Φ f‖}) ?_).2 (hK.inter_right (isClosed_le continuous_const
      (eval_continuous f).norm)) |>.of_isClosed_subset ?_ ?_
  · rintro Φ ⟨hΦ | rfl, hΦε⟩
    · obtain ⟨χ, hχ⟩ := toCharacterSpace_surjective μ ⟨Φ, hΦ⟩
      exact ⟨χ, congrArg Subtype.val hχ⟩
    · exact absurd (hΦε.trans_eq norm_zero) hε.not_ge
  · exact isClosed_le continuous_const (continuous_fourierIntegral (L1.integrable_coeFn f)).norm
  · exact fun χ hχ ↦ ⟨Or.inl (toCharacterSpace μ χ).2, hχ⟩

private theorem tendsto_fourierIntegral_cocompact_aux {f : G → ℂ} (hf : Integrable f μ) :
    Tendsto (fourierIntegral μ f) (cocompact (AddPontryaginDual G)) (𝓝 0) := by
  rw [← fourierIntegral_congr_ae hf.coeFn_toL1]
  refine NormedAddGroup.tendsto_nhds_zero.2 fun ε hε ↦ ?_
  filter_upwards [(isCompact_setOf_le_norm_fourierIntegral μ (hf.toL1 f)
    hε).compl_mem_cocompact] with χ hχ
  exact not_le.1 hχ

/-- The **Riemann–Lebesgue lemma**: the Fourier transform of an integrable function vanishes at
infinity. -/
theorem tendsto_fourierIntegral_cocompact {f : G → E} (hf : Integrable f μ) :
    Tendsto (fourierIntegral μ f) (cocompact (AddPontryaginDual G)) (𝓝 0) := by
  -- By the case `E = ℂ`, this holds for the functions `1_s • c`. The general case follows since
  -- these functions span a dense subspace of `L¹` and `‖fourierIntegral μ f χ‖ ≤ ‖f‖`.
  by_cases hE : CompleteSpace E
  swap
  · have : fourierIntegral μ f = 0 := by
      ext χ
      simp [fourierIntegral, integral, hE]
    exact this ▸ tendsto_const_nhds
  refine hf.induction (P := fun f ↦ Tendsto (fourierIntegral μ f) (cocompact _) (𝓝 0))
    (fun c s hs hμs ↦ ?_) (fun f g _ hf hg hf' hg' ↦ ?_) ?_ (fun f g hfg _ hf' ↦ ?_)
  · have h1 : Integrable (s.indicator fun _ ↦ (1 : ℂ)) μ :=
      (integrableOn_const hμs.ne).integrable_indicator hs
    have h2 : (s.indicator fun _ ↦ c) = fun x ↦ s.indicator (fun _ ↦ (1 : ℂ)) x • c := by
      ext x
      by_cases hx : x ∈ s <;> simp [hx]
    rw [h2, fourierIntegral_smul_const]
    simpa using (tendsto_fourierIntegral_cocompact_aux μ h1).smul_const c
  · rw [fourierIntegral_add hf hg, ← add_zero (0 : E)]
    exact hf'.add hg'
  · refine isClosed_of_closure_subset fun f hf ↦ NormedAddGroup.tendsto_nhds_zero.2
      fun ε hε ↦ ?_
    obtain ⟨g, hg, hfg⟩ := Metric.mem_closure_iff.1 hf (ε / 2) (half_pos hε)
    filter_upwards [NormedAddGroup.tendsto_nhds_zero.1 hg (ε / 2) (half_pos hε)] with χ hχ
    calc ‖fourierIntegral μ f χ‖
      _ = ‖fourierIntegral μ (f - g : Lp E 1 μ) χ + fourierIntegral μ g χ‖ := by
        rw [← fourierIntegral_coeFn_add, sub_add_cancel]
      _ ≤ ‖fourierIntegral μ (f - g : Lp E 1 μ) χ‖ + ‖fourierIntegral μ g χ‖ := norm_add_le _ _
      _ < ε / 2 + ε / 2 :=
        add_lt_add ((norm_fourierIntegral_coeFn_le _ χ).trans_lt (by rwa [← dist_eq_norm])) hχ
      _ = ε := add_halves ε
  · rwa [← fourierIntegral_congr_ae hfg]

/-- The Fourier transform as a homomorphism of non-unital algebras from `L¹(G)` to the continuous
functions on the Pontryagin dual vanishing at infinity. -/
noncomputable def fourierL1 : Lp ℂ 1 μ →ₙₐ[ℂ] C₀(AddPontryaginDual G, ℂ) where
  toFun f :=
    ⟨⟨fourierIntegral μ f, continuous_fourierIntegral (L1.integrable_coeFn f)⟩,
      tendsto_fourierIntegral_cocompact μ (L1.integrable_coeFn f)⟩
  map_smul' c f := by ext χ; exact fourierIntegral_coeFn_smul c f χ
  map_zero' := by ext χ; exact fourierIntegral_coeFn_zero χ
  map_add' f g := by ext χ; exact fourierIntegral_coeFn_add f g χ
  map_mul' f g := by ext χ; exact fourierIntegral_mul f g χ

@[simp]
theorem fourierL1_apply (f : Lp ℂ 1 μ) (χ : AddPontryaginDual G) :
    fourierL1 μ f χ = fourierIntegral μ f χ :=
  rfl

theorem norm_fourierL1_le (f : Lp ℂ 1 μ) : ‖fourierL1 μ f‖ ≤ ‖f‖ := by
  rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm,
    BoundedContinuousFunction.norm_le (norm_nonneg f)]
  exact fun χ ↦ norm_fourierIntegral_coeFn_le f χ

/-- The Fourier transform intertwines the involution of `L¹(G)` and the complex conjugation. -/
theorem fourierL1_involution (f : Lp ℂ 1 μ) :
    fourierL1 μ (L1.involution f) = star (fourierL1 μ f) := by
  ext χ
  exact fourierIntegral_involution f χ

/-- The Fourier transforms of the elements of `L¹(G)` separate the points of the Pontryagin
dual. -/
theorem exists_fourierL1_ne {χ η : AddPontryaginDual G} (h : χ ≠ η) :
    ∃ f : Lp ℂ 1 μ, fourierL1 μ f χ ≠ fourierL1 μ f η := by
  -- This is `toCharacterSpace_injective`.
  by_contra! h'
  exact h (toCharacterSpace_injective μ (CharacterSpace.ext h'))

/-- The Fourier transforms of the elements of `L¹(G)` do not vanish simultaneously. -/
theorem exists_fourierL1_ne_zero (χ : AddPontryaginDual G) :
    ∃ f : Lp ℂ 1 μ, fourierL1 μ f χ ≠ 0 := by
  by_contra! h
  exact (toCharacterSpace μ χ).2.1 (ContinuousLinearMap.ext h)

/-- The range of the Fourier transform is dense in the space of continuous functions vanishing
at infinity. -/
theorem denseRange_fourierL1 : DenseRange (fourierL1 μ) := by
  -- The range is a subalgebra which is closed under complex conjugation (`fourierL1_involution`),
  -- separates points (`exists_fourierL1_ne`) and vanishes nowhere (`exists_fourierL1_ne_zero`).
  -- Apply the Stone–Weierstrass theorem.
  let A : NonUnitalStarSubalgebra ℂ C₀(AddPontryaginDual G, ℂ) :=
    { NonUnitalAlgHom.range (fourierL1 μ) with
      star_mem' := by
        rintro _ ⟨f, rfl⟩
        exact ⟨L1.involution f, fourierL1_involution μ f⟩ }
  refine ZeroAtInftyContinuousMap.dense_of_separatesPoints A (fun χ η h ↦ ?_) fun χ ↦ ?_
  · obtain ⟨f, hf⟩ := exists_fourierL1_ne μ h
    exact ⟨_, ⟨f, rfl⟩, hf⟩
  · obtain ⟨f, hf⟩ := exists_fourierL1_ne_zero μ χ
    exact ⟨_, ⟨f, rfl⟩, hf⟩

/-- The quasispectrum of an element of `L¹(G)` is the range of its Fourier transform, together
with `0`. -/
theorem quasispectrum_eq_insert_zero_range_fourierL1 (f : Lp ℂ 1 μ) :
    quasispectrum ℂ f = insert 0 (Set.range (fourierL1 μ f)) := by
  refine Set.Subset.antisymm (fun z hz ↦ ?_) (Set.insert_subset (quasispectrum.zero_mem ℂ f) ?_)
  · -- The spectrum of an element of a commutative unital Banach algebra is the set of its values
    -- under the characters. Apply this to the unitization of `L¹(G)` with the `L¹` norm: the
    -- restriction to `L¹(G)` of a character `Ψ` is either `0` or a character of `L¹(G)`.
    let : NormedCommRing (WithLp 1 (Unitization ℂ (Lp ℂ 1 μ))) :=
      { WithLp.instUnitizationNormedRing with
        mul_comm := fun x y ↦ WithLp.ofLp_injective _ (mul_comm _ _) }
    have hz' : z ∈ spectrum ℂ (WithLp.toLp 1 (f : Unitization ℂ (Lp ℂ 1 μ))) := by
      rw [← AlgEquiv.spectrum_eq (WithLp.unitizationAlgEquiv (𝕜 := ℂ) (A := Lp ℂ 1 μ) ℂ)]
      exact Unitization.quasispectrum_eq_spectrum_inr ℂ f ▸ hz
    obtain ⟨Ψ, rfl⟩ := CharacterSpace.mem_spectrum_iff_exists.1 hz'
    let Φ : StrongDual ℂ (Lp ℂ 1 μ) := LinearMap.mkContinuous
      { toFun g :=  Ψ (WithLp.toLp 1 (g : Unitization ℂ (Lp ℂ 1 μ)))
        map_add' g h := by rw [Unitization.inr_add, WithLp.toLp_add, map_add]
        map_smul' c g := by rw [Unitization.inr_smul, WithLp.toLp_smul, map_smul]; rfl }
      ‖CharacterSpace.toCLM Ψ‖ fun g ↦ ((CharacterSpace.toCLM Ψ).le_opNorm _).trans_eq
        (by rw [WithLp.unitization_norm_inr])
    by_cases hΦ : StrongDual.toWeakDual Φ = 0
    · exact Or.inl (DFunLike.congr_fun hΦ f)
    · have hmul (g h : Lp ℂ 1 μ) : Φ (g * h) = Φ g * Φ h := by
        change Ψ (WithLp.toLp 1 ((g * h : Lp ℂ 1 μ) : Unitization ℂ (Lp ℂ 1 μ))) = _
        rw [Unitization.inr_mul]
        exact map_mul Ψ (WithLp.toLp 1 (g : Unitization ℂ (Lp ℂ 1 μ))) (WithLp.toLp 1 _)
      obtain ⟨χ, hχ⟩ := toCharacterSpace_surjective μ ⟨StrongDual.toWeakDual Φ, hΦ, hmul⟩
      exact Or.inr ⟨χ, DFunLike.congr_fun hχ f⟩
  · rintro _ ⟨χ, rfl⟩
    refine NonUnitalAlgHom.quasispectrum_apply_subset (toCharacterSpace μ χ) f ?_
    simp [quasispectrum_eq_spectrum_union_zero, spectrum.mem_iff]

/-- The spectral radius of an element of `L¹(G)` is the uniform norm of its Fourier
transform. -/
theorem spectralRadius_inr_eq_nnnorm_fourierL1 (f : Lp ℂ 1 μ) :
    spectralRadius ℂ (f : Unitization ℂ (Lp ℂ 1 μ)) = ‖fourierL1 μ f‖₊ := by
  have hbdd : BddAbove (Set.range fun χ ↦ ‖fourierL1 μ f χ‖₊) :=
    ⟨‖fourierL1 μ f‖₊, Set.forall_mem_range.2 (fourierL1 μ f).toBCF.nnnorm_coe_le_nnnorm⟩
  rw [spectralRadius, Unitization.quasispectrum_inr_eq ℂ ℂ f,
    quasispectrum_eq_insert_zero_range_fourierL1, iSup_insert, iSup_range, nnnorm_zero,
    ENNReal.coe_zero, sup_of_le_right (by simp), ← ENNReal.coe_iSup hbdd]
  exact congrArg _ (fourierL1 μ f).toBCF.nnnorm_eq_iSup_nnnorm.symm

end AddPontryaginDual
