/-
Copyright (c) 2026 Wenrong Zou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wenrong Zou
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.CStarAlgebra.Spectrum
public import Mathlib.Analysis.Normed.Operator.Extend
public import PontryaginDuality.Convolution.L2
public import PontryaginDuality.Fourier.L1
public import PontryaginDuality.Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.ZeroAtInfty

/-!
# `C₀(Ĝ)` as the enveloping C⋆-algebra of `L¹(G)`

Let `G` be a locally compact abelian group with a regular Haar measure `μ`. Every homomorphism of
involutive algebras from `L¹(G)` to a C⋆-algebra is bounded by the uniform norm of the Fourier
transform. Hence the regular representation of `L¹(G)` on `L²(G)` extends to a representation of
`C₀(AddPontryaginDual G, ℂ)`, and the Fourier transform is injective on `L¹(G)`.

## Main definitions

* `AddPontryaginDual.fourierMultiplier μ`: the representation of `C₀(AddPontryaginDual G, ℂ)` on
  `L²(G)` such that `fourierMultiplier μ (fourierL1 μ f) g = f ⋆ g`.
* `AddPontryaginDual.spectralCLM μ f g`: the continuous linear functional
  `Φ ↦ ⟪g, fourierMultiplier μ Φ f⟫` on `C₀(AddPontryaginDual G, ℂ)`, for `f g : L²(G)`.
* `AddPontryaginDual.spectralMeasure μ f`: the finite regular measure representing
  `spectralCLM μ f f`.

## Main statements

* `AddPontryaginDual.norm_map_le_norm_fourierL1`: the universal property.
* `AddPontryaginDual.norm_regularRep_le`: `‖f ⋆ g‖₂ ≤ ‖fourierL1 μ f‖ * ‖g‖₂`.
* `AddPontryaginDual.fourierL1_injective`: the Fourier transform is injective on `L¹(G)`.
* `AddPontryaginDual.exists_fourierL1_sub_one_lt_convL2_sub_lt`: approximate units.
* `AddPontryaginDual.spectralMeasure_univ`: the total mass of `spectralMeasure μ f` is `‖f‖ ^ 2`.
* `AddPontryaginDual.integral_spectralMeasure_convL2`: the measure `spectralMeasure μ (φ ⋆ f)` has
  density `‖fourierL1 μ φ‖ ^ 2` with respect to `spectralMeasure μ f`.

## Implementation notes

Bourbaki introduces the enveloping C⋆-algebra `St(G)` of `L¹(G)` and proves that the Fourier
transform extends to an isomorphism `St(G) ≃ C₀(Ĝ)`. We do not construct `St(G)`: the statements
about `St(G)` are stated for `C₀(AddPontryaginDual G, ℂ)`.

For `f ∈ A(G)`, i.e. `f` in the span of the functions `f₁ * f₂` with `f₁, f₂ ∈ L¹ ∩ L²`, Bourbaki
defines a bounded measure `μ_f` on `Ĝ` such that `(φ * f)(e) = ∫ Fφ dμ_f`. A bounded measure in the
sense of Bourbaki is a continuous linear functional on `C₀(Ĝ)`: the measure `μ_f` for
`f = f₁ * f₂⋆` is `spectralCLM μ f₁ f₂`, and `spectralMeasure μ f₁` is the measure in the sense of
Mathlib which represents it when `f₁ = f₂`.

## References

* [N. Bourbaki, *Théories spectrales*, Chap. I, §6, n°6–7 and Chap. II, §1, n°2–3][bourbaki1967]
-/

@[expose] public section

open MeasureTheory Measure Filter Topology
open scoped ComplexOrder ComplexConjugate ZeroAtInfty ENNReal

namespace AddPontryaginDual

variable {G : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsAddHaarMeasure]
  [μ.Regular]

/-! ### The universal property -/

/-- `C₀(AddPontryaginDual G, ℂ)` is the enveloping C⋆-algebra of `L¹(G)`: every homomorphism of
involutive algebras from `L¹(G)` to a C⋆-algebra is bounded by the uniform norm of the Fourier
transform. -/
theorem norm_map_le_norm_fourierL1 {B : Type*} [NonUnitalCStarAlgebra B]
    (π : Lp ℂ 1 μ →ₙₐ[ℂ] B) (hπ : ∀ f, π (L1.involution f) = star (π f)) (f : Lp ℂ 1 μ) :
    ‖π f‖ ≤ ‖fourierL1 μ f‖ := by
  -- Let `h = involution f * f`. Then `‖π f‖ ^ 2 = ‖π h‖`, which is the spectral radius of `π h`
  -- since `π h` is self-adjoint (TS I §6 n°3, (2)). A homomorphism does not increase the spectral
  -- radius (TS I §6 n°3, Prop. 1), and the spectral radius of `h` in `L¹(G)` is
  -- `‖fourierL1 μ h‖ = ‖fourierL1 μ f‖ ^ 2` by `spectralRadius_inr_eq_nnnorm_fourierL1`
  -- (TS II §1 n°1, Prop. 1 and Cor. 1).
  have key : ‖π (L1.involution f * f)‖₊ ≤ ‖fourierL1 μ (L1.involution f * f)‖₊ := by
    have hsa : IsSelfAdjoint (π (L1.involution f * f) : Unitization ℂ B) := by
      rw [map_mul, hπ]
      exact (IsSelfAdjoint.star_mul_self (π f)).inr ℂ
    have h1 : spectralRadius ℂ (π (L1.involution f * f)) ≤
        spectralRadius ℂ (L1.involution f * f) :=
      iSup_le_iSup_of_subset (NonUnitalAlgHom.quasispectrum_apply_subset π _)
    rwa [← Unitization.spectralRadius_inr (𝕜 := ℂ), hsa.spectralRadius_eq_nnnorm,
      Unitization.nnnorm_inr, ← Unitization.spectralRadius_inr (𝕜 := ℂ),
      spectralRadius_inr_eq_nnnorm_fourierL1, ENNReal.coe_le_coe] at h1
  refine (mul_self_le_mul_self_iff (norm_nonneg _) (norm_nonneg _)).2 ?_
  rw [← CStarRing.norm_star_mul_self, ← CStarRing.norm_star_mul_self, ← hπ, ← map_mul,
    ← fourierL1_involution, ← map_mul]
  exact key

/-- The norm of the convolution operator `g ↦ f ⋆ g` on `L²(G)` is bounded by the uniform norm of
the Fourier transform of `f`. -/
theorem norm_regularRep_le (f : Lp ℂ 1 μ) : ‖L1.regularRep μ f‖ ≤ ‖fourierL1 μ f‖ :=
  norm_map_le_norm_fourierL1 μ (L1.regularRep μ) (L1.regularRep_involution μ) f

theorem norm_convL2_le_norm_fourierL1_mul (f : Lp ℂ 1 μ) (g : Lp ℂ 2 μ) :
    ‖L1.convL2 f g‖ ≤ ‖fourierL1 μ f‖ * ‖g‖ :=
  ((L1.regularRep μ f).le_opNorm g).trans
    (mul_le_mul_of_nonneg_right (norm_regularRep_le μ f) (norm_nonneg g))

/-- The Fourier transform is injective on `L¹(G)`. -/
theorem fourierL1_injective : Function.Injective (fourierL1 μ) := by
  -- TS II §1 n°2, Prop. 3: the regular representation is injective and bounded by the uniform
  -- norm of the Fourier transform.
  refine (injective_iff_map_eq_zero (fourierL1 μ)).2 fun f hf ↦ L1.regularRep_injective μ ?_
  rw [map_zero]
  exact norm_le_zero_iff.1 ((norm_regularRep_le μ f).trans_eq (by rw [hf, norm_zero]))

/-! ### The representation of `C₀(Ĝ)` on `L²(G)` -/

/-- The representation of `C₀(AddPontryaginDual G, ℂ)` on `L²(G)` which extends the regular
representation of `L¹(G)` (see `AddPontryaginDual.fourierMultiplier_fourierL1`). After the
Plancherel theorem, `fourierMultiplier μ Φ` is the Fourier multiplier with symbol `Φ`. -/
noncomputable def fourierMultiplier :
    C₀(AddPontryaginDual G, ℂ) →L[ℂ] Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  LinearMap.extendOfNorm
    { toFun := L1.regularRep μ, map_add' := map_add _, map_smul' := map_smul _ }
    { toFun := fourierL1 μ, map_add' := map_add _, map_smul' := map_smul _ }

theorem fourierMultiplier_fourierL1 (f : Lp ℂ 1 μ) :
    fourierMultiplier μ (fourierL1 μ f) = L1.regularRep μ f :=
  LinearMap.extendOfNorm_eq (denseRange_fourierL1 μ)
    ⟨1, fun f ↦ (norm_regularRep_le μ f).trans_eq (one_mul _).symm⟩ f

theorem norm_fourierMultiplier_le (Φ : C₀(AddPontryaginDual G, ℂ)) :
    ‖fourierMultiplier μ Φ‖ ≤ ‖Φ‖ :=
  (LinearMap.norm_extendOfNorm_apply_le (denseRange_fourierL1 μ) 1
    (fun f ↦ (norm_regularRep_le μ f).trans_eq (one_mul _).symm) Φ).trans_eq (one_mul _)

theorem fourierMultiplier_mul (Φ Ψ : C₀(AddPontryaginDual G, ℂ)) :
    fourierMultiplier μ (Φ * Ψ) = fourierMultiplier μ Φ * fourierMultiplier μ Ψ := by
  -- By `denseRange_fourierL1`, since both sides are continuous.
  refine (denseRange_fourierL1 μ).induction_on₂ (isClosed_eq
    ((fourierMultiplier μ).continuous.comp (continuous_fst.mul continuous_snd))
    (((fourierMultiplier μ).continuous.comp continuous_fst).mul
      ((fourierMultiplier μ).continuous.comp continuous_snd))) (fun f g ↦ ?_) Φ Ψ
  rw [← map_mul (fourierL1 μ), fourierMultiplier_fourierL1, fourierMultiplier_fourierL1,
    fourierMultiplier_fourierL1, map_mul]

theorem fourierMultiplier_star (Φ : C₀(AddPontryaginDual G, ℂ)) :
    fourierMultiplier μ (star Φ) = star (fourierMultiplier μ Φ) := by
  -- By `denseRange_fourierL1`, `fourierL1_involution` and `L1.regularRep_involution`.
  refine (denseRange_fourierL1 μ).induction_on Φ (isClosed_eq
    ((fourierMultiplier μ).continuous.comp continuous_star)
    (continuous_star.comp (fourierMultiplier μ).continuous)) fun f ↦ ?_
  rw [← fourierL1_involution, fourierMultiplier_fourierL1, fourierMultiplier_fourierL1,
    L1.regularRep_involution]

/-- **Approximate units**: for every compact subset `K` of the Pontryagin dual and every
`f ∈ L²(G)`, there is `φ ∈ L¹(G)` with `‖φ‖ ≤ 1` whose Fourier transform is close to `1` on `K`
and such that `φ ⋆ f` is close to `f`. -/
theorem exists_fourierL1_sub_one_lt_convL2_sub_lt {K : Set (AddPontryaginDual G)}
    (hK : IsCompact K) (f : Lp ℂ 2 μ) {ε : ℝ} (hε : 0 < ε) :
    ∃ φ : Lp ℂ 1 μ, ‖φ‖ ≤ 1 ∧ (∀ χ ∈ K, ‖fourierL1 μ φ χ - 1‖ < ε) ∧
      ‖L1.convL2 φ f - f‖ < ε := by
  -- TS II §1 n°3, Lemme 1. Take `φ ≥ 0` with integral `1` supported in a small neighborhood `W` of
  -- `0`. Since `K` is compact for the compact-open topology, `‖χ x - 1‖ < ε` for all `χ ∈ K` and
  -- `x ∈ W` if `W` is small, hence `‖fourierL1 μ φ χ - 1‖ < ε`. The last property is
  -- `L1.exists_nhds_zero_norm_convL2_sub_lt`.
  obtain ⟨U, hU, h⟩ := L1.exists_nhds_zero_norm_convL2_sub_lt f hε
  have hV : ∀ᶠ x in 𝓝 (0 : G), ∀ χ ∈ K, ‖(χ.toAddChar (-x) : ℂ) - 1‖ < ε / 2 := by
    refine hK.eventually_forall_of_forall_eventually fun χ _ ↦ ?_
    have hc : Continuous fun p : G × AddPontryaginDual G ↦ ‖(p.2.toAddChar (-p.1) : ℂ) - 1‖ :=
      ((continuous_subtype_val.comp (continuous_toAddChar_uncurry.comp
        (continuous_snd.prodMk continuous_fst.neg))).sub continuous_const).norm
    exact (hc.tendsto (0, χ)).eventually (gt_mem_nhds (by simpa using half_pos hε))
  obtain ⟨W, ⟨hW0, hW, hW'⟩, hWUV⟩ :=
    (isCompact_isClosed_basis_nhds (0 : G)).mem_iff.1 (inter_mem hU hV)
  have hμW : μ W ≠ ∞ := hW.measure_lt_top.ne
  have hμW0 : 0 < μ.real W := ENNReal.toReal_pos (measure_pos_of_mem_nhds μ hW0).ne' hμW
  -- `φ` is the normalized indicator function of `W`.
  have hu1 : Integrable (W.indicator fun _ ↦ ((μ.real W)⁻¹ : ℂ)) μ :=
    (integrableOn_const hμW).integrable_indicator hW'.measurableSet
  have hu : hu1.toL1 _ =ᵐ[μ] W.indicator fun _ ↦ ((μ.real W)⁻¹ : ℂ) := hu1.coeFn_toL1
  have hn : ‖hu1.toL1 (W.indicator fun _ ↦ ((μ.real W)⁻¹ : ℂ))‖ = 1 := by
    rw [L1.norm_eq_integral_norm, integral_congr_ae (hu.mono fun x hx ↦ by rw [hx]),
      integral_congr_ae (.of_forall fun x ↦ norm_indicator_eq_indicator_norm _ _),
      integral_indicator_const _ hW'.measurableSet]
    simp [hμW0.ne', abs_of_pos hμW0]
  refine ⟨hu1.toL1 _, hn.le, fun χ hχ ↦ ?_, h _ ?_ hn ?_⟩
  · have hc : Continuous fun x : G ↦ (χ.toAddChar (-x) : ℂ) :=
      continuous_subtype_val.comp (χ.continuous_toAddChar.comp continuous_neg)
    have h1 : fourierL1 μ (hu1.toL1 _) χ =
        ∫ x in W, (χ.toAddChar (-x) : ℂ) * ((μ.real W)⁻¹ : ℂ) ∂μ := by
      rw [fourierL1_apply, fourierIntegral_congr_ae hu, fourierIntegral_apply,
        ← integral_indicator hW'.measurableSet]
      refine integral_congr_ae (.of_forall fun x ↦ ?_)
      by_cases hx : x ∈ W <;> simp [hx, Circle.smul_def]
    have h2 : ∫ _ in W, ((μ.real W)⁻¹ : ℂ) ∂μ = 1 := by
      rw [setIntegral_const, Complex.real_smul, mul_inv_cancel₀]
      exact_mod_cast hμW0.ne'
    have h3 : fourierL1 μ (hu1.toL1 _) χ - 1 =
        ∫ x in W, ((χ.toAddChar (-x) : ℂ) * ((μ.real W)⁻¹ : ℂ) - ((μ.real W)⁻¹ : ℂ)) ∂μ := by
      have hi : IntegrableOn (fun x ↦ (χ.toAddChar (-x) : ℂ) * ((μ.real W)⁻¹ : ℂ)) W μ :=
        (hc.mul continuous_const).continuousOn.integrableOn_compact' hW hW'.measurableSet
      rw [integral_sub hi (integrableOn_const (C := ((μ.real W)⁻¹ : ℂ)) hμW), ← h1, h2]
    rw [h3]
    refine (norm_setIntegral_le_of_norm_le_const hW.measure_lt_top
      (C := ε / 2 * (μ.real W)⁻¹) fun x hx ↦ ?_).trans_lt ?_
    · rw [← sub_one_mul, norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hμW0.le]
      exact mul_le_mul_of_nonneg_right ((hWUV hx).2 χ hχ).le (inv_nonneg.2 hμW0.le)
    · rw [mul_assoc, inv_mul_cancel₀ hμW0.ne', mul_one]
      exact half_lt_self hε
  · filter_upwards [hu] with x hx
    rw [hx]
    by_cases hxW : x ∈ W <;> simp [hxW, abs_of_pos hμW0]
  · filter_upwards [hu] with x hx hxU
    rw [hx, Set.indicator_of_notMem fun hxW ↦ hxU (hWUV hxW).1]

/-! ### Spectral measures -/

/-- The continuous linear functional `Φ ↦ ⟪g, fourierMultiplier μ Φ f⟫` on
`C₀(AddPontryaginDual G, ℂ)`, for `f g : L²(G)`. -/
noncomputable def spectralCLM (f g : Lp ℂ 2 μ) : C₀(AddPontryaginDual G, ℂ) →L[ℂ] ℂ :=
  (innerSL ℂ g).comp ((ContinuousLinearMap.apply ℂ (Lp ℂ 2 μ) f).comp (fourierMultiplier μ))

theorem spectralCLM_apply (f g : Lp ℂ 2 μ) (Φ : C₀(AddPontryaginDual G, ℂ)) :
    spectralCLM μ f g Φ = inner ℂ g (fourierMultiplier μ Φ f) :=
  rfl

/-- The functional `spectralCLM μ f g` is given by `φ ↦ ⟪g, φ ⋆ f⟫` on the Fourier transforms of
the elements of `L¹(G)`. If `f` and `g` are in `L¹ ∩ L²`, this is the value at `0` of
`φ * f * g⋆`. -/
theorem spectralCLM_fourierL1 (f g : Lp ℂ 2 μ) (φ : Lp ℂ 1 μ) :
    spectralCLM μ f g (fourierL1 μ φ) = inner ℂ g (L1.convL2 φ f) := by
  -- TS II §1 n°3, Lemme 2.
  rw [spectralCLM_apply, fourierMultiplier_fourierL1, L1.regularRep_apply]

theorem spectralCLM_self_mul_star_nonneg (f : Lp ℂ 2 μ) (Φ : C₀(AddPontryaginDual G, ℂ)) :
    0 ≤ spectralCLM μ f f (Φ * star Φ) := by
  -- By `fourierMultiplier_mul` and `fourierMultiplier_star`, this is
  -- `‖fourierMultiplier μ (star Φ) f‖ ^ 2`.
  rw [spectralCLM_apply, fourierMultiplier_mul, fourierMultiplier_star,
    mul_apply_eq_comp, ContinuousLinearMap.star_eq_adjoint,
    ← ContinuousLinearMap.adjoint_inner_left]
  exact Complex.nonneg_iff.2 ⟨inner_self_nonneg (𝕜 := ℂ), (inner_self_im (𝕜 := ℂ) _).symm⟩

variable [MeasurableSpace (AddPontryaginDual G)] [BorelSpace (AddPontryaginDual G)]

/-- The spectral measure of `f ∈ L²(G)`: the finite regular measure on the Pontryagin dual
such that `∫ χ, Φ χ ∂spectralMeasure μ f = ⟪f, fourierMultiplier μ Φ f⟫`. -/
noncomputable def spectralMeasure (f : Lp ℂ 2 μ) : Measure (AddPontryaginDual G) :=
  ComplexRMK.rieszMeasure (spectralCLM μ f f) (spectralCLM_self_mul_star_nonneg μ f)

instance (f : Lp ℂ 2 μ) : IsFiniteMeasure (spectralMeasure μ f) := by
  unfold spectralMeasure
  infer_instance

instance (f : Lp ℂ 2 μ) : (spectralMeasure μ f).Regular := by
  unfold spectralMeasure
  infer_instance

theorem integral_spectralMeasure (f : Lp ℂ 2 μ) (Φ : C₀(AddPontryaginDual G, ℂ)) :
    ∫ χ, Φ χ ∂spectralMeasure μ f = inner ℂ f (fourierMultiplier μ Φ f) :=
  ComplexRMK.integral_rieszMeasure _ _ Φ

/-- The total mass of the spectral measure of `f` is `‖f‖ ^ 2`. -/
theorem spectralMeasure_univ (f : Lp ℂ 2 μ) : spectralMeasure μ f Set.univ = ‖f‖ₑ ^ 2 := by
  -- Let `K` be a compact set which carries most of the mass. By
  -- `exists_fourierL1_sub_one_lt_convL2_sub_lt`, there is `φ` such that `fourierL1 μ φ` is bounded
  -- by `1` and close to `1` on `K`, and `∫ χ, fourierL1 μ φ χ ∂spectralMeasure μ f = ⟪f, φ ⋆ f⟫`
  -- is close to `⟪f, f⟫`.
  set m := spectralMeasure μ f
  suffices h : (m.real Set.univ : ℂ) = inner ℂ f f by
    have h' : m.real Set.univ = ‖f‖ ^ 2 :=
      ((Complex.ofReal_re _).symm.trans (congrArg Complex.re h)).trans
        (inner_self_eq_norm_sq (𝕜 := ℂ) f)
    rw [← ofReal_measureReal (measure_ne_top m _), h', ENNReal.ofReal_pow (norm_nonneg _),
      ofReal_norm]
  refine eq_of_forall_dist_le fun ε hε ↦ ?_
  have hC0 : 0 < m.real Set.univ + 2 + ‖f‖ + 1 := by positivity
  set δ := ε / (m.real Set.univ + 2 + ‖f‖ + 1) with hδ
  have hδ0 : 0 < δ := div_pos hε hC0
  obtain ⟨K, -, hK, hKm⟩ := MeasurableSet.univ.exists_isCompact_lt_add
    (measure_ne_top m Set.univ) (ENNReal.ofReal_pos.2 hδ0).ne'
  have hKc : m.real Kᶜ ≤ δ := by
    have h := ENNReal.toReal_mono
      (ENNReal.add_ne_top.2 ⟨measure_ne_top m K, ENNReal.ofReal_ne_top⟩) hKm.le
    rw [ENNReal.toReal_add (measure_ne_top m K) ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal hδ0.le] at h
    rw [measureReal_compl hK.measurableSet]
    exact sub_le_iff_le_add'.2 h
  obtain ⟨φ, hφ1, hφK, hφf⟩ := exists_fourierL1_sub_one_lt_convL2_sub_lt μ hK f hδ0
  have hint : Integrable (fourierL1 μ φ) m :=
    .of_bound (map_continuous _).aestronglyMeasurable ‖fourierL1 μ φ‖
      (.of_forall (fourierL1 μ φ).norm_apply_le_norm)
  have hI : ∫ χ, fourierL1 μ φ χ ∂m = inner ℂ f (L1.convL2 φ f) := by
    rw [integral_spectralMeasure, fourierMultiplier_fourierL1, L1.regularRep_apply]
  have hind : Integrable (fun χ ↦ δ + Kᶜ.indicator (fun _ ↦ (2 : ℝ)) χ) m :=
    (integrable_const _).add ((integrable_const _).indicator hK.measurableSet.compl)
  have h1 : ‖(m.real Set.univ : ℂ) - ∫ χ, fourierL1 μ φ χ ∂m‖ ≤ δ * m.real Set.univ + 2 * δ := by
    have e : ∫ χ, fourierL1 μ φ χ ∂m - (m.real Set.univ : ℂ) = ∫ χ, (fourierL1 μ φ χ - 1) ∂m := by
      rw [integral_sub hint (integrable_const _), integral_const, Complex.real_smul, mul_one]
    rw [norm_sub_rev, e]
    calc ‖∫ χ, (fourierL1 μ φ χ - 1) ∂m‖
      _ ≤ ∫ χ, (δ + Kᶜ.indicator (fun _ ↦ (2 : ℝ)) χ) ∂m := by
        refine norm_integral_le_of_norm_le hind (.of_forall fun χ ↦ ?_)
        by_cases hχ : χ ∈ K
        · simpa [hχ] using (hφK χ hχ).le
        · have : ‖fourierL1 μ φ χ - 1‖ ≤ 1 + 1 :=
            (norm_sub_le _ _).trans (add_le_add (((fourierL1 μ φ).norm_apply_le_norm χ).trans
              ((norm_fourierL1_le μ φ).trans hφ1)) (by simp))
          simpa [hχ] using this.trans (by linarith)
      _ = δ * m.real Set.univ + 2 * m.real Kᶜ := by
        rw [integral_add (integrable_const _)
          ((integrable_const _).indicator hK.measurableSet.compl), integral_const,
          integral_indicator_const _ hK.measurableSet.compl, smul_eq_mul, smul_eq_mul]
        ring
      _ ≤ δ * m.real Set.univ + 2 * δ := by gcongr
  have h2 : ‖inner ℂ f (L1.convL2 φ f) - inner ℂ f f‖ ≤ ‖f‖ * δ := by
    rw [← inner_sub_right]
    exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left hφf.le (norm_nonneg _))
  calc dist (m.real Set.univ : ℂ) (inner ℂ f f)
    _ ≤ dist (m.real Set.univ : ℂ) (∫ χ, fourierL1 μ φ χ ∂m) +
        dist (∫ χ, fourierL1 μ φ χ ∂m) (inner ℂ f f) := dist_triangle _ _ _
    _ ≤ (δ * m.real Set.univ + 2 * δ) + ‖f‖ * δ := by
      rw [dist_eq_norm, dist_eq_norm, hI]
      exact add_le_add (hI ▸ h1) h2
    _ ≤ δ * (m.real Set.univ + 2 + ‖f‖ + 1) := by nlinarith
    _ = ε := by
      rw [hδ]
      field_simp

/-- The measure `spectralMeasure μ (φ ⋆ f)` has density `‖fourierL1 μ φ‖ ^ 2` with respect to
`spectralMeasure μ f`. -/
theorem integral_spectralMeasure_convL2 (φ : Lp ℂ 1 μ) (f : Lp ℂ 2 μ)
    (Φ : C₀(AddPontryaginDual G, ℂ)) :
    ∫ χ, Φ χ ∂spectralMeasure μ (L1.convL2 φ f) =
      ∫ χ, Φ χ * ‖fourierL1 μ φ χ‖ ^ 2 ∂spectralMeasure μ f := by
  -- By `fourierMultiplier_mul` and `fourierMultiplier_star`,
  -- `⟪φ ⋆ f, fourierMultiplier μ Φ (φ ⋆ f)⟫ = ⟪f, fourierMultiplier μ (star Fφ * Φ * Fφ) f⟫`.
  have h := integral_spectralMeasure μ f (star (fourierL1 μ φ) * Φ * fourierL1 μ φ)
  rw [fourierMultiplier_mul, fourierMultiplier_mul, fourierMultiplier_star,
    fourierMultiplier_fourierL1, mul_apply_eq_comp, mul_apply_eq_comp,
    ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right,
    L1.regularRep_apply] at h
  rw [integral_spectralMeasure, ← h]
  refine integral_congr_ae (.of_forall fun χ ↦ ?_)
  simp only [FunLike.coe_mul, ZeroAtInftyContinuousMap.coe_star, Pi.mul_apply,
    Pi.star_apply, RCLike.star_def, ← Complex.conj_mul']
  ring

end AddPontryaginDual
