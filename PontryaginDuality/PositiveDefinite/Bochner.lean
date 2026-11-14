/-
Copyright (c) 2026 Wenrong Zou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wenrong Zou
-/
module

public import PontryaginDuality.Fourier.L1
public import PontryaginDuality.Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.ZeroAtInfty
public import PontryaginDuality.PositiveDefinite.Basic

import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.Normed.Algebra.UnitizationL1
import Mathlib.Analysis.Normed.Operator.Extend
import PontryaginDuality.Mathlib.MeasureTheory.Function.ContinuousMapDense

/-!
# Bochner's theorem

Let `G` be a locally compact abelian group. Bochner's theorem states that the continuous positive
definite functions on `G` are exactly the functions of the form `x ↦ ∫ χ, χ x ∂ν`, where `ν` is a
finite regular measure on the Pontryagin dual of `G`, and that `ν` is unique.

## Main definitions

* `AddPontryaginDual.bochnerMeasure φ`: the finite regular measure on `AddPontryaginDual G`
  associated with a continuous positive definite function `φ : G → ℂ`. It is `0` if `φ` is not
  continuous and positive definite.

## Main statements

* `IsPositiveDefinite.norm_integral_mul_le`: the key estimate
  `‖∫ x, f x * φ x ∂μ‖ ≤ ‖φ 0‖ * ‖fourierL1 μ f‖`.
* `IsPositiveDefinite.exists_measure_integral_toAddChar`: **Bochner's theorem** (existence).
* `AddPontryaginDual.measure_ext_of_integral_toAddChar`: a finite regular measure `ν` on the
  Pontryagin dual is determined by the function `x ↦ ∫ χ, χ x ∂ν` (uniqueness in Bochner's
  theorem).
* `AddPontryaginDual.ae_eq_zero_of_fourierIntegralInv_eq_zero`: the inverse Fourier transform is
  injective on `L¹` of the Pontryagin dual.

## Implementation notes

We follow the proof of [W. Rudin, *Fourier Analysis on Groups*, Section 1.4][rudin1962], which
only uses the Gelfand theory of `L¹(G)` (and neither the Gelfand–Naimark–Segal construction nor
the Krein–Milman theorem).

## References

* [W. Rudin, *Fourier Analysis on Groups*, Section 1.4][rudin1962]
* [G. B. Folland, *A Course in Abstract Harmonic Analysis*, Section 4.2][folland2016]
-/

@[expose] public section

open MeasureTheory Measure Filter Topology
open scoped ComplexOrder ComplexConjugate ZeroAtInfty ENNReal NNReal

variable {G : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
  [LocallyCompactSpace G]

section Estimate

variable [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsAddHaarMeasure] [μ.Regular]

omit [AddCommGroup G] [IsTopologicalAddGroup G] [LocallyCompactSpace G] [μ.IsAddHaarMeasure]
  [μ.Regular] in
private theorem integrable_coeFn_mul {φ : G → ℂ} (hφc : Continuous φ) {C : ℝ}
    (hφ : ∀ x, ‖φ x‖ ≤ C) (f : Lp ℂ 1 μ) : Integrable (fun x ↦ f x * φ x) μ :=
  (L1.integrable_coeFn f).mul_bdd hφc.aestronglyMeasurable (.of_forall hφ)

/-- The continuous linear functional `f ↦ ∫ x, f x * φ x ∂μ` on `L¹(G)` associated with a bounded
continuous function `φ`. -/
private noncomputable def integralMulCLM {φ : G → ℂ} (hφc : Continuous φ) {C : ℝ}
    (hφ : ∀ x, ‖φ x‖ ≤ C) : Lp ℂ 1 μ →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun f ↦ ∫ x, f x * φ x ∂μ
      map_add' := fun f g ↦ by
        rw [← integral_add (integrable_coeFn_mul μ hφc hφ f) (integrable_coeFn_mul μ hφc hφ g)]
        refine integral_congr_ae ?_
        filter_upwards [Lp.coeFn_add f g] with x hx
        rw [hx, Pi.add_apply, add_mul]
      map_smul' := fun c f ↦ by
        rw [RingHom.id_apply, smul_eq_mul, ← integral_const_mul]
        refine integral_congr_ae ?_
        filter_upwards [Lp.coeFn_smul c f] with x hx
        rw [hx, Pi.smul_apply, smul_eq_mul, mul_assoc] }
    C fun f ↦ by
      rw [L1.norm_eq_integral_norm, ← integral_const_mul]
      refine norm_integral_le_of_norm_le ((L1.integrable_coeFn f).norm.const_mul C)
        (.of_forall fun x ↦ ?_)
      rw [norm_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right (hφ x) (norm_nonneg _)

/-- If `φ` is continuous and positive definite, then `∫ x, (g * g⋆) x * φ x ∂μ ≥ 0` for all `g`
in `L¹(G)`. -/
private theorem IsPositiveDefinite.integralMulCLM_mul_involution_nonneg {φ : G → ℂ}
    (hφ : IsPositiveDefinite φ) (hφc : Continuous φ) (g : Lp ℂ 1 μ) :
    0 ≤ integralMulCLM μ hφc hφ.norm_apply_le (g * L1.involution g) := by
  set T : Lp ℂ 1 μ →L[ℂ] ℂ := integralMulCLM μ hφc hφ.norm_apply_le
  have hT (g : Lp ℂ 1 μ) : T g = ∫ x, g x * φ x ∂μ := rfl
  -- `T (g * h⋆) = ∫ y, g y * ∫ z, conj (h z) * φ (-z + y)`.
  have hTmul (g h : Lp ℂ 1 μ) : T (g * L1.involution h) =
      ∫ y, g y * ∫ z, conj (h z) * φ (-z + y) ∂μ ∂μ := by
    rw [L1.mul_def, ← T.integral_comp_comm (L1.integrable_smul_translate g _)]
    refine integral_congr_ae (.of_forall fun y ↦ ?_)
    beta_reduce
    rw [map_smul, smul_eq_mul, hT]
    congr 1
    calc ∫ x, (DomAddAct.mk (-y) +ᵥ L1.involution h : Lp ℂ 1 μ) x * φ x ∂μ
      _ = ∫ x, conj (h (-(-y + x))) * φ x ∂μ := by
        refine integral_congr_ae ?_
        filter_upwards [DomAddAct.vadd_Lp_ae_eq (DomAddAct.mk (-y)) (L1.involution h),
          (measurePreserving_add_left μ (-y)).quasiMeasurePreserving.tendsto_ae.eventually
            (L1.coeFn_involution h)] with x h1 h2
        simp only [Equiv.symm_apply_apply, vadd_eq_add] at h1
        rw [h1, h2]
      _ = ∫ x, conj (h (-x)) * φ (y + x) ∂μ := by
        rw [← integral_add_left_eq_self (fun x ↦ conj (h (-x)) * φ (y + x)) (-y)]
        simp only [add_neg_cancel_left]
      _ = ∫ z, conj (h z) * φ (-z + y) ∂μ := by
        rw [← integral_neg_eq_self (fun z ↦ conj (h z) * φ (-z + y)) μ]
        simp only [neg_neg, add_comm]
  -- `T (g * g⋆) ≥ 0`: by density, we may assume that `g` is continuous with compact support.
  have hpos (g : Lp ℂ 1 μ) : 0 ≤ T (g * L1.involution g) := by
    refine Dense.induction (Lp.dense_hasCompactSupport_continuous (E := ℂ) (μ := μ)
      ENNReal.one_ne_top) ?_ (isClosed_Ici.preimage
        (T.continuous.comp (continuous_id.mul L1.continuous_involution))) g
    rintro g ⟨u, hgu, hus, huc⟩
    have hin (y : G) : ∫ z, conj (g z) * φ (-z + y) ∂μ = ∫ z, conj (u z) * φ (-z + y) ∂μ :=
      integral_congr_ae (by filter_upwards [hgu] with z hz; rw [hz])
    have : T (g * L1.involution g) = ∫ y, ∫ z, conj (u z) * φ (-z + y) * u y ∂μ ∂μ := by
      rw [hTmul]
      refine integral_congr_ae ?_
      filter_upwards [hgu] with y hy
      rw [hy, hin, mul_comm, integral_mul_const]
    rw [this, integral_integral_swap_of_hasCompactSupport
      (f := fun y z ↦ conj (u z) * φ (-z + y) * u y)
      (((Complex.continuous_conj.comp (huc.comp continuous_snd)).mul
        (hφc.comp (continuous_snd.neg.add continuous_fst))).mul (huc.comp continuous_fst))
      (.intro (hus.isCompact.prod hus.isCompact) fun p hp ↦ by
        by_cases h1 : p.1 ∈ tsupport u
        · have h2 : p.2 ∉ tsupport u := fun h2 ↦ hp ⟨h1, h2⟩
          simp [Function.uncurry, image_eq_zero_of_notMem_tsupport h2]
        · simp [Function.uncurry, image_eq_zero_of_notMem_tsupport h1])]
    exact hφ.integral_integral_nonneg hφc huc hus
  exact hpos g

open AddPontryaginDual in
/-- The key estimate in the proof of Bochner's theorem: the linear functional
`f ↦ ∫ x, f x * φ x ∂μ` on `L¹(G)` associated with a continuous positive definite function `φ`
is bounded with respect to the uniform norm of the Fourier transform. -/
theorem IsPositiveDefinite.norm_integral_mul_le {φ : G → ℂ} (hφ : IsPositiveDefinite φ)
    (hφc : Continuous φ) (f : Lp ℂ 1 μ) :
    ‖∫ x, f x * φ x ∂μ‖ ≤ ‖φ 0‖ * ‖fourierL1 μ f‖ := by
  -- Write `T f = ∫ x, f x * φ x ∂μ`, `g⋆ = L1.involution g` and `c = ‖φ 0‖`.
  set c := ‖φ 0‖ with hc
  let T : Lp ℂ 1 μ →L[ℂ] ℂ := integralMulCLM μ hφc hφ.norm_apply_le
  have hT (g : Lp ℂ 1 μ) : T g = ∫ x, g x * φ x ∂μ := rfl
  have hTn (g : Lp ℂ 1 μ) : ‖T g‖ ≤ c * ‖g‖ :=
    (T.le_opNorm g).trans (mul_le_mul_of_nonneg_right
      (LinearMap.mkContinuous_norm_le _ (norm_nonneg _) _) (norm_nonneg _))
  change ‖T f‖ ≤ c * ‖fourierL1 μ f‖
  have hpos (g : Lp ℂ 1 μ) : 0 ≤ T (g * L1.involution g) :=
    hφ.integralMulCLM_mul_involution_nonneg μ hφc g
  have hre (g : Lp ℂ 1 μ) : (T (g * L1.involution g)).re = ‖T (g * L1.involution g)‖ := by
    have h0 := Complex.nonneg_iff.1 (hpos g)
    rw [← Complex.abs_re_eq_norm.2 h0.2.symm, abs_of_nonneg h0.1]
  -- `T (g⋆) = conj (T g)`.
  have hTinv (g : Lp ℂ 1 μ) : T (L1.involution g) = conj (T g) := by
    rw [hT, hT, ← integral_conj, ← integral_neg_eq_self (fun x ↦ conj (g x * φ x)) μ]
    refine integral_congr_ae ?_
    filter_upwards [L1.coeFn_involution g] with x hx
    rw [hx, map_mul, hφ.apply_neg, Complex.conj_conj]
  have hTsymm (g h : Lp ℂ 1 μ) : T (g * L1.involution h) = conj (T (h * L1.involution g)) := by
    rw [← hTinv, L1.involution_mul, L1.involution_involution, mul_comm]
  -- Hence `(g, h) ↦ T (h * g⋆)` is a positive semidefinite Hermitian form, and it satisfies the
  -- Cauchy–Schwarz inequality.
  let core : PreInnerProductSpace.Core ℂ (Lp ℂ 1 μ) :=
    { inner := fun g h ↦ T (h * L1.involution g)
      conj_inner_symm := fun g h ↦ (hTsymm h g).symm
      re_inner_nonneg := fun g ↦ (norm_nonneg _).trans (hre g).ge
      add_left := fun g h k ↦ by simp only [L1.involution_add, mul_add, map_add]
      smul_left := fun g h r ↦ by
        simp only [L1.involution_smul, mul_smul_comm, map_smul, smul_eq_mul] }
  have hCS (g h : Lp ℂ 1 μ) : ‖T (h * L1.involution g)‖ ^ 2 ≤
      ‖T (g * L1.involution g)‖ * ‖T (h * L1.involution h)‖ := by
    have := @InnerProductSpace.Core.inner_mul_inner_self_le ℂ _ _ _ _ core g h
    change ‖T (h * L1.involution g)‖ * ‖T (g * L1.involution h)‖ ≤
      (T (g * L1.involution g)).re * (T (h * L1.involution h)).re at this
    rwa [hTsymm g h, RCLike.norm_conj, ← sq, hre, hre] at this
  -- Using approximate units, we get `‖T g‖ ^ 2 ≤ c * ‖T (g * g⋆)‖`.
  have hCS' (g : Lp ℂ 1 μ) : ‖T g‖ ^ 2 ≤ c * ‖T (g * L1.involution g)‖ := by
    set r := ‖T (g * L1.involution g)‖
    suffices h : ‖T g‖ ≤ √(c * r) from
      (pow_le_pow_left₀ (norm_nonneg _) h 2).trans_eq (Real.sq_sqrt (by positivity))
    refine le_of_forall_pos_le_add fun ε hε ↦ ?_
    obtain ⟨u, hu1, hu⟩ := L1.exists_norm_eq_one_norm_mul_sub_lt g (ε := ε / (c + 1))
      (by positivity)
    have h1 : ‖T (u * g)‖ ≤ √(c * r) := by
      have := hCS (L1.involution u) g
      rw [L1.involution_involution, mul_comm g u] at this
      refine Real.le_sqrt_of_sq_le (this.trans ?_)
      gcongr
      calc ‖T (L1.involution u * u)‖
        _ ≤ c * ‖L1.involution u * u‖ := hTn _
        _ ≤ c * (‖L1.involution u‖ * ‖u‖) := by gcongr; exact norm_mul_le _ _
        _ = c := by rw [L1.norm_involution, hu1, mul_one, mul_one]
    calc ‖T g‖
      _ = ‖T (u * g) - T (u * g - g)‖ := by rw [← map_sub, sub_sub_cancel]
      _ ≤ ‖T (u * g)‖ + ‖T (u * g - g)‖ := norm_sub_le _ _
      _ ≤ √(c * r) + c * (ε / (c + 1)) :=
        add_le_add h1 ((hTn _).trans (by gcongr))
      _ ≤ √(c * r) + ε := by
        gcongr
        rw [← mul_div_assoc, div_le_iff₀ (by positivity)]
        nlinarith [norm_nonneg (φ 0)]
  -- The case `c = 0` is trivial.
  obtain hc0 | hc0 := (norm_nonneg (φ 0)).eq_or_lt
  · have := hTn f
    rw [hc, ← hc0, zero_mul] at this ⊢
    exact this
  -- Iterating this inequality with `h 0 = f * f⋆` and `h (k + 1) = h k * h k`, we get
  -- `(‖T f‖ / c) ^ 2 ^ (k + 1) ≤ ‖h k‖`.
  let h : ℕ → Lp ℂ 1 μ := fun k ↦ Nat.rec (f * L1.involution f) (fun _ g ↦ g * g) k
  have hsucc (k : ℕ) : h (k + 1) = h k * h k := rfl
  have hsa (k : ℕ) : L1.involution (h k) = h k := by
    induction k with
    | zero =>
      change L1.involution (f * L1.involution f) = f * L1.involution f
      rw [L1.involution_mul, L1.involution_involution, mul_comm]
    | succ k ih => rw [hsucc, L1.involution_mul, ih]
  have hiter (k : ℕ) : (‖T f‖ / c) ^ 2 ^ (k + 1) ≤ ‖T (h k)‖ / c := by
    induction k with
    | zero =>
      rw [zero_add, pow_one, div_pow, div_le_div_iff₀ (by positivity) hc0]
      calc ‖T f‖ ^ 2 * c
        _ ≤ c * ‖T (h 0)‖ * c := by gcongr; exact hCS' f
        _ = ‖T (h 0)‖ * c ^ 2 := by ring
    | succ k ih =>
      calc (‖T f‖ / c) ^ 2 ^ (k + 1 + 1)
        _ = ((‖T f‖ / c) ^ 2 ^ (k + 1)) ^ 2 := by rw [← pow_mul, ← pow_succ]
        _ ≤ (‖T (h k)‖ / c) ^ 2 := pow_le_pow_left₀ (by positivity) ih 2
        _ = ‖T (h k)‖ ^ 2 / c ^ 2 := div_pow _ _ _
        _ ≤ c * ‖T (h (k + 1))‖ / c ^ 2 := by
          gcongr
          have := hCS' (h k)
          rwa [hsa k] at this
        _ = ‖T (h (k + 1))‖ / c := by field_simp
  have hiter' (k : ℕ) : (‖T f‖ / c) ^ 2 ^ (k + 1) ≤ ‖h k‖ :=
    (hiter k).trans (div_le_of_le_mul₀ hc0.le (norm_nonneg _) (by rw [mul_comm]; exact hTn _))
  -- By Gelfand's formula, `‖h k‖ ^ (1 / 2 ^ k)` tends to the spectral radius of `h 0`, which is
  -- `‖fourierL1 μ (h 0)‖ = ‖fourierL1 μ f‖ ^ 2`.
  let b : WithLp 1 (Unitization ℂ (Lp ℂ 1 μ)) := WithLp.toLp 1 (Unitization.inr (h 0))
  have hb (k : ℕ) : b ^ 2 ^ k = WithLp.toLp 1 (Unitization.inr (h k)) := by
    induction k with
    | zero => rw [pow_zero, pow_one]
    | succ k ih =>
      rw [pow_succ, pow_mul, ih, sq, hsucc, Unitization.inr_mul]
      rfl
  have hρ : spectralRadius ℂ b = ENNReal.ofReal (‖fourierL1 μ f‖ ^ 2) := by
    have h0 : ‖fourierL1 μ (h 0)‖ = ‖fourierL1 μ f‖ ^ 2 := by
      change ‖fourierL1 μ (f * L1.involution f)‖ = _
      rw [map_mul, fourierL1_involution, sq]
      exact CStarRing.norm_self_mul_star
    have hq : quasispectrum ℂ b =
        quasispectrum ℂ (Unitization.inr (h 0) : Unitization ℂ (Lp ℂ 1 μ)) := by
      rw [quasispectrum_eq_spectrum_union_zero, quasispectrum_eq_spectrum_union_zero,
        ← AlgEquiv.spectrum_eq (WithLp.unitizationAlgEquiv (𝕜 := ℂ) (A := Lp ℂ 1 μ) ℂ) b]
      rfl
    rw [← h0, ofReal_norm, enorm_eq_nnnorm, ← spectralRadius_inr_eq_nnnorm_fourierL1,
      spectralRadius, spectralRadius, hq]
  have hle : ENNReal.ofReal ((‖T f‖ / c) ^ 2) ≤ spectralRadius ℂ b := by
    refine ge_of_tendsto' ((spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius b).comp
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : 1 < 2))) fun k ↦ ?_
    have ht : ENNReal.ofReal ((‖T f‖ / c) ^ 2) ^ 2 ^ k ≤ ‖b ^ 2 ^ k‖₊ := by
      rw [hb, WithLp.unitization_nnnorm_inr, ← ENNReal.ofReal_pow (by positivity), ← pow_mul,
        ← pow_succ', ← enorm_eq_nnnorm, ← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (hiter' k)
    calc ENNReal.ofReal ((‖T f‖ / c) ^ 2)
      _ = (ENNReal.ofReal ((‖T f‖ / c) ^ 2) ^ 2 ^ k) ^ (1 / (2 ^ k : ℕ) : ℝ) := by
        rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul, mul_one_div_cancel (by positivity),
          ENNReal.rpow_one]
      _ ≤ _ := ENNReal.rpow_le_rpow ht (by positivity)
  rw [hρ, ENNReal.ofReal_le_ofReal_iff (by positivity),
    sq_le_sq₀ (by positivity) (norm_nonneg _), div_le_iff₀ hc0, mul_comm] at hle
  exact hle

end Estimate

namespace AddPontryaginDual

variable [MeasurableSpace (AddPontryaginDual G)] [BorelSpace (AddPontryaginDual G)]

section FourierStieltjes

omit [IsTopologicalAddGroup G] [LocallyCompactSpace G] [MeasurableSpace (AddPontryaginDual G)]
  [BorelSpace (AddPontryaginDual G)] in
/-- The elements of the Pontryagin dual are positive definite functions. -/
theorem isPositiveDefinite_toAddChar (χ : AddPontryaginDual G) :
    IsPositiveDefinite fun x ↦ (χ.toAddChar x : ℂ) :=
  χ.toAddChar.isPositiveDefinite

omit [IsTopologicalAddGroup G] [LocallyCompactSpace G] in
/-- The function `x ↦ ∫ χ, χ x ∂ν` is positive definite for every finite measure `ν` on the
Pontryagin dual. -/
theorem isPositiveDefinite_integral_toAddChar (ν : Measure (AddPontryaginDual G))
    [IsFiniteMeasure ν] : IsPositiveDefinite fun x : G ↦ ∫ χ, (χ.toAddChar x : ℂ) ∂ν := by
  -- The matrix is the Gram matrix of the functions `χ ↦ χ (x i)` in `L²(ν)`.
  refine isPositiveDefinite_iff_forall_fin.2 fun n x ↦ ?_
  have he (i : Fin n) : MemLp (fun χ : AddPontryaginDual G ↦ (χ.toAddChar (x i) : ℂ)) 2 ν :=
    .of_bound (continuous_subtype_val.comp (continuous_toAddChar_apply _)).aestronglyMeasurable
      1 (.of_forall fun χ ↦ by simp)
  convert Matrix.posSemidef_gram ℂ fun i ↦ (he i).toLp _ using 1
  ext i j
  simp only [Matrix.of_apply, Matrix.gram_apply, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [(he i).coeFn_toLp, (he j).coeFn_toLp] with χ hi hj
  simp [hi, hj, AddChar.map_add_eq_mul, AddChar.map_neg_eq_inv, ← Circle.coe_inv_eq_conj,
    mul_comm]

/-- The function `x ↦ ∫ χ, χ x ∂ν` is continuous for every finite regular measure `ν` on the
Pontryagin dual. -/
theorem continuous_integral_toAddChar (ν : Measure (AddPontryaginDual G)) [IsFiniteMeasure ν]
    [ν.Regular] : Continuous fun x : G ↦ ∫ χ, (χ.toAddChar x : ℂ) ∂ν := by
  -- This is `continuous_fourierIntegralInv` applied to the constant function `1`.
  refine (continuous_fourierIntegralInv (ν := ν) (integrable_const (1 : ℂ))).congr fun x ↦ ?_
  simp [fourierIntegralInv, Circle.smul_def]

/-- A finite regular measure `ν` on the Pontryagin dual is determined by the function
`x ↦ ∫ χ, χ x ∂ν`. This is the uniqueness part of Bochner's theorem. -/
theorem measure_ext_of_integral_toAddChar {ν₁ ν₂ : Measure (AddPontryaginDual G)}
    [IsFiniteMeasure ν₁] [IsFiniteMeasure ν₂] [ν₁.Regular] [ν₂.Regular]
    (h : ∀ x : G, ∫ χ, (χ.toAddChar x : ℂ) ∂ν₁ = ∫ χ, (χ.toAddChar x : ℂ) ∂ν₂) : ν₁ = ν₂ := by
  borelize G
  let μ : Measure G := Measure.addHaar
  -- By the multiplication formula, the two measures have the same integrals against the Fourier
  -- transforms of the elements of `L¹(G)`.
  have h1 (f : Lp ℂ 1 μ) : ∫ χ, fourierL1 μ f χ ∂ν₁ = ∫ χ, fourierL1 μ f χ ∂ν₂ := by
    have e (ν : Measure (AddPontryaginDual G)) [IsFiniteMeasure ν] [ν.Regular] :
        ∫ χ, fourierL1 μ f χ ∂ν = ∫ x, f x * ∫ χ, (χ.toAddChar (-x) : ℂ) ∂ν ∂μ := by
      simpa [fourierIntegralInv, Circle.smul_def] using
        integral_fourierIntegral_mul (ν := ν) (L1.integrable_coeFn f) (integrable_const (1 : ℂ))
    rw [e, e]
    simp_rw [h]
  -- Since these are dense, the same holds for all continuous functions vanishing at infinity.
  have h2 (Φ : C₀(AddPontryaginDual G, ℂ)) : ∫ χ, Φ χ ∂ν₁ = ∫ χ, Φ χ ∂ν₂ := by
    exact (denseRange_fourierL1 μ).induction_on Φ (isClosed_eq
      ZeroAtInftyContinuousMap.continuous_integral
      ZeroAtInftyContinuousMap.continuous_integral) h1
  refine Measure.ext_of_integral_eq_on_compactlySupported fun g ↦ ?_
  have := h2 ⟨⟨fun χ ↦ (g χ : ℂ), Complex.continuous_ofReal.comp g.continuous⟩,
    (g.hasCompactSupport.comp_left Complex.ofReal_zero).is_zero_at_infty⟩
  simpa [integral_complex_ofReal] using this

/-- The inverse Fourier transform is injective on `L¹` of the Pontryagin dual. -/
theorem ae_eq_zero_of_fourierIntegralInv_eq_zero {ν : Measure (AddPontryaginDual G)} [ν.Regular]
    {F : AddPontryaginDual G → ℂ} (hF : Integrable F ν) (h : fourierIntegralInv ν F = 0) :
    F =ᵐ[ν] 0 := by
  -- By the multiplication formula, `∫ χ, Φ χ * F χ ∂ν = 0` for all `Φ` in the range of
  -- `fourierL1 μ`, hence for all continuous functions `Φ` vanishing at infinity.
  borelize G
  let μ : Measure G := Measure.addHaar
  have h1 (f : Lp ℂ 1 μ) : ∫ χ, fourierL1 μ f χ * F χ ∂ν = 0 := by
    have := integral_fourierIntegral_mul (ν := ν) (L1.integrable_coeFn f) hF
    rw [h] at this
    simpa using this
  have h2 (Φ : C₀(AddPontryaginDual G, ℂ)) : ∫ χ, Φ χ * F χ ∂ν = 0 :=
    (denseRange_fourierL1 μ).induction_on Φ
      (isClosed_eq (ZeroAtInftyContinuousMap.continuous_integral_mul hF) continuous_const) h1
  refine hF.ae_eq_zero_of_forall_integral_smul_eq_zero fun g hg hgc ↦ ?_
  simpa using h2 ⟨⟨fun χ ↦ (g χ : ℂ), Complex.continuous_ofReal.comp hg⟩,
    (hgc.comp_left Complex.ofReal_zero).is_zero_at_infty⟩

end FourierStieltjes

section Bochner

section CLM

variable [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsAddHaarMeasure] [μ.Regular]
  {φ : G → ℂ} (hφ : IsPositiveDefinite φ) (hφc : Continuous φ)

/-- The continuous linear functional on `C₀(AddPontryaginDual G, ℂ)` associated with a continuous
positive definite function `φ`: by `IsPositiveDefinite.norm_integral_mul_le`, the linear functional
`fourierL1 μ f ↦ ∫ x, f x * φ (-x) ∂μ` is well defined and bounded on the range of `fourierL1 μ`,
which is dense. -/
private noncomputable def bochnerCLM : C₀(AddPontryaginDual G, ℂ) →L[ℂ] ℂ :=
  (integralMulCLM μ (hφc.comp continuous_neg) hφ.comp_neg.norm_apply_le).toLinearMap.extendOfNorm
    { toFun := fourierL1 μ, map_add' := map_add _, map_smul' := map_smul _ }

omit [MeasurableSpace (AddPontryaginDual G)] [BorelSpace (AddPontryaginDual G)] in
private theorem bochnerCLM_fourierL1 (f : Lp ℂ 1 μ) :
    bochnerCLM μ hφ hφc (fourierL1 μ f) = ∫ x, f x * φ (-x) ∂μ :=
  LinearMap.extendOfNorm_eq (denseRange_fourierL1 μ)
    ⟨_, hφ.comp_neg.norm_integral_mul_le μ (hφc.comp continuous_neg)⟩ f

omit [MeasurableSpace (AddPontryaginDual G)] [BorelSpace (AddPontryaginDual G)] in
private theorem bochnerCLM_mul_star_nonneg (F : C₀(AddPontryaginDual G, ℂ)) :
    0 ≤ bochnerCLM μ hφ hφc (F * star F) := by
  -- This holds for `F` in the range of `fourierL1 μ`, which is dense.
  refine (denseRange_fourierL1 μ).induction_on F (isClosed_Ici.preimage
    ((bochnerCLM μ hφ hφc).continuous.comp (continuous_id.mul continuous_star))) fun f ↦ ?_
  rw [← fourierL1_involution, ← map_mul, bochnerCLM_fourierL1]
  exact hφ.comp_neg.integralMulCLM_mul_involution_nonneg μ (hφc.comp continuous_neg) f

/-- If `bochnerCLM μ hφ hφc` is the integral against `ν`, then `φ x = ∫ χ, χ x ∂ν`. -/
private theorem eq_integral_toAddChar_of_bochnerCLM {ν : Measure (AddPontryaginDual G)}
    [IsFiniteMeasure ν] [ν.Regular]
    (hν : ∀ F : C₀(AddPontryaginDual G, ℂ), ∫ χ, F χ ∂ν = bochnerCLM μ hφ hφc F) (x : G) :
    φ x = ∫ χ, (χ.toAddChar x : ℂ) ∂ν := by
  have hψ := hφ.comp_neg
  have hψc : Continuous fun x ↦ φ (-x) := hφc.comp continuous_neg
  -- By the multiplication formula, `∫ y, f y * D y ∂μ = 0` for all `f`, where
  -- `D y = φ (-y) - ∫ χ, χ (-y) ∂ν`.
  have hρ : Continuous fun y : G ↦ ∫ χ, (χ.toAddChar (-y) : ℂ) ∂ν :=
    (continuous_integral_toAddChar ν).comp continuous_neg
  have hρ' (y : G) : ‖∫ χ, (χ.toAddChar (-y) : ℂ) ∂ν‖ ≤ ν.real Set.univ :=
    (norm_integral_le_of_norm_le_const (.of_forall fun χ ↦ by simp)).trans_eq (one_mul _)
  let D : G → ℂ := fun y ↦ φ (-y) - ∫ χ, (χ.toAddChar (-y) : ℂ) ∂ν
  have hD : Continuous D := hψc.sub hρ
  have key (f : Lp ℂ 1 μ) : ∫ y, f y * D y ∂μ = 0 := by
    have h1 : ∫ y, f y * φ (-y) ∂μ = ∫ y, f y * ∫ χ, (χ.toAddChar (-y) : ℂ) ∂ν ∂μ :=
      calc ∫ y, f y * φ (-y) ∂μ
        _ = ∫ χ, fourierL1 μ f χ ∂ν := by rw [hν, bochnerCLM_fourierL1]
        _ = _ := by
          simpa [fourierIntegralInv, Circle.smul_def] using integral_fourierIntegral_mul
            (ν := ν) (L1.integrable_coeFn f) (integrable_const (1 : ℂ))
    simp_rw [D, mul_sub]
    rw [integral_sub (integrable_coeFn_mul μ hψc hψ.norm_apply_le f)
      (integrable_coeFn_mul μ hρ hρ' f), h1]
    exact sub_self _
  -- Since `D` is continuous, it vanishes everywhere.
  have hD0 (y₀ : G) : D y₀ = 0 := by
    by_contra hy₀
    obtain ⟨u, hu1, -, huc, hu01⟩ := exists_continuous_one_zero_of_isCompact
      (isCompact_singleton (x := y₀)) isClosed_empty (Set.disjoint_empty _)
    have hfc : Continuous fun y ↦ conj (D y) * (u y : ℂ) :=
      (Complex.continuous_conj.comp hD).mul (Complex.continuous_ofReal.comp u.continuous)
    have hfs : HasCompactSupport fun y ↦ conj (D y) * (u y : ℂ) :=
      (huc.comp_left Complex.ofReal_zero).mul_left
    have hfi : Integrable (fun y ↦ conj (D y) * (u y : ℂ)) μ :=
      hfc.integrable_of_hasCompactSupport hfs
    have h0 : ∫ y, conj (D y) * (u y : ℂ) * D y ∂μ = 0 := by
      rw [← key (hfi.toL1 _)]
      refine integral_congr_ae ?_
      filter_upwards [hfi.coeFn_toL1] with y hy
      rw [hy]
    have hpos : 0 < ∫ y, ‖D y‖ ^ 2 * u y ∂μ :=
      Continuous.integral_pos_of_hasCompactSupport_nonneg_ne_zero (x := y₀)
        ((hD.norm.pow 2).mul u.continuous) huc.mul_left
        (fun y ↦ mul_nonneg (sq_nonneg _) (hu01 y).1)
        (by simpa [hu1 (Set.mem_singleton y₀)] using hy₀)
    have : ∫ y, conj (D y) * (u y : ℂ) * D y ∂μ = ((∫ y, ‖D y‖ ^ 2 * u y ∂μ : ℝ) : ℂ) := by
      rw [← integral_complex_ofReal]
      refine integral_congr_ae (.of_forall fun y ↦ ?_)
      simp only [Complex.ofReal_mul, Complex.ofReal_pow, ← Complex.conj_mul']
      ring
    rw [this] at h0
    exact hpos.ne' (by exact_mod_cast h0)
  simpa [D, sub_eq_zero] using hD0 (-x)

end CLM

open Classical in
/-- The finite regular measure on the Pontryagin dual associated with a continuous positive
definite function `φ` by Bochner's theorem: the measure representing the linear functional
`fourierL1 μ f ↦ ∫ x, f x * φ (-x) ∂μ`, where `μ` is a Haar measure on `G`. It is defined to be `0`
if `φ` is not continuous and positive definite. -/
@[no_expose]
noncomputable def bochnerMeasure (φ : G → ℂ) : Measure (AddPontryaginDual G) :=
  if h : IsPositiveDefinite φ ∧ Continuous φ then
    letI : MeasurableSpace G := borel G
    haveI : BorelSpace G := ⟨rfl⟩
    ComplexRMK.rieszMeasure (bochnerCLM Measure.addHaar h.1 h.2)
      (bochnerCLM_mul_star_nonneg Measure.addHaar h.1 h.2)
  else 0

variable {φ : G → ℂ}

instance : IsFiniteMeasure (bochnerMeasure φ) := by
  unfold bochnerMeasure
  split_ifs <;> infer_instance

instance : (bochnerMeasure φ).Regular := by
  unfold bochnerMeasure
  split_ifs <;> infer_instance

theorem integral_toAddChar_bochnerMeasure (hφ : IsPositiveDefinite φ) (hφc : Continuous φ)
    (x : G) : ∫ χ, (χ.toAddChar x : ℂ) ∂bochnerMeasure φ = φ x := by
  unfold bochnerMeasure
  split_ifs with h
  · borelize G
    exact (eq_integral_toAddChar_of_bochnerCLM Measure.addHaar hφ hφc
      (ComplexRMK.integral_rieszMeasure _ _) x).symm
  · exact absurd ⟨hφ, hφc⟩ h

/-- **Bochner's theorem**: every continuous positive definite function on a locally compact
abelian group is of the form `x ↦ ∫ χ, χ x ∂ν` for a finite regular measure `ν` on the Pontryagin
dual. -/
theorem _root_.IsPositiveDefinite.exists_measure_integral_toAddChar
    (hφ : IsPositiveDefinite φ) (hφc : Continuous φ) :
    ∃ ν : Measure (AddPontryaginDual G), IsFiniteMeasure ν ∧ ν.Regular ∧
      ∀ x, φ x = ∫ χ, (χ.toAddChar x : ℂ) ∂ν :=
  ⟨bochnerMeasure φ, inferInstance, inferInstance,
    fun x ↦ (integral_toAddChar_bochnerMeasure hφ hφc x).symm⟩

/-- The measure given by Bochner's theorem is unique. -/
theorem eq_bochnerMeasure {ν : Measure (AddPontryaginDual G)} [IsFiniteMeasure ν] [ν.Regular]
    (h : ∀ x, φ x = ∫ χ, (χ.toAddChar x : ℂ) ∂ν) : ν = bochnerMeasure φ := by
  have hφ : IsPositiveDefinite φ := by
    convert isPositiveDefinite_integral_toAddChar ν using 1
    exact funext h
  have hφc : Continuous φ := by
    convert continuous_integral_toAddChar ν using 1
    exact funext h
  refine measure_ext_of_integral_toAddChar fun x ↦ ?_
  rw [integral_toAddChar_bochnerMeasure hφ hφc, h x]

@[simp]
theorem bochnerMeasure_integral_toAddChar (ν : Measure (AddPontryaginDual G)) [IsFiniteMeasure ν]
    [ν.Regular] : bochnerMeasure (fun x : G ↦ ∫ χ, (χ.toAddChar x : ℂ) ∂ν) = ν :=
  (eq_bochnerMeasure fun _ ↦ rfl).symm

end Bochner

section Parseval

variable [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsAddHaarMeasure] [μ.Regular]

omit [μ.IsAddHaarMeasure] in
/-- A Parseval-type formula: the integral of an integrable function `f` against a continuous
positive definite function `φ` is the integral of the Fourier transform of `f` against the measure
associated with `φ`. -/
theorem integral_mul_eq_integral_fourierIntegral_neg {φ : G → ℂ} (hφ : IsPositiveDefinite φ)
    (hφc : Continuous φ) {f : G → ℂ} (hf : Integrable f μ) :
    ∫ x, f x * φ x ∂μ = ∫ χ, fourierIntegral μ f (-χ) ∂bochnerMeasure φ := by
  -- Replace `φ x` by `∫ χ, χ x ∂bochnerMeasure φ` and exchange the two integrals.
  simpa [fourierIntegralInv, Circle.smul_def, integral_toAddChar_bochnerMeasure hφ hφc] using
    integral_mul_fourierIntegralInv (ν := bochnerMeasure φ) hf (integrable_const (1 : ℂ))

end Parseval

end AddPontryaginDual
