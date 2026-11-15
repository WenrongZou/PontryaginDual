/-
Copyright (c) 2026 Wenrong Zou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wenrong Zou
-/
module

public import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real

import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Measures with a continuous density and compactly supported functions

Let `μ` be a regular measure on a locally compact space and let `ρ` be a bounded continuous
nonnegative function. The measure `μ.withDensity ρ` is not known to be regular a priori, so
`MeasureTheory.Measure.ext_of_integral_eq_on_compactlySupported` does not apply to it directly.
In this file we prove some results which replace it.

## Main statements

* `MeasureTheory.Measure.withDensity_apply_le_of_forall_isCompact_le`: an upper bound for
  `μ.withDensity ρ` on compact closed sets extends to all measurable sets.
* `MeasureTheory.Measure.withDensity_eq_of_forall_integral_mul_eq`: if `ν` is a finite regular
  measure such that `∫ x, ψ x * ρ x ∂μ = ∫ x, ψ x ∂ν` for all continuous functions `ψ` with
  compact support, then `ν = μ.withDensity ρ`.
* `MeasureTheory.eLpNorm_two_le_of_forall_enorm_integral_mul_le`: a bounded continuous function
  `h` such that `u ↦ ∫ x, u x * h x ∂μ` is bounded with respect to the `L²` norm on continuous
  functions with compact support is in `L²`.
-/

public section

open MeasureTheory Set
open scoped CompactlySupported ENNReal NNReal ComplexConjugate

namespace MeasureTheory

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] {μ ν : Measure X}
  [μ.Regular]

namespace Measure

/-- Let `μ` be a regular measure, let `ρ` be a bounded continuous nonnegative function and let `τ`
be a monotone function on sets with `τ univ ≠ ∞`. If `μ.withDensity ρ K ≤ τ K` for all compact
closed sets `K`, then this holds for all measurable sets. -/
theorem withDensity_apply_le_of_forall_isCompact_le [R1Space X] {ρ : X → ℝ≥0} (hρ : Continuous ρ)
    {C : ℝ≥0} (hρC : ∀ x, ρ x ≤ C) {τ : Set X → ℝ≥0∞} (hτ : Monotone τ) (hτ' : τ univ ≠ ∞)
    (h : ∀ K, IsCompact K → IsClosed K → μ.withDensity (fun x ↦ (ρ x : ℝ≥0∞)) K ≤ τ K)
    {A : Set X} (hA : MeasurableSet A) : μ.withDensity (fun x ↦ (ρ x : ℝ≥0∞)) A ≤ τ A := by
  set m : Measure X := μ.withDensity fun x ↦ (ρ x : ℝ≥0∞) with hm
  have hmC : m ≤ (C : ℝ≥0∞) • μ := by
    rw [← withDensity_const]
    exact withDensity_mono (.of_forall fun x ↦ ENNReal.coe_le_coe.2 (hρC x))
  -- The inequality holds on sets of finite `μ`-measure, which are approximated from inside by
  -- compact closed sets.
  have hfin {B : Set X} (hB : MeasurableSet B) (hμB : μ B ≠ ∞) : m B ≤ τ B := by
    refine ENNReal.le_of_forall_pos_le_add fun ε hε _ ↦ ?_
    obtain ⟨K, hKB, hKc, hKcl, hBK⟩ := hB.exists_isCompact_isClosed_sdiff_lt hμB
      (ε := ((ε / (C + 1) : ℝ≥0) : ℝ≥0∞)) (by positivity)
    have hCε : C * (ε / (C + 1)) ≤ ε := by
      rw [← mul_div_assoc, div_le_iff₀ (by positivity), mul_add, mul_one, mul_comm]
      exact le_self_add
    calc m B
      _ ≤ m (B ∩ K) + m (B \ K) := measure_le_inter_add_sdiff m B K
      _ ≤ τ B + C * μ (B \ K) :=
        add_le_add ((measure_mono inter_subset_right).trans ((h K hKc hKcl).trans (hτ hKB)))
          (hmC _)
      _ ≤ τ B + ε := by
        gcongr
        exact (mul_le_mul_right hBK.le _).trans (by exact_mod_cast hCε)
  -- The sets `V n = {x | 1 < n * ρ x}` have finite `μ`-measure and cover `{x | ρ x ≠ 0}`.
  let V : ℕ → Set X := fun n ↦ {x | 1 < (n : ℝ≥0) * ρ x}
  have hVo (n : ℕ) : IsOpen (V n) := isOpen_lt continuous_const (continuous_const.mul hρ)
  have hVm : Monotone V := fun n n' hn x (hx : 1 < (n : ℝ≥0) * ρ x) ↦
    hx.trans_le (mul_le_mul_of_nonneg_right (Nat.cast_le.2 hn) zero_le)
  have hVμ (n : ℕ) : μ (V n) ≠ ∞ := by
    rw [(hVo n).measure_eq_iSup_isCompact]
    refine ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.natCast_ne_top n) hτ')
      (iSup₂_le fun K hKV ↦ iSup_le fun hKc ↦ ?_)
    have hKV' : closure K ⊆ V n := hKc.closure_subset_of_isOpen (hVo n) hKV
    calc μ K
      _ ≤ μ (closure K) := measure_mono subset_closure
      _ = ∫⁻ _ in closure K, 1 ∂μ := (setLIntegral_one _).symm
      _ ≤ ∫⁻ x in closure K, n * ρ x ∂μ :=
        setLIntegral_mono' isClosed_closure.measurableSet fun x hx ↦ by
          exact_mod_cast (hKV' hx).le
      _ = n * m (closure K) := by
        rw [lintegral_const_mul _ hρ.measurable.coe_nnreal_ennreal,
          withDensity_apply _ isClosed_closure.measurableSet]
      _ ≤ n * τ univ :=
        mul_le_mul_right ((h _ hKc.closure isClosed_closure).trans (hτ (subset_univ _))) _
  have h0 : m (A \ ⋃ n, V n) = 0 := by
    have hAV : MeasurableSet (A \ ⋃ n, V n) :=
      hA.diff (MeasurableSet.iUnion fun n ↦ (hVo n).measurableSet)
    rw [hm, withDensity_apply _ hAV]
    refine le_antisymm ((setLIntegral_mono' hAV fun x hx ↦ ?_).trans_eq lintegral_zero) zero_le
    by_contra hx0
    have hρx : 0 < ρ x := pos_iff_ne_zero.2 fun h ↦ hx0 (by simp [h])
    obtain ⟨n, hn⟩ := exists_nat_gt (ρ x)⁻¹
    exact hx.2 (mem_iUnion.2 ⟨n, (inv_lt_iff_one_lt_mul₀ hρx).1 hn⟩)
  calc m A
    _ ≤ m (A ∩ ⋃ n, V n) + m (A \ ⋃ n, V n) := measure_le_inter_add_sdiff m A _
    _ = ⨆ n, m (A ∩ V n) := by
      rw [h0, add_zero, inter_iUnion,
        Monotone.measure_iUnion fun n n' hn ↦ inter_subset_inter_right A (hVm hn)]
    _ ≤ τ A := iSup_le fun n ↦
      (hfin (hA.inter (hVo n).measurableSet)
        (ne_top_of_le_ne_top (hVμ n) (measure_mono inter_subset_right))).trans
        (hτ inter_subset_left)

/-- Let `μ` and `ν` be regular measures, with `ν` finite, and let `ρ` be a bounded continuous
nonnegative function. If `∫ x, ψ x * ρ x ∂μ = ∫ x, ψ x ∂ν` for all continuous functions `ψ` with
compact support, then `ν` has density `ρ` with respect to `μ`. -/
theorem withDensity_eq_of_forall_integral_mul_eq [T2Space X] [LocallyCompactSpace X] [ν.Regular]
    [IsFiniteMeasure ν] {ρ : X → ℝ≥0} (hρ : Continuous ρ) {C : ℝ≥0} (hρC : ∀ x, ρ x ≤ C)
    (h : ∀ ψ : C_c(X, ℝ), ∫ x, ψ x * ρ x ∂μ = ∫ x, ψ x ∂ν) :
    μ.withDensity (fun x ↦ (ρ x : ℝ≥0∞)) = ν := by
  set m : Measure X := μ.withDensity fun x ↦ (ρ x : ℝ≥0∞) with hm
  have : IsLocallyFiniteMeasure m := .withDensity_coe hρ
  have hint (ψ : C_c(X, ℝ)) : ∫ x, ψ x ∂m = ∫ x, ψ x ∂ν := by
    rw [hm, integral_withDensity_eq_integral_smul hρ.measurable, ← h]
    simp only [NNReal.smul_def, smul_eq_mul, mul_comm]
  -- `m ≤ ν` on compact sets, since `ν` is outer regular, hence on all measurable sets.
  have hle : m ≤ ν := Measure.le_iff.2 fun A hA ↦
    withDensity_apply_le_of_forall_isCompact_le hρ hρC (τ := ν) (fun _ _ hst ↦ measure_mono hst)
      (measure_ne_top ν univ) (fun K hK _ ↦
        RealRMK.measure_le_of_isCompact_of_integral (fun ψ ↦ (hint ψ).le) hK) hA
  -- The two measures have the same total mass.
  have huniv : ν univ ≤ m univ := by
    rw [isOpen_univ.measure_eq_iSup_isCompact]
    refine iSup₂_le fun K _ ↦ iSup_le fun hKc ↦ ?_
    obtain ⟨f, hf1, hf2, -, hf4⟩ :=
      exists_continuousMap_one_of_isCompact_subset_isOpen hKc isOpen_univ K.subset_univ
    let ψ : C_c(X, ℝ) := ⟨f, hf2⟩
    have hψ0 (ξ : Measure X) : 0 ≤ᵐ[ξ] ψ := .of_forall fun x ↦ (hf4 x).1
    calc ν K
      _ = ∫⁻ _ in K, 1 ∂ν := (setLIntegral_one K).symm
      _ ≤ ∫⁻ x in K, ENNReal.ofReal (ψ x) ∂ν :=
        setLIntegral_mono' hKc.measurableSet fun x hx ↦ by
          change 1 ≤ ENNReal.ofReal (f x)
          rw [hf1 hx, Pi.one_apply, ENNReal.ofReal_one]
      _ ≤ ∫⁻ x, ENNReal.ofReal (ψ x) ∂ν := setLIntegral_le_lintegral K _
      _ = ∫⁻ x, ENNReal.ofReal (ψ x) ∂m := by
        rw [← ofReal_integral_eq_lintegral_ofReal ψ.integrable (hψ0 ν),
          ← ofReal_integral_eq_lintegral_ofReal ψ.integrable (hψ0 m), hint]
      _ ≤ ∫⁻ _, 1 ∂m := lintegral_mono fun x ↦ by
        change ENNReal.ofReal (f x) ≤ 1
        exact ENNReal.ofReal_le_one.2 (hf4 x).2
      _ = m univ := lintegral_one
  have : IsFiniteMeasure m := isFiniteMeasure_of_le ν hle
  exact Measure.eq_of_le_of_measure_univ_eq hle (le_antisymm (hle univ) huniv)

end Measure

omit [TopologicalSpace X] [BorelSpace X] [μ.Regular] in
theorem sq_eLpNorm_two {E : Type*} [NormedAddCommGroup E] {f : X → E}
    (hf : AEStronglyMeasurable f μ) : eLpNorm f 2 μ ^ 2 = ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ := by
  simpa using eLpNorm_nnreal_pow_eq_lintegral (p := 2) two_ne_zero hf

/-- If `h` is a bounded continuous function such that
`‖∫ x, u x * h x ∂μ‖ₑ ≤ C * eLpNorm u 2 μ` for all continuous functions `u` with compact support,
then `eLpNorm h 2 μ ≤ C`. -/
theorem eLpNorm_two_le_of_forall_enorm_integral_mul_le [R1Space X] [LocallyCompactSpace X]
    {h : X → ℂ} (hh : Continuous h) {M : ℝ} (hM : ∀ x, ‖h x‖ ≤ M) {C : ℝ≥0∞}
    (hC : ∀ u : X → ℂ, Continuous u → HasCompactSupport u →
      ‖∫ x, u x * h x ∂μ‖ₑ ≤ C * eLpNorm u 2 μ) :
    eLpNorm h 2 μ ≤ C := by
  rcases eq_or_ne C ∞ with rfl | hCtop
  · exact le_top
  -- Testing the assumption against `u = θ * conj h`, we get `∫ x, θ x * ‖h x‖ ^ 2 ∂μ ≤ C ^ 2` if
  -- `θ` is continuous with compact support and `0 ≤ θ ≤ 1`.
  have hint {θ : X → ℝ} (hθc : Continuous θ) (hθs : HasCompactSupport θ) :
      Integrable (fun x ↦ θ x * ‖h x‖ ^ 2) μ :=
    (hθc.mul (hh.norm.pow 2)).integrable_of_hasCompactSupport hθs.mul_right
  have hθ {θ : X → ℝ} (hθc : Continuous θ) (hθs : HasCompactSupport θ)
      (hθ01 : ∀ x, 0 ≤ θ x ∧ θ x ≤ 1) : ENNReal.ofReal (∫ x, θ x * ‖h x‖ ^ 2 ∂μ) ≤ C ^ 2 := by
    set I := ∫ x, θ x * ‖h x‖ ^ 2 ∂μ with hI
    have hI0 : 0 ≤ I := integral_nonneg fun x ↦ mul_nonneg (hθ01 x).1 (sq_nonneg _)
    have hu : Continuous fun x ↦ (θ x : ℂ) * conj (h x) :=
      (Complex.continuous_ofReal.comp hθc).mul (Complex.continuous_conj.comp hh)
    have huc : HasCompactSupport fun x ↦ (θ x : ℂ) * conj (h x) :=
      (hθs.comp_left Complex.ofReal_zero).mul_right
    have h1 : ∫ x, (θ x : ℂ) * conj (h x) * h x ∂μ = (I : ℂ) := by
      rw [hI, ← integral_complex_ofReal]
      refine integral_congr_ae (.of_forall fun x ↦ ?_)
      simp only [Complex.ofReal_mul, Complex.ofReal_pow, mul_assoc, Complex.conj_mul']
    have h2 : eLpNorm (fun x ↦ (θ x : ℂ) * conj (h x)) 2 μ ^ 2 ≤ ENNReal.ofReal I := by
      rw [sq_eLpNorm_two hu.aestronglyMeasurable, hI, ofReal_integral_eq_lintegral_ofReal
        (hint hθc hθs) (.of_forall fun x ↦ mul_nonneg (hθ01 x).1 (sq_nonneg _))]
      refine lintegral_mono fun x ↦ ?_
      rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [norm_mul, Complex.norm_real, RCLike.norm_conj, Real.norm_eq_abs, mul_pow, sq_abs]
      exact mul_le_mul_of_nonneg_right (by nlinarith [hθ01 x]) (sq_nonneg _)
    have h3 : ENNReal.ofReal I ≤ C * eLpNorm (fun x ↦ (θ x : ℂ) * conj (h x)) 2 μ := by
      have := hC _ hu huc
      rwa [h1, ← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg hI0] at this
    rcases eq_or_ne (ENNReal.ofReal I) 0 with h0 | h0
    · rw [h0]
      exact zero_le
    · refine (ENNReal.mul_le_mul_iff_left h0 ENNReal.ofReal_ne_top).1 ?_
      calc ENNReal.ofReal I * ENNReal.ofReal I
        _ ≤ C * eLpNorm (fun x ↦ (θ x : ℂ) * conj (h x)) 2 μ *
            (C * eLpNorm (fun x ↦ (θ x : ℂ) * conj (h x)) 2 μ) := mul_le_mul' h3 h3
        _ = C ^ 2 * eLpNorm (fun x ↦ (θ x : ℂ) * conj (h x)) 2 μ ^ 2 := by ring
        _ ≤ C ^ 2 * ENNReal.ofReal I := by gcongr
  -- Hence the measure with density `‖h x‖ ^ 2` is bounded by `C ^ 2` on compact closed sets.
  have hK (K : Set X) (hKc : IsCompact K) (hKcl : IsClosed K) :
      μ.withDensity (fun x ↦ ((‖h x‖₊ ^ 2 : ℝ≥0) : ℝ≥0∞)) K ≤ C ^ 2 := by
    obtain ⟨θ, hθ1, hθ2, -, hθ4⟩ :=
      exists_continuousMap_one_of_isCompact_subset_isOpen hKc isOpen_univ K.subset_univ
    rw [withDensity_apply _ hKcl.measurableSet]
    calc ∫⁻ x in K, ((‖h x‖₊ ^ 2 : ℝ≥0) : ℝ≥0∞) ∂μ
      _ ≤ ∫⁻ x in K, ENNReal.ofReal (θ x * ‖h x‖ ^ 2) ∂μ :=
        setLIntegral_mono' hKcl.measurableSet fun x hx ↦ by
          rw [hθ1 hx, Pi.one_apply, one_mul, ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm,
            enorm_eq_nnnorm, ENNReal.coe_pow]
      _ ≤ ∫⁻ x, ENNReal.ofReal (θ x * ‖h x‖ ^ 2) ∂μ := setLIntegral_le_lintegral K _
      _ = ENNReal.ofReal (∫ x, θ x * ‖h x‖ ^ 2 ∂μ) :=
        (ofReal_integral_eq_lintegral_ofReal (hint θ.continuous hθ2)
          (.of_forall fun x ↦ mul_nonneg (hθ4 x).1 (sq_nonneg _))).symm
      _ ≤ C ^ 2 := hθ θ.continuous hθ2 hθ4
  have hfin : eLpNorm h 2 μ ^ 2 ≤ C ^ 2 := by
    rw [sq_eLpNorm_two hh.aestronglyMeasurable]
    refine le_of_eq_of_le ?_ (Measure.withDensity_apply_le_of_forall_isCompact_le
      (ρ := fun x ↦ ‖h x‖₊ ^ 2) (hh.nnnorm.pow 2) (C := M.toNNReal ^ 2) (fun x ↦ ?_)
      (τ := fun _ ↦ C ^ 2) monotone_const (ENNReal.pow_ne_top hCtop) hK MeasurableSet.univ)
    · rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
      simp only [enorm_eq_nnnorm, ENNReal.coe_pow]
    · gcongr
      exact (Real.le_toNNReal_iff_coe_le ((norm_nonneg _).trans (hM x))).2 (hM x)
  exact (ENNReal.pow_le_pow_left_iff two_ne_zero).1 hfin

end MeasureTheory
