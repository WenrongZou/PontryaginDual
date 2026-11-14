/-
Copyright (c) 2026 Wenrong Zou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wenrong Zou
-/
module

public import Mathlib.Analysis.Complex.Order
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
public import Mathlib.Topology.ContinuousMap.ZeroAtInfty

/-!
# Riesz–Markov–Kakutani representation theorem for `C₀(X, ℂ)`

A continuous linear functional `Λ` on `C₀(X, ℂ)` such that `0 ≤ Λ (F * star F)` for all `F` is the
integral against a finite regular measure. This follows from the version of the theorem for
positive linear functionals on `C_c(X, ℝ)`.

## Main definitions

* `ComplexRMK.rieszMeasure Λ hΛ`: the finite regular measure representing `Λ`.

## Main statements

* `ComplexRMK.integral_rieszMeasure`: `∫ x, F x ∂rieszMeasure Λ hΛ = Λ F`.
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ZeroAtInfty CompactlySupported ComplexOrder ComplexConjugate

namespace ZeroAtInftyContinuousMap

variable {X : Type*} [TopologicalSpace X]

theorem norm_apply_le_norm (F : C₀(X, ℂ)) (x : X) : ‖F x‖ ≤ ‖F‖ := by
  rw [← norm_toBCF_eq_norm]
  exact F.toBCF.norm_coe_le_norm x

theorem norm_le_of_forall_norm_apply_le (F : C₀(X, ℂ)) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ x, ‖F x‖ ≤ C) : ‖F‖ ≤ C := by
  rw [← norm_toBCF_eq_norm]
  exact (BoundedContinuousFunction.norm_le hC).2 h

variable [MeasurableSpace X] [OpensMeasurableSpace X] {ν : Measure X}

/-- If `F` is integrable, then `Φ ↦ ∫ x, Φ x * F x ∂ν` is continuous on `C₀(X, ℂ)`. -/
theorem continuous_integral_mul {F : X → ℂ} (hF : Integrable F ν) :
    Continuous fun Φ : C₀(X, ℂ) ↦ ∫ x, Φ x * F x ∂ν := by
  have hi (Φ : C₀(X, ℂ)) : Integrable (fun x ↦ Φ x * F x) ν :=
    hF.bdd_mul (c := ‖Φ‖) (map_continuous Φ).aestronglyMeasurable
      (.of_forall Φ.norm_apply_le_norm)
  refine (LipschitzWith.of_dist_le_mul (K := (∫ x, ‖F x‖ ∂ν).toNNReal) fun Φ Ψ ↦ ?_).continuous
  rw [dist_eq_norm, dist_eq_norm, ← integral_sub (hi Φ) (hi Ψ),
    Real.coe_toNNReal _ (integral_nonneg fun _ ↦ norm_nonneg _), mul_comm]
  refine (norm_integral_le_of_norm_le (hF.norm.const_mul ‖Φ - Ψ‖)
    (.of_forall fun x ↦ ?_)).trans_eq (integral_const_mul _ _)
  rw [← sub_mul, norm_mul]
  exact mul_le_mul_of_nonneg_right ((Φ - Ψ).norm_apply_le_norm x) (norm_nonneg _)

/-- For a finite measure `ν`, the integral is continuous on `C₀(X, ℂ)`. -/
theorem continuous_integral [IsFiniteMeasure ν] :
    Continuous fun Φ : C₀(X, ℂ) ↦ ∫ x, Φ x ∂ν := by
  simpa using continuous_integral_mul (ν := ν) (integrable_const (1 : ℂ))

end ZeroAtInftyContinuousMap

namespace ComplexRMK

variable {X : Type*} [TopologicalSpace X]

/-- A real-valued continuous function with compact support, as an element of `C₀(X, ℂ)`. -/
def ofReal (g : C_c(X, ℝ)) : C₀(X, ℂ) :=
  ⟨⟨fun x ↦ (g x : ℂ), Complex.continuous_ofReal.comp g.continuous⟩,
    (g.hasCompactSupport.comp_left Complex.ofReal_zero).is_zero_at_infty⟩

@[simp]
theorem ofReal_apply (g : C_c(X, ℝ)) (x : X) : ofReal g x = (g x : ℂ) :=
  rfl

variable (Λ : C₀(X, ℂ) →L[ℂ] ℂ) (hΛ : ∀ F, 0 ≤ Λ (F * star F))

include hΛ in
/-- If `0 ≤ Λ (F * star F)` for all `F`, then `Λ` is real on real-valued functions, and it is
nonnegative on nonnegative functions. -/
theorem apply_ofReal_im_and_re (g : C_c(X, ℝ)) :
    (Λ (ofReal g)).im = 0 ∧ (0 ≤ g → 0 ≤ (Λ (ofReal g)).re) := by
  -- Write `g` as a difference of squares.
  let r : C_c(X, ℝ) → C₀(X, ℂ) := fun g ↦
    ⟨⟨fun x ↦ (√(max (g x) 0) : ℂ), Complex.continuous_ofReal.comp
      (Real.continuous_sqrt.comp (g.continuous.max continuous_const))⟩,
      (g.hasCompactSupport.comp_left (g := fun t : ℝ ↦ (√(max t 0) : ℂ))
        (by simp)).is_zero_at_infty⟩
  have hr (g : C_c(X, ℝ)) (x : X) : (r g * star (r g)) x = (max (g x) 0 : ℝ) := by
    change (√(max (g x) 0) : ℂ) * conj (√(max (g x) 0) : ℂ) = _
    rw [Complex.conj_ofReal, ← Complex.ofReal_mul, Real.mul_self_sqrt (le_max_right _ _)]
  have hg : ofReal g = r g * star (r g) - r (-g) * star (r (-g)) := by
    ext x
    rw [_root_.sub_apply, hr, hr, ofReal_apply, ← Complex.ofReal_sub]
    exact congrArg _ (max_zero_sub_eq_self (g x)).symm
  have h1 := Complex.nonneg_iff.1 (hΛ (r g))
  have h2 := Complex.nonneg_iff.1 (hΛ (r (-g)))
  refine ⟨by rw [hg, map_sub, Complex.sub_im, ← h1.2, ← h2.2, sub_zero], fun hg0 ↦ ?_⟩
  have : r (-g) = 0 := by
    ext x
    change (√(max (-g x) 0) : ℂ) = 0
    rw [max_eq_right (neg_nonpos.2 (hg0 x)), Real.sqrt_zero, Complex.ofReal_zero]
  rw [hg, this, zero_mul, sub_zero]
  exact h1.1

/-- The positive linear functional on `C_c(X, ℝ)` induced by a continuous linear functional `Λ`
on `C₀(X, ℂ)` such that `0 ≤ Λ (F * star F)` for all `F`. -/
noncomputable def toPositiveLinearMap : C_c(X, ℝ) →ₚ[ℝ] ℝ :=
  PositiveLinearMap.mk₀
    { toFun := fun g ↦ (Λ (ofReal g)).re
      map_add' := fun g₁ g₂ ↦ by
        rw [show ofReal (g₁ + g₂) = ofReal g₁ + ofReal g₂ from
          ZeroAtInftyContinuousMap.ext fun x ↦ Complex.ofReal_add _ _, map_add, Complex.add_re]
      map_smul' := fun c g ↦ by
        rw [show ofReal (c • g) = (c : ℂ) • ofReal g from
          ZeroAtInftyContinuousMap.ext fun x ↦ Complex.ofReal_mul _ _, map_smul, smul_eq_mul,
          Complex.re_ofReal_mul]
        rfl }
    fun g hg ↦ (apply_ofReal_im_and_re Λ hΛ g).2 hg

variable [T2Space X] [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X]

/-- The finite regular measure representing a continuous linear functional `Λ` on `C₀(X, ℂ)` such
that `0 ≤ Λ (F * star F)` for all `F`. -/
noncomputable def rieszMeasure : Measure X :=
  RealRMK.rieszMeasure (toPositiveLinearMap Λ hΛ)

instance : (rieszMeasure Λ hΛ).Regular :=
  RealRMK.regular_rieszMeasure _

theorem apply_ofReal (g : C_c(X, ℝ)) : Λ (ofReal g) = ∫ x, (g x : ℂ) ∂rieszMeasure Λ hΛ := by
  rw [integral_complex_ofReal, rieszMeasure, RealRMK.integral_rieszMeasure]
  exact Complex.ext rfl (by simpa using (apply_ofReal_im_and_re Λ hΛ g).1)

instance : IsFiniteMeasure (rieszMeasure Λ hΛ) := by
  -- The measure is finite since `Λ` is bounded.
  refine ⟨lt_of_le_of_lt ?_ (ENNReal.ofReal_lt_top (r := ‖Λ‖))⟩
  rw [isOpen_univ.measure_eq_iSup_isCompact]
  refine iSup₂_le fun K _ ↦ iSup_le fun hK ↦ ?_
  obtain ⟨f, hf1, hf2, -, hf4⟩ :=
    exists_continuousMap_one_of_isCompact_subset_isOpen hK isOpen_univ K.subset_univ
  refine (RealRMK.rieszMeasure_le_of_eq_one (toPositiveLinearMap Λ hΛ) (f := ⟨f, hf2⟩)
    (fun x ↦ (hf4 x).1) hK fun x hx ↦ hf1 hx).trans (ENNReal.ofReal_le_ofReal ?_)
  calc (Λ (ofReal ⟨f, hf2⟩)).re
    _ ≤ ‖Λ (ofReal ⟨f, hf2⟩)‖ := Complex.re_le_norm _
    _ ≤ ‖Λ‖ * ‖ofReal ⟨f, hf2⟩‖ := Λ.le_opNorm _
    _ ≤ ‖Λ‖ * 1 := by
      gcongr
      refine ZeroAtInftyContinuousMap.norm_le_of_forall_norm_apply_le _ zero_le_one fun x ↦ ?_
      rw [ofReal_apply, Complex.norm_real, Real.norm_eq_abs]
      change |f x| ≤ 1
      exact abs_le.2 ⟨by linarith [(hf4 x).1], (hf4 x).2⟩
    _ = ‖Λ‖ := mul_one _

/-- The **Riesz–Markov–Kakutani representation theorem** for `C₀(X, ℂ)`: a continuous linear
functional `Λ` such that `0 ≤ Λ (F * star F)` for all `F` is the integral against the finite
regular measure `rieszMeasure Λ hΛ`. -/
theorem integral_rieszMeasure (F : C₀(X, ℂ)) : ∫ x, F x ∂rieszMeasure Λ hΛ = Λ F := by
  -- By continuity, it suffices to approximate `F` by functions with compact support.
  refine (isClosed_eq ZeroAtInftyContinuousMap.continuous_integral Λ.continuous).closure_subset
    (Metric.mem_closure_iff.2 fun ε hε ↦ ?_)
  obtain ⟨t, ht, htF⟩ := mem_cocompact.1
    ((zero_at_infty F).eventually (Metric.ball_mem_nhds 0 (half_pos hε)))
  obtain ⟨e, he1, -, hec, he01⟩ :=
    exists_continuous_one_zero_of_isCompact ht isClosed_empty (Set.disjoint_empty _)
  let g₁ : C_c(X, ℝ) := ⟨⟨fun x ↦ e x * (F x).re,
    e.continuous.mul (Complex.continuous_re.comp (map_continuous F))⟩, hec.mul_right⟩
  let g₂ : C_c(X, ℝ) := ⟨⟨fun x ↦ e x * (F x).im,
    e.continuous.mul (Complex.continuous_im.comp (map_continuous F))⟩, hec.mul_right⟩
  have hi (g : C_c(X, ℝ)) : Integrable (fun x ↦ (g x : ℂ)) (rieszMeasure Λ hΛ) :=
    (Complex.continuous_ofReal.comp g.continuous).integrable_of_hasCompactSupport
      (g.hasCompactSupport.comp_left Complex.ofReal_zero)
  have hi' : Integrable (fun x ↦ Complex.I • (g₂ x : ℂ)) (rieszMeasure Λ hΛ) :=
    (hi g₂).smul Complex.I
  refine ⟨ofReal g₁ + Complex.I • ofReal g₂, ?_, ?_⟩
  · change ∫ x, ((g₁ x : ℂ) + Complex.I • (g₂ x : ℂ)) ∂rieszMeasure Λ hΛ =
      Λ (ofReal g₁ + Complex.I • ofReal g₂)
    rw [map_add, map_smul, apply_ofReal Λ hΛ, apply_ofReal Λ hΛ, integral_add (hi g₁) hi',
      integral_smul]
  · rw [dist_eq_norm]
    refine lt_of_le_of_lt (ZeroAtInftyContinuousMap.norm_le_of_forall_norm_apply_le _
      (half_pos hε).le fun x ↦ ?_) (half_lt_self hε)
    have hx : (F - (ofReal g₁ + Complex.I • ofReal g₂)) x = ((1 - e x : ℝ) : ℂ) * F x := by
      change F x - ((e x * (F x).re : ℝ) + Complex.I * (e x * (F x).im : ℝ)) = _
      apply Complex.ext
      · simp
        ring
      · simp
        ring
    rw [hx, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    by_cases hxt : x ∈ t
    · simpa [he1 hxt] using (half_pos hε).le
    · have h1 : ‖F x‖ ≤ ε / 2 := le_of_lt (by simpa using htF hxt)
      have h2 : |1 - e x| ≤ 1 := abs_le.2 ⟨by linarith [(he01 x).2], by linarith [(he01 x).1]⟩
      exact (mul_le_of_le_one_left (norm_nonneg _) h2).trans h1

end ComplexRMK
