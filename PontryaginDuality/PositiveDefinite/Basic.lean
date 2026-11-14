/-
Copyright (c) 2026 Wenrong Zou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wenrong Zou
-/
module

public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Measure.Haar.Unique

import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.MeasureTheory.Function.LpSpace.DomAct.Continuous

/-!
# Positive definite functions on groups

A function `φ : G → 𝕜` on an additive group is *positive definite* (or *of positive type*) if the
kernel `(x, y) ↦ φ (-x + y)` is positive semidefinite, i.e. if for all `x₁, …, xₙ : G` the matrix
`(φ (-xᵢ + xⱼ))ᵢⱼ` is positive semidefinite. Note that, despite the classical name, this is a
semidefiniteness condition.

## Main definitions

* `IsPositiveDefinite φ`: the function `φ : G → 𝕜` is positive definite. It is defined as the
  positive semidefiniteness of the matrix `(φ (-x + y))` indexed by `G` (see `Matrix.PosSemidef`).

## Main statements

* `isPositiveDefinite_iff_forall_fin`: the formulation in terms of finite families.
* `IsPositiveDefinite.apply_neg`, `IsPositiveDefinite.norm_apply_le`: a positive definite function
  satisfies `φ (-x) = conj (φ x)` and `‖φ x‖ ≤ ‖φ 0‖`.
* `AddChar.isPositiveDefinite`: unitary characters are positive definite.
* `isPositiveDefinite_integral_mul_conj`: the function `x ↦ ∫ y, f y * conj (f (-x + y)) ∂μ` is
  positive definite for `f` in `L²`. This is the convolution of `f` and `x ↦ conj (f (-x))`.
* `IsPositiveDefinite.integral_integral_nonneg`: the integral form of positive definiteness for
  continuous functions.
* `exists_isPositiveDefinite_hasCompactSupport`: on a locally compact group, there are continuous
  positive definite functions supported in arbitrarily small neighborhoods of `0`.

## References

* [G. B. Folland, *A Course in Abstract Harmonic Analysis*, Section 3.3][folland2016]
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ComplexOrder ComplexConjugate ENNReal Pointwise

variable {G 𝕜 : Type*} [AddGroup G] [RCLike 𝕜]

/-- A function `φ : G → 𝕜` on an additive group is positive definite if the kernel
`(x, y) ↦ φ (-x + y)` is positive semidefinite, i.e. if the matrix `(φ (-x + y))` indexed by `G`
is positive semidefinite. See `isPositiveDefinite_iff_forall_fin` for the formulation in terms of
finite families of elements of `G`. -/
def IsPositiveDefinite (φ : G → 𝕜) : Prop :=
  (Matrix.of fun x y : G ↦ φ (-x + y)).PosSemidef

namespace IsPositiveDefinite

variable {φ ψ : G → 𝕜}

/-- If `φ` is positive definite, then the matrix `(φ (-xᵢ + xⱼ))ᵢⱼ` is positive semidefinite for
every family `x` of elements of `G`. -/
theorem posSemidef (hφ : IsPositiveDefinite φ) {ι : Type*} (x : ι → G) :
    (Matrix.of fun i j ↦ φ (-x i + x j)).PosSemidef :=
  Matrix.PosSemidef.submatrix hφ x

theorem sum_nonneg (hφ : IsPositiveDefinite φ) {ι : Type*} [Fintype ι] (x : ι → G) (c : ι → 𝕜) :
    0 ≤ ∑ i, ∑ j, conj (c i) * φ (-x i + x j) * c j := by
  simpa [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc] using
    (hφ.posSemidef x).dotProduct_mulVec_nonneg c

theorem apply_zero_nonneg (hφ : IsPositiveDefinite φ) : 0 ≤ φ 0 := by
  simpa using hφ.sum_nonneg (fun _ : Fin 1 ↦ (0 : G)) fun _ ↦ 1

theorem apply_neg (hφ : IsPositiveDefinite φ) (x : G) : φ (-x) = conj (φ x) := by
  simpa using (hφ.isHermitian.apply x 0).symm

theorem norm_apply_le (hφ : IsPositiveDefinite φ) (x : G) : ‖φ x‖ ≤ ‖φ 0‖ := by
  -- The determinant of the matrix associated with `0` and `x` is nonnegative.
  have h := (hφ.posSemidef ![0, x]).det_nonneg
  rw [Matrix.det_fin_two] at h
  simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, neg_zero, zero_add,
    add_zero, neg_add_cancel, hφ.apply_neg, RCLike.mul_conj, sub_nonneg] at h
  have h0 : φ 0 = (‖φ 0‖ : 𝕜) := (RCLike.norm_of_nonneg' hφ.apply_zero_nonneg).symm
  rw [h0, ← RCLike.ofReal_mul, ← RCLike.ofReal_pow, RCLike.ofReal_le_ofReal, ← sq] at h
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h

protected theorem zero : IsPositiveDefinite (0 : G → 𝕜) :=
  Matrix.PosSemidef.zero

protected theorem add (hφ : IsPositiveDefinite φ) (hψ : IsPositiveDefinite ψ) :
    IsPositiveDefinite (φ + ψ) :=
  Matrix.PosSemidef.add hφ hψ

protected theorem smul (hφ : IsPositiveDefinite φ) {c : ℝ} (hc : 0 ≤ c) :
    IsPositiveDefinite (c • φ) :=
  Matrix.PosSemidef.smul hφ hc

/-- The product of two positive definite functions is positive definite. This follows from the
Schur product theorem. -/
protected theorem mul (hφ : IsPositiveDefinite φ) (hψ : IsPositiveDefinite ψ) :
    IsPositiveDefinite (φ * ψ) :=
  Matrix.PosSemidef.hadamard hφ hψ

protected theorem star (hφ : IsPositiveDefinite φ) : IsPositiveDefinite fun x ↦ conj (φ x) := by
  unfold IsPositiveDefinite
  convert Matrix.PosSemidef.transpose hφ using 1
  ext x y
  simp [← hφ.apply_neg]

theorem comp_neg (hφ : IsPositiveDefinite φ) : IsPositiveDefinite fun x ↦ φ (-x) := by
  simpa only [hφ.apply_neg] using hφ.star

end IsPositiveDefinite

/-- A function `φ` is positive definite if and only if the matrix `(φ (-xᵢ + xⱼ))ᵢⱼ` is positive
semidefinite for all `x₁, …, xₙ : G`. -/
theorem isPositiveDefinite_iff_forall_fin {φ : G → 𝕜} :
    IsPositiveDefinite φ ↔
      ∀ (n : ℕ) (x : Fin n → G), (Matrix.of fun i j ↦ φ (-x i + x j)).PosSemidef := by
  refine ⟨fun h n x ↦ h.posSemidef x, fun h ↦ ⟨?_, fun c ↦ ?_⟩⟩
  · exact Matrix.IsHermitian.ext fun x y ↦ by simpa using (h 2 ![x, y]).isHermitian.apply 0 1
  · classical
    have hs : ((Matrix.of fun x y : G ↦ φ (-x + y)).submatrix (↑) (↑) :
        Matrix c.support c.support 𝕜).PosSemidef :=
      (Matrix.posSemidef_submatrix_equiv c.support.equivFin.symm).1
        (h _ fun i ↦ (c.support.equivFin.symm i : G))
    simpa [Finsupp.sum, ← Finset.sum_attach c.support, ← Finset.subtype_mem_eq_attach,
      ← Finsupp.subtypeDomain_apply, ← Finsupp.support_subtypeDomain] using hs.2 _

/-- Unitary characters are positive definite. -/
theorem AddChar.isPositiveDefinite (ψ : AddChar G Circle) :
    IsPositiveDefinite fun x ↦ (ψ x : ℂ) := by
  refine isPositiveDefinite_iff_forall_fin.2 fun n x ↦ ?_
  convert Matrix.posSemidef_vecMulVec_self_star fun i ↦ (ψ (-x i) : ℂ) using 1
  ext i j
  simp [Matrix.vecMulVec_apply, AddChar.map_add_eq_mul, AddChar.map_neg_eq_inv,
    ← Circle.coe_inv_eq_conj]

section Measure

variable [MeasurableSpace G] [TopologicalSpace G] [IsTopologicalAddGroup G] [BorelSpace G]
  {μ : Measure G}

/-- If `f` is in `L²`, then `x ↦ ∫ y, f y * conj (f (-x + y)) ∂μ` is positive definite. -/
theorem isPositiveDefinite_integral_mul_conj [μ.IsAddLeftInvariant] {f : G → 𝕜}
    (hf : MemLp f 2 μ) : IsPositiveDefinite fun x ↦ ∫ y, f y * conj (f (-x + y)) ∂μ := by
  -- The matrix is the transpose of the Gram matrix of the translates of `f` in `L²`.
  refine isPositiveDefinite_iff_forall_fin.2 fun n x ↦ ?_
  have hF (i : Fin n) : MemLp (fun z ↦ f (-x i + z)) 2 μ :=
    hf.comp_measurePreserving (measurePreserving_add_left μ (-x i))
  convert (Matrix.posSemidef_gram 𝕜 fun i ↦ (hF i).toLp _).transpose using 1
  ext i j
  simp only [Matrix.of_apply, Matrix.transpose_apply, Matrix.gram_apply, L2.inner_def]
  rw [← integral_add_left_eq_self _ (-x i)]
  refine integral_congr_ae ?_
  filter_upwards [(hF i).coeFn_toLp, (hF j).coeFn_toLp] with z hi hj
  simp [hi, hj, neg_add_rev, add_assoc]

/-- If `f` is in `L²`, then `x ↦ ∫ y, f y * conj (f (-x + y)) ∂μ` is continuous. -/
theorem continuous_integral_mul_conj [LocallyCompactSpace G] [μ.IsAddHaarMeasure] [μ.Regular]
    {f : G → 𝕜} (hf : MemLp f 2 μ) : Continuous fun x ↦ ∫ y, f y * conj (f (-x + y)) ∂μ := by
  -- Translations act continuously on `L²` (`Lp.instContinuousVAddDomAddAct`).
  have : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨ENNReal.ofNat_ne_top⟩
  have hc : Continuous fun x : G ↦ inner 𝕜 (DomAddAct.mk (-x) +ᵥ hf.toLp f) (hf.toLp f) :=
    ((DomAddAct.continuous_mk.comp continuous_neg).vadd continuous_const).inner continuous_const
  refine hc.congr fun x ↦ ?_
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp, DomAddAct.vadd_Lp_ae_eq (DomAddAct.mk (-x)) (hf.toLp f),
    (measurePreserving_add_left μ (-x)).quasiMeasurePreserving.tendsto_ae.eventually
      hf.coeFn_toLp] with y h1 h2 h3
  simp only [Equiv.symm_apply_apply, vadd_eq_add] at h2
  rw [h2, h3, h1, RCLike.inner_apply]

omit [MeasurableSpace G] [BorelSpace G] in
/-- Two-sided uniform continuity of a continuous function on a compact set. -/
private theorem exists_isOpen_dist_lt {φ : G → 𝕜} (hφ : Continuous φ) {L : Set G}
    (hL : IsCompact L) {ε : ℝ} (hε : 0 < ε) :
    ∃ W : Set G, IsOpen W ∧ (0 : G) ∈ W ∧
      ∀ a ∈ L, ∀ v ∈ W, ∀ w ∈ W, dist (φ (-v + a + w)) (φ a) < ε := by
  obtain ⟨N, hN, h⟩ := hL.mem_uniformity_of_prod (s := Set.univ) (q := ((0 : G), (0 : G)))
    (f := fun (p : G × G) (a : G) ↦ φ (-p.1 + a + p.2))
    (hφ.comp (((continuous_fst.comp continuous_fst).neg.add continuous_snd).add
      (continuous_snd.comp continuous_fst))).continuousOn (Set.mem_univ _)
    (Metric.dist_mem_uniformity hε)
  rw [nhdsWithin_univ] at hN
  obtain ⟨U₁, hU₁, U₂, hU₂, hU⟩ := mem_nhds_prod_iff.1 hN
  refine ⟨interior (U₁ ∩ U₂), isOpen_interior, mem_interior_iff_mem_nhds.2 (inter_mem hU₁ hU₂),
    fun a ha v hv w hw ↦ ?_⟩
  simpa using h (v, w) (hU ⟨(interior_subset hv).1, (interior_subset hw).2⟩) a ha

/-- A compact closed set is a finite disjoint union of measurable sets which are small with
respect to a given neighborhood of `0`. -/
private theorem exists_measurableSet_partition {K W : Set G} (hK : IsCompact K) (hK' : IsClosed K)
    (hW : IsOpen W) (h0 : (0 : G) ∈ W) :
    ∃ (n : ℕ) (p : Fin n → G) (E : Fin n → Set G), (∀ i, p i ∈ K) ∧ (∀ i, MeasurableSet (E i)) ∧
      Pairwise (Function.onFun Disjoint E) ∧ ⋃ i, E i = K ∧ ∀ i, ∀ x ∈ E i, -p i + x ∈ W := by
  have hU (p : G) : IsOpen ((fun x ↦ -p + x) ⁻¹' W) := hW.preimage (by fun_prop)
  obtain ⟨t, htK, ht⟩ := hK.elim_nhds_subcover (fun p ↦ (fun x ↦ -p + x) ⁻¹' W) fun p _ ↦
    (hU p).mem_nhds (by simpa using h0)
  let p : Fin t.card → G := fun i ↦ (t.equivFin.symm i : G)
  let A : Fin t.card → Set G := fun i ↦ (fun x ↦ -p i + x) ⁻¹' W ∩ K
  have hA (i : Fin t.card) : MeasurableSet (A i) := (hU _).measurableSet.inter hK'.measurableSet
  refine ⟨t.card, p, disjointed A, fun i ↦ htK _ (t.equivFin.symm i).2, fun i ↦ ?_,
    disjoint_disjointed A, ?_, fun i x hx ↦ (disjointed_subset A i hx).1⟩
  · rw [disjointed, Finset.sup_set_eq_biUnion]
    exact (hA i).diff (Finset.measurableSet_biUnion _ fun j _ ↦ hA j)
  · rw [iUnion_disjointed]
    refine Set.Subset.antisymm (Set.iUnion_subset fun i ↦ Set.inter_subset_right) fun x hx ↦ ?_
    obtain ⟨q, hq, hxq⟩ := Set.mem_iUnion₂.1 (ht hx)
    exact Set.mem_iUnion.2 ⟨t.equivFin ⟨q, hq⟩, by simpa [A, p] using ⟨hxq, hx⟩⟩

/-- The integral form of positive definiteness, for continuous functions. -/
theorem IsPositiveDefinite.integral_integral_nonneg [IsFiniteMeasureOnCompacts μ] {φ : G → 𝕜}
    (hφ : IsPositiveDefinite φ) (hφc : Continuous φ) {f : G → 𝕜} (hf : Continuous f)
    (hf' : HasCompactSupport f) :
    0 ≤ ∫ x, ∫ y, conj (f x) * φ (-x + y) * f y ∂μ ∂μ := by
  -- We approximate the integral by Riemann sums, which are nonnegative by
  -- `IsPositiveDefinite.sum_nonneg`.
  have hfi : Integrable f μ := hf.integrable_of_hasCompactSupport hf'
  have hfi' : Integrable (fun x ↦ conj (f x)) μ :=
    (RCLike.continuous_conj.comp hf).integrable_of_hasCompactSupport
      (hf'.comp_left (map_zero _))
  set m := ∫ x, ‖f x‖ ∂μ
  have hm : 0 ≤ m := integral_nonneg fun _ ↦ norm_nonneg _
  suffices H : ∀ ε > 0, ∃ S : 𝕜, 0 ≤ S ∧
      ‖(∫ x, ∫ y, conj (f x) * φ (-x + y) * f y ∂μ ∂μ) - S‖ ≤ ε * m * m by
    refine isClosed_Ici.closure_subset (Metric.mem_closure_iff.2 fun δ hδ ↦ ?_)
    obtain ⟨S, hS, hIS⟩ := H (δ / (m * m + 1)) (by positivity)
    refine ⟨S, hS, (dist_eq_norm _ _).trans_lt (hIS.trans_lt ?_)⟩
    rw [mul_assoc, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    exact mul_lt_mul_of_pos_left (lt_add_one _) hδ
  intro ε hε
  -- A partition `E` of the support of `f`, with points `p i`, such that `φ (-x + y)` is close to
  -- `φ (-p i + p j)` for `x ∈ E i` and `y ∈ E j`.
  obtain ⟨W, hW, h0, hWφ⟩ := exists_isOpen_dist_lt hφc
    ((hf'.isCompact.prod hf'.isCompact).image (f := fun q : G × G ↦ -q.1 + q.2) (by fun_prop)) hε
  obtain ⟨n, p, E, hpK, hE, hEd, hEK, hEW⟩ :=
    exists_measurableSet_partition hf'.isCompact (isClosed_tsupport f) hW h0
  have hφ' (i j : Fin n) (x : G) (hx : x ∈ E i) (y : G) (hy : y ∈ E j) :
      ‖φ (-x + y) - φ (-p i + p j)‖ ≤ ε := by
    have := hWφ (-p i + p j) ⟨(p i, p j), ⟨hpK i, hpK j⟩, rfl⟩ _ (hEW i x hx) _ (hEW j y hy)
    rw [dist_eq_norm] at this
    simpa [neg_add_rev, add_assoc] using this.le
  -- The Riemann sum `S` is the integral of the function `g`.
  let c : Fin n → 𝕜 := fun i ↦ ∫ x in E i, f x ∂μ
  let g (x y : G) : 𝕜 := ∑ i, ∑ j,
    (E i).indicator (fun x ↦ conj (f x)) x * φ (-p i + p j) * (E j).indicator f y
  have hg (x : G) : ∫ y, g x y ∂μ =
      ∑ i, ∑ j, (E i).indicator (fun x ↦ conj (f x)) x * φ (-p i + p j) * c j := by
    rw [integral_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦
      (hfi.indicator (hE j)).const_mul _]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [integral_finsetSum _ fun j _ ↦ (hfi.indicator (hE j)).const_mul _]
    exact Finset.sum_congr rfl fun j _ ↦ by rw [integral_const_mul, integral_indicator (hE j)]
  have hS : ∫ x, ∫ y, g x y ∂μ ∂μ = ∑ i, ∑ j, conj (c i) * φ (-p i + p j) * c j := by
    simp_rw [hg]
    rw [integral_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦
      ((hfi'.indicator (hE i)).mul_const _).mul_const _]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [integral_finsetSum _ fun j _ ↦ ((hfi'.indicator (hE i)).mul_const _).mul_const _]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [integral_mul_const, integral_mul_const, integral_indicator (hE i), integral_conj]
  -- `g` is close to the integrand.
  have hbound (x y : G) :
      ‖conj (f x) * φ (-x + y) * f y - g x y‖ ≤ ε * ‖f x‖ * ‖f y‖ := by
    by_cases hx : x ∈ tsupport f
    swap
    · have (i : Fin n) : (E i).indicator (fun x ↦ conj (f x)) x = 0 :=
        Set.indicator_apply_eq_zero.2 fun _ ↦ by simp [image_eq_zero_of_notMem_tsupport hx]
      simp [g, this, image_eq_zero_of_notMem_tsupport hx]
    by_cases hy : y ∈ tsupport f
    swap
    · have (j : Fin n) : (E j).indicator f y = 0 :=
        Set.indicator_apply_eq_zero.2 fun _ ↦ image_eq_zero_of_notMem_tsupport hy
      simp [g, this, image_eq_zero_of_notMem_tsupport hy]
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 (hEK ▸ hx)
    obtain ⟨j, hj⟩ := Set.mem_iUnion.1 (hEK ▸ hy)
    have hgxy : g x y = conj (f x) * φ (-p i + p j) * f y := by
      simp only [g]
      rw [Finset.sum_eq_single i (fun i' _ hi' ↦ Finset.sum_eq_zero fun j' _ ↦ by
          rw [Set.indicator_of_notMem (Set.disjoint_left.1 (hEd hi') · hi), zero_mul, zero_mul])
        (by simp),
        Finset.sum_eq_single j (fun j' _ hj' ↦ by
          rw [Set.indicator_of_notMem (Set.disjoint_left.1 (hEd hj') · hj), mul_zero]) (by simp),
        Set.indicator_of_mem hi, Set.indicator_of_mem hj]
    rw [hgxy, ← sub_mul, ← mul_sub, norm_mul, norm_mul, RCLike.norm_conj, mul_comm ε]
    gcongr
    exact hφ' i j x hi y hj
  -- Integrability of the various functions.
  have h1 (x : G) : Integrable (fun y ↦ conj (f x) * φ (-x + y) * f y) μ :=
    Continuous.integrable_of_hasCompactSupport (by fun_prop) hf'.mul_left
  have h2 (x : G) : Integrable (fun y ↦ g x y) μ :=
    integrable_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦
      (hfi.indicator (hE j)).const_mul _
  have h3 : Integrable (fun x ↦ ∫ y, conj (f x) * φ (-x + y) * f y ∂μ) μ := by
    simp_rw [mul_assoc, integral_const_mul]
    refine Continuous.integrable_of_hasCompactSupport
      (.mul (RCLike.continuous_conj.comp hf) ?_) (hf'.comp_left (map_zero _)).mul_right
    exact continuousOn_univ.1 (continuousOn_integral_of_compact_support hf'.isCompact
      (Continuous.continuousOn (by fun_prop)) fun x y _ hy ↦ by
        rw [image_eq_zero_of_notMem_tsupport hy, mul_zero])
  have h4 : Integrable (fun x ↦ ∫ y, g x y ∂μ) μ := by
    simp_rw [hg]
    exact integrable_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦
      ((hfi'.indicator (hE i)).mul_const _).mul_const _
  refine ⟨_, hφ.sum_nonneg p c, ?_⟩
  rw [← hS, ← integral_sub h3 h4]
  simp_rw [← integral_sub (h1 _) (h2 _)]
  calc ‖∫ x, ∫ y, (conj (f x) * φ (-x + y) * f y - g x y) ∂μ ∂μ‖
    _ ≤ ∫ x, ε * ‖f x‖ * m ∂μ :=
      norm_integral_le_of_norm_le ((hfi.norm.const_mul ε).mul_const m) (.of_forall fun x ↦
        (norm_integral_le_of_norm_le (hfi.norm.const_mul _) (.of_forall (hbound x))).trans_eq
          (integral_const_mul _ _))
    _ = ε * m * m := by rw [integral_mul_const, integral_const_mul]

end Measure

/-- On a locally compact group, there are continuous positive definite functions with compact
support contained in an arbitrarily small neighborhood of `0`. -/
theorem exists_isPositiveDefinite_hasCompactSupport [TopologicalSpace G] [IsTopologicalAddGroup G]
    [LocallyCompactSpace G] {U : Set G} (hU : U ∈ 𝓝 (0 : G)) :
    ∃ φ : G → ℂ, Continuous φ ∧ HasCompactSupport φ ∧ IsPositiveDefinite φ ∧ tsupport φ ⊆ U ∧
      φ 0 ≠ 0 := by
  -- Take `φ x = ∫ y, f y * conj (f (-x + y)) ∂μ` where `μ` is a Haar measure and `f` is a nonzero
  -- continuous function supported in a closed neighborhood `V` of `0` with `V - V ⊆ U`.
  borelize G
  let μ : Measure G := Measure.addHaar
  obtain ⟨V₁, hV₁, hV₁U⟩ := exists_nhds_half_neg hU
  obtain ⟨V, hV, hVc, hVV₁⟩ := exists_mem_nhds_isClosed_subset hV₁
  obtain ⟨g, hg1, hg0, hgc, -⟩ := exists_continuous_one_zero_of_isCompact
    (isCompact_singleton (x := (0 : G))) (isOpen_interior (s := V)).isClosed_compl
    (Set.disjoint_singleton_left.2 fun h ↦ h (mem_interior_iff_mem_nhds.2 hV))
  let f : G → ℂ := fun x ↦ (g x : ℂ)
  have hf : Continuous f := Complex.continuous_ofReal.comp g.continuous
  have hfc : HasCompactSupport f := hgc.comp_left Complex.ofReal_zero
  have hfV : tsupport f ⊆ V := closure_minimal (fun x hx ↦ by_contra fun hxV ↦ hx (by
    simp [f, hg0 fun h ↦ hxV (interior_subset h)])) hVc
  have hf2 : MemLp f 2 μ := hf.memLp_of_hasCompactSupport hfc
  have hsupp : tsupport (fun x ↦ ∫ y, f y * conj (f (-x + y)) ∂μ) ⊆
      tsupport f + -tsupport f := by
    refine closure_minimal (fun x hx ↦ ?_) ((isClosed_tsupport f).neg.add_left_of_isCompact hfc)
    by_contra hxC
    refine hx (integral_eq_zero_of_ae (.of_forall fun y ↦ ?_))
    by_contra hy
    obtain ⟨h1, h2⟩ := mul_ne_zero_iff.1 hy
    exact hxC ⟨y, subset_tsupport _ h1, -(-x + y),
      Set.neg_mem_neg.2 (subset_tsupport _ ((map_ne_zero _).1 h2)), by simp⟩
  refine ⟨fun x ↦ ∫ y, f y * conj (f (-x + y)) ∂μ, continuous_integral_mul_conj hf2,
    (hfc.isCompact.add hfc.isCompact.neg).of_isClosed_subset (isClosed_tsupport _) hsupp,
    isPositiveDefinite_integral_mul_conj hf2, hsupp.trans ?_, ?_⟩
  · rintro _ ⟨a, ha, b, hb, rfl⟩
    simpa using hV₁U a (hVV₁ (hfV ha)) (-b) (hVV₁ (hfV (Set.mem_neg.1 hb)))
  · have hpos : 0 < ∫ y, g y * g y ∂μ :=
      Continuous.integral_pos_of_hasCompactSupport_nonneg_ne_zero (x := 0) (by fun_prop)
        hgc.mul_left (fun y ↦ mul_self_nonneg _) (by simp [hg1 (Set.mem_singleton 0)])
    have : ∫ y, f y * conj (f (-0 + y)) ∂μ = ((∫ y, g y * g y ∂μ : ℝ) : ℂ) := by
      rw [← integral_complex_ofReal]
      exact integral_congr_ae (.of_forall fun y ↦ by simp [f])
    change ∫ y, f y * conj (f (-0 + y)) ∂μ ≠ 0
    rw [this]
    exact_mod_cast hpos.ne'
