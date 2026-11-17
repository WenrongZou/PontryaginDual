/-
Copyright (c) 2026 Wenrong Zou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wenrong Zou
-/
module

public import PontryaginDuality.Duality.DoubleDual
public import PontryaginDuality.Inversion.Plancherel
public import PontryaginDuality.Mathlib.Topology.Algebra.Group.LocallyCompactSubgroup

import PontryaginDuality.Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.WithDensity

/-!
# Pontryagin duality

Let `G` be a locally compact Hausdorff abelian group. The Pontryagin duality theorem states that
the canonical map from `G` to its double Pontryagin dual is an isomorphism of topological groups.

## Main definitions

* `AddPontryaginDual.doubleDualEquiv G`: the canonical isomorphism of topological groups
  `G ≃ₜ+ AddPontryaginDual (AddPontryaginDual G)`.

## Main statements

* `AddPontryaginDual.isInducing_doubleDualEmb`: the canonical map induces the topology of `G`.
* `AddPontryaginDual.isClosed_range_doubleDualEmb`: the range of the canonical map is closed.
* `AddPontryaginDual.doubleDualEmb_surjective`: the canonical map is surjective.
* `AddPontryaginDual.exists_toAddChar_ne_one`: the characters of `G` separate points.
* `AddPontryaginDual.dualAddHaar_dualAddHaar`: the canonical map sends a Haar measure to the dual
  of its dual.

## Overview of the proof

The proof uses Fourier analysis on `G` and on its Pontryagin dual, and follows [bourbaki1967],
Chap. II, §1. It does not use positive definite functions.

1. `L¹(G)` is a commutative Banach algebra under convolution
   (`PontryaginDuality.Convolution.L1Algebra`).
2. The Pontryagin dual of `G` is the character space of `L¹(G)`, and the Fourier transform is the
   Gelfand transform (`PontryaginDuality.Fourier.CharacterSpace`, n°1, Prop. 1). In particular
   the Fourier transform maps `L¹(G)` onto a dense subalgebra of the continuous functions
   vanishing at infinity, and its uniform norm is given by the spectral radius
   (`PontryaginDuality.Fourier.L1`).
3. `L¹(G)` acts on `L²(G)` by convolution (`PontryaginDuality.Convolution.L2`). Since the bounded
   operators on `L²(G)` form a C⋆-algebra, the norm of the operator `g ↦ f ⋆ g` is bounded by the
   uniform norm of the Fourier transform of `f`. Hence the continuous functions vanishing at
   infinity on the Pontryagin dual act on `L²(G)`, and every `f ∈ L²(G)` has a spectral measure
   on the Pontryagin dual (`PontryaginDuality.Fourier.CStar`, n°2 and n°3, Lemmes 1 and 2).
4. The dual Haar measure is obtained by gluing the spectral measures divided by their densities,
   and the Fourier transform preserves the `L²` norm on `L¹ ∩ L²`
   (`PontryaginDuality.Inversion.DualHaar`, n°3).
5. The Plancherel theorem, the Fourier inversion formula for the functions `f * g⋆` with `f` and
   `g` in `L¹ ∩ L²`, and the existence of integrable functions whose Fourier transform is
   supported in a given open set (`PontryaginDuality.Inversion.Plancherel`, n°3, Th. 1 and n°4,
   Prop. 4 and 5).
6. The duality theorem (this file, n°5, Th. 2): the inversion formula implies that the canonical
   map is inducing; its range is a locally compact subgroup, hence it is closed; if it were not
   surjective, step 5 applied to the Pontryagin dual of `G` would contradict the injectivity of
   the inverse Fourier transform.

## References

* [N. Bourbaki, *Théories spectrales*, Chap. II, §1][bourbaki1967]
* [G. B. Folland, *A Course in Abstract Harmonic Analysis*, Section 4.3][folland2016]
-/

@[expose] public section

open MeasureTheory Measure Filter Topology
open scoped ComplexConjugate ENNReal NNReal

namespace AddPontryaginDual

variable (G : Type*) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
  [LocallyCompactSpace G]

/-- The canonical map from a locally compact abelian group to its double dual induces the topology
of the group. -/
theorem isInducing_doubleDualEmb : IsInducing (doubleDualEmb G) := by
  -- By `IsTopologicalAddGroup.isInducing_iff_nhds_zero` and the continuity of `doubleDualEmb G`,
  -- it suffices to prove that for every neighborhood `U` of `0` in `G` there is a neighborhood `W`
  -- of `0` in the double dual whose preimage is contained in `U`.
  -- Equip `G` and its dual with their Borel `σ`-algebras, let `μ` be a Haar measure on `G`, and let
  -- `ν = μ.dualAddHaar`. Let `V` be a neighborhood of `0` such that `V - V ⊆ U`, let `u ≥ 0` be a
  -- continuous function with compact support contained in `V` such that `u 0 = 1`, and let
  -- `h x = ∫ y, u y * conj (u (-x + y)) ∂μ`. Then `h 0 ≠ 0` and `h` vanishes outside `U`. By the
  -- inversion formula (`fourierIntegralInv_fourierIntegral_mul_conj`) and
  -- `fourierIntegral_doubleDualEmb`, `h x = fourierIntegral ν Φ (doubleDualEmb G (-x))`, where
  -- `Φ = fourierIntegral μ u * conj (fourierIntegral μ u)` is `ν`-integrable. Its Fourier transform
  -- is continuous (`continuous_fourierIntegral`), so `W = {ξ | fourierIntegral ν Φ (-ξ) ≠ 0}` is an
  -- open neighborhood of `0`. If `doubleDualEmb G x ∈ W`, then `h x ≠ 0`, hence `x ∈ U`.
  refine IsTopologicalAddGroup.isInducing_iff_nhds_zero.2 (le_antisymm ?_ fun U hU ↦ ?_)
  · have h := (map_continuous (doubleDualEmb G)).tendsto 0
    rw [map_zero] at h
    exact h.le_comap
  borelize G (AddPontryaginDual G)
  let μ : Measure G := Measure.addHaar
  obtain ⟨V, hV, hVU⟩ := exists_nhds_half_neg hU
  obtain ⟨θ, hθ1, hθ0, hθc, -⟩ := exists_continuous_one_zero_of_isCompact
    (isCompact_singleton (x := (0 : G))) (isOpen_interior (s := V)).isClosed_compl
    (Set.disjoint_singleton_left.2 fun h ↦ h (mem_interior_iff_mem_nhds.2 hV))
  have hu : Continuous fun x ↦ (θ x : ℂ) := Complex.continuous_ofReal.comp θ.continuous
  have huc : HasCompactSupport fun x ↦ (θ x : ℂ) := hθc.comp_left Complex.ofReal_zero
  have hui : Integrable (fun x ↦ (θ x : ℂ)) μ := hu.integrable_of_hasCompactSupport huc
  have hu2 : MemLp (fun x ↦ (θ x : ℂ)) 2 μ := hu.memLp_of_hasCompactSupport huc
  have hθV (x : G) (h : (θ x : ℂ) ≠ 0) : x ∈ V := by
    by_contra hx
    exact h (by simp [hθ0 fun h' ↦ hx (interior_subset h')])
  have hΦ := integrable_fourierIntegral_mul_conj hui hu2 hui hu2
  have hΘ := continuous_fourierIntegral hΦ
  have hΘx (x : G) :
      fourierIntegral μ.dualAddHaar (fun χ ↦ fourierIntegral μ (fun x ↦ (θ x : ℂ)) χ *
        conj (fourierIntegral μ (fun x ↦ (θ x : ℂ)) χ)) (-doubleDualEmb G x) =
        ∫ y, (θ y : ℂ) * conj (θ (-x + y) : ℂ) ∂μ := by
    rw [← map_neg, fourierIntegral_doubleDualEmb, neg_neg,
      fourierIntegralInv_fourierIntegral_mul_conj hui hu2 hui hu2]
  refine Filter.mem_comap.2
    ⟨{ξ | fourierIntegral μ.dualAddHaar (fun χ ↦ fourierIntegral μ (fun x ↦ (θ x : ℂ)) χ *
        conj (fourierIntegral μ (fun x ↦ (θ x : ℂ)) χ)) (-ξ) ≠ 0},
      (isOpen_ne_fun (hΘ.comp continuous_neg) continuous_const).mem_nhds ?_, fun x hx ↦ ?_⟩
  · have hpos : 0 < ∫ y, θ y * θ y ∂μ :=
      Continuous.integral_pos_of_hasCompactSupport_nonneg_ne_zero (x := 0)
        (θ.continuous.mul θ.continuous) hθc.mul_left (fun y ↦ mul_self_nonneg _)
        (by simp [hθ1 (Set.mem_singleton 0)])
    have h0 : ∫ y, (θ y : ℂ) * conj (θ (-0 + y) : ℂ) ∂μ = ((∫ y, θ y * θ y ∂μ : ℝ) : ℂ) := by
      rw [← integral_complex_ofReal]
      refine integral_congr_ae (.of_forall fun y ↦ ?_)
      simp
    have h := hΘx 0
    rw [map_zero, h0] at h
    exact fun h' ↦ hpos.ne' (by exact_mod_cast h.symm.trans h')
  · have hx' : ∫ y, (θ y : ℂ) * conj (θ (-x + y) : ℂ) ∂μ ≠ 0 :=
      fun h' ↦ hx ((hΘx x).trans h')
    by_contra hxU
    refine hx' (integral_eq_zero_of_ae (.of_forall fun y ↦ ?_))
    by_contra h
    obtain ⟨h1, h2⟩ := mul_ne_zero_iff.1 h
    have h3 : y - (-x + y) ∈ U :=
      hVU y (hθV y h1) _ (hθV _ fun h' ↦ h2 (by simp [h']))
    exact hxU (by simpa using h3)

variable [T2Space G]

/-- The canonical map from a locally compact Hausdorff abelian group to its double dual is
injective. -/
theorem doubleDualEmb_injective : Function.Injective (doubleDualEmb G) :=
  (isInducing_doubleDualEmb G).injective

/-- The canonical map from a locally compact Hausdorff abelian group to its double dual is a
topological embedding. -/
theorem isEmbedding_doubleDualEmb : IsEmbedding (doubleDualEmb G) :=
  ⟨isInducing_doubleDualEmb G, doubleDualEmb_injective G⟩

/-- The range of the canonical map from a locally compact Hausdorff abelian group to its double
dual is closed. -/
theorem isClosed_range_doubleDualEmb : IsClosed (Set.range (doubleDualEmb G)) := by
  -- The range is an additive subgroup of the double dual. It is homeomorphic to `G` by
  -- `isEmbedding_doubleDualEmb`, hence locally compact. Apply
  -- `AddSubgroup.isClosed_of_locallyCompactSpace`.
  let H : AddSubgroup (AddPontryaginDual (AddPontryaginDual G)) :=
    (doubleDualEmb G).toAddMonoidHom.range
  have : LocallyCompactSpace H :=
    (isEmbedding_doubleDualEmb G).toHomeomorph.symm.isClosedEmbedding.locallyCompactSpace
  exact AddSubgroup.isClosed_of_locallyCompactSpace (H := H)

/-- The canonical map from a locally compact Hausdorff abelian group to its double dual is
surjective. -/
theorem doubleDualEmb_surjective : Function.Surjective (doubleDualEmb G) := by
  -- Assume that the complement `U` of the range is nonempty; it is open by
  -- `isClosed_range_doubleDualEmb`. Equip `G` and its dual and double dual with their Borel
  -- `σ`-algebras, let `μ` be a Haar measure on `G`, and let `ν = μ.dualAddHaar`.
  -- By `exists_integrable_fourierIntegral_ne_zero`, applied to the Pontryagin dual of `G` and
  -- to `ν`, there is a `ν`-integrable function `F` on the dual of `G` such that
  -- `fourierIntegral ν F` is nonzero and vanishes outside `U`, in particular on the range of
  -- `doubleDualEmb G`. By `fourierIntegral_doubleDualEmb`, this means that
  -- `fourierIntegralInv ν F = 0`, hence `F = 0` almost everywhere by
  -- `ae_eq_zero_of_fourierIntegralInv_eq_zero`, and `fourierIntegral ν F = 0` by
  -- `fourierIntegral_congr_ae`, a contradiction.
  by_contra hsurj
  have hne : (Set.range (doubleDualEmb G))ᶜ.Nonempty :=
    Set.nonempty_compl.2 fun h ↦ hsurj (Set.range_eq_univ.1 h)
  borelize G (AddPontryaginDual G) (AddPontryaginDual (AddPontryaginDual G))
  let μ : Measure G := Measure.addHaar
  obtain ⟨F, hF, hF0, hFU⟩ := exists_integrable_fourierIntegral_ne_zero μ.dualAddHaar
    (isClosed_range_doubleDualEmb G).isOpen_compl hne
  have hinv : fourierIntegralInv μ.dualAddHaar F = 0 := by
    ext x
    rw [← neg_neg x, ← fourierIntegral_doubleDualEmb]
    exact hFU _ fun h ↦ h (Set.mem_range_self _)
  refine hF0 ?_
  rw [fourierIntegral_congr_ae (ae_eq_zero_of_fourierIntegralInv_eq_zero hF hinv)]
  ext ξ
  simp [fourierIntegral]

theorem doubleDualEmb_bijective : Function.Bijective (doubleDualEmb G) :=
  ⟨doubleDualEmb_injective G, doubleDualEmb_surjective G⟩

/-- **Pontryagin duality**: a locally compact Hausdorff abelian group is canonically isomorphic,
as a topological group, to its double Pontryagin dual. -/
noncomputable def doubleDualEquiv : G ≃ₜ+ AddPontryaginDual (AddPontryaginDual G) where
  __ := AddEquiv.ofBijective (doubleDualEmb G) (doubleDualEmb_bijective G)
  continuous_toFun := map_continuous (doubleDualEmb G)
  continuous_invFun :=
    ((Equiv.ofBijective _ (doubleDualEmb_bijective G)).toHomeomorphOfIsInducing
      (isInducing_doubleDualEmb G)).symm.continuous

variable {G}

@[simp]
theorem coe_doubleDualEquiv : ⇑(doubleDualEquiv G) = doubleDualEmb G :=
  rfl

theorem doubleDualEquiv_apply (x : G) (χ : AddPontryaginDual G) :
    doubleDualEquiv G x χ = χ x :=
  rfl

/-- The characters of a locally compact Hausdorff abelian group separate points. -/
theorem exists_toAddChar_ne_one {x : G} (hx : x ≠ 0) :
    ∃ χ : AddPontryaginDual G, χ.toAddChar x ≠ 1 := by
  by_contra! h
  refine hx (doubleDualEmb_injective G ?_)
  rw [map_zero]
  refine AddPontryaginDual.ext fun χ ↦ ?_
  exact Additive.toMul.injective (h χ)

/-- The canonical map from `G` to its double dual sends a Haar measure `μ` to the dual of the
dual of `μ`. -/
theorem dualAddHaar_dualAddHaar [MeasurableSpace G] [BorelSpace G]
    [MeasurableSpace (AddPontryaginDual G)] [BorelSpace (AddPontryaginDual G)]
    [MeasurableSpace (AddPontryaginDual (AddPontryaginDual G))]
    [BorelSpace (AddPontryaginDual (AddPontryaginDual G))] (μ : Measure G) [μ.IsAddHaarMeasure]
    [μ.Regular] : μ.dualAddHaar.dualAddHaar = Measure.map (doubleDualEmb G) μ := by
  -- TS II §1 n°5, Th. 2. Both are regular Haar measures on the double dual, hence they are
  -- proportional. Let `F ≠ 0` be a continuous function with compact support on the dual. By
  -- `eLpNorm_two_fourierIntegral` on the dual, the `L²` norm of `fourierIntegral μ.dualAddHaar F`
  -- for `μ.dualAddHaar.dualAddHaar` is the `L²` norm of `F`. By `fourierIntegral_doubleDualEmb`
  -- and `coeFn_fourierL2_symm`, this is also its `L²` norm for the image of `μ`.
  have hmR : (Measure.map (doubleDualEmb G) μ).Regular :=
    Regular.map (doubleDualEquiv G).toHomeomorph
  have hmH : (Measure.map (doubleDualEmb G) μ).IsAddHaarMeasure :=
    (doubleDualEquiv G).isAddHaarMeasure_map μ
  obtain ⟨c, hc⟩ : ∃ c : ℝ≥0, μ.dualAddHaar.dualAddHaar = c • Measure.map (doubleDualEmb G) μ :=
    ⟨_, isAddLeftInvariant_eq_smul_of_regular _ _⟩
  obtain ⟨F, hF, hFc, hF0⟩ : ∃ F : AddPontryaginDual G → ℂ,
      Continuous F ∧ HasCompactSupport F ∧ F 0 ≠ 0 := by
    obtain ⟨θ, hθ1, -, hθc, -⟩ := exists_continuous_one_zero_of_isCompact
      (isCompact_singleton (x := (0 : AddPontryaginDual G))) isClosed_empty
      (Set.disjoint_empty _)
    exact ⟨fun χ ↦ (θ χ : ℂ), Complex.continuous_ofReal.comp θ.continuous,
      hθc.comp_left Complex.ofReal_zero, by simp [hθ1 (Set.mem_singleton 0)]⟩
  have hFi : Integrable F μ.dualAddHaar := hF.integrable_of_hasCompactSupport hFc
  have hF2 : MemLp F 2 μ.dualAddHaar := hF.memLp_of_hasCompactSupport hFc
  have hN0 : eLpNorm F 2 μ.dualAddHaar ≠ 0 := fun h ↦ hF0 (congr_fun
    ((hF.ae_eq_iff_eq μ.dualAddHaar continuous_zero).1 ((eLpNorm_eq_zero_iff two_ne_zero).1 h)) 0)
  have hc' : Continuous (fourierIntegral μ.dualAddHaar F) := continuous_fourierIntegral hFi
  have h1 : eLpNorm (fourierIntegral μ.dualAddHaar F) 2 μ.dualAddHaar.dualAddHaar =
      eLpNorm F 2 μ.dualAddHaar := eLpNorm_two_fourierIntegral μ.dualAddHaar hFi hF2
  have h2 : eLpNorm (fourierIntegral μ.dualAddHaar F) 2 (Measure.map (doubleDualEmb G) μ) =
      eLpNorm F 2 μ.dualAddHaar := by
    rw [eLpNorm_map_measure hc'.aestronglyMeasurable
        (map_continuous (doubleDualEmb G)).aemeasurable,
      show fourierIntegral μ.dualAddHaar F ∘ doubleDualEmb G =
        fourierIntegralInv μ.dualAddHaar F ∘ Neg.neg from
        funext fun x ↦ fourierIntegral_doubleDualEmb μ.dualAddHaar F x,
      eLpNorm_comp_measurePreserving (continuous_fourierIntegralInv hFi).aestronglyMeasurable
        (measurePreserving_neg μ),
      ← eLpNorm_congr_ae (coeFn_fourierL2_symm hFi hF2), ← Lp.enorm_def, ← Lp.enorm_toLp hF2,
      enorm_eq_nnnorm, enorm_eq_nnnorm, LinearIsometryEquiv.nnnorm_map]
  have h3 : eLpNorm (fourierIntegral μ.dualAddHaar F) 2 μ.dualAddHaar.dualAddHaar ^ 2 =
      c * eLpNorm (fourierIntegral μ.dualAddHaar F) 2 (Measure.map (doubleDualEmb G) μ) ^ 2 := by
    rw [sq_eLpNorm_two hc'.aestronglyMeasurable, sq_eLpNorm_two hc'.aestronglyMeasurable, hc,
      lintegral_smul_measure, ENNReal.smul_def, smul_eq_mul]
  rw [h1, h2] at h3
  have hc1 : (c : ℝ≥0∞) = 1 :=
    (ENNReal.mul_left_inj (pow_ne_zero 2 hN0) (ENNReal.pow_ne_top hF2.eLpNorm_lt_top.ne)).1
      (h3.symm.trans (one_mul _).symm)
  rw [hc, show c = 1 by exact_mod_cast hc1, one_smul]

end AddPontryaginDual
