/-
Copyright (c) 2026 Wenrong Zou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wenrong Zou
-/
module

public import PontryaginDuality.Duality.DoubleDual
public import PontryaginDuality.Inversion.Plancherel
public import PontryaginDuality.Mathlib.Topology.Algebra.Group.LocallyCompactSubgroup

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

## Overview of the proof

The proof uses Fourier analysis on `G` and on its Pontryagin dual, and follows
[folland2016] and [rudin1962].

1. `L¹(G)` is a commutative Banach algebra under convolution
   (`PontryaginDuality.Convolution.L1Algebra`).
2. The Pontryagin dual of `G` is the character space of `L¹(G)`, and the Fourier transform is the
   Gelfand transform (`PontryaginDuality.Fourier.CharacterSpace`). In particular the Fourier
   transform maps `L¹(G)` onto a dense subalgebra of the continuous functions vanishing at
   infinity, and its uniform norm is given by the spectral radius
   (`PontryaginDuality.Fourier.L1`).
3. Bochner's theorem: the continuous positive definite functions on `G` are the functions
   `x ↦ ∫ χ, χ x ∂ν` for a unique finite regular measure `ν` on the Pontryagin dual
   (`PontryaginDuality.PositiveDefinite.Bochner`).
4. The Fourier inversion theorem for integrable continuous positive definite functions, with
   respect to the dual Haar measure (`PontryaginDuality.Inversion.DualHaar`).
5. The Plancherel theorem, and the existence of integrable functions whose Fourier transform is
   supported in a given open set (`PontryaginDuality.Inversion.Plancherel`).
6. The duality theorem (this file): the inversion theorem implies that the canonical map is
   inducing; its range is a locally compact subgroup, hence it is closed; if it were not
   surjective, step 5 applied to the Pontryagin dual of `G` would contradict the injectivity of
   the inverse Fourier transform.

## References

* [G. B. Folland, *A Course in Abstract Harmonic Analysis*, Section 4.3][folland2016]
* [W. Rudin, *Fourier Analysis on Groups*, Section 1.7][rudin1962]
-/

@[expose] public section

open MeasureTheory Measure Filter Topology

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
  -- `ν = μ.dualAddHaar`. Let `φ` be a continuous positive definite function with compact support
  -- contained in `U` such that `φ 0 ≠ 0` (`exists_isPositiveDefinite_hasCompactSupport`). By the
  -- inversion theorem (`fourierIntegralInv_fourierIntegral`) and `fourierIntegral_doubleDualEmb`,
  -- `φ x = fourierIntegral ν (fourierIntegral μ φ) (doubleDualEmb G (-x))`. Since
  -- `fourierIntegral μ φ` is `ν`-integrable (`integrable_fourierIntegral`), its Fourier transform
  -- is continuous (`continuous_fourierIntegral`), so
  -- `W = {ξ | fourierIntegral ν (fourierIntegral μ φ) (-ξ) ≠ 0}` is an open neighborhood of `0`.
  -- If `doubleDualEmb G x ∈ W`, then `φ x ≠ 0`, hence `x ∈ U`.
  refine IsTopologicalAddGroup.isInducing_iff_nhds_zero.2 (le_antisymm ?_ fun U hU ↦ ?_)
  · have h := (map_continuous (doubleDualEmb G)).tendsto 0
    rw [map_zero] at h
    exact h.le_comap
  borelize G (AddPontryaginDual G)
  let μ : Measure G := Measure.addHaar
  obtain ⟨φ, hφ, hφc, hφp, hφU, hφ0⟩ := exists_isPositiveDefinite_hasCompactSupport hU
  have hφi : Integrable φ μ := hφ.integrable_of_hasCompactSupport hφc
  have hΘ : Continuous (fourierIntegral μ.dualAddHaar (fourierIntegral μ φ)) :=
    continuous_fourierIntegral (integrable_fourierIntegral hφ hφi hφp)
  have hΘx (x : G) :
      fourierIntegral μ.dualAddHaar (fourierIntegral μ φ) (-doubleDualEmb G x) = φ x := by
    rw [← map_neg, fourierIntegral_doubleDualEmb, neg_neg,
      fourierIntegralInv_fourierIntegral hφ hφi hφp]
  refine Filter.mem_comap.2
    ⟨{ξ | fourierIntegral μ.dualAddHaar (fourierIntegral μ φ) (-ξ) ≠ 0},
      (isOpen_ne_fun (hΘ.comp continuous_neg) continuous_const).mem_nhds ?_, fun x hx ↦ ?_⟩
  · have h := hΘx 0
    rw [map_zero] at h
    change fourierIntegral μ.dualAddHaar (fourierIntegral μ φ) (-0) ≠ 0
    rw [h]
    exact hφ0
  · have hx' : fourierIntegral μ.dualAddHaar (fourierIntegral μ φ) (-doubleDualEmb G x) ≠ 0 := hx
    rw [hΘx] at hx'
    exact hφU (subset_tsupport φ hx')

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

end AddPontryaginDual
