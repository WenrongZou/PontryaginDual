/-
Copyright (c) 2026 Wenrong Zou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wenrong Zou
-/
module

public import Mathlib.Analysis.Convolution
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.MeasureTheory.Function.LpSpace.DomAct.Continuous
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# The convolution algebra `L¹(G)`

Let `G` be a locally compact additive group with a regular (left) Haar measure `μ`. In this file
we turn `L¹(G) = MeasureTheory.Lp 𝕜 1 μ` into a (non-unital) Banach algebra under convolution,
which is commutative if `G` is.

## Main definitions

* `MeasureTheory.L1.instMul`: the convolution product on `L¹(G)`,
  `f * g = ∫ y, f y • τ_y g ∂μ` where `τ_y g = (x ↦ g (-y + x))` is the left translate of `g` and
  the integral is a Bochner integral in `L¹(G)`.
* `MeasureTheory.L1.instNonUnitalNormedRing`, `MeasureTheory.L1.instNonUnitalNormedCommRing`:
  `L¹(G)` is a non-unital normed (commutative) ring.
* `MeasureTheory.L1.involution`: the involution `f ↦ (x ↦ conj (f (-x)))` of `L¹(G)`, for
  commutative `G`.

## Main statements

* `MeasureTheory.L1.coeFn_mul_of_hasCompactSupport`: for continuous functions with compact
  support on a commutative group, the product is given by `MeasureTheory.convolution`.
* `MeasureTheory.L1.exists_nhds_zero_norm_mul_sub_lt`: approximate units.

## Design decisions

* The product is defined as an `L¹(G)`-valued Bochner integral, using the action of `Gᵈᵃᵃ` on
  `L¹(G)` by translations, and not as `(hf.integrable_convolution L hg).toL1`. The reason is that
  `MeasureTheory.Integrable.integrable_convolution` and `MeasureTheory.convolution_assoc` need the
  assumptions `[SFinite μ]` and `[MeasurableAdd₂ G]`. A Haar measure on a group which is not
  `σ`-compact is not `s`-finite, and the addition of a group which is not second-countable need
  not be measurable with respect to the product of the Borel `σ`-algebras, so these lemmas are not
  available for general locally compact groups. With the definition as a Bochner integral,
  `‖f * g‖ ≤ ‖f‖ * ‖g‖` follows from `norm_integral_le_integral_norm`, and associativity follows
  from the fact that continuous linear maps commute with Bochner integrals.
* The ring structure is registered directly on `MeasureTheory.Lp 𝕜 1 μ`. Note that the existing
  instance `Star (Lp 𝕜 1 μ)` is the pointwise conjugation, which is *not* the involution of the
  group algebra; this is why `MeasureTheory.L1.involution` is a plain function.

## TODO

* The involution should be a `StarRing` structure; this probably requires a type synonym.
* The modular function is needed to define the involution on non-unimodular groups.
* The multiplicative version.
-/

@[expose] public section

open MeasureTheory Measure Filter Topology
open scoped ENNReal ComplexConjugate Convolution

namespace MeasureTheory.L1

variable {G 𝕜 : Type*} [RCLike 𝕜] [MeasurableSpace G]

section AddGroup

variable [AddGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [LocallyCompactSpace G]
  [BorelSpace G] {μ : Measure G} [μ.IsAddHaarMeasure] [μ.Regular]

/-- The convolution product on `L¹(G)`: `f * g = ∫ y, f y • τ_y g ∂μ`, where
`τ_y g = (x ↦ g (-y + x))`. The integral is a Bochner integral with values in `L¹(G)`. -/
noncomputable instance instMul : Mul (Lp 𝕜 1 μ) where
  mul f g := ∫ y, f y • (DomAddAct.mk (-y) +ᵥ g) ∂μ

omit [LocallyCompactSpace G] [μ.Regular] in
theorem mul_def (f g : Lp 𝕜 1 μ) : f * g = ∫ y, f y • (DomAddAct.mk (-y) +ᵥ g) ∂μ :=
  rfl

/-- The function `y ↦ f y • τ_y g` is Bochner integrable. -/
theorem integrable_smul_translate (f g : Lp 𝕜 1 μ) :
    Integrable (fun y ↦ f y • (DomAddAct.mk (-y) +ᵥ g)) μ := by
  -- `y ↦ τ_y g` is continuous and bounded (`Lp.instContinuousVAddDomAddAct`) and `f` is integrable.
  -- For the strong measurability, note that `f` vanishes almost everywhere outside a `σ`-compact
  -- set, on which the continuous map `y ↦ τ_y g` has separable range.
  sorry

protected theorem norm_mul_le (f g : Lp 𝕜 1 μ) : ‖f * g‖ ≤ ‖f‖ * ‖g‖ := by
  -- `norm_integral_le_integral_norm` and `‖τ_y g‖ = ‖g‖`.
  sorry

/-- Translations commute with the convolution product: `τ_c (f * g) = τ_c f * g`. -/
theorem translate_mul (c : G) (f g : Lp 𝕜 1 μ) :
    DomAddAct.mk c +ᵥ (f * g) = (DomAddAct.mk c +ᵥ f) * g := by
  sorry

protected theorem mul_add (f g h : Lp 𝕜 1 μ) : f * (g + h) = f * g + f * h := by
  sorry

protected theorem add_mul (f g h : Lp 𝕜 1 μ) : (f + g) * h = f * h + g * h := by
  sorry

protected theorem zero_mul (f : Lp 𝕜 1 μ) : 0 * f = 0 := by
  sorry

protected theorem mul_zero (f : Lp 𝕜 1 μ) : f * 0 = 0 := by
  sorry

/-- Associativity of the convolution product on `L¹(G)`. -/
protected theorem mul_assoc (f g h : Lp 𝕜 1 μ) : f * g * h = f * (g * h) := by
  -- The map `k ↦ k * h` is continuous and linear, hence it commutes with the Bochner integral
  -- `f * g = ∫ y, f y • τ_y g ∂μ`. Conclude by `translate_mul`. No Fubini is needed.
  sorry

protected theorem smul_mul (c : 𝕜) (f g : Lp 𝕜 1 μ) : (c • f) * g = c • (f * g) := by
  sorry

protected theorem mul_smul (c : 𝕜) (f g : Lp 𝕜 1 μ) : f * (c • g) = c • (f * g) := by
  sorry

/-- `L¹(G)` is a non-unital normed ring under convolution. -/
noncomputable instance instNonUnitalNormedRing : NonUnitalNormedRing (Lp 𝕜 1 μ) where
  __ := (inferInstance : NormedAddCommGroup (Lp 𝕜 1 μ))
  left_distrib := L1.mul_add
  right_distrib := L1.add_mul
  zero_mul := L1.zero_mul
  mul_zero := L1.mul_zero
  mul_assoc := L1.mul_assoc
  norm_mul_le := L1.norm_mul_le

instance instIsScalarTower : IsScalarTower 𝕜 (Lp 𝕜 1 μ) (Lp 𝕜 1 μ) where
  smul_assoc := L1.smul_mul

instance instSMulCommClass : SMulCommClass 𝕜 (Lp 𝕜 1 μ) (Lp 𝕜 1 μ) where
  smul_comm c f g := (L1.mul_smul c f g).symm

/-- **Approximate units** in `L¹(G)`: if `u ≥ 0` has integral `1` and is supported in a small
neighborhood of `0`, then `u * f` is close to `f`. -/
theorem exists_nhds_zero_norm_mul_sub_lt (f : Lp 𝕜 1 μ) {ε : ℝ} (hε : 0 < ε) :
    ∃ U ∈ 𝓝 (0 : G), ∀ u : Lp 𝕜 1 μ, (∀ᵐ x ∂μ, u x = (‖u x‖ : 𝕜)) → ‖u‖ = 1 →
      (∀ᵐ x ∂μ, x ∉ U → u x = 0) → ‖u * f - f‖ < ε := by
  -- `u * f - f = ∫ y, u y • (τ_y f - f) ∂μ` and `y ↦ τ_y f` is continuous at `0`.
  sorry

end AddGroup

section AddCommGroup

variable [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [LocallyCompactSpace G]
  [BorelSpace G] {μ : Measure G} [μ.IsAddHaarMeasure] [μ.Regular]

/-- For continuous functions with compact support, the product in `L¹(G)` is the usual
convolution. -/
theorem coeFn_mul_of_hasCompactSupport {f g : G → 𝕜} (hf : Continuous f)
    (hf' : HasCompactSupport f) (hg : Continuous g) (hg' : HasCompactSupport g) :
    ((hf.integrable_of_hasCompactSupport hf').toL1 f *
      (hg.integrable_of_hasCompactSupport hg').toL1 g : Lp 𝕜 1 μ) =ᵐ[μ]
      f ⋆[.mul 𝕜 𝕜, μ] g := by
  -- Test against continuous functions with compact support and use
  -- `integral_integral_swap_of_hasCompactSupport`.
  sorry

/-- Commutativity of the convolution product on `L¹(G)` for commutative `G`. -/
protected theorem mul_comm (f g : Lp 𝕜 1 μ) : f * g = g * f := by
  -- By density and continuity of the product, it suffices to consider continuous functions with
  -- compact support, for which one can use `coeFn_mul_of_hasCompactSupport` and
  -- `MeasureTheory.convolution_flip`.
  sorry

/-- If `G` is commutative, then `L¹(G)` is a commutative non-unital normed ring under
convolution. -/
noncomputable instance instNonUnitalNormedCommRing : NonUnitalNormedCommRing (Lp 𝕜 1 μ) where
  __ := (inferInstance : NonUnitalNormedRing (Lp 𝕜 1 μ))
  mul_comm := L1.mul_comm

/-- The involution `f ↦ (x ↦ conj (f (-x)))` of `L¹(G)`. -/
noncomputable def involution (f : Lp 𝕜 1 μ) : Lp 𝕜 1 μ :=
  Lp.compMeasurePreserving Neg.neg (measurePreserving_neg μ) (star f)

theorem coeFn_involution (f : Lp 𝕜 1 μ) : involution f =ᵐ[μ] fun x ↦ conj (f (-x)) := by
  sorry

@[simp]
theorem involution_involution (f : Lp 𝕜 1 μ) : involution (involution f) = f := by
  sorry

@[simp]
theorem norm_involution (f : Lp 𝕜 1 μ) : ‖involution f‖ = ‖f‖ := by
  sorry

@[simp]
theorem involution_add (f g : Lp 𝕜 1 μ) : involution (f + g) = involution f + involution g := by
  sorry

@[simp]
theorem involution_smul (c : 𝕜) (f : Lp 𝕜 1 μ) : involution (c • f) = conj c • involution f := by
  sorry

@[simp]
theorem involution_mul (f g : Lp 𝕜 1 μ) : involution (f * g) = involution f * involution g := by
  sorry

end AddCommGroup

end MeasureTheory.L1
