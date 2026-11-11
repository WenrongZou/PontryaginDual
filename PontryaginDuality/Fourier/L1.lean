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

/-- The **Riemann–Lebesgue lemma**: the Fourier transform of an integrable function vanishes at
infinity. -/
theorem tendsto_fourierIntegral_cocompact {f : G → E} (hf : Integrable f μ) :
    Tendsto (fourierIntegral μ f) (cocompact (AddPontryaginDual G)) (𝓝 0) := by
  -- For `E = ℂ`: `characterSpace ℂ (Lp ℂ 1 μ) ∪ {0}` is weak-* compact
  -- (`WeakDual.CharacterSpace.union_zero_isClosed` and the Banach–Alaoglu theorem), and
  -- `Φ ↦ Φ f` is continuous on this set and vanishes at `0`. Then use
  -- `characterSpaceHomeomorph`. The general case follows by approximating `f` in `L¹` by finite
  -- sums `∑ i, f i • e i` with `f i : G → ℂ` integrable, using `norm_fourierIntegral_coeFn_le`.
  sorry

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
  sorry

/-- The Fourier transform intertwines the involution of `L¹(G)` and the complex conjugation. -/
theorem fourierL1_involution (f : Lp ℂ 1 μ) :
    fourierL1 μ (L1.involution f) = star (fourierL1 μ f) := by
  sorry

/-- The Fourier transforms of the elements of `L¹(G)` separate the points of the Pontryagin
dual. -/
theorem exists_fourierL1_ne {χ η : AddPontryaginDual G} (h : χ ≠ η) :
    ∃ f : Lp ℂ 1 μ, fourierL1 μ f χ ≠ fourierL1 μ f η := by
  -- This is `toCharacterSpace_injective`.
  sorry

/-- The Fourier transforms of the elements of `L¹(G)` do not vanish simultaneously. -/
theorem exists_fourierL1_ne_zero (χ : AddPontryaginDual G) :
    ∃ f : Lp ℂ 1 μ, fourierL1 μ f χ ≠ 0 := by
  sorry

/-- The range of the Fourier transform is dense in the space of continuous functions vanishing
at infinity. -/
theorem denseRange_fourierL1 : DenseRange (fourierL1 μ) := by
  -- The range is a subalgebra which is closed under complex conjugation (`fourierL1_involution`),
  -- separates points (`exists_fourierL1_ne`) and vanishes nowhere (`exists_fourierL1_ne_zero`).
  -- Apply the Stone–Weierstrass theorem on the one-point compactification.
  sorry

/-- The quasispectrum of an element of `L¹(G)` is the range of its Fourier transform, together
with `0`. -/
theorem quasispectrum_eq_insert_zero_range_fourierL1 (f : Lp ℂ 1 μ) :
    quasispectrum ℂ f = insert 0 (Set.range (fourierL1 μ f)) := by
  -- The spectrum of an element of a commutative unital Banach algebra is the range of its Gelfand
  -- transform. Apply this to the unitization of `L¹(G)` (with the `L¹` norm, see
  -- `WithLp.instUnitizationNormedRing`), whose characters are the characters of `L¹(G)`
  -- and `(c, f) ↦ c`, and use `toCharacterSpace_surjective`.
  sorry

/-- The spectral radius of an element of `L¹(G)` is the uniform norm of its Fourier
transform. -/
theorem spectralRadius_inr_eq_nnnorm_fourierL1 (f : Lp ℂ 1 μ) :
    spectralRadius ℂ (f : Unitization ℂ (Lp ℂ 1 μ)) = ‖fourierL1 μ f‖₊ := by
  -- `quasispectrum_eq_insert_zero_range_fourierL1` and `Unitization.quasispectrum_eq_spectrum_inr`.
  sorry

end AddPontryaginDual
