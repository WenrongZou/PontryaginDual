/-
Copyright (c) 2026 Wenrong Zou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wenrong Zou
-/
module

public import Mathlib.Topology.Algebra.Module.Spaces.CharacterSpace
public import PontryaginDuality.Fourier.Basic

/-!
# The Pontryagin dual as the character space of `L¹(G)`

Let `G` be a locally compact abelian group with a regular Haar measure `μ`. Every
`χ : AddPontryaginDual G` defines a character of the commutative Banach algebra `L¹(G)`, namely
`f ↦ fourierIntegral μ f χ`. We state that this gives a homeomorphism between
`AddPontryaginDual G` and the character space of `L¹(G)` (i.e. its Gelfand spectrum): the Fourier
transform is the Gelfand transform of `L¹(G)`.

## Main definitions

* `AddPontryaginDual.fourierIntegralCLM μ χ`: the continuous linear map
  `f ↦ fourierIntegral μ f χ` on `L¹(G; E)`.
* `AddPontryaginDual.toCharacterSpace μ χ`: the character of `L¹(G)` associated with `χ`.
* `AddPontryaginDual.characterSpaceHomeomorph μ`: the homeomorphism
  `AddPontryaginDual G ≃ₜ characterSpace ℂ (Lp ℂ 1 μ)`.

## Main statements

* `AddPontryaginDual.toCharacterSpace_surjective`: every character of `L¹(G)` comes from a unique
  element of `AddPontryaginDual G`.
* `AddPontryaginDual.isHomeomorph_toCharacterSpace`: the compact-open topology on
  `AddPontryaginDual G` agrees with the weak-* topology on the character space.

## References

* [G. B. Folland, *A Course in Abstract Harmonic Analysis*, Section 4.1][folland2016]
-/

@[expose] public section

open MeasureTheory Measure Filter Topology WeakDual

namespace AddPontryaginDual

variable {G E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [LocallyCompactSpace G]
  [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsAddHaarMeasure] [μ.Regular]

/-- The Fourier transform at `χ : AddPontryaginDual G`, as a continuous linear map on
`L¹(G; E)`. -/
noncomputable def fourierIntegralCLM (χ : AddPontryaginDual G) : Lp E 1 μ →L[ℂ] E :=
  LinearMap.mkContinuous
    { toFun := fun f ↦ fourierIntegral μ f χ
      map_add' := fun f g ↦ fourierIntegral_coeFn_add f g χ
      map_smul' := fun c f ↦ fourierIntegral_coeFn_smul c f χ } 1
    fun f ↦ (norm_fourierIntegral_coeFn_le f χ).trans_eq (one_mul _).symm

@[simp]
theorem fourierIntegralCLM_apply (χ : AddPontryaginDual G) (f : Lp E 1 μ) :
    fourierIntegralCLM μ χ f = fourierIntegral μ f χ :=
  rfl

theorem norm_fourierIntegralCLM_le (χ : AddPontryaginDual G) :
    ‖(fourierIntegralCLM μ χ : Lp E 1 μ →L[ℂ] E)‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

/-- The linear functional `f ↦ fourierIntegral μ f χ` is a character of the Banach algebra
`L¹(G)`. -/
theorem toWeakDual_fourierIntegralCLM_mem_characterSpace (χ : AddPontryaginDual G) :
    StrongDual.toWeakDual (fourierIntegralCLM μ χ) ∈ characterSpace ℂ (Lp ℂ 1 μ) := by
  -- It is multiplicative by `fourierIntegral_mul`. It is nonzero: `χ • g` has nonzero Fourier
  -- transform at `χ` if `g ≥ 0` is a nonzero continuous function with compact support.
  sorry

/-- The character of the Banach algebra `L¹(G)` associated with `χ : AddPontryaginDual G`,
namely `f ↦ fourierIntegral μ f χ`. -/
noncomputable def toCharacterSpace (χ : AddPontryaginDual G) : characterSpace ℂ (Lp ℂ 1 μ) :=
  ⟨StrongDual.toWeakDual (fourierIntegralCLM μ χ),
    toWeakDual_fourierIntegralCLM_mem_characterSpace μ χ⟩

@[simp]
theorem toCharacterSpace_apply (χ : AddPontryaginDual G) (f : Lp ℂ 1 μ) :
    toCharacterSpace μ χ f = fourierIntegral μ f χ :=
  rfl

/-- Different characters of `G` define different characters of `L¹(G)`. -/
theorem toCharacterSpace_injective : Function.Injective (toCharacterSpace μ) := by
  -- If `χ ≠ η`, then `x ↦ χ (-x) - η (-x)` is a nonzero continuous function, hence its integral
  -- against some continuous function with compact support is nonzero.
  sorry

/-- Every character of `L¹(G)` is of the form `f ↦ fourierIntegral μ f χ`. -/
theorem toCharacterSpace_surjective : Function.Surjective (toCharacterSpace μ) := by
  -- Let `Φ` be a character of `L¹(G)` and let `f` be such that `Φ f ≠ 0`. Set
  -- `ψ x = Φ (τ_x f) / Φ f`. By `L1.translate_mul`, `Φ (τ_x f) * Φ g = Φ f * Φ (τ_x g)`, hence `ψ`
  -- does not depend on `f` and it is multiplicative. It is continuous since `x ↦ τ_x f` is
  -- continuous, and bounded since `‖Φ‖ ≤ 1`, hence it takes values in the unit circle.
  -- Finally, applying `Φ` to the Bochner integral `g * f = ∫ y, g y • τ_y f ∂μ` gives
  -- `Φ g * Φ f = Φ f * ∫ y, g y * ψ y ∂μ`.
  sorry

theorem continuous_toCharacterSpace : Continuous (toCharacterSpace μ) := by
  -- This amounts to the continuity of `fourierIntegral μ f` for all `f : Lp ℂ 1 μ`.
  sorry

/-- The compact-open topology on the Pontryagin dual agrees with the weak-* topology on the
character space of `L¹(G)`. -/
theorem isHomeomorph_toCharacterSpace : IsHomeomorph (toCharacterSpace μ) := by
  -- It remains to prove that the inverse map is continuous. If `Φ f ≠ 0`, then
  -- `(Φ, x) ↦ Φ (τ_x f) / Φ f` is jointly continuous, since `x ↦ τ_x f` is continuous and the
  -- characters are equicontinuous. Hence if `Φ_i → Φ`, then the corresponding characters of `G`
  -- converge uniformly on compact sets.
  sorry

/-- The Pontryagin dual of `G` is homeomorphic to the character space of `L¹(G)`. -/
noncomputable def characterSpaceHomeomorph :
    AddPontryaginDual G ≃ₜ characterSpace ℂ (Lp ℂ 1 μ) :=
  IsHomeomorph.homeomorph _ (isHomeomorph_toCharacterSpace μ)

@[simp]
theorem characterSpaceHomeomorph_apply (χ : AddPontryaginDual G) :
    characterSpaceHomeomorph μ χ = toCharacterSpace μ χ :=
  rfl

end AddPontryaginDual
