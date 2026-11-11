/-
Copyright (c) 2026 Wenrong Zou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wenrong Zou
-/
module

public import PontryaginDuality.Convolution.L1Algebra
public import PontryaginDuality.Fourier.AddChar

/-!
# The Fourier transform on a locally compact abelian group

Let `G` be a locally compact abelian group with a Haar measure `μ`. The Fourier transform of
`f : G → E` is the function on the Pontryagin dual of `G` given by
`χ ↦ ∫ x, χ (-x) • f x ∂μ`.

## Main definitions

* `AddPontryaginDual.fourierIntegral μ f`: the Fourier transform of `f : G → E` with respect to
  the measure `μ`, as a function `AddPontryaginDual G → E`.
* `AddPontryaginDual.fourierIntegralInv ν F`: the inverse Fourier transform of
  `F : AddPontryaginDual G → E` with respect to the measure `ν` on `AddPontryaginDual G`, as a
  function `G → E`. It is given by `x ↦ ∫ χ, χ x • F χ ∂ν`.

## Main statements

* `AddPontryaginDual.continuous_fourierIntegral`: the Fourier transform of an integrable function
  is continuous.
* `AddPontryaginDual.fourierIntegral_mul`: the Fourier transform turns the convolution product of
  `L¹(G)` into the pointwise product.

## Implementation notes

`VectorFourier.fourierIntegral e μ L f w = ∫ v, e (-L v w) • f v ∂μ` is the special case where `G`
is a module `V` and the character is `v ↦ e (L v w)`.
-/

@[expose] public section

open MeasureTheory Measure Filter Topology
open scoped ComplexConjugate

namespace AddPontryaginDual

variable {G E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [MeasurableSpace G]
  [AddCommGroup G] [TopologicalSpace G]

section Defs

variable {μ : Measure G} {f g : G → E} {χ : AddPontryaginDual G}

/-- The Fourier transform of `f : G → E` with respect to the measure `μ`, as a function on the
Pontryagin dual of `G`. It sends a character `χ` to `∫ x, χ (-x) • f x ∂μ`. -/
noncomputable def fourierIntegral (μ : Measure G) (f : G → E) (χ : AddPontryaginDual G) : E :=
  ∫ x, χ.toAddChar (-x) • f x ∂μ

/-- The inverse Fourier transform of `F : AddPontryaginDual G → E` with respect to the measure `ν`
on the Pontryagin dual of `G`. It sends `x : G` to `∫ χ, χ x • F χ ∂ν`. -/
noncomputable def fourierIntegralInv [MeasurableSpace (AddPontryaginDual G)]
    (ν : Measure (AddPontryaginDual G)) (F : AddPontryaginDual G → E) (x : G) : E :=
  ∫ χ, χ.toAddChar x • F χ ∂ν

theorem fourierIntegral_apply : fourierIntegral μ f χ = ∫ x, χ.toAddChar (-x) • f x ∂μ :=
  rfl

omit [MeasurableSpace G] in
theorem fourierIntegralInv_apply [MeasurableSpace (AddPontryaginDual G)]
    {ν : Measure (AddPontryaginDual G)} {F : AddPontryaginDual G → E} {x : G} :
    fourierIntegralInv ν F x = ∫ χ, χ.toAddChar x • F χ ∂ν :=
  rfl

theorem fourierIntegral_congr_ae (h : f =ᵐ[μ] g) : fourierIntegral μ f = fourierIntegral μ g := by
  ext χ
  refine integral_congr_ae ?_
  filter_upwards [h] with x hx
  rw [hx]

/-- The uniform norm of the Fourier transform of `f` is bounded by the `L¹` norm of `f`. -/
theorem norm_fourierIntegral_le_integral_norm (μ : Measure G) (f : G → E)
    (χ : AddPontryaginDual G) : ‖fourierIntegral μ f χ‖ ≤ ∫ x, ‖f x‖ ∂μ := by
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  simp_rw [Circle.norm_smul]

theorem fourierIntegral_const_smul (μ : Measure G) (c : ℂ) (f : G → E) :
    fourierIntegral μ (c • f) = c • fourierIntegral μ f := by
  ext χ
  simp only [fourierIntegral, Pi.smul_apply, smul_comm _ c, integral_smul]

/-- The Fourier transform turns multiplication by a character into translation. -/
theorem fourierIntegral_toAddChar_smul (μ : Measure G) (η : AddPontryaginDual G) (f : G → E)
    (χ : AddPontryaginDual G) :
    fourierIntegral μ (fun x ↦ η.toAddChar x • f x) χ = fourierIntegral μ f (χ - η) := by
  sorry

end Defs

section AddGroup

variable [IsTopologicalAddGroup G] [LocallyCompactSpace G] [BorelSpace G]
  {μ : Measure G} [μ.IsAddHaarMeasure] [μ.Regular] {f : G → E}

theorem fourierIntegral_add {g : G → E} (hf : Integrable f μ) (hg : Integrable g μ) :
    fourierIntegral μ (f + g) = fourierIntegral μ f + fourierIntegral μ g := by
  sorry

/-- The Fourier transform turns translation into multiplication by a character. -/
theorem fourierIntegral_comp_add_left (f : G → E) (a : G) (χ : AddPontryaginDual G) :
    fourierIntegral μ (fun x ↦ f (a + x)) χ = χ.toAddChar a • fourierIntegral μ f χ := by
  sorry

/-- The Fourier transform turns the involution `f ↦ (x ↦ conj (f (-x)))` into the complex
conjugation. -/
theorem fourierIntegral_conj_neg (f : G → ℂ) (χ : AddPontryaginDual G) :
    fourierIntegral μ (fun x ↦ conj (f (-x))) χ = conj (fourierIntegral μ f χ) := by
  sorry

/-- The Fourier transform of an integrable function is continuous. -/
theorem continuous_fourierIntegral (hf : Integrable f μ) : Continuous (fourierIntegral μ f) := by
  -- For every `ε > 0` there is a compact set `K` with `∫ x in Kᶜ, ‖f x‖ ∂μ < ε` (by regularity),
  -- and the topology of `AddPontryaginDual G` is the topology of uniform convergence on compact
  -- sets.
  sorry

/-- The inverse Fourier transform of an integrable function is continuous. -/
theorem continuous_fourierIntegralInv [MeasurableSpace (AddPontryaginDual G)]
    [BorelSpace (AddPontryaginDual G)] {ν : Measure (AddPontryaginDual G)} [ν.Regular]
    {F : AddPontryaginDual G → E} (hF : Integrable F ν) :
    Continuous (fourierIntegralInv ν F) := by
  -- Compact subsets of `AddPontryaginDual G` are equicontinuous since `G` is locally compact.
  sorry

section Lp

/-! ### The Fourier transform of elements of `L¹(G)` -/

theorem fourierIntegral_coeFn_zero (χ : AddPontryaginDual G) :
    fourierIntegral μ (0 : Lp E 1 μ) χ = 0 := by
  sorry

theorem fourierIntegral_coeFn_add (f g : Lp E 1 μ) (χ : AddPontryaginDual G) :
    fourierIntegral μ (f + g : Lp E 1 μ) χ = fourierIntegral μ f χ + fourierIntegral μ g χ := by
  sorry

theorem fourierIntegral_coeFn_smul (c : ℂ) (f : Lp E 1 μ) (χ : AddPontryaginDual G) :
    fourierIntegral μ (c • f : Lp E 1 μ) χ = c • fourierIntegral μ f χ := by
  sorry

theorem norm_fourierIntegral_coeFn_le (f : Lp E 1 μ) (χ : AddPontryaginDual G) :
    ‖fourierIntegral μ f χ‖ ≤ ‖f‖ := by
  sorry

end Lp

/-- The Fourier transform turns the convolution product of `L¹(G)` into the pointwise product. -/
theorem fourierIntegral_mul (f g : Lp ℂ 1 μ) (χ : AddPontryaginDual G) :
    fourierIntegral μ (f * g : Lp ℂ 1 μ) χ = fourierIntegral μ f χ * fourierIntegral μ g χ := by
  -- Apply the continuous linear functional `fourierIntegral μ · χ` to the Bochner integral
  -- `f * g = ∫ y, f y • τ_y g ∂μ` and use `fourierIntegral_comp_add_left`.
  sorry

theorem fourierIntegral_involution (f : Lp ℂ 1 μ) (χ : AddPontryaginDual G) :
    fourierIntegral μ (L1.involution f) χ = conj (fourierIntegral μ f χ) := by
  sorry

end AddGroup

end AddPontryaginDual
