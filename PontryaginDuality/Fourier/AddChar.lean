/-
Copyright (c) 2026 Wenrong Zou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wenrong Zou
-/
module

public import Mathlib.Algebra.Group.AddChar
public import PontryaginDuality.Mathlib.Topology.Algebra.PontryaginDual

/-!
# Elements of the additive Pontryagin dual as additive characters

An element `χ` of `AddPontryaginDual A` is a continuous additive homomorphism
`A →+ Additive Circle`. In order to do Fourier analysis, we need the corresponding function
`A → Circle`, which turns addition into multiplication. In Mathlib, such functions are called
additive characters; they are the objects used by the existing Fourier analysis library (see e.g.
`VectorFourier.fourierIntegral`).

## Main definitions

* `AddPontryaginDual.toAddChar χ`: the additive character `A → Circle` associated with
  `χ : AddPontryaginDual A`. We have `χ.toAddChar a = (χ a).toMul`.

## Implementation notes

All the files of this project access the values of the elements of `AddPontryaginDual A` through
`AddPontryaginDual.toAddChar`. In particular, they do not depend on the fact that the codomain is
implemented as `Additive Circle`.
-/

@[expose] public section

namespace AddPontryaginDual

variable {A : Type*} [AddMonoid A] [TopologicalSpace A]

@[simp]
theorem add_apply (χ η : AddPontryaginDual A) (a : A) : (χ + η) a = χ a + η a :=
  rfl

@[simp]
theorem neg_apply (χ : AddPontryaginDual A) (a : A) : (-χ) a = -χ a :=
  rfl

@[simp]
theorem sub_apply (χ η : AddPontryaginDual A) (a : A) : (χ - η) a = χ a - η a :=
  rfl

/-- The additive character `A → Circle` associated with an element of the additive Pontryagin
dual of `A`. -/
noncomputable def toAddChar (χ : AddPontryaginDual A) : AddChar A Circle :=
  AddChar.toAddMonoidHomEquiv.symm (AddMonoidHom.ofClass χ)

theorem toAddChar_apply (χ : AddPontryaginDual A) (a : A) : χ.toAddChar a = (χ a).toMul :=
  rfl

theorem toAddChar_injective :
    Function.Injective (toAddChar : AddPontryaginDual A → AddChar A Circle) := by
  intro χ η h
  refine AddPontryaginDual.ext fun a ↦ ?_
  exact Additive.toMul.injective (DFunLike.congr_fun h a)

@[simp]
theorem toAddChar_inj {χ η : AddPontryaginDual A} : χ.toAddChar = η.toAddChar ↔ χ = η :=
  toAddChar_injective.eq_iff

/-- The element of the additive Pontryagin dual of `A` associated with a continuous additive
character `A → Circle`. -/
noncomputable def ofAddChar (ψ : AddChar A Circle) (hψ : Continuous ψ) : AddPontryaginDual A :=
  (⟨AddChar.toAddMonoidHomEquiv ψ, continuous_ofMul.comp hψ⟩ : A →ₜ+ AdditiveCircle)

@[simp]
theorem toAddChar_ofAddChar (ψ : AddChar A Circle) (hψ : Continuous ψ) :
    (ofAddChar ψ hψ).toAddChar = ψ :=
  rfl

@[simp]
theorem toAddChar_zero_apply (a : A) : (0 : AddPontryaginDual A).toAddChar a = 1 :=
  rfl

@[simp]
theorem toAddChar_add_apply (χ η : AddPontryaginDual A) (a : A) :
    (χ + η).toAddChar a = χ.toAddChar a * η.toAddChar a :=
  rfl

@[simp]
theorem toAddChar_neg_apply (χ : AddPontryaginDual A) (a : A) :
    (-χ).toAddChar a = (χ.toAddChar a)⁻¹ :=
  rfl

@[simp]
theorem toAddChar_sub_apply (χ η : AddPontryaginDual A) (a : A) :
    (χ - η).toAddChar a = χ.toAddChar a / η.toAddChar a :=
  rfl

@[fun_prop]
theorem continuous_toAddChar (χ : AddPontryaginDual A) : Continuous χ.toAddChar :=
  continuous_toMul.comp (map_continuous χ)

instance : ContinuousEvalConst (AddPontryaginDual A) A AdditiveCircle :=
  inferInstanceAs (ContinuousEvalConst (A →ₜ+ AdditiveCircle) A AdditiveCircle)

instance [LocallyCompactSpace A] : ContinuousEval (AddPontryaginDual A) A AdditiveCircle :=
  inferInstanceAs (ContinuousEval (A →ₜ+ AdditiveCircle) A AdditiveCircle)

/-- For every `a : A`, the evaluation `χ ↦ χ.toAddChar a` is continuous. -/
@[fun_prop]
theorem continuous_toAddChar_apply (a : A) :
    Continuous fun χ : AddPontryaginDual A ↦ χ.toAddChar a :=
  continuous_toMul.comp (continuous_eval_const a)

/-- If `A` is locally compact, then the evaluation `(χ, a) ↦ χ.toAddChar a` is jointly
continuous. -/
theorem continuous_toAddChar_uncurry [LocallyCompactSpace A] :
    Continuous fun p : AddPontryaginDual A × A ↦ p.1.toAddChar p.2 :=
  continuous_toMul.comp continuous_eval

/-- A map `f` into the additive Pontryagin dual is continuous if `(x, a) ↦ (f x).toAddChar a` is
jointly continuous. -/
theorem continuous_of_continuous_uncurry {X : Type*} [TopologicalSpace X]
    (f : X → AddPontryaginDual A) (h : Continuous fun p : X × A ↦ (f p.1).toAddChar p.2) :
    Continuous f :=
  ContinuousAddMonoidHom.continuous_of_continuous_uncurry (B := A) (C := AdditiveCircle) f
    (continuous_ofMul.comp h)

end AddPontryaginDual
