/-
Copyright (c) 2026 Wenrong Zou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wenrong Zou
-/
module

public import Mathlib.Topology.Algebra.PontryaginDual

/-!
# The additive Pontryagin dual

This file is a temporary copy of the additive part of
[Mathlib PR #45838](https://github.com/leanprover-community/mathlib4/pull/45838). It has to be
deleted once this PR is merged and the Mathlib dependency of this project is updated.

In the PR, `AddPontryaginDual` and its basic API are generated from `PontryaginDual` by
`to_additive`. Since we cannot tag the declarations of Mathlib from here, everything is defined by
hand in this file, with the same names as in the PR.

## Main definitions

* `AdditiveCircle`: the circle group, written additively.
* `AddPontryaginDual A`: the group of continuous additive homomorphisms `A →+ Additive Circle`.
* `AddPontryaginDual.toMultiplicative`: the additive Pontryagin dual of `A` is homeomorphic to the
  Pontryagin dual of `Multiplicative A`.
-/

@[expose] public section

noncomputable section

/-! ### The circle as an additive group -/

/-- The circle group, written additively. -/
abbrev AdditiveCircle : Type :=
  Additive Circle

namespace AdditiveCircle

instance instAddCommGroup : AddCommGroup AdditiveCircle := inferInstance

instance instTopologicalSpace : TopologicalSpace AdditiveCircle := inferInstance

instance instIsTopologicalAddGroup : IsTopologicalAddGroup AdditiveCircle := inferInstance

end AdditiveCircle

/-! ### The additive Pontryagin dual -/

variable (A B H : Type*) [AddMonoid A] [AddMonoid B] [AddGroup H]
  [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace H] [IsTopologicalAddGroup H]

/-- The additive Pontryagin dual of `A` is the group of continuous additive homomorphisms
`A → Additive Circle`. -/
def AddPontryaginDual :=
  A →ₜ+ AdditiveCircle

instance instTopologicalSpaceAddPontryaginDual : TopologicalSpace (AddPontryaginDual A) :=
  inferInstanceAs (TopologicalSpace (A →ₜ+ AdditiveCircle))

variable {A B}

namespace AddPontryaginDual

open ContinuousAddMonoidHom

instance : AddCommGroup (AddPontryaginDual A) :=
  inferInstanceAs (AddCommGroup (A →ₜ+ AdditiveCircle))

instance : T2Space (AddPontryaginDual A) := inferInstanceAs (T2Space (A →ₜ+ AdditiveCircle))

instance : IsTopologicalAddGroup (AddPontryaginDual A) :=
  inferInstanceAs (IsTopologicalAddGroup (A →ₜ+ AdditiveCircle))

instance : Inhabited (AddPontryaginDual A) := inferInstanceAs (Inhabited (A →ₜ+ AdditiveCircle))

instance instFunLikeAdditiveCircle : FunLike (AddPontryaginDual A) A AdditiveCircle :=
  inferInstanceAs (FunLike (A →ₜ+ AdditiveCircle) A AdditiveCircle)

instance instContinuousMapClassAdditiveCircle :
    ContinuousMapClass (AddPontryaginDual A) A AdditiveCircle :=
  inferInstanceAs (ContinuousMapClass (A →ₜ+ AdditiveCircle) A AdditiveCircle)

instance instAddMonoidHomClassAdditiveCircle :
    AddMonoidHomClass (AddPontryaginDual A) A AdditiveCircle :=
  inferInstanceAs (AddMonoidHomClass (A →ₜ+ AdditiveCircle) A AdditiveCircle)

instance [DiscreteTopology A] : CompactSpace (AddPontryaginDual A) :=
  inferInstanceAs (CompactSpace (A →ₜ+ AdditiveCircle))

@[ext]
theorem ext {ψ φ : AddPontryaginDual A} (h : ∀ a, ψ a = φ a) : ψ = φ :=
  DFunLike.ext _ _ h

@[simp]
theorem zero_apply (a : A) : (0 : AddPontryaginDual A) a = 0 :=
  rfl

/-- `AddPontryaginDual` is a contravariant functor. -/
def map (f : A →ₜ+ B) : (AddPontryaginDual B) →ₜ+ (AddPontryaginDual A) :=
  f.compLeft AdditiveCircle

@[simp]
theorem map_apply (f : A →ₜ+ B) (x : AddPontryaginDual B) (y : A) : map f x y = x (f y) :=
  rfl

variable (A)

/-- The additive Pontryagin dual of `A` is homeomorphic to the Pontryagin dual of
`Multiplicative A`. -/
def toMultiplicative : AddPontryaginDual A ≃ₜ PontryaginDual (Multiplicative A) where
  toFun φ := ⟨AddMonoidHom.toMultiplicativeLeft φ.toAddMonoidHom, φ.continuous_toFun⟩
  invFun ψ := ⟨MonoidHom.toAdditiveRight ψ.toMonoidHom, ψ.continuous_toFun⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun :=
    (ContinuousMonoidHom.isInducing_toContinuousMap _ _).continuous_iff.2
      (ContinuousAddMonoidHom.isInducing_toContinuousMap A _).continuous
  continuous_invFun :=
    (ContinuousAddMonoidHom.isInducing_toContinuousMap A _).continuous_iff.2
      (ContinuousMonoidHom.isInducing_toContinuousMap _ _).continuous

variable {A} in
@[simp]
theorem toMultiplicative_apply (φ : AddPontryaginDual A) (a : Multiplicative A) :
    toMultiplicative A φ a = (φ a.toAdd).toMul :=
  rfl

instance [LocallyCompactSpace H] : LocallyCompactSpace (AddPontryaginDual H) :=
  have : LocallyCompactSpace (Multiplicative H) := ‹LocallyCompactSpace H›
  (toMultiplicative H).isClosedEmbedding.locallyCompactSpace

/-- A compact additive monoid has discrete Pontryagin dual. -/
instance [CompactSpace A] : DiscreteTopology (AddPontryaginDual A) :=
  have : CompactSpace (Multiplicative A) := ‹CompactSpace A›
  (toMultiplicative A).symm.discreteTopology

instance [DiscreteTopology A] [CompactSpace A] : Finite (AddPontryaginDual A) :=
  finite_of_compact_of_discrete

end AddPontryaginDual
