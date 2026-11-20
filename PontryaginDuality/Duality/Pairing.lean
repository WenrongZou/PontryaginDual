/-
Copyright (c) 2026 Wenrong Zou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wenrong Zou
-/
module

public import PontryaginDuality.Duality.Basic

/-!
# Nondegenerate pairings

Let `G` and `H` be locally compact abelian groups, with `H` Hausdorff. A continuous homomorphism
`f : G → Ĥ` is the same as a pairing `(x, y) ↦ f x y` on `G × H`. If `f` is a topological
embedding and the pairing is nondegenerate in `H`, then `f` is an isomorphism of topological
groups, and so is the map `H → Ĝ` sending `y` to `x ↦ f x y`. This is a consequence of the
duality theorem.

## Main definitions

* `AddPontryaginDual.mapEquiv e`: the isomorphism of Pontryagin duals induced by an isomorphism
  `e` of topological additive monoids.
* `AddPontryaginDual.equivOfIsEmbedding`: the isomorphism `G ≃ₜ+ Ĥ` given by such an `f`.
* `AddPontryaginDual.flipEquivOfIsEmbedding`: the isomorphism `H ≃ₜ+ Ĝ` given by such an `f`.

## Main statements

* `AddPontryaginDual.exists_apply_ne_zero_of_notMem`: the characters vanishing on a closed
  subgroup `K` separate the points outside `K` from `K`.
* `AddPontryaginDual.surjective_of_isEmbedding`: a topological embedding `f : G → Ĥ` such that
  the pairing `(x, y) ↦ f x y` is nondegenerate in `H` is surjective.
-/

@[expose] public section

open Topology

namespace AddPontryaginDual

section MapEquiv

variable {A B : Type*} [AddMonoid A] [AddMonoid B] [TopologicalSpace A] [TopologicalSpace B]

/-- An isomorphism of topological additive monoids induces an isomorphism of their Pontryagin
duals. -/
noncomputable def mapEquiv (e : A ≃ₜ+ B) : AddPontryaginDual B ≃ₜ+ AddPontryaginDual A where
  toFun := map (e : A →ₜ+ B)
  invFun := map (e.symm : B →ₜ+ A)
  left_inv χ := ext fun b ↦ congr_arg χ (e.apply_symm_apply b)
  right_inv χ := ext fun a ↦ congr_arg χ (e.symm_apply_apply a)
  map_add' := map_add (map (e : A →ₜ+ B))
  continuous_toFun := map_continuous (map (e : A →ₜ+ B))
  continuous_invFun := map_continuous (map (e.symm : B →ₜ+ A))

@[simp]
theorem mapEquiv_apply (e : A ≃ₜ+ B) (χ : AddPontryaginDual B) (a : A) :
    mapEquiv e χ a = χ (e a) :=
  rfl

end MapEquiv

section Separation

variable {G : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
  [LocallyCompactSpace G]

theorem exists_apply_ne_zero [T2Space G] {x : G} (hx : x ≠ 0) :
    ∃ χ : AddPontryaginDual G, χ x ≠ 0 := by
  obtain ⟨χ, hχ⟩ := exists_toAddChar_ne_one hx
  exact ⟨χ, fun h ↦ hχ (by simp [toAddChar_apply, h])⟩

/-- The characters of `G` vanishing on a closed subgroup `K` separate the points outside `K` from
`K`. -/
theorem exists_apply_ne_zero_of_notMem {K : AddSubgroup G} (hK : IsClosed (K : Set G)) {x : G}
    (hx : x ∉ K) : ∃ χ : AddPontryaginDual G, (∀ y ∈ K, χ y = 0) ∧ χ x ≠ 0 := by
  -- Apply `exists_apply_ne_zero` to the locally compact Hausdorff group `G ⧸ K`.
  have := hK
  obtain ⟨χ, hχ⟩ := exists_apply_ne_zero ((QuotientAddGroup.eq_zero_iff (N := K) x).not.2 hx)
  refine ⟨map ⟨QuotientAddGroup.mk' K, QuotientAddGroup.continuous_mk⟩ χ, fun y hy ↦ ?_, hχ⟩
  change χ (y : G ⧸ K) = 0
  rw [(QuotientAddGroup.eq_zero_iff y).2 hy, map_zero]

end Separation

variable {G H : Type*} [AddCommGroup G] [TopologicalSpace G] [LocallyCompactSpace G]
  [AddCommGroup H] [TopologicalSpace H] [IsTopologicalAddGroup H] [LocallyCompactSpace H]
  [T2Space H]

/-- Let `f : G → Ĥ` be a topological embedding. If the pairing `(x, y) ↦ f x y` on `G × H` is
nondegenerate in `H`, then `f` is surjective. -/
theorem surjective_of_isEmbedding {f : G →ₜ+ AddPontryaginDual H} (hf : IsEmbedding f)
    (h : ∀ y : H, (∀ x, f x y = 0) → y = 0) : Function.Surjective f := by
  -- The range of `f` is closed. A character of `Ĥ` vanishing on it is the evaluation at some
  -- `y : H` by the duality theorem, and `y = 0` by `h`.
  intro χ
  by_contra hχ
  obtain ⟨ξ, hξ, hξχ⟩ := exists_apply_ne_zero_of_notMem (K := f.toAddMonoidHom.range)
    (f.toAddMonoidHom.isClosed_range_of_isEmbedding hf) (x := χ) (by simpa using hχ)
  obtain ⟨y, rfl⟩ := doubleDualEmb_surjective H ξ
  rw [h y fun x ↦ hξ _ ⟨x, rfl⟩, map_zero, zero_apply] at hξχ
  exact hξχ rfl

theorem bijective_of_isEmbedding {f : G →ₜ+ AddPontryaginDual H} (hf : IsEmbedding f)
    (h : ∀ y : H, (∀ x, f x y = 0) → y = 0) : Function.Bijective f :=
  ⟨hf.injective, surjective_of_isEmbedding hf h⟩

/-- A topological embedding `f : G → Ĥ` such that the pairing `(x, y) ↦ f x y` on `G × H` is
nondegenerate in `H` is an isomorphism of topological groups. -/
noncomputable def equivOfIsEmbedding (f : G →ₜ+ AddPontryaginDual H) (hf : IsEmbedding f)
    (h : ∀ y : H, (∀ x, f x y = 0) → y = 0) : G ≃ₜ+ AddPontryaginDual H where
  __ := AddEquiv.ofBijective f (bijective_of_isEmbedding hf h)
  continuous_toFun := map_continuous f
  continuous_invFun :=
    ((Equiv.ofBijective _ (bijective_of_isEmbedding hf h)).toHomeomorphOfIsInducing
      hf.isInducing).symm.continuous

@[simp]
theorem coe_equivOfIsEmbedding (f : G →ₜ+ AddPontryaginDual H) (hf : IsEmbedding f)
    (h : ∀ y : H, (∀ x, f x y = 0) → y = 0) : ⇑(equivOfIsEmbedding f hf h) = f :=
  rfl

/-- Let `f : G → Ĥ` be a topological embedding such that the pairing `(x, y) ↦ f x y` on `G × H`
is nondegenerate in `H`. Then the map `H → Ĝ` sending `y` to `x ↦ f x y` is an isomorphism of
topological groups. -/
noncomputable def flipEquivOfIsEmbedding (f : G →ₜ+ AddPontryaginDual H) (hf : IsEmbedding f)
    (h : ∀ y : H, (∀ x, f x y = 0) → y = 0) : H ≃ₜ+ AddPontryaginDual G :=
  (doubleDualEquiv H).trans (mapEquiv (equivOfIsEmbedding f hf h))

@[simp]
theorem flipEquivOfIsEmbedding_apply_apply (f : G →ₜ+ AddPontryaginDual H) (hf : IsEmbedding f)
    (h : ∀ y : H, (∀ x, f x y = 0) → y = 0) (y : H) (x : G) :
    flipEquivOfIsEmbedding f hf h y x = f x y :=
  rfl

end AddPontryaginDual
