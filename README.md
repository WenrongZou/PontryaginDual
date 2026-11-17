# Pontryagin duality in Lean 4

A formalization of Pontryagin duality for locally compact Hausdorff abelian groups, on top of
Mathlib. The main theorem is

```lean
AddPontryaginDual.doubleDualEquiv G : G ≃ₜ+ AddPontryaginDual (AddPontryaginDual G)
```

with a multiplicative version `PontryaginDual.doubleDualEquiv`. Along the way we prove the
Plancherel theorem (`AddPontryaginDual.fourierL2`), the Fourier inversion formula and the
regularity of `L¹(G)`, and we construct the dual Haar measure `MeasureTheory.Measure.dualAddHaar`.

The repository contains two complete proofs, on two branches:

* `main` follows Rudin and Folland, through positive definite functions and Bochner's theorem;
* `Bourbaki` follows Bourbaki, *Théories spectrales*, Chap. II, §1, through the regular
  representation of `L¹(G)` on `L²(G)`. It does not use positive definite functions.

## Common part

Both proofs start from the Gelfand theory of `L¹(G)` and end with the same argument.

1. `L¹(G)` is a commutative Banach algebra under convolution, with the involution
   `f⋆(x) = conj (f (-x))` (`Convolution/L1Algebra.lean`).
2. The Pontryagin dual `Ĝ` is the character space of `L¹(G)` and the Fourier transform is the
   Gelfand transform (`Fourier/CharacterSpace.lean`). Hence `‖Ff‖∞` is the spectral radius of `f`,
   and the image of `L¹(G)` is dense in `C₀(Ĝ)` by Stone–Weierstrass (`Fourier/L1.lean`). By the
   multiplication formula, the density implies that the inverse Fourier transform is injective on
   `L¹(Ĝ)`.
3. From the inversion formula for enough functions, the canonical map `G → Ĝ^` is a topological
   embedding. Its range is a locally compact subgroup, hence closed. If it were not surjective,
   the regularity of `L¹(Ĝ)` would give a nonzero integrable function on `Ĝ` whose Fourier
   transform vanishes on the range, contradicting the injectivity of the inverse Fourier transform
   (`Duality/Basic.lean`).

The two branches differ in how they obtain the dual Haar measure, the Plancherel theorem and the
inversion formula.

## Branch `main`: positive definite functions and Bochner's theorem

References: Rudin, *Fourier Analysis on Groups*, §1.4–1.5; Folland, *A Course in Abstract
Harmonic Analysis*, §3.3, §4.2–4.3.

1. **Positive definite functions** (`PositiveDefinite/Basic.lean`). For `u ∈ L²(G)`, the function
   `u * u⋆` is positive definite, and there are continuous positive definite functions with
   support in any neighborhood of `0`.
2. **Bochner's theorem** (`PositiveDefinite/Bochner.lean`). For a continuous positive definite
   `φ`, the form `(g, h) ↦ ∫ (h * g⋆) φ` on `L¹(G)` is positive semidefinite. Cauchy–Schwarz and
   approximate units give the key estimate `|∫ f φ| ≤ φ(0) ‖Ff‖∞`. So `f ↦ ∫ f φ` extends to a
   positive functional on `C₀(Ĝ)`, which the Riesz–Markov–Kakutani theorem turns into a finite
   measure `bochnerMeasure φ` with `φ(x) = ∫ χ(x) dν(χ)`.
3. **Dual Haar measure and inversion** (`Inversion/DualHaar.lean`). For integrable continuous
   positive definite `f` and `g`, `Ff · bochnerMeasure g = Fg · bochnerMeasure f`. Gluing the
   measures `bochnerMeasure f / Ff` gives a translation-invariant measure on `Ĝ`, the dual Haar
   measure. Then `bochnerMeasure f` has density `Ff ≥ 0` with respect to it, which is the inversion
   theorem for integrable continuous positive definite functions.
4. **Plancherel** (`Inversion/Plancherel.lean`). Applying the inversion theorem to `u * u⋆` at `0`
   gives `‖Fu‖₂ = ‖u‖₂` for `u` continuous with compact support, and the Fourier transform extends
   to `L²`. Surjectivity uses the injectivity of the inverse Fourier transform on `L¹(Ĝ)`. The
   regularity of `L¹(G)` follows from the Plancherel theorem.

## Branch `Bourbaki`: the regular representation and spectral measures

Reference: Bourbaki, *Théories spectrales*, Chap. I, §6 and Chap. II, §1 (1967).

1. **Regular representation** (`Convolution/L2.lean`). `L¹(G)` acts on `L²(G)` by convolution,
   `regularRep : L¹(G) →ₙₐ L(L²(G))`, and `regularRep (f⋆)` is the adjoint of `regularRep f`.
2. **`C₀(Ĝ)` as the enveloping C⋆-algebra** (`Fourier/CStar.lean`). Since `L(L²(G))` is a
   C⋆-algebra, `‖π f‖² = ‖π(f⋆ * f)‖` is a spectral radius. It is bounded by the spectral radius
   of `f⋆ * f` in `L¹(G)`, which is `‖F(f⋆ * f)‖∞ = ‖Ff‖∞²`. Hence `‖f ⋆ g‖₂ ≤ ‖Ff‖∞ ‖g‖₂`, and
   `regularRep` extends to a representation `fourierMultiplier` of `C₀(Ĝ)` on `L²(G)`.
3. **Spectral measures** (`Fourier/CStar.lean`). For `g ∈ L²(G)`, `Φ ↦ ⟪g, fourierMultiplier Φ g⟫`
   is a positive functional on `C₀(Ĝ)`. The Riesz–Markov–Kakutani theorem turns it into a finite
   measure `spectralMeasure μ g`. Approximate units show that its total mass is `‖g‖₂²`, and
   `spectralMeasure μ (φ ⋆ g)` has density `|Fφ|²` with respect to `spectralMeasure μ g`.
4. **Dual Haar measure** (`Inversion/DualHaar.lean`). For `f`, `g ∈ L¹ ∩ L²`, commutativity of
   convolution gives `|Ff|² · spectralMeasure μ g = |Fg|² · spectralMeasure μ f`. Gluing the
   measures `spectralMeasure μ g / |Fg|²` gives the dual Haar measure `ν`. Translation invariance
   comes from multiplying `g` by characters. Then `spectralMeasure μ f = |Ff|² · ν`, and comparing
   total masses gives `‖Ff‖₂ = ‖f‖₂` directly, without an inversion theorem.
5. **Plancherel and inversion** (`Inversion/Plancherel.lean`). The Fourier transform extends to a
   unitary operator `L²(G) ≃ L²(Ĝ)`. The Parseval formula gives the inversion formula for the
   functions `f * g⋆` with `f`, `g ∈ L¹ ∩ L²`. As on `main`, the regularity of `L¹(G)` follows
   from the Plancherel theorem.
6. **Duality** (`Duality/Basic.lean`). The common argument above. In addition, the dual of the
   dual Haar measure is the image of `μ` under `G ≃ Ĝ^` (`dualAddHaar_dualAddHaar`).

## Building

```sh
lake exe cache get
lake build
```

Supporting results that should eventually go to Mathlib are in `PontryaginDuality/Mathlib/`.
