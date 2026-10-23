/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.HilbertScheme.FlatteningBridge
public import Aglib.AlgebraicGeometry.FlatteningStratification.Global

/-!
# The flattening strata of the structure module of a closed subscheme

Let `S` be locally Noetherian, `s : S ⟶ Spec A`, `ι ≃ Fin (n + 1)` and `Z` a closed subscheme of
`X_S = P^n_A ×_{Spec A} S`. Its structure module `𝒪_Z` is coherent (`hF`); this holds for every
`Z`, by `Z.affineLocallyFiniteType_quotientModule`, and the stratum does not depend on the proof
`hF`. For a polynomial `Φ`
and a locally Noetherian `T`, a morphism `g : T ⟶ S` factors through the flattening stratum `S_Φ`
of `𝒪_Z` if and only if the pulled-back closed subscheme `Z.comap (pullbackBaseChange ι s g)` of
`P^n_A ×_{Spec A} T` is a point of `Hilb^Φ(T)`
(`ProjectiveSpace.exists_lift_flatteningStratumι_iff_isHilbertFamily`). The universal property of
the strata (`exists_lift_flatteningStratumι_iff_pullbackBaseChange`) is a condition on the pullback
`F_T` of `𝒪_Z` along `pullbackBaseChange ι s g`, and `F_T ≅ 𝒪_{Z_T}` without any flatness
(`quotientModulePullbackIso`); the Hilbert functor in the language of the strata
(`isHilbertFamily_iff_relativeFlat_and_fiberHilbertPolynomialAt`) then applies to `Z_T`. This is
property (F) of Nitsure, *Construction of Hilbert and Quot schemes*, arXiv:math/0504590v1, §5,
"Use of Flattening Stratification", p. 26, with `E = O_X` and `F = 𝒪_Z`.

* `Scheme.Cohomology.fiberHilbertPolynomialAt_congr`: chart fiber polynomials are invariant under
  isomorphisms of modules.
* `ProjectiveSpace.isHilbertFamily_comap_pullbackBaseChange_iff`: `Z_T ∈ Hilb^Φ(T)` if and only if
  `F_T` is flat over `T` with chart fiber polynomial `Φ` at every point; no Noetherian hypothesis.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.ProjectiveSpace
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open scoped Polynomial

universe u

namespace AlgebraicGeometry

namespace Scheme.Cohomology

variable {A : Type u} [CommRing A] (ι : Type u) {S : Scheme.{u}} (s : S ⟶ Spec (CommRingCat.of A))

/-- Chart fiber polynomials are invariant under isomorphisms of modules. -/
theorem fiberHilbertPolynomialAt_congr {F F' : (pullback (toSpec A ι) s).Modules} (e : F ≅ F')
    (y : S) : fiberHilbertPolynomialAt ι s F y = fiberHilbertPolynomialAt ι s F' y := by
  unfold fiberHilbertPolynomialAt
  exact projectiveHilbertPolynomial_congr _ ι
    ((Scheme.Modules.pullback _).mapIso ((Scheme.Modules.pullback _).mapIso e))

end Scheme.Cohomology

namespace ProjectiveSpace

open Scheme.Cohomology

variable {A : Type u} [CommRing A] (ι : Type u) {S : Scheme.{u}}
  (s : S ⟶ Spec (CommRingCat.of A)) (Z : (pullback (toSpec A ι) s).IdealSheafData)

/-- **Points of the Hilbert functor through `F_T`**: for finitely many coordinates, a closed
subscheme `Z ⊆ X_S` and `g : T ⟶ S`, the pulled-back closed subscheme
`Z_T = Z.comap (pullbackBaseChange ι s g)` is a point of `Hilb^Φ(T)` if and only if the pullback
`F_T` of `𝒪_Z` along `pullbackBaseChange ι s g` is flat over `T` and has chart fiber polynomial
`Φ` at every point of `T`. -/
theorem isHilbertFamily_comap_pullbackBaseChange_iff [Finite ι] {T : Scheme.{u}} (g : T ⟶ S)
    (Φ : ℚ[X]) :
    IsHilbertFamily ι Φ (g ≫ s) (Z.comap (pullbackBaseChange ι s g)) ↔
      relativeFlat (pullback.snd (toSpec A ι) (g ≫ s))
          ((Scheme.Modules.pullback (pullbackBaseChange ι s g)).obj Z.quotientModule) ∧
        ∀ t : T, fiberHilbertPolynomialAt ι (g ≫ s)
          ((Scheme.Modules.pullback (pullbackBaseChange ι s g)).obj Z.quotientModule) t = Φ := by
  rw [isHilbertFamily_iff_relativeFlat_and_fiberHilbertPolynomialAt]
  have E := Z.quotientModulePullbackIso (pullbackBaseChange ι s g)
  refine and_congr ⟨relativeFlat_of_iso _ E, relativeFlat_of_iso _ E.symm⟩
    (forall_congr' fun t => ?_)
  rw [fiberHilbertPolynomialAt_congr ι (g ≫ s) E t]

variable [IsLocallyNoetherian S] (n : ℕ) (e : ι ≃ Fin (n + 1))
  (hF : affineLocallyFiniteType (pullback (toSpec A ι) s) Z.quotientModule)

include e in
/-- **The flattening strata of `𝒪_Z` represent the Hilbert functor of `Z`** (Nitsure,
arXiv:math/0504590v1, §5, property (F), p. 26, with `E = O_X`): for a locally Noetherian base
`S`, `ι ≃ Fin (n + 1)`, a closed subscheme `Z ⊆ X_S` (`hF`, the coherence of `𝒪_Z`, holds for
every `Z` by `Z.affineLocallyFiniteType_quotientModule`) and a polynomial `Φ`, a morphism
`g : T ⟶ S` from a locally Noetherian `T` factors through the flattening stratum `S_Φ` of `𝒪_Z` if
and only if `Z.comap (pullbackBaseChange ι s g)` is a point of `Hilb^Φ(T)`. No flatness of `Z`
over `S` is assumed. -/
theorem exists_lift_flatteningStratumι_iff_isHilbertFamily (Φ : ℚ[X]) {T : Scheme.{u}}
    [IsLocallyNoetherian T] (g : T ⟶ S) :
    (∃ h : T ⟶ flatteningStratum ι s n e hF Φ, h ≫ flatteningStratumι ι s n e hF Φ = g) ↔
      IsHilbertFamily ι Φ (g ≫ s) (Z.comap (pullbackBaseChange ι s g)) := by
  have : Finite ι := Finite.of_equiv _ e.symm
  rw [exists_lift_flatteningStratumι_iff_pullbackBaseChange,
    isHilbertFamily_comap_pullbackBaseChange_iff]

end ProjectiveSpace

end AlgebraicGeometry
