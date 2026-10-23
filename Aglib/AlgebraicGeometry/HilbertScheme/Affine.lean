/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.HilbertScheme.Injectivity

/-!
# Points of the Hilbert functor over affine pieces of the test scheme

Let `Z` be a point of the Hilbert functor `Hilb^Φ(T)` of `P^n_A` (`IsHilbertFamily ι Φ g Z`, for
`g : T ⟶ Spec A`) and `x : Spec B ⟶ T` a morphism from an affine scheme, for instance an affine
open `Spec B ⊆ T` or `T = Spec B` itself. The pullback `Z_x = Z.comap (pointMap ι g x)` is a
closed subscheme of `P^n_B` (`pointMap` is defined for every ring), and it is a point of the
affine form used in `DirectImage` and `Injectivity`:

* `IsHilbertFamily.flat_comap_pointMap`: `Z_x` is flat over `B`, since the square
  `P^n_B ⟶ P^n_A ×_{Spec A} T` over `x` is cartesian (`isPullback_pointMap`);
* `IsHilbertFamily.primeFiber_comap_pointMap`: every fiber of `Z_x` over a prime of `B` is a fiber
  of `Z` over a field point of `T` (`map_comp_pointMap`), hence has Hilbert polynomial `Φ`.

Consequently (Nitsure, *Construction of Hilbert and Quot schemes*, arXiv:math/0504590v1, §5,
pp. 24–25), for `B` Noetherian and `r ≥ hilbertRegularityBound n Φ`:
`H^q(P^n_B, I_{Z_x}(r)) = 0` for `q ≥ 1`, `H^0(P^n_B, I_{Z_x}(r))` is projective and commutes with
every base change, and `I_{Z_x}` is regular, so `I_{Z_x}(r)` is globally generated. Over
`T = Spec B` (`x = 𝟙`) the map `pointMap ι g (𝟙 _)` is an isomorphism (`isIso_pointMap_id`), and
two points of
`Hilb^Φ(Spec B)` with the same sections of `I(r) ⊆ 𝒪(r)` are equal
(`IsHilbertFamily.eq_of_idealTwistSections_eq`).
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped Polynomial

universe u

namespace AlgebraicGeometry

namespace ProjectiveSpace

open Scheme.Cohomology

variable (ι : Type u) {A : Type u} [CommRing A]

variable {Φ : ℚ[X]} {T : Scheme.{u}} {g : T ⟶ Spec (CommRingCat.of A)}
  {Z : (pullback (toSpec A ι) g).IdealSheafData}

/-- **The pullback of a point of the Hilbert functor to an affine piece is flat**: for every
`x : Spec B ⟶ T`, the closed subscheme `Z.comap (pointMap ι g x)` of `P^n_B` is flat over `B`. -/
theorem IsHilbertFamily.flat_comap_pointMap (hZ : IsHilbertFamily ι Φ g Z) {B : Type u}
    [CommRing B] (x : Spec (CommRingCat.of B) ⟶ T) :
    Flat ((Z.comap (pointMap ι g x)).subschemeι ≫ toSpec B ι) := by
  have := hZ.flat
  let b := pointMap ι g x
  have hsq : IsPullback (pullback.snd b Z.subschemeι)
      (pullback.fst b Z.subschemeι ≫ toSpec B ι)
      (Z.subschemeι ≫ pullback.snd (toSpec A ι) g) x :=
    (IsPullback.of_hasPullback b Z.subschemeι).flip.paste_vert (isPullback_pointMap ι g x)
  have hfl : Flat (pullback.fst b Z.subschemeι ≫ toSpec B ι) :=
    MorphismProperty.of_isPullback hsq this
  rw [← Scheme.IdealSheafData.comapIso_hom_fst Z b, Category.assoc]
  infer_instance

/-- **The fibers of the pullback to an affine piece**: the fiber of `Z.comap (pointMap ι g x)`
over a prime `p` of `B` is the fiber of `Z` at the field point `Spec κ(p) ⟶ Spec B ⟶ T`. -/
theorem IsHilbertFamily.primeFiber_comap_pointMap (hZ : IsHilbertFamily ι Φ g Z) {B : Type u}
    [CommRing B] (x : Spec (CommRingCat.of B) ⟶ T) (p : PrimeSpectrum B) :
    subschemeHilbertPolynomial ι p.asIdeal.ResidueField
      (primeFiber ι (Z.comap (pointMap ι g x)) p) = Φ := by
  rw [primeFiber, ← Scheme.IdealSheafData.comap_comp, map_comp_pointMap]
  exact hZ.subschemeHilbertPolynomial_fiber _ _

variable (n : ℕ) (e : ι ≃ Fin (n + 1))

include e in
/-- **Direct images over an affine piece** (Nitsure, arXiv:math/0504590v1, §5, p. 25): for a
point `Z` of `Hilb^Φ(T)`, a morphism `x : Spec B ⟶ T` with `B` Noetherian and
`r ≥ hilbertRegularityBound n Φ`, the higher cohomology of `I_{Z_x}(r)` on `P^n_B` vanishes. -/
theorem IsHilbertFamily.subsingleton_moduleCohomology_idealTwist (hZ : IsHilbertFamily ι Φ g Z)
    {B : Type u} [CommRing B] [IsNoetherianRing B] (x : Spec (CommRingCat.of B) ⟶ T) (r : ℤ)
    (hr : hilbertRegularityBound n Φ ≤ r) (q : ℕ) (hq : q ≠ 0) :
    Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace B ι)
      (idealTwist ι (Z.comap (pointMap ι g x)) r)) q) :=
  haveI := hZ.flat_comap_pointMap ι x
  ProjectiveSpace.subsingleton_moduleCohomology_idealTwist ι n e _
    (hZ.primeFiber_comap_pointMap ι x) r hr q hq

include e in
/-- **`H^0` of the twisted ideal sheaf over an affine piece is projective** for
`r ≥ hilbertRegularityBound n Φ`. -/
theorem IsHilbertFamily.projective_moduleCohomology_idealTwist (hZ : IsHilbertFamily ι Φ g Z)
    {B : Type u} [CommRing B] [IsNoetherianRing B] (x : Spec (CommRingCat.of B) ⟶ T) (r : ℤ)
    (hr : hilbertRegularityBound n Φ ≤ r) :
    letI := moduleCohomologyModuleOfHom (ProjectiveSpace B ι)
      ((toSpec B ι).appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom)
      (idealTwist ι (Z.comap (pointMap ι g x)) r) 0
    Module.Projective B (Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace B ι)
      (idealTwist ι (Z.comap (pointMap ι g x)) r)) 0) :=
  haveI := hZ.flat_comap_pointMap ι x
  ProjectiveSpace.projective_moduleCohomology_idealTwist ι n e _
    (hZ.primeFiber_comap_pointMap ι x) r hr

include e in
/-- **Base change of the direct images over an affine piece**: for every ring map
`σ : B →+* C`, the base-change map of `H^q(P^n_B, I_{Z_x}(r))` is an isomorphism, for
`r ≥ hilbertRegularityBound n Φ`. -/
theorem IsHilbertFamily.isIso_moduleCohomologyBaseChangeMap_idealTwist
    (hZ : IsHilbertFamily ι Φ g Z) {B : Type u} [CommRing B] [IsNoetherianRing B]
    (x : Spec (CommRingCat.of B) ⟶ T) (r : ℤ) (hr : hilbertRegularityBound n Φ ≤ r) (q : ℕ)
    {C : Type u} [CommRing C] (σ : B →+* C) :
    IsIso (moduleCohomologyBaseChangeMap (toSpec B ι) σ
      (idealTwist ι (Z.comap (pointMap ι g x)) r) q) :=
  haveI := hZ.flat_comap_pointMap ι x
  ProjectiveSpace.isIso_moduleCohomologyBaseChangeMap_idealTwist ι n e _
    (hZ.primeFiber_comap_pointMap ι x) r hr q σ

include e in
/-- **The fiber dimension of the direct image over an affine piece**: the fiber of
`H^0(I_{Z_x}(r))` over a prime `p` of `B` has dimension `C(r + n, n) - Φ(r)`. -/
theorem IsHilbertFamily.moduleFiberCohomologyDimension_idealTwist
    (hZ : IsHilbertFamily ι Φ g Z) {B : Type u} [CommRing B] (x : Spec (CommRingCat.of B) ⟶ T)
    (r : ℕ) (hr : hilbertRegularityBound n Φ ≤ r) (p : PrimeSpectrum B) :
    (moduleFiberCohomologyDimension (toSpec B ι) (idealTwist ι (Z.comap (pointMap ι g x)) r) 0 p :
        ℚ) = ((r + n).choose n : ℚ) - Φ.eval (r : ℚ) :=
  haveI := hZ.flat_comap_pointMap ι x
  ProjectiveSpace.moduleFiberCohomologyDimension_idealTwist ι n e _
    (hZ.primeFiber_comap_pointMap ι x) r hr p

include e in
/-- **Global generation over an affine piece** (Lemma 2.1 (c) on `P^n_B`): `I_{Z_x}(r)` is
generated by its global sections for `r ≥ hilbertRegularityBound n Φ`. -/
theorem IsHilbertFamily.epi_globalSectionsEval_idealTwist (hZ : IsHilbertFamily ι Φ g Z)
    {B : Type u} [CommRing B] [IsNoetherianRing B] (x : Spec (CommRingCat.of B) ⟶ T) (r : ℤ)
    (hr : hilbertRegularityBound n Φ ≤ r) :
    Epi (Scheme.Modules.globalSectionsEval (idealTwist ι (Z.comap (pointMap ι g x)) r)) :=
  haveI := hZ.flat_comap_pointMap ι x
  ProjectiveSpace.epi_globalSectionsEval_idealTwist ι n e _ (hZ.primeFiber_comap_pointMap ι x) r
    hr

include e in
/-- **Injectivity over an affine test scheme** (Nitsure, arXiv:math/0504590v1, §5, p. 26): two
points `Z`, `Z'` of `Hilb^Φ(Spec B)`, `B` Noetherian, whose ideal sheaves on
`P^n_B ≅ P^n_A ×_{Spec A} Spec B` have the same global sections of `I(r) ⊆ 𝒪(r)` for some
`r ≥ hilbertRegularityBound n Φ`, are equal. -/
theorem IsHilbertFamily.eq_of_idealTwistSections_eq {B : Type u} [CommRing B]
    [IsNoetherianRing B] {g : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of A)}
    {Z Z' : (pullback (toSpec A ι) g).IdealSheafData} (hZ : IsHilbertFamily ι Φ g Z)
    (hZ' : IsHilbertFamily ι Φ g Z') (r : ℤ) (hr : hilbertRegularityBound n Φ ≤ r)
    (h : idealTwistSections ι (Z.comap (pointMap ι g (𝟙 _))) r =
      idealTwistSections ι (Z'.comap (pointMap ι g (𝟙 _))) r) : Z = Z' := by
  have := hZ.flat_comap_pointMap ι (𝟙 _)
  have := hZ'.flat_comap_pointMap ι (𝟙 _)
  have hc := ProjectiveSpace.eq_of_idealTwistSections_eq ι n e _ _
    (hZ.primeFiber_comap_pointMap ι (𝟙 _)) (hZ'.primeFiber_comap_pointMap ι (𝟙 _)) r hr h
  have hinv (W : (pullback (toSpec A ι) g).IdealSheafData) :
      (W.comap (pointMap ι g (𝟙 _))).comap (inv (pointMap ι g (𝟙 _))) = W := by
    rw [← Scheme.IdealSheafData.comap_comp, IsIso.inv_hom_id, Scheme.IdealSheafData.comap_id]
  rw [← hinv Z, ← hinv Z', hc]

end ProjectiveSpace

end AlgebraicGeometry
