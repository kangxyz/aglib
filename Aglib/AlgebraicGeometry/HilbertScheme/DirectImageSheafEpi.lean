/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.HilbertScheme.DirectImageSheafQuotient
public import Aglib.AlgebraicGeometry.HilbertScheme.Point
public import Aglib.AlgebraicGeometry.Modules.Locality.Epimorphisms
public import Aglib.AlgebraicGeometry.Cohomology.Projective.GlobalSections.DirectImage
public import Aglib.AlgebraicGeometry.ProjectiveSpace.BaseChange.MonomialMap
public import Aglib.AlgebraicGeometry.Cohomology.Modules.DegreeZero

/-!
# The evaluation map onto the direct image is an epimorphism

For a locally Noetherian scheme `T` over `Spec A`, a point `Z` of `Hilb^Φ(T)`, `ι ≃ Fin (n + 1)`
and a natural number `r ≥ hilbertRegularityBound n Φ`, the evaluation map
`directImageQuotientMap : 𝒪_T^{monomials} ⟶ π_* 𝒪_Z(r)` is an epimorphism
(`IsHilbertFamily.epi_directImageQuotientMap`): the surjection `π_{T*} E_T(r) → π_{T*} F(r)` of
Nitsure, *Construction of Hilbert and Quot schemes*, arXiv:math/0504590v1, §5, p. 26, which rests
on (**), p. 25.

The proof is local on `T`. Over an affine open `x : Spec B ⟶ T` (`B` Noetherian), the cartesian
square `isPullback_pointMap` has open immersions on both sides, so its base-change mate is
invertible and `pushforwardFreeMap_baseChange` identifies `x^*` of the evaluation map with the
evaluation map of the closed subscheme `Z_x ⊆ P^n_B`. That map factors as
`𝒪^{monomials} ⟶ (toSpec)_* 𝒪(r) ⟶ (toSpec)_* 𝒪_{Z_x}(r)`
(`pullbackFreeMap_monomialMap`, `ProjectiveSpace/BaseChange/MonomialMap`, identifies the
pulled-back monomials with those of `P^n_B`):

* the first map is an epimorphism because the monomials form a basis of
  `H^0(P^n_B, 𝒪(r)) = B[x]_r` (`epi_pushforwardFreeMap_monomialMap`,
  `Cohomology/Projective/GlobalSections/DirectImage`);
* the second map is surjective on global sections by the surjectivity of
  `H^0(𝒪(r)) ⟶ H^0(𝒪_{Z_x}(r))` (`exact_moduleCohomology_twistedShortComplex`, which uses
  `H^1(I_{Z_x}(r)) = 0`).

Both target sheaves are quasi-coherent, so surjectivity on global sections gives an epimorphism
on `Spec B` (`epi_of_epi_globalSections`).
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open scoped Polynomial

universe u

namespace AlgebraicGeometry

namespace ProjectiveSpace

open Scheme.Cohomology

section StandardFamily

variable (ι : Type u) (n : ℕ) (e : ι ≃ Fin (n + 1)) {B : Type u} [CommRing B] {Φ : ℚ[X]}

include e in
/-- **Restriction to `W` is surjective on direct images over `Spec B`**: for `W ⊆ P^n_B` flat over
the Noetherian ring `B` with all fiber Hilbert polynomials `Φ` and `r ≥ hilbertRegularityBound n Φ`,
`(toSpec)_* 𝒪(r) ⟶ (toSpec)_* 𝒪_W(r)` is an epimorphism (Nitsure, arXiv:math/0504590v1, §5,
p. 25, (**)). -/
theorem epi_pushforward_twistedRestriction [IsNoetherianRing B]
    (W : (ProjectiveSpace B ι).IdealSheafData) [Flat (W.subschemeι ≫ toSpec B ι)]
    (hfib : ∀ p : PrimeSpectrum B,
      subschemeHilbertPolynomial ι p.asIdeal.ResidueField (primeFiber ι W p) = Φ)
    (r : ℕ) (hr : hilbertRegularityBound n Φ ≤ r) :
    Epi ((Scheme.Modules.pushforward (toSpec B ι)).map
      (W.twistedRestriction (twistingSheaf B ι (r : ℤ)))) := by
  have : Finite ι := Finite.of_equiv _ e.symm
  have : (twistingSheaf B ι (r : ℤ)).IsQuasicoherent := inferInstance
  have hW := affineLocallyFiniteType_quotientTwist ι n e W r
  have : (quotientTwist ι W r).IsQuasicoherent :=
    quasicoherent_of_affineCharts _ (fun R j _ => (hW R j).1)
  have := isQuasicoherent_pushforward_toSpec ι (twistingSheaf B ι (r : ℤ))
  have : ((Scheme.Modules.pushforward (toSpec B ι)).obj
      (twistingSheaf B ι (r : ℤ) ⊗ W.quotientModule)).IsQuasicoherent :=
    isQuasicoherent_pushforward_toSpec ι (quotientTwist ι W r)
  suffices hΓ : Function.Surjective (moduleSpecΓFunctor.map
      ((Scheme.Modules.pushforward (toSpec B ι)).map
        (W.twistedRestriction (twistingSheaf B ι (r : ℤ))))).hom by
    have : Epi (moduleSpecΓFunctor.map ((Scheme.Modules.pushforward (toSpec B ι)).map
        (W.twistedRestriction (twistingSheaf B ι (r : ℤ))))) :=
      (ModuleCat.epi_iff_surjective _).mpr hΓ
    exact epi_of_epi_globalSections (CommRingCat.of B) _
  intro y
  let := h0Module ι (unitTwist (B := B) ι r)
  let := h0Module ι (quotientTwist ι W r)
  obtain ⟨v, hv⟩ := (exact_moduleCohomology_twistedShortComplex ι n e W hfib r hr).2.2
    ((Sheaf.H.equiv₀ (moduleAddSheaf _ (quotientTwist ι W r)) Limits.isTerminalTop).symm y)
  let s := Sheaf.H.equiv₀ (moduleAddSheaf _ (unitTwist (B := B) ι r)) Limits.isTerminalTop v
  refine ⟨(ρ_ (twistingSheaf B ι (r : ℤ))).hom.val.app (op ⊤) s, ?_⟩
  have hg := equiv₀_moduleCohomologyMapOfHom
    ((toSpec B ι).appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom)
    (twistedShortComplex ι W r).g v
  have hy : Sheaf.H.equiv₀ (moduleAddSheaf _ (twistedShortComplex ι W r).X₃)
      Limits.isTerminalTop ((Sheaf.H.equiv₀ (moduleAddSheaf _ (quotientTwist ι W r))
        Limits.isTerminalTop).symm y) = y :=
    Equiv.apply_symm_apply _ y
  rw [hv, hy] at hg
  have hρ := congrArg (fun k => k.val.app (op ⊤) s) (ρ_ (twistingSheaf B ι (r : ℤ))).hom_inv_id
  dsimp only at hρ
  change ((ρ_ (twistingSheaf B ι (r : ℤ))).inv ≫
      (twistingSheaf B ι (r : ℤ) ◁ W.toQuotientModule)).val.app (op ⊤)
    ((ρ_ (twistingSheaf B ι (r : ℤ))).hom.val.app (op ⊤) s) = y
  change (twistingSheaf B ι (r : ℤ) ◁ W.toQuotientModule).val.app (op ⊤)
    ((((ρ_ (twistingSheaf B ι (r : ℤ))).hom ≫ (ρ_ (twistingSheaf B ι (r : ℤ))).inv).val.app
      (op ⊤)) s) = y
  rw [hρ]
  exact hg.symm

end StandardFamily

section Family

variable (ι : Type u) {A : Type u} [CommRing A] (n : ℕ) (e : ι ≃ Fin (n + 1)) {Φ : ℚ[X]}
  {T : Scheme.{u}} {g : T ⟶ Spec (CommRingCat.of A)}
  {Z : (pullback (toSpec A ι) g).IdealSheafData}

include e in
/-- **The evaluation map over an affine open is an epimorphism**: for an open immersion
`x : Spec B ⟶ T` with `B` Noetherian, the pullback of `directImageQuotientMap` along `x` is an
epimorphism. -/
theorem IsHilbertFamily.epi_pullbackFreeMap_directImageQuotientMap
    (hZ : IsHilbertFamily ι Φ g Z) {B : Type u} [CommRing B] [IsNoetherianRing B]
    (x : Spec (CommRingCat.of B) ⟶ T) [IsOpenImmersion x] (r : ℕ)
    (hr : hilbertRegularityBound n Φ ≤ r) :
    Epi (pullbackFreeMap x (directImageQuotientMap ι g Z r)) := by
  have hsq := isPullback_pointMap ι g x
  have hiso : IsIso ((cartesianBaseChangeMap (pointMap ι g x) (toSpec B ι)
      (pullback.snd (toSpec A ι) g) x hsq).app (familyQuotientTwist ι g Z r)) :=
    isIso_cartesianBaseChangeMap_of_isOpenImmersion _ _ _ _ _ _
  have hnat : pullbackFreeMap x (directImageQuotientMap ι g Z r) ≫
      (cartesianBaseChangeMap (pointMap ι g x) (toSpec B ι)
        (pullback.snd (toSpec A ι) g) x hsq).app (familyQuotientTwist ι g Z r) ≫
      (Scheme.Modules.pushforward (toSpec B ι)).map (familyQuotientTwistPointIso ι g Z x r).hom =
      pushforwardFreeMap (toSpec B ι)
        (pullbackFreeMap (map (pointRingHom g x) ι) (monomialMap ι A r) ≫
          (twistingPullbackIso (pointRingHom g x) ι r).hom ≫
            (Z.comap (pointMap ι g x)).twistedRestriction (twistingSheaf B ι (r : ℤ))) :=
    pushforwardFreeMap_baseChange (pointMap ι g x) (toSpec B ι)
      (pullback.snd (toSpec A ι) g) x hsq (familyQuotientMonomialMap ι g Z r) _
      (familyQuotientTwistPointIso ι g Z x r)
      (pullbackFreeMap_familyQuotientMonomialMap_pointMap ι g x Z r)
  rw [reassoc_of% (pullbackFreeMap_monomialMap ι (pointRingHom g x) r)] at hnat
  have : Flat ((Z.comap (pointMap ι g x)).subschemeι ≫ toSpec B ι) := hZ.flat_comap_pointMap ι x
  have h1 := epi_pushforwardFreeMap_monomialMap ι n e (B := B) r
  have h2 := epi_pushforward_twistedRestriction ι n e (Z.comap (pointMap ι g x))
    (hZ.primeFiber_comap_pointMap ι x) r hr
  have hcomp : pushforwardFreeMap (toSpec B ι) (monomialMap ι B r ≫
      (Z.comap (pointMap ι g x)).twistedRestriction (twistingSheaf B ι (r : ℤ))) =
      pushforwardFreeMap (toSpec B ι) (monomialMap ι B r) ≫
        (Scheme.Modules.pushforward (toSpec B ι)).map
          ((Z.comap (pointMap ι g x)).twistedRestriction (twistingSheaf B ι (r : ℤ))) := by
    rw [pushforwardFreeMap_def, pushforwardFreeMap_def, ← Category.assoc,
      Adjunction.homEquiv_naturality_right]
  rw [hcomp] at hnat
  have hepi : Epi (pullbackFreeMap x (directImageQuotientMap ι g Z r) ≫
      ((cartesianBaseChangeMap (pointMap ι g x) (toSpec B ι)
        (pullback.snd (toSpec A ι) g) x hsq).app (familyQuotientTwist ι g Z r) ≫
      (Scheme.Modules.pushforward (toSpec B ι)).map
        (familyQuotientTwistPointIso ι g Z x r).hom)) := by
    rw [hnat]
    exact epi_comp _ _
  exact (epi_comp_iff_of_isIso _ _).mp hepi

variable [IsLocallyNoetherian T]

include e in
/-- **The evaluation map is an epimorphism** (Nitsure, arXiv:math/0504590v1, §5, p. 26): for a
locally Noetherian `T`, a point `Z` of `Hilb^Φ(T)` and a natural number
`r ≥ hilbertRegularityBound n Φ`, `𝒪_T^{monomials} ⟶ π_* 𝒪_Z(r)` is an epimorphism. -/
theorem IsHilbertFamily.epi_directImageQuotientMap (hZ : IsHilbertFamily ι Φ g Z) (r : ℕ)
    (hr : hilbertRegularityBound n Φ ≤ r) : Epi (directImageQuotientMap ι g Z r) := by
  let U := T.affineOpenCover
  refine Scheme.Modules.epi_of_pullback_openCover (fun i => Spec (U.X i)) U.f
    (fun x => by obtain ⟨y, hy⟩ := U.covers x; exact ⟨U.idx x, y, hy⟩) _ fun i => ?_
  have : IsLocallyNoetherian (Spec (U.X i)) := isLocallyNoetherian_of_isOpenImmersion (U.f i)
  have : IsNoetherianRing (U.X i) := isLocallyNoetherian_Spec.mp inferInstance
  have h := hZ.epi_pullbackFreeMap_directImageQuotientMap ι n e (B := U.X i) (U.f i) r hr
  rw [pullbackFreeMap_def] at h
  exact epi_of_epi ((pullbackFreeIso (U.f i) (Monomials ι r)).inv) _

end Family

end ProjectiveSpace

end AlgebraicGeometry
