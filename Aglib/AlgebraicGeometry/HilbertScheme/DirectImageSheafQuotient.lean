/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.HilbertScheme.DirectImageSheaf
public import Aglib.AlgebraicGeometry.ProjectiveSpace.HomogeneousEvaluation
public import Aglib.AlgebraicGeometry.Modules.BaseChange.FreeMap
public import Aglib.AlgebraicGeometry.Modules.BaseChange.CartesianInvertibility
public import Aglib.AlgebraicGeometry.ProjectiveSpace.BaseChange.HomogeneousSections
public import Aglib.RingTheory.MvPolynomial.CoordinatePieces

/-!
# The evaluation map onto the direct image of a Hilbert family

Let `T` be a scheme over `Spec A`, `π : P^n_A ×_{Spec A} T ⟶ T` and `Z ⊆ P^n_A ×_{Spec A} T` a
closed subscheme. The monomials `x^a` of degree `r` (`Monomials ι r`) are global sections of
`𝒪(r)` on `P^n_A` (`monomialSection`); together they form
`monomialMap : 𝒪^{monomials} ⟶ 𝒪(r)` (`ProjectiveSpace/HomogeneousEvaluation`). Pulled back
along the first projection and restricted to `Z`, they give
`familyQuotientMonomialMap : 𝒪^{monomials} ⟶ 𝒪_Z(r)` on `P^n_A ×_{Spec A} T`, and its adjoint is
the **evaluation map** `directImageQuotientMap : 𝒪_T^{monomials} ⟶ π_* 𝒪_Z(r)` of Nitsure,
*Construction of Hilbert and Quot schemes*, arXiv:math/0504590v1, §5, p. 26: the quotient
`π_{T*} E_T(r) → π_{T*} F(r)`, with `π_* 𝒪(r) = Sym^r` written in the monomial basis.

**Naturality.** For `f : T' ⟶ T` over `Spec A` with base-changed map
`b = baseChangeMap ι g g' f h`, the evaluation map of `Z.comap b` is the pullback along `f` of the
evaluation map of `Z`, followed by the base-change mate of the cartesian square
`isPullback_baseChangeMap` and the identification `b^* 𝒪_Z(r) ≅ 𝒪_{Z.comap b}(r)`
(`directImageQuotientMap_baseChange`). For a locally Noetherian `T`, a point `Z` of `Hilb^Φ(T)`
and `r ≥ hilbertRegularityBound n Φ` the mate is invertible
(`IsHilbertFamily.isIso_cartesianBaseChangeMap_baseChangeMap`, Nitsure, p. 25, via Theorem 3.7);
for an open immersion `f` it is invertible for every `Z`
(`isIso_cartesianBaseChangeMap_baseChangeMap_of_isOpenImmersion`).

Over a point `x : Spec K ⟶ T`, the pullback of `familyQuotientMonomialMap` along
`pointMap ι g x` is the monomial map of `P^n_K` restricted to `Z_x`
(`pullbackFreeMap_familyQuotientMonomialMap_pointMap`).
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry.Scheme.Modules
open scoped Polynomial

universe u

namespace AlgebraicGeometry

namespace ProjectiveSpace

section Family

variable (ι : Type u) {A : Type u} [CommRing A] {T : Scheme.{u}}
  (g : T ⟶ Spec (CommRingCat.of A))

/-- The monomial sections of `𝒪(r)` on `P^n_A ×_{Spec A} T`: the pullback of `monomialMap` along
the first projection. -/
def familyMonomialMap (r : ℕ) :
    SheafOfModules.free (Monomials ι r) ⟶ familyTwistingSheaf ι g r :=
  pullbackFreeMap (pullback.fst (toSpec A ι) g) (monomialMap ι A r)

/-- The monomial sections of `𝒪_Z(r)` on `P^n_A ×_{Spec A} T`: `familyMonomialMap` followed by
the restriction `𝒪(r) ⟶ 𝒪(r) ⊗ 𝒪_Z`. -/
def familyQuotientMonomialMap (Z : (pullback (toSpec A ι) g).IdealSheafData) (r : ℕ) :
    SheafOfModules.free (Monomials ι r) ⟶ familyQuotientTwist ι g Z r :=
  familyMonomialMap ι g r ≫ Z.twistedRestriction (familyTwistingSheaf ι g r)

/-- The value of `familyQuotientMonomialMap`, as a named equation at variable arguments. -/
theorem familyQuotientMonomialMap_eq (Z : (pullback (toSpec A ι) g).IdealSheafData) (r : ℕ) :
    familyQuotientMonomialMap ι g Z r =
      pullbackFreeMap (pullback.fst (toSpec A ι) g) (monomialMap ι A r) ≫
        Z.twistedRestriction
          ((Scheme.Modules.pullback (pullback.fst (toSpec A ι) g)).obj
            (twistingSheaf A ι (r : ℤ))) :=
  rfl

/-- **The evaluation map** `𝒪_T^{monomials} ⟶ π_* 𝒪_Z(r)` (Nitsure, arXiv:math/0504590v1, §5,
p. 26): the adjoint of `familyQuotientMonomialMap`; it sends the basis element of `x^a` to the
section `x^a` of `𝒪_Z(r)`. -/
def directImageQuotientMap (Z : (pullback (toSpec A ι) g).IdealSheafData) (r : ℕ) :
    SheafOfModules.free (R := T.ringCatSheaf) (Monomials ι r) ⟶ directImageSheaf ι g Z r :=
  pushforwardFreeMap (pullback.snd (toSpec A ι) g) (familyQuotientMonomialMap ι g Z r)

/-- **The monomial sections of `𝒪_Z(r)` under pullback**: for `p : Y ⟶ P^n_A ×_{Spec A} T` and an
identification `d` of the pullback of `𝒪(r)` along `p ≫ fst`, the pullback of
`familyQuotientMonomialMap` is the pulled-back monomial map restricted to `Z.comap p`. -/
theorem pullbackFreeMap_familyQuotientMonomialMap {Y : Scheme.{u}}
    (p : Y ⟶ pullback (toSpec A ι) g) (Z : (pullback (toSpec A ι) g).IdealSheafData) (r : ℕ)
    {L' : Y.Modules}
    (d : (Scheme.Modules.pullback (p ≫ pullback.fst (toSpec A ι) g)).obj
      (twistingSheaf A ι (r : ℤ)) ≅ L') :
    pullbackFreeMap p (familyQuotientMonomialMap ι g Z r) ≫
        (Z.pullbackTensorQuotientIso p
          ((Scheme.Modules.pullbackComp p (pullback.fst (toSpec A ι) g)).app _ ≪≫ d)).hom =
      pullbackFreeMap (p ≫ pullback.fst (toSpec A ι) g) (monomialMap ι A r) ≫ d.hom ≫
        (Z.comap p).twistedRestriction L' := by
  rw [familyQuotientMonomialMap, pullbackFreeMap_comp_right, Category.assoc,
    Z.pullback_map_twistedRestriction, Iso.trans_hom, Iso.app_hom, Category.assoc,
    familyMonomialMap, pullbackFreeMap_comp_assoc]

/-- `pullbackFreeMap_familyQuotientMonomialMap` when `p ≫ fst = q`: the pulled-back monomial map is
`pullbackFreeMap q monomialMap`. Stated at variable `p` and `q`, so that the instances at concrete
fibre products are plain applications. -/
theorem pullbackFreeMap_familyQuotientMonomialMap_of_comp_fst {Y : Scheme.{u}}
    (p : Y ⟶ pullback (toSpec A ι) g) (q : Y ⟶ ProjectiveSpace A ι)
    (hq : p ≫ pullback.fst (toSpec A ι) g = q) (Z : (pullback (toSpec A ι) g).IdealSheafData)
    (r : ℕ) :
    pullbackFreeMap p (familyQuotientMonomialMap ι g Z r) ≫
        (Z.pullbackTensorQuotientIso p
          ((Scheme.Modules.pullbackComp p (pullback.fst (toSpec A ι) g)).app _ ≪≫
            (Scheme.Modules.pullbackCongr hq).app (twistingSheaf A ι (r : ℤ)))).hom =
      pullbackFreeMap q (monomialMap ι A r) ≫
        (Z.comap p).twistedRestriction
          ((Scheme.Modules.pullback q).obj (twistingSheaf A ι (r : ℤ))) := by
  rw [pullbackFreeMap_familyQuotientMonomialMap, Iso.app_hom, ← Category.assoc,
    pullbackFreeMap_congr]

/-- `pullbackFreeMap_familyQuotientMonomialMap` when `p ≫ fst = q`, followed by an
identification `d` of `q^* 𝒪(r)`. Stated at variable `p`, `q` and `d`. -/
theorem pullbackFreeMap_familyQuotientMonomialMap_of_comp_fst_comp {Y : Scheme.{u}}
    (p : Y ⟶ pullback (toSpec A ι) g) (q : Y ⟶ ProjectiveSpace A ι)
    (hq : p ≫ pullback.fst (toSpec A ι) g = q) (Z : (pullback (toSpec A ι) g).IdealSheafData)
    (r : ℕ) {L' : Y.Modules}
    (d : (Scheme.Modules.pullback q).obj (twistingSheaf A ι (r : ℤ)) ≅ L') :
    pullbackFreeMap p (familyQuotientMonomialMap ι g Z r) ≫
        (Z.pullbackTensorQuotientIso p
          ((Scheme.Modules.pullbackComp p (pullback.fst (toSpec A ι) g)).app _ ≪≫
            (Scheme.Modules.pullbackCongr hq).app (twistingSheaf A ι (r : ℤ)) ≪≫ d)).hom =
      pullbackFreeMap q (monomialMap ι A r) ≫ d.hom ≫ (Z.comap p).twistedRestriction L' := by
  rw [pullbackFreeMap_familyQuotientMonomialMap, Iso.trans_hom, Iso.app_hom, Category.assoc,
    ← Category.assoc (pullbackFreeMap _ _), pullbackFreeMap_congr]

variable {T' : Scheme.{u}} (g' : T' ⟶ Spec (CommRingCat.of A)) (f : T' ⟶ T) (h : f ≫ g = g')

/-- `𝒪_Z(r)` under the base-changed map: `b^* 𝒪_Z(r) ≅ 𝒪_{Z.comap b}(r)`. -/
def familyQuotientTwistBaseChangeIso (Z : (pullback (toSpec A ι) g).IdealSheafData) (r : ℤ) :
    (Scheme.Modules.pullback (baseChangeMap ι g g' f h)).obj (familyQuotientTwist ι g Z r) ≅
      familyQuotientTwist ι g' (Z.comap (baseChangeMap ι g g' f h)) r :=
  Z.pullbackTensorQuotientIso (baseChangeMap ι g g' f h)
    (baseChangeMapTwistingPullbackIso ι f h r)

/-- The value of `familyQuotientTwistBaseChangeIso`, as a named equation at variable
arguments. -/
theorem familyQuotientTwistBaseChangeIso_eq (Z : (pullback (toSpec A ι) g).IdealSheafData)
    (r : ℤ) :
    familyQuotientTwistBaseChangeIso ι g g' f h Z r =
      Z.pullbackTensorQuotientIso (baseChangeMap ι g g' f h)
        ((Scheme.Modules.pullbackComp (baseChangeMap ι g g' f h)
          (pullback.fst (toSpec A ι) g)).app _ ≪≫
          (Scheme.Modules.pullbackCongr (baseChangeMap_fst ι g g' f h)).app
            (twistingSheaf A ι r)) :=
  rfl

/-- **The monomial sections of `𝒪_Z(r)` are natural**: along the base-changed map
`b = baseChangeMap ι g g' f h`, `familyQuotientMonomialMap` pulls back to that of `Z.comap b`. -/
theorem pullbackFreeMap_familyQuotientMonomialMap_baseChangeMap
    (Z : (pullback (toSpec A ι) g).IdealSheafData) (r : ℕ) :
    pullbackFreeMap (baseChangeMap ι g g' f h) (familyQuotientMonomialMap ι g Z r) ≫
        (familyQuotientTwistBaseChangeIso ι g g' f h Z r).hom =
      familyQuotientMonomialMap ι g' (Z.comap (baseChangeMap ι g g' f h)) r :=
  ((congrArg (fun i => pullbackFreeMap (baseChangeMap ι g g' f h)
      (familyQuotientMonomialMap ι g Z r) ≫ i.hom)
    (familyQuotientTwistBaseChangeIso_eq ι g g' f h Z r)).trans
      (pullbackFreeMap_familyQuotientMonomialMap_of_comp_fst ι g (baseChangeMap ι g g' f h)
        (pullback.fst (toSpec A ι) g') (baseChangeMap_fst ι g g' f h) Z r)).trans
    (familyQuotientMonomialMap_eq ι g' (Z.comap (baseChangeMap ι g g' f h)) r).symm

/-- **The evaluation map is natural** (Nitsure, arXiv:math/0504590v1, §5, p. 26): for `f : T' ⟶ T`
over `Spec A` and `b = baseChangeMap ι g g' f h`, the pullback along `f` of the evaluation map of
`Z`, followed by the base-change mate of `isPullback_baseChangeMap` and
`π'_* (b^* 𝒪_Z(r) ≅ 𝒪_{Z.comap b}(r))`, is the evaluation map of `Z.comap b`. -/
theorem directImageQuotientMap_baseChange (Z : (pullback (toSpec A ι) g).IdealSheafData)
    (r : ℕ) :
    pullbackFreeMap f (directImageQuotientMap ι g Z r) ≫
        (cartesianBaseChangeMap (baseChangeMap ι g g' f h) (pullback.snd (toSpec A ι) g')
          (pullback.snd (toSpec A ι) g) f (isPullback_baseChangeMap ι g g' f h)).app
            (familyQuotientTwist ι g Z r) ≫
          (Scheme.Modules.pushforward (pullback.snd (toSpec A ι) g')).map
            (familyQuotientTwistBaseChangeIso ι g g' f h Z r).hom =
      directImageQuotientMap ι g' (Z.comap (baseChangeMap ι g g' f h)) r :=
  pushforwardFreeMap_baseChange _ _ _ _ _ _ _ _
    (pullbackFreeMap_familyQuotientMonomialMap_baseChangeMap ι g g' f h Z r)

/-- For an open immersion `f`, the base-change mate of `isPullback_baseChangeMap` is invertible. -/
theorem isIso_cartesianBaseChangeMap_baseChangeMap_of_isOpenImmersion [IsOpenImmersion f]
    (M : (pullback (toSpec A ι) g).Modules) :
    IsIso ((cartesianBaseChangeMap (baseChangeMap ι g g' f h) (pullback.snd (toSpec A ι) g')
      (pullback.snd (toSpec A ι) g) f (isPullback_baseChangeMap ι g g' f h)).app M) :=
  have : IsOpenImmersion (baseChangeMap ι g g' f h) :=
    MorphismProperty.of_isPullback (isPullback_baseChangeMap ι g g' f h).flip inferInstance
  isIso_cartesianBaseChangeMap_of_isOpenImmersion _ _ _ _ _ M

variable {K : Type u} [CommRing K] (x : Spec (CommRingCat.of K) ⟶ T)

/-- The value of `familyQuotientTwistPointIso`, as a named equation at variable arguments. -/
theorem familyQuotientTwistPointIso_eq (Z : (pullback (toSpec A ι) g).IdealSheafData) (r : ℤ) :
    familyQuotientTwistPointIso ι g Z x r =
      Z.pullbackTensorQuotientIso (pointMap ι g x)
        ((Scheme.Modules.pullbackComp (pointMap ι g x) (pullback.fst (toSpec A ι) g)).app _ ≪≫
          (Scheme.Modules.pullbackCongr (pointMap_fst ι g x)).app (twistingSheaf A ι r) ≪≫
            twistingPullbackIso (pointRingHom g x) ι r) :=
  rfl

/-- **The monomial sections of `𝒪_Z(r)` over a point**: along `pointMap ι g x`,
`familyQuotientMonomialMap` pulls back, under `familyQuotientTwistPointIso`, to the monomial map
of `P^n_K` (through `twistingPullbackIso`) restricted to `Z_x`. -/
theorem pullbackFreeMap_familyQuotientMonomialMap_pointMap
    (Z : (pullback (toSpec A ι) g).IdealSheafData) (r : ℕ) :
    pullbackFreeMap (pointMap ι g x) (familyQuotientMonomialMap ι g Z r) ≫
        (familyQuotientTwistPointIso ι g Z x r).hom =
      pullbackFreeMap (map (pointRingHom g x) ι) (monomialMap ι A r) ≫
        (twistingPullbackIso (pointRingHom g x) ι r).hom ≫
          (Z.comap (pointMap ι g x)).twistedRestriction (twistingSheaf K ι r) :=
  (congrArg (fun i => pullbackFreeMap (pointMap ι g x) (familyQuotientMonomialMap ι g Z r) ≫ i.hom)
    (familyQuotientTwistPointIso_eq ι g x Z r)).trans
    (pullbackFreeMap_familyQuotientMonomialMap_of_comp_fst_comp ι g (pointMap ι g x)
      (map (pointRingHom g x) ι) (pointMap_fst ι g x) Z r
      (twistingPullbackIso (pointRingHom g x) ι r))

end Family

section LocallyNoetherian

variable (ι : Type u) {A : Type u} [CommRing A] (n : ℕ) (e : ι ≃ Fin (n + 1)) {Φ : ℚ[X]}
  {T : Scheme.{u}} [IsLocallyNoetherian T] {g : T ⟶ Spec (CommRingCat.of A)}
  {Z : (pullback (toSpec A ι) g).IdealSheafData}

include e in
/-- **Base change of `π_* 𝒪_Z(r)` along every morphism over `Spec A`**: for a locally Noetherian
`T`, a point `Z` of `Hilb^Φ(T)` and `r ≥ hilbertRegularityBound n Φ`, the base-change mate of the
cartesian square `isPullback_baseChangeMap` is invertible (Nitsure, arXiv:math/0504590v1, §5,
p. 25, via Theorem 3.7). -/
theorem IsHilbertFamily.isIso_cartesianBaseChangeMap_baseChangeMap (hZ : IsHilbertFamily ι Φ g Z)
    (r : ℕ) (hr : hilbertRegularityBound n Φ ≤ r) {T' : Scheme.{u}}
    (g' : T' ⟶ Spec (CommRingCat.of A)) (f : T' ⟶ T) (h : f ≫ g = g') :
    IsIso ((cartesianBaseChangeMap (baseChangeMap ι g g' f h) (pullback.snd (toSpec A ι) g')
      (pullback.snd (toSpec A ι) g) f (isPullback_baseChangeMap ι g g' f h)).app
        (familyQuotientTwist ι g Z r)) :=
  isIso_cartesianBaseChangeMap_of_isIso_moduleBaseChangeMap _ _ _ _ _ _
    (hZ.isIso_moduleBaseChangeMap_directImageSheaf ι n e r hr f)

end LocallyNoetherian

end ProjectiveSpace

end AlgebraicGeometry
