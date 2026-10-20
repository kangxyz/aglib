/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Coherent.Support.CodimensionOneStalk
public import Aglib.AlgebraicGeometry.Spec.DiscreteValuationRing
public import Aglib.AlgebraicGeometry.Modules.Coherent.Support.SmallModel
public import Aglib.AlgebraicGeometry.Modules.Coherent.FlatPullback

/-!
Native migration from `R5Lab.Aglib.AlgebraicGeometry.Modules.Support.PrincipalStalk` at R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`f85b83b67b9ec8bbfd3dc9cb03f43d94ca3d2b688826f60531a70a3496754cc0`.
Original objects, maps, universes and explicit hypotheses are retained.
Native providers replace duplicate implementations.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry.Scheme.Modules.Coherent (coherentExactPullback coherentPullback
    coherentPullbackCompIso)
attribute [local instance] Abelian.hasFiniteBiproducts
namespace AlgebraicGeometry.Scheme.Modules.Coherent.Support
universe u
open AlgebraicGeometry.Scheme.Modules.Coherent.Support
variable (X : Scheme.{u}) [IsNoetherian X] [IsIntegral X]

open _root_.AlgebraicGeometry.Scheme.Modules.Coherent (coherentGlobalSmallSupport
    coherentRestrictionIsoPullback)
open _root_.AlgebraicGeometry.Scheme.Modules.QuasiCoherent (finiteTypeSheavesRestriction
    principalOpen)

section PrincipalDictionary
variable [∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)]

def uniformizer (x : CodimensionOnePoint X) : x.localRing :=
  (IsDiscreteValuationRing.exists_irreducible x.localRing).choose

theorem uniformizer_irreducible (x : CodimensionOnePoint X) :
    Irreducible (uniformizer X x) :=
  (IsDiscreteValuationRing.exists_irreducible x.localRing).choose_spec

/-- Principal-open restriction followed by the literal fraction-field
isomorphism is the unchanged local fraction pullback. -/
def principalFractionComparison (x : CodimensionOnePoint X) :
    finiteTypeSheavesRestriction (principalOpen x.localRing (uniformizer X x)) ⋙
      coherentPullback (Scheme.Spec.DiscreteValuationRing.genericIso x.localRing X.functionField
        (uniformizer_irreducible X x)).hom ≅ (localFraction X x).toFunctor :=
  Functor.isoWhiskerRight
    (coherentRestrictionIsoPullback (principalOpen x.localRing (uniformizer X x))) _ ≪≫
  (coherentPullbackCompIso
    (Scheme.Spec.DiscreteValuationRing.genericIso x.localRing X.functionField
        (uniformizer_irreducible X x)).hom
    (principalOpen x.localRing (uniformizer X x))).symm ≪≫
  eqToIso (by rw [Scheme.Spec.DiscreteValuationRing.genericIso_open_triangle]; rfl)

/-- The local fraction-support category is the pin's actual principal-open
support category; this is equality of kernels, not a new K-group premise. -/
theorem principalSupport_eq_localSupport (x : CodimensionOnePoint X) :
    coherentGlobalSmallSupport
      (principalOpen x.localRing (uniformizer X x)) = localSupport X x := by
  funext M
  apply propext
  change (_root_.CategoryTheory.SmallModel.functor.{u + 1}
    (finiteTypeSheavesRestriction (principalOpen x.localRing (uniformizer X x)))).kernel M ↔
    (_root_.CategoryTheory.SmallModel.functor.{u + 1} (localFraction X x).toFunctor).kernel M
  rw [_root_.CategoryTheory.SmallModel.kernel_iff,
    _root_.CategoryTheory.SmallModel.kernel_iff]
  let e := Scheme.Spec.DiscreteValuationRing.genericIso x.localRing X.functionField
      (uniformizer_irreducible X x)
  have : (finiteTypeSheavesRestriction e.hom).IsEquivalence :=
    (AlgebraicGeometry.Scheme.Modules.Coherent.Localization.Stalk.coherentIsoEquivalence
        e).isEquivalence_inverse
  have : (coherentPullback e.hom).IsEquivalence :=
    Functor.isEquivalence_of_iso (coherentRestrictionIsoPullback e.hom)
  constructor
  · intro h
    exact ((coherentPullback e.hom).map_isZero h).of_iso
      ((principalFractionComparison X x).app _).symm
  · intro h
    exact IsZero.of_full_of_faithful_of_isZero (coherentPullback e.hom) _
      (h.of_iso ((principalFractionComparison X x).app _))

/-- Identity-on-the-underlying-local-sheaf transport to the actual principal
support. This supplies an exact functor for the public closed devissage map. -/
def localToPrincipalEquivalence (x : CodimensionOnePoint X) :
    (localSupport X x).FullSubcategory ≌
      (coherentGlobalSmallSupport (principalOpen x.localRing (uniformizer X x))).FullSubcategory :=
  (CategoryTheory.Equivalence.refl : Coh (Spec x.localRing) ≌
    Coh (Spec x.localRing)).congrFullSubcategory
    (principalSupport_eq_localSupport X x)

instance localToPrincipalEquivalence_additive (x : CodimensionOnePoint X) :
    (localToPrincipalEquivalence X x).functor.Additive := by
  let := preservesBinaryBiproducts_of_preservesBinaryProducts
    (localToPrincipalEquivalence X x).functor
  exact Functor.additive_of_preservesBinaryBiproducts _

def localToPrincipalExact (x : CodimensionOnePoint X) :
    _root_.CategoryTheory.ExactCategory.ExactFunctor
    (_root_.CategoryTheory.ObjectProperty.subcategoryExactStructure (localSupport X x))
    (_root_.CategoryTheory.ObjectProperty.subcategoryExactStructure
      (coherentGlobalSmallSupport (principalOpen x.localRing (uniformizer X x)))) where
  toFunctor := (localToPrincipalEquivalence X x).functor
  map_conflation _ h := h.map_of_exact _

instance localToPrincipalExact_isEquivalence (x : CodimensionOnePoint X) :
    (localToPrincipalExact X x).toFunctor.IsEquivalence :=
  (localToPrincipalEquivalence X x).isEquivalence_functor

end PrincipalDictionary
end AlgebraicGeometry.Scheme.Modules.Coherent.Support
