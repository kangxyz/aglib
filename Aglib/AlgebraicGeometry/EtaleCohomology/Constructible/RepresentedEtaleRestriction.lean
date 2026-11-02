/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.RepresentedEtaleTorsion
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Basic.AffineLocality
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.EtaleRestriction

/-! # Restriction of the original etale representation and affine-local constructibility

The actual postcomposition/base-change adjunction restricts the original lifted
Yoneda representation. The abelian inverse-image comparison is then forgotten
only after it has been constructed. No commutation of an unspecified inverse
image with underlying sets, and no base change of a non-etale representer, is used.
Affine-open restrictions remove the separated-base condition from bounded-torsion
constructibility. Quasi-compactness of the etale structural map is explicit.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.RepresentedEtaleRestriction

universe u
attribute [local instance] hasSheafifyLarge

variable {S V : Scheme.{u}} (j : V ⟶ S) [Etale j]

/-- The original adjunction on etale test schemes identifies the lifted Yoneda
presheaf of the actual base change with literal restriction. -/
def etaleYonedaRestrictionIso (E : S.Etale) :
    uliftYoneda.{u + 1}.obj ((siteBaseChange j).obj E) ≅
      (siteEtalePostcompose j).op ⋙ uliftYoneda.{u + 1}.obj E :=
  Functor.isoWhiskerRight ((siteEtalePostcomposeAdj j).compYonedaIso.app E)
      uliftFunctor.{u + 1} ≪≫
    Functor.associator (siteEtalePostcompose j).op (yoneda.obj E) uliftFunctor.{u + 1}

/-- The actual abelian inverse image has the same underlying representation on
the actual etale pullback object. The forgetful functor is applied to the already
constructed abelian restriction isomorphism. -/
def etaleRepresentedInverseImageIso (E : S.Etale)
    (F : AbelianSheaf.{u, u + 1} S)
    (e : uliftYoneda.{u + 1}.obj E ≅
      F.obj ⋙ CategoryTheory.forget AddCommGrpCat.{u + 1}) :
    uliftYoneda.{u + 1}.obj ((siteBaseChange j).obj E) ≅
      ((inverseImage j).obj F).obj ⋙ CategoryTheory.forget AddCommGrpCat.{u + 1} :=
  etaleYonedaRestrictionIso j E ≪≫
    Functor.isoWhiskerLeft (siteEtalePostcompose j).op e ≪≫
    (Functor.associator (siteEtalePostcompose j).op F.obj
      (CategoryTheory.forget AddCommGrpCat.{u + 1})).symm ≪≫
    Functor.isoWhiskerRight
      ((sheafToPresheaf V.smallEtaleTopology AddCommGrpCat.{u + 1}).mapIso
        ((inverseImageEtaleIso j).app F)).symm
      (CategoryTheory.forget AddCommGrpCat.{u + 1})

omit [Etale j] in
/-- Over a locally Noetherian base, a quasi-compact etale representing object
makes the original bounded-torsion abelian sheaf constructible. No separatedness
or global quasi-compactness of the base is required. -/
theorem isConstructible_of_quasiCompact_etale_represented
    [IsLocallyNoetherian S] (E : S.Etale) [QuasiCompact E.hom]
    (F : AbelianSheaf.{u, u + 1} S)
    (e : uliftYoneda.{u + 1}.obj E ≅
      F.obj ⋙ CategoryTheory.forget AddCommGrpCat.{u + 1})
    (n : ℕ) (hn : 0 < n) (hkill : KilledBy n F) : IsConstructible F := by
  apply isConstructible_of_affineOpenPullbacks
  intro U
  have : IsAffine U.1.toScheme := U.property
  have : IsNoetherian U.1.toScheme := ⟨⟩
  let E' := (siteBaseChange U.1.ι).obj E
  have : CompactSpace E'.left := by
    change CompactSpace ↑(pullback E.hom U.1.ι : Scheme.{u})
    infer_instance
  exact RepresentedEtaleTorsion.isConstructible_of_represented_etale E'
    ((inverseImage U.1.ι).obj F) (etaleRepresentedInverseImageIso U.1.ι E F e)
    n (killedBy_pullback U.1.ι hkill) hn

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.RepresentedEtaleRestriction
