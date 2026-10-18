/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

/- Current interface basis: 46f53465aaf3b0167049e9c8e9e2294111bb4281.
Original construction and mathematical provenance are retained below. -/
public import Aglib.AlgebraicGeometry.Cohomology.EtaleH1.Torsors
public import Aglib.AlgebraicGeometry.Cohomology.EtaleH1.RepresentedBaseChange
public import Mathlib.CategoryTheory.Sites.CoverPreserving

/-!
# Concrete restriction to étale charts and set-valued inverse image

Construction prerequisite for `K2-018#eq:k2018-pointed-character`, frozen basis
`7f86e4a1763cc4ec35e9b0a8acd659750355a0de`. Restriction is actual precomposition
with postcomposition of étale test schemes. Its comparison to scheme inverse
image is obtained from the actual postcomposition/base-change adjunction.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace AlgebraicGeometry.Scheme.EtaleH1
universe u
attribute [local instance] hasSheafifyLarge
variable {X S : Scheme.{u}}

/-- Composition of étale test schemes with an étale chart. -/
abbrev siteEtalePostcompose (f : S ⟶ X) [Etale f] : S.Etale ⥤ X.Etale :=
  MorphismProperty.Over.map ⊤ (show Etale f from inferInstance)

instance siteEtalePostcompose_preservesPullbacks (f : S ⟶ X) [Etale f] :
    PreservesLimitsOfShape WalkingCospan (siteEtalePostcompose f) := by
  let G := Scheme.Etale.forget X ⋙ Over.forget X
  have : PreservesLimitsOfShape WalkingCospan (siteEtalePostcompose f ⋙ G) := by
    change PreservesLimitsOfShape WalkingCospan (Scheme.Etale.forget S ⋙ Over.forget S)
    infer_instance
  exact preservesLimitsOfShape_of_reflects_of_preserves _ G

/-- Postcomposition preserves jointly surjective étale families. -/
theorem siteEtalePostcompose_coverPreserving (f : S ⟶ X) [Etale f] :
    CoverPreserving (Scheme.smallEtaleTopology S) (Scheme.smallEtaleTopology X)
      (siteEtalePostcompose f) where
  cover_preserve {U} {R} hR := by
    change R ∈ S.smallGrothendieckTopology @Etale U at hR
    change _ ∈ X.smallGrothendieckTopology @Etale _
    rw [Scheme.smallGrothendieckTopology_eq_toGrothendieck_smallPretopology _ le_rfl,
      Scheme.mem_toGrothendieck_smallPretopology] at hR ⊢
    intro x
    obtain ⟨V, g, v, hg, hge, hv⟩ := hR x
    exact ⟨(siteEtalePostcompose f).obj V, (siteEtalePostcompose f).map g, v,
      Sieve.image_mem_functorPushforward _ _ hg, hge, hv⟩

instance siteEtalePostcompose_continuous (f : S ⟶ X) [Etale f] :
    (siteEtalePostcompose f).IsContinuous (Scheme.smallEtaleTopology S)
      (Scheme.smallEtaleTopology X) := by
  let : Functor.PreservesOneHypercovers.{u + 1} (siteEtalePostcompose f)
      (Scheme.smallEtaleTopology S) (Scheme.smallEtaleTopology X) :=
    Functor.PreservesOneHypercovers.of_coverPreserving
      (siteEtalePostcompose_coverPreserving f)
  infer_instance

/-- Actual precomposition restriction of abelian sheaves to an étale chart. -/
abbrev etaleRestriction (f : S ⟶ X) [Etale f] :
    AbelianSheaf.{u, u + 1} X ⥤ AbelianSheaf.{u, u + 1} S :=
  (siteEtalePostcompose f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
    (Scheme.smallEtaleTopology S) (Scheme.smallEtaleTopology X)

/-- The genuine postcomposition/base-change adjunction on small étale sites. -/
def siteEtalePostcomposeAdj (f : S ⟶ X) [Etale f] :
    siteEtalePostcompose f ⊣ siteBaseChange f :=
  MorphismProperty.Over.mapPullbackAdj @Etale ⊤ f inferInstance trivial

/-- Scheme inverse image along an étale chart is actual sheaf restriction. -/
def inverseImageEtaleIso (f : S ⟶ X) [Etale f] :
    inverseImage f ≅ etaleRestriction f :=
  (inverseImageAdjunction f).leftAdjointUniq
    ((siteEtalePostcomposeAdj f).sheafPushforwardContinuous (E := AddCommGrpCat.{u + 1})
        (Scheme.smallEtaleTopology S) (Scheme.smallEtaleTopology X))

/-- The actual inverse-image functor for sheaves of sets in the site universe. -/
def setInverseImage (f : S ⟶ X) : SetSheaf X ⥤ SetSheaf S :=
  (siteBaseChange f).sheafPullback (Type (u + 1))
    (Scheme.smallEtaleTopology X) (Scheme.smallEtaleTopology S)

/-- Direct image of set sheaves along actual base change of test schemes. -/
abbrev setDirectImage (f : S ⟶ X) : SetSheaf S ⥤ SetSheaf X :=
  (siteBaseChange f).sheafPushforwardContinuous (Type (u + 1))
    (Scheme.smallEtaleTopology X) (Scheme.smallEtaleTopology S)

/-- The adjunction between inverse image and direct image of set-valued sheaves
on the small étale sites along the scheme morphism `f`. -/
abbrev setInverseImageAdjunction (f : S ⟶ X) :
    setInverseImage f ⊣ setDirectImage f :=
  (siteBaseChange f).sheafAdjunctionContinuous (Type (u + 1))
    (Scheme.smallEtaleTopology X) (Scheme.smallEtaleTopology S)

/-- Actual restriction of sheaves of sets to an étale chart. -/
abbrev setEtaleRestriction (f : S ⟶ X) [Etale f] : SetSheaf X ⥤ SetSheaf S :=
  (siteEtalePostcompose f).sheafPushforwardContinuous (Type (u + 1))
    (Scheme.smallEtaleTopology S) (Scheme.smallEtaleTopology X)

/-- Set-valued scheme inverse image on an étale chart is actual restriction. -/
def setInverseImageEtaleIso (f : S ⟶ X) [Etale f] :
    setInverseImage f ≅ setEtaleRestriction f :=
  ((siteBaseChange f).sheafAdjunctionContinuous (Type (u + 1))
    (Scheme.smallEtaleTopology X) (Scheme.smallEtaleTopology S)).leftAdjointUniq
      ((siteEtalePostcomposeAdj f).sheafPushforwardContinuous (E := Type (u + 1))
          (Scheme.smallEtaleTopology S) (Scheme.smallEtaleTopology X))

/-- The underlying set sheaf, functorially in abelian coefficients. -/
abbrev underlyingSetFunctor (X : Scheme.{u}) : AbelianSheaf.{u, u + 1} X ⥤ SetSheaf X :=
  sheafCompose (Scheme.smallEtaleTopology X) (CategoryTheory.forget AddCommGrpCat.{u + 1})

/-- Forgetting addition commutes with the actual scheme inverse image. The
proof uses preservation of filtered left Kan extensions and sheafification,
not a supplied base-change comparison. -/
def inverseImageUnderlyingSetIso (f : S ⟶ X) :
    inverseImage f ⋙ underlyingSetFunctor S ≅
      underlyingSetFunctor X ⋙ setInverseImage f := by
  letI := flat_of_preservesFiniteLimits (siteBaseChange f)
  letI : (CategoryTheory.forget AddCommGrpCat.{u + 1}).PreservesLeftKanExtensions (siteBaseChange
    f).op :=
    fun P => forget_preserves_flat_leftKan (siteBaseChange f) P
  let eA := Functor.sheafPullbackConstruction.sheafPullbackIso (siteBaseChange f)
    AddCommGrpCat.{u + 1} (Scheme.smallEtaleTopology X) (Scheme.smallEtaleTopology S)
  let eT := Functor.sheafPullbackConstruction.sheafPullbackIso (siteBaseChange f)
    (Type (u + 1)) (Scheme.smallEtaleTopology X) (Scheme.smallEtaleTopology S)
  let c := sheafComposeNatIso (Scheme.smallEtaleTopology S) (CategoryTheory.forget
    AddCommGrpCat.{u + 1})
    (sheafificationAdjunction _ AddCommGrpCat.{u + 1}) (sheafificationAdjunction _ (Type (u + 1)))
  let k := (CategoryTheory.forget AddCommGrpCat.{u + 1}).lanCompIsoOfPreserves (siteBaseChange f).op
  exact Functor.isoWhiskerRight eA (underlyingSetFunctor S) ≪≫
    Functor.isoWhiskerLeft
      (sheafToPresheaf (Scheme.smallEtaleTopology X) AddCommGrpCat.{u + 1} ⋙
        (siteBaseChange f).op.lan) c.symm ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft (sheafToPresheaf (Scheme.smallEtaleTopology X) AddCommGrpCat.{u +
        1}) k)
      (presheafToSheaf (Scheme.smallEtaleTopology S) (Type (u + 1))) ≪≫
    Functor.isoWhiskerLeft (underlyingSetFunctor X) eT.symm

/-- The genuine inverse image of set sheaves is left exact. -/
instance setInverseImage_preservesFiniteLimits (f : S ⟶ X) :
    PreservesFiniteLimits (setInverseImage f) := by
  let := flat_of_preservesFiniteLimits (siteBaseChange f)
  let := CategoryTheory.Functor.LargePresheaf.typeLan_preservesFiniteLimits (siteBaseChange f)
  exact Functor.sheafPullbackConstruction.preservesFiniteLimits
    (siteBaseChange f) (Type (u + 1))
    (Scheme.smallEtaleTopology X) (Scheme.smallEtaleTopology S)

/-- The underlying-set comparison respects the canonical adjunction unit,
so it transports literal sections through actual scheme inverse image. -/
theorem inverseImageUnderlyingSetIso_unit (f : S ⟶ X) (L : AbelianSheaf.{u, u + 1} X) :
    (underlyingSetFunctor X).map ((inverseImageAdjunction f).unit.app L) ≫
      (setDirectImage f).map ((inverseImageUnderlyingSetIso f).hom.app L) =
    (setInverseImageAdjunction f).unit.app ((underlyingSetFunctor X).obj L) := by
  let := flat_of_preservesFiniteLimits (siteBaseChange f)
  let : (CategoryTheory.forget AddCommGrpCat.{u + 1}).PreservesLeftKanExtensions (siteBaseChange
    f).op :=
    fun P => forget_preserves_flat_leftKan (siteBaseChange f) P
  let eA := Functor.sheafPullbackConstruction.sheafPullbackIso (siteBaseChange f)
    AddCommGrpCat.{u + 1} (Scheme.smallEtaleTopology X) (Scheme.smallEtaleTopology S)
  let eT := Functor.sheafPullbackConstruction.sheafPullbackIso (siteBaseChange f)
    (Type (u + 1)) (Scheme.smallEtaleTopology X) (Scheme.smallEtaleTopology S)
  let c := sheafComposeNatIso (Scheme.smallEtaleTopology S) (CategoryTheory.forget
    AddCommGrpCat.{u + 1})
    (sheafificationAdjunction _ AddCommGrpCat.{u + 1}) (sheafificationAdjunction _ (Type (u + 1)))
  let k := (CategoryTheory.forget AddCommGrpCat.{u + 1}).lanCompIsoOfPreserves (siteBaseChange f).op
  have hA := Adjunction.unit_leftAdjointUniq_hom_app (inverseImageAdjunction f)
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (siteBaseChange f)
      AddCommGrpCat.{u + 1} (Scheme.smallEtaleTopology X) (Scheme.smallEtaleTopology S)) L
  have hT := Adjunction.unit_leftAdjointUniq_hom_app (setInverseImageAdjunction f)
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (siteBaseChange f)
      (Type (u + 1)) (Scheme.smallEtaleTopology X) (Scheme.smallEtaleTopology S))
        ((underlyingSetFunctor X).obj L)
  apply (cancel_mono ((setDirectImage f).map
    (eT.hom.app ((underlyingSetFunctor X).obj L)))).mp
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  have hAU := congrArg (fun a => (CategoryTheory.forget AddCommGrpCat.{u + 1}).map (a.hom.app U)) hA
  have hTU := congrArg (fun a => a.hom.app U) hT
  let F := (siteBaseChange f).op
  let A := F.lan.obj L.obj
  let V := F.obj U
  change (CategoryTheory.forget AddCommGrpCat.{u + 1}).map (((inverseImageAdjunction f).unit.app
    L).hom.app U) ≫
      (CategoryTheory.forget AddCommGrpCat.{u + 1}).map ((eA.hom.app L).hom.app V) =
    (CategoryTheory.forget AddCommGrpCat.{u + 1}).map ((F.leftKanExtensionUnit L.obj).app U ≫
      (toSheafify (Scheme.smallEtaleTopology S) A).app V) at hAU
  change ((setInverseImageAdjunction f).unit.app ((underlyingSetFunctor X).obj L)).hom.app U ≫
      (eT.hom.app ((underlyingSetFunctor X).obj L)).hom.app V =
    (F.leftKanExtensionUnit (L.obj ⋙ CategoryTheory.forget AddCommGrpCat.{u + 1})).app U ≫
      (toSheafify (Scheme.smallEtaleTopology S)
        (F.lan.obj (L.obj ⋙ CategoryTheory.forget AddCommGrpCat.{u + 1}))).app V at hTU
  have hcancel : (eT.inv.app ((underlyingSetFunctor X).obj L)).hom.app V ≫
      (eT.hom.app ((underlyingSetFunctor X).obj L)).hom.app V = 𝟙 _ :=
    congrArg (fun a => a.hom.app V) (eT.inv_hom_id_app ((underlyingSetFunctor X).obj L))
  change (CategoryTheory.forget AddCommGrpCat.{u + 1}).map (((inverseImageAdjunction f).unit.app
    L).hom.app U) ≫
      (CategoryTheory.forget AddCommGrpCat.{u + 1}).map ((eA.hom.app L).hom.app V) ≫
      (c.inv.app A).hom.app V ≫
      ((presheafToSheaf (Scheme.smallEtaleTopology S) (Type (u + 1))).map
        (k.hom.app L.obj)).hom.app V ≫
      (eT.inv.app ((underlyingSetFunctor X).obj L)).hom.app V ≫
      (eT.hom.app ((underlyingSetFunctor X).obj L)).hom.app V = _
  erw [hcancel, Category.comp_id]
  change ((CategoryTheory.forget AddCommGrpCat.{u + 1}).map (((inverseImageAdjunction f).unit.app
    L).hom.app U) ≫
      (CategoryTheory.forget AddCommGrpCat.{u + 1}).map ((eA.hom.app L).hom.app V)) ≫
      (c.inv.app A).hom.app V ≫
      ((presheafToSheaf (Scheme.smallEtaleTopology S) (Type (u + 1))).map
        (k.hom.app L.obj)).hom.app V =
    ((setInverseImageAdjunction f).unit.app ((underlyingSetFunctor X).obj L)).hom.app U ≫
      (eT.hom.app ((underlyingSetFunctor X).obj L)).hom.app V
  erw [hAU, hTU, Functor.map_comp]
  have hc : (CategoryTheory.forget AddCommGrpCat.{u + 1}).map ((toSheafify
    (Scheme.smallEtaleTopology S) A).app V) ≫
      (c.inv.app A).hom.app V =
    (toSheafify (Scheme.smallEtaleTopology S) (A ⋙ CategoryTheory.forget AddCommGrpCat.{u +
      1})).app V :=
    congr_app (sheafComposeIso_inv_fac (Scheme.smallEtaleTopology S) (CategoryTheory.forget
      AddCommGrpCat.{u + 1})
      A) V
  have hn := (congr_app (toSheafify_naturality (Scheme.smallEtaleTopology S) (k.hom.app L.obj))
    V).symm
  have hk := Functor.leftKanExtensionCompIsoOfPreserves_hom_fac_app
    (CategoryTheory.forget AddCommGrpCat.{u + 1}) L.obj F U
  change (toSheafify (Scheme.smallEtaleTopology S) (A ⋙ CategoryTheory.forget AddCommGrpCat.{u +
    1})).app V ≫
      ((presheafToSheaf (Scheme.smallEtaleTopology S) (Type (u + 1))).map
        (k.hom.app L.obj)).hom.app V =
    (k.hom.app L.obj).app V ≫
      (toSheafify (Scheme.smallEtaleTopology S)
        (F.lan.obj (L.obj ⋙ CategoryTheory.forget AddCommGrpCat.{u + 1}))).app V at hn
  change (CategoryTheory.forget AddCommGrpCat.{u + 1}).map ((F.leftKanExtensionUnit L.obj).app U) ≫
      (k.hom.app L.obj).app V =
    (F.leftKanExtensionUnit (L.obj ⋙ CategoryTheory.forget AddCommGrpCat.{u + 1})).app U at hk
  simp only [Category.assoc] at ⊢
  erw [← Category.assoc ((CategoryTheory.forget AddCommGrpCat.{u + 1}).map ((toSheafify
    (Scheme.smallEtaleTopology
    S) A).app V)),
    hc, hn, ← Category.assoc, hk]

end AlgebraicGeometry.Scheme.EtaleH1

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 461171e9be62450de6ff1276225f8aa87a9359a48fb9c38a1581aff3073b1215.
Definitions, hypotheses and universes are retained modulo native names. -/
