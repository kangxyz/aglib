/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.FibreProductBaseChangeMap
public import Aglib.AlgebraicGeometry.EtaleCohomology.Derived.BaseChange
public import Aglib.AlgebraicGeometry.EtaleCohomology.GeometricPoints.InverseImage
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.FibreProductStalkRepresentatives
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.GeometricFibreTransfer

/-! # The original higher exchange over a common geometric point

An explicit original neighborhood-germ formula implies the common-point
exchange equation. The coefficient rectangle and germ representatives are
the actual passed suppliers. This conditional module has no dependency on
the proof of the neighborhood formula or on a chosen relation between marked models.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Stalk

universe u w w' s s' e dX dS dX' dS'

attribute [local instance] hasSheafifyLarge

open Continuity Finite.GeometricNeighborhood

private theorem addHom_square_iff_prepost
    {A : Type*} {B : Type*} {C : Type*} {D : Type*} {E : Type*}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] [AddCommGroup D]
    [AddCommGroup E]
    (pre : A →+ E) (post : E →+ B) (m : A →+ B) (hm : m = post.comp pre)
    (b : A →+ C) (b' : B →+ D) (d : C →+ D) :
    b'.comp m = d.comp b ↔ ∀ z, b' (post (pre z)) = d (b z) := by
  subst m
  constructor
  · intro h z
    exact DFunLike.congr_fun h z
  · intro h
    exact AddMonoidHom.ext h

/-- Evaluate a whole equation of the actual raw group maps before any native
cohomology data enters the composition-evaluation proof. -/
private theorem rawGroupSquare_apply {A B C D : AddCommGrpCat.{e}}
    (r : A ⟶ B) (v : B ⟶ D) (u : A ⟶ C) (s : C ⟶ D)
    (h : r ≫ v = u ≫ s) (x : A) : v (r x) = s (u x) := by
  have hs := ConcreteCategory.congr_hom (C := AddCommGrpCat.{e}) h x
  simpa only [CategoryTheory.comp_apply] using hs

private theorem relativeCohomologyTransfer_mk_value
    {X₀ A₀ B₀ : Scheme.{u}}
    [hA : HasExt.{e} (AbelianSheaf.{u, u + 1} A₀)]
    [hB : HasExt.{e} (AbelianSheaf.{u, u + 1} B₀)]
    (a : A₀ ⟶ X₀) (b : B₀ ⟶ X₀) (v : Over.mk a ⟶ Over.mk b)
    (F₀ : AbelianSheaf.{u, u + 1} X₀) (q₀ : ℕ) :
    @relativeCohomologyTransfer.{u, e} X₀ F₀ q₀
      (Over.mk a) (Over.mk b) hA hB v =
      @cohomologyTriangleTransfer.{u, e} X₀ A₀ B₀ hA hB
        a b v.left (Over.w v) F₀ q₀ := rfl

variable {X S X' S' : Scheme.{u}}
  (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
  (h : f' ≫ g = g' ≫ f) {Ω : Type u} [hΩField : Field Ω] [hΩSep : IsSepClosed Ω]
  (ζ : Spec (.of Ω) ⟶ S')
  [hXExt : HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
  [hX'Ext : HasExt.{w'} (AbelianSheaf.{u, u + 1} X')]
  [hSourceSlice : ∀ U : S.Etale, HasExt.{s}
    (Sheaf (@GrothendieckTopology.over.{u, u + 1} X.Etale
      (inferInstance : Category.{u} X.Etale) (Scheme.smallEtaleTopology X)
      ((siteBaseChange f).obj U)) AddCommGrpCat.{u + 1})]
  [hTargetSlice : ∀ V : S'.Etale, HasExt.{s'}
    (Sheaf (@GrothendieckTopology.over.{u, u + 1} X'.Etale
      (inferInstance : Category.{u} X'.Etale) (Scheme.smallEtaleTopology X')
      ((siteBaseChange f').obj V)) AddCommGrpCat.{u + 1})]
  [hZU : ∀ U : S.Etale, HasExt.{e} (AbelianSheaf.{u, u + 1} (pullback U.hom f))]
  [hZV : ∀ V : S'.Etale, HasExt.{e} (AbelianSheaf.{u, u + 1} (pullback V.hom f'))]
  [hFiber : HasExt.{e} (AbelianSheaf.{u, u + 1} (pullback (ζ ≫ g) f))]
  [hFiber' : HasExt.{e} (AbelianSheaf.{u, u + 1} (pullback ζ f'))]

local instance geometricEquationSourceFiberExt :
    HasExt.{e} (AbelianSheaf.{u, u + 1} (Over.mk (pullback.snd (ζ ≫ g) f)).left) :=
  hFiber

local instance geometricEquationTargetFiberExt :
    HasExt.{e} (AbelianSheaf.{u, u + 1} (Over.mk (pullback.snd ζ f')).left) :=
  hFiber'

local instance geometricEquationSourceNeighborhoodExt
    (d : (pointSmallEtale (ζ ≫ g)).fiber.Elements) :
    HasExt.{e} (AbelianSheaf.{u, u + 1}
      ((pointedNeighborhoodBaseChangedDiagram Ω (ζ ≫ g) f).obj d).left) :=
  hZU d.obj

local instance geometricEquationTargetNeighborhoodExt
    (d : (pointSmallEtale ζ).fiber.Elements) :
    HasExt.{e} (AbelianSheaf.{u, u + 1}
      ((pointedNeighborhoodBaseChangedDiagram Ω ζ f').obj d).left) :=
  hZV d.obj

section ActualMap

variable (F : AbelianSheaf.{u, u + 1} X) (q : ℕ)

/-- The original stalk unit followed by the stalk of the supplied actual
sheaf morphism. This construction uses no derived-category model. -/
def higherDirectImageStalkMapOfHom
    (β : (inverseImage g).obj ((higherDirectImage f q).obj F) ⟶
      (higherDirectImage f' q).obj ((inverseImage g').obj F)) :
    ((pointSmallEtale (ζ ≫ g)).sheafFiber (A := AddCommGrpCat.{u + 1})).obj
      ((higherDirectImage f q).obj F) →+
    ((pointSmallEtale ζ).sheafFiber (A := AddCommGrpCat.{u + 1})).obj
      ((higherDirectImage f' q).obj ((inverseImage g').obj F)) :=
  (((pointSmallEtale ζ).sheafFiber (A := AddCommGrpCat.{u + 1})).map β).hom.comp
    ((StalkInverseImage.stalkUnitNatIso g ζ).hom.app ((higherDirectImage f q).obj F)).hom

omit hXExt hX'Ext hSourceSlice hTargetSlice hZU hZV hFiber hFiber' in
/-- The actual-morphism constructor has the literal original unit formula. -/
theorem higherDirectImageStalkMapOfHom_apply
    (β : (inverseImage g).obj ((higherDirectImage f q).obj F) ⟶
      (higherDirectImage f' q).obj ((inverseImage g').obj F))
    (z : ((pointSmallEtale (ζ ≫ g)).sheafFiber (A := AddCommGrpCat.{u + 1})).obj
      ((higherDirectImage f q).obj F)) :
    higherDirectImageStalkMapOfHom.{u} f f' g g' ζ F q β z =
      ((pointSmallEtale ζ).sheafFiber (A := AddCommGrpCat.{u + 1})).map β
        ((StalkInverseImage.stalkUnitNatIso g ζ).hom.app
          ((higherDirectImage f q).obj F) z) := rfl

/-- The exact comparison square for an actual sheaf morphism, retaining the
original geometric coefficient transfer and both original comparison maps. -/
def geometricCohomologyComparisonEquationOfHom
    (β : (inverseImage g).obj ((higherDirectImage f q).obj F) ⟶
      (higherDirectImage f' q).obj ((inverseImage g').obj F))
    (b : ((pointSmallEtale (ζ ≫ g)).sheafFiber (A := AddCommGrpCat.{u + 1})).obj
      ((higherDirectImage f q).obj F) →+
        Sheaf.H.{e} ((inverseImage (pullback.snd (ζ ≫ g) f)).obj F) q)
    (b' : ((pointSmallEtale ζ).sheafFiber (A := AddCommGrpCat.{u + 1})).obj
      ((higherDirectImage f' q).obj ((inverseImage g').obj F)) →+
        Sheaf.H.{e} ((inverseImage (pullback.snd ζ f')).obj ((inverseImage g').obj F)) q) : Prop :=
  b'.comp (higherDirectImageStalkMapOfHom.{u} f f' g g' ζ F q β) =
    (geometricFibreCohomologyTransfer.{u, e} f f' g g' h ζ F q).hom.comp b

omit hXExt hX'Ext hSourceSlice hTargetSlice hZU hZV in
/-- The whole actual-morphism square is equivalent to its original pointwise formula. -/
theorem geometricCohomologyComparisonEquationOfHom_iff_original
    (β : (inverseImage g).obj ((higherDirectImage f q).obj F) ⟶
      (higherDirectImage f' q).obj ((inverseImage g').obj F))
    (b : ((pointSmallEtale (ζ ≫ g)).sheafFiber (A := AddCommGrpCat.{u + 1})).obj
      ((higherDirectImage f q).obj F) →+
        Sheaf.H.{e} ((inverseImage (pullback.snd (ζ ≫ g) f)).obj F) q)
    (b' : ((pointSmallEtale ζ).sheafFiber (A := AddCommGrpCat.{u + 1})).obj
      ((higherDirectImage f' q).obj ((inverseImage g').obj F)) →+
        Sheaf.H.{e} ((inverseImage (pullback.snd ζ f')).obj ((inverseImage g').obj F)) q) :
    geometricCohomologyComparisonEquationOfHom.{u, e} f f' g g' h ζ
      (hFiber := hFiber) (hFiber' := hFiber') F q β b b' ↔
      ∀ z, b' (((pointSmallEtale ζ).sheafFiber (A := AddCommGrpCat.{u + 1})).map β
          ((StalkInverseImage.stalkUnitNatIso g ζ).hom.app
            ((higherDirectImage f q).obj F) z)) =
        geometricFibreCohomologyTransfer.{u, e} f f' g g' h ζ F q (b z) :=
  addHom_square_iff_prepost
    ((StalkInverseImage.stalkUnitNatIso g ζ).hom.app ((higherDirectImage f q).obj F)).hom
    (((pointSmallEtale ζ).sheafFiber (A := AddCommGrpCat.{u + 1})).map β).hom
    (higherDirectImageStalkMapOfHom.{u} f f' g g' ζ F q β) rfl
    b b' (geometricFibreCohomologyTransfer.{u, e} f f' g g' h ζ F q).hom

omit hXExt hX'Ext hSourceSlice hTargetSlice in
/-- The exact original raw-map rectangle, before any scalar evaluation. -/
private theorem geometricCohomologyComparison_neighborhood_whole
    (U : S.Etale) (p : (pointSmallEtale (ζ ≫ g)).fiber.obj U) :
    (cohomologyTransfer.{u, e} (fibreProductBaseChangeMap f f' g g' h U)
      ((inverseImageSquareIso (pullback.snd U.hom f)
        (pullback.snd ((siteBaseChange g).obj U).hom f')
        g' (fibreProductBaseChangeMap f f' g g' h U)
        (fibreProductBaseChangeMap_snd f f' g g' h U).symm).inv.app F) q) ≫
      (relativeCohomologyTransfer.{u, e} ((inverseImage g').obj F) q
        (geometricFibrePointedMap Ω ζ f'
          { obj := (siteBaseChange g).obj U
            val := CoefficientStalkBaseChange.pulledBackPoint g ζ U p })) =
      (relativeCohomologyTransfer.{u, e} F q
        (geometricFibrePointedMap Ω (ζ ≫ g) f { obj := U, val := p })) ≫
        (geometricFibreCohomologyTransfer.{u, e} f f' g g' h ζ F q) := by
  let T := cohomologyTransfer.{u, e} (fibreProductBaseChangeMap f f' g g' h U)
    ((inverseImageSquareIso (pullback.snd U.hom f)
      (pullback.snd ((siteBaseChange g).obj U).hom f')
      g' (fibreProductBaseChangeMap f f' g g' h U)
      (fibreProductBaseChangeMap_snd f f' g g' h U).symm).inv.app F) q
  let uRaw := relativeCohomologyTransfer.{u, e} F q
    (geometricFibrePointedMap Ω (ζ ≫ g) f { obj := U, val := p })
  let vRaw := relativeCohomologyTransfer.{u, e} ((inverseImage g').obj F) q
    (geometricFibrePointedMap Ω ζ f'
      { obj := (siteBaseChange g).obj U
        val := CoefficientStalkBaseChange.pulledBackPoint g ζ U p })
  let dRaw := geometricFibreCohomologyTransfer.{u, e} f f' g g' h ζ F q
  let uTriangle := @cohomologyTriangleTransfer.{u, e} X
    (pullback (ζ ≫ g) f) (pullback U.hom f) hFiber (hZU U)
    (pullback.snd (ζ ≫ g) f) (pullback.snd U.hom f)
    (geometricFibrePointedMap Ω (ζ ≫ g) f { obj := U, val := p }).left
    (Over.w (geometricFibrePointedMap Ω (ζ ≫ g) f { obj := U, val := p })) F q
  let vTriangle := @cohomologyTriangleTransfer.{u, e} X'
    (pullback ζ f') (pullback ((siteBaseChange g).obj U).hom f')
    hFiber' (hZV ((siteBaseChange g).obj U))
    (pullback.snd ζ f') (pullback.snd ((siteBaseChange g).obj U).hom f')
    (geometricFibrePointedMap Ω ζ f'
      { obj := (siteBaseChange g).obj U
        val := CoefficientStalkBaseChange.pulledBackPoint g ζ U p }).left
    (Over.w (geometricFibrePointedMap Ω ζ f'
      { obj := (siteBaseChange g).obj U
        val := CoefficientStalkBaseChange.pulledBackPoint g ζ U p }))
    ((inverseImage g').obj F) q
  let dSquare := @cohomologySquareTransfer.{u, e} X X'
    (pullback ζ f') (pullback (ζ ≫ g) f) hFiber' hFiber
    (pullback.snd (ζ ≫ g) f) (pullback.snd ζ f')
    g' (geometricFibreBaseChangeMap f f' g g' h ζ)
    (geometricFibreBaseChangeMap_snd f f' g g' h ζ).symm F q
  change T ≫ vRaw = uRaw ≫ dRaw
  have hu : uRaw = uTriangle :=
    @relativeCohomologyTransfer_mk_value.{u, e} X
      (pullback (ζ ≫ g) f) (pullback U.hom f) hFiber (hZU U)
      (pullback.snd (ζ ≫ g) f) (pullback.snd U.hom f)
      (geometricFibrePointedMap Ω (ζ ≫ g) f { obj := U, val := p }) F q
  have hv : vRaw = vTriangle :=
    @relativeCohomologyTransfer_mk_value.{u, e} X'
      (pullback ζ f') (pullback ((siteBaseChange g).obj U).hom f')
      hFiber' (hZV ((siteBaseChange g).obj U))
      (pullback.snd ζ f') (pullback.snd ((siteBaseChange g).obj U).hom f')
      (geometricFibrePointedMap Ω ζ f'
        { obj := (siteBaseChange g).obj U
          val := CoefficientStalkBaseChange.pulledBackPoint g ζ U p })
      ((inverseImage g').obj F) q
  have hd : dRaw = dSquare := rfl
  have hP : T ≫ vTriangle = uTriangle ≫ dSquare :=
    @geometricFibreCohomologyTransfer_neighborhood_triangle.{u, e} X S X' S'
      f f' g g' h Ω hΩField hΩSep ζ hFiber hFiber' F q U
      (hZU U) (hZV ((siteBaseChange g).obj U)) p
      (fibreProductBaseChangeMap f f' g g' h U)
      (fibreProductBaseChangeMap_fst f f' g g' h U)
      (fibreProductBaseChangeMap_snd f f' g g' h U)
  exact (congrArg (fun k => T ≫ k) hv).trans
    (hP.trans (congrArg₂ (fun a b => a ≫ b) hu.symm hd.symm))

set_option maxHeartbeats 500000 in
-- The native germ comparison exhausted the default kernel budget. Its existing
-- finite local allowance follows the pointwise proof; compatibility wrappers
-- below use the default.
/-- The original germ formula and coefficient rectangle compare the actual
stalk maps pointwise. The comparison functions need no additive structure, and
no derived-category data is present in this native specialization. -/
theorem geometricCohomologyComparison_pointwise_of_hom_neighborhoodGerms
    (β : (inverseImage g).obj ((higherDirectImage f q).obj F) ⟶
      (higherDirectImage f' q).obj ((inverseImage g').obj F))
    (hN : ∀ (U : S.Etale) (p : (pointSmallEtale (ζ ≫ g)).fiber.obj U)
      (y : Sheaf.H.{e} ((inverseImage (pullback.snd U.hom f)).obj F) q),
      (pointSmallEtale ζ).sheafFiber.map β
          ((StalkInverseImage.stalkUnitNatIso g ζ).hom.app ((higherDirectImage f q).obj F)
            (@fibreProductCohomologyGerm.{u, w, s, e} X S f U
              hXExt (hSourceSlice U) (hZU U) F q Ω hΩField hΩSep (ζ ≫ g) p y)) =
        @fibreProductCohomologyGerm.{u, w', s', e} X' S' f' ((siteBaseChange g).obj U)
          hX'Ext (hTargetSlice ((siteBaseChange g).obj U)) (hZV ((siteBaseChange g).obj U))
          ((inverseImage g').obj F) q Ω hΩField hΩSep ζ
          (CoefficientStalkBaseChange.pulledBackPoint g ζ U p)
          (Continuity.cohomologyTransfer.{u, e} (fibreProductBaseChangeMap f f' g g' h U)
            ((inverseImageSquareIso (pullback.snd U.hom f)
              (pullback.snd ((siteBaseChange g).obj U).hom f')
              g' (fibreProductBaseChangeMap f f' g g' h U)
              (fibreProductBaseChangeMap_snd f f' g g' h U).symm).inv.app F) q y))
    (b : ((pointSmallEtale (ζ ≫ g)).sheafFiber (A := AddCommGrpCat.{u + 1})).obj
      ((higherDirectImage f q).obj F) →
        Sheaf.H.{e} ((inverseImage (pullback.snd (ζ ≫ g) f)).obj F) q)
    (b' : ((pointSmallEtale ζ).sheafFiber (A := AddCommGrpCat.{u + 1})).obj
      ((higherDirectImage f' q).obj ((inverseImage g').obj F)) →
        Sheaf.H.{e} ((inverseImage (pullback.snd ζ f')).obj ((inverseImage g').obj F)) q)
    (hb : ∀ (U : S.Etale) (p : (pointSmallEtale (ζ ≫ g)).fiber.obj U)
      (y : Sheaf.H.{e} ((inverseImage (pullback.snd U.hom f)).obj F) q),
      b (@fibreProductCohomologyGerm.{u, w, s, e} X S f U
              hXExt (hSourceSlice U) (hZU U) F q Ω hΩField hΩSep (ζ ≫ g) p y) =
        relativeCohomologyTransfer.{u, e} F q
          (geometricFibrePointedMap Ω (ζ ≫ g) f { obj := U, val := p }) y)
    (hb' : ∀ (V : S'.Etale) (p : (pointSmallEtale ζ).fiber.obj V)
      (y : Sheaf.H.{e} ((inverseImage (pullback.snd V.hom f')).obj
        ((inverseImage g').obj F)) q),
      b' (@fibreProductCohomologyGerm.{u, w', s', e} X' S' f' V
        hX'Ext (hTargetSlice V) (hZV V) ((inverseImage g').obj F) q Ω hΩField hΩSep ζ p y) =
        relativeCohomologyTransfer.{u, e} ((inverseImage g').obj F) q
          (geometricFibrePointedMap Ω ζ f' { obj := V, val := p }) y)
    : ∀ z, b' (((pointSmallEtale ζ).sheafFiber (A := AddCommGrpCat.{u + 1})).map β
          ((StalkInverseImage.stalkUnitNatIso g ζ).hom.app
            ((higherDirectImage f q).obj F) z)) =
        geometricFibreCohomologyTransfer.{u, e} f f' g g' h ζ F q (b z) := by
  intro z
  obtain ⟨U, p, y, hy⟩ := @exists_fibreProductCohomologyGerm.{u, w, s, e}
    X S f hXExt hSourceSlice hZU F q Ω hΩField hΩSep (ζ ≫ g) z
  have hstart :
      b'
        (((pointSmallEtale ζ).sheafFiber (A := AddCommGrpCat.{u + 1})).map β
          ((StalkInverseImage.stalkUnitNatIso g ζ).hom.app ((higherDirectImage f q).obj F)
            (@fibreProductCohomologyGerm.{u, w, s, e} X S f U
              hXExt (hSourceSlice U) (hZU U) F q Ω hΩField hΩSep (ζ ≫ g) p y))) =
      b'
        (@fibreProductCohomologyGerm.{u, w', s', e} X' S' f' ((siteBaseChange g).obj U)
          hX'Ext (hTargetSlice ((siteBaseChange g).obj U)) (hZV ((siteBaseChange g).obj U))
          ((inverseImage g').obj F) q Ω hΩField hΩSep ζ
          (CoefficientStalkBaseChange.pulledBackPoint g ζ U p)
          (cohomologyTransfer.{u, e} (fibreProductBaseChangeMap f f' g g' h U)
            ((inverseImageSquareIso (pullback.snd U.hom f)
              (pullback.snd ((siteBaseChange g).obj U).hom f')
              g' (fibreProductBaseChangeMap f f' g g' h U)
              (fibreProductBaseChangeMap_snd f f' g g' h U).symm).inv.app F) q y)) :=
    congrArg
      (fun t : ((pointSmallEtale ζ).sheafFiber (A := AddCommGrpCat.{u + 1})).obj
          ((higherDirectImage f' q).obj ((inverseImage g').obj F)) => b' t)
      (hN U p y)
  have htarget :
      b'
        (@fibreProductCohomologyGerm.{u, w', s', e} X' S' f' ((siteBaseChange g).obj U)
          hX'Ext (hTargetSlice ((siteBaseChange g).obj U)) (hZV ((siteBaseChange g).obj U))
          ((inverseImage g').obj F) q Ω hΩField hΩSep ζ
          (CoefficientStalkBaseChange.pulledBackPoint g ζ U p)
          (cohomologyTransfer.{u, e} (fibreProductBaseChangeMap f f' g g' h U)
            ((inverseImageSquareIso (pullback.snd U.hom f)
              (pullback.snd ((siteBaseChange g).obj U).hom f')
              g' (fibreProductBaseChangeMap f f' g g' h U)
              (fibreProductBaseChangeMap_snd f f' g g' h U).symm).inv.app F) q y)) =
      (relativeCohomologyTransfer.{u, e} ((inverseImage g').obj F) q
        (geometricFibrePointedMap Ω ζ f'
          { obj := (siteBaseChange g).obj U
            val := CoefficientStalkBaseChange.pulledBackPoint g ζ U p })
        (cohomologyTransfer.{u, e} (fibreProductBaseChangeMap f f' g g' h U)
          ((inverseImageSquareIso (pullback.snd U.hom f)
            (pullback.snd ((siteBaseChange g).obj U).hom f')
            g' (fibreProductBaseChangeMap f f' g g' h U)
            (fibreProductBaseChangeMap_snd f f' g g' h U).symm).inv.app F) q y)) :=
    hb' ((siteBaseChange g).obj U)
      (CoefficientStalkBaseChange.pulledBackPoint g ζ U p)
      (cohomologyTransfer.{u, e} (fibreProductBaseChangeMap f f' g g' h U)
        ((inverseImageSquareIso (pullback.snd U.hom f)
          (pullback.snd ((siteBaseChange g).obj U).hom f')
          g' (fibreProductBaseChangeMap f f' g g' h U)
          (fibreProductBaseChangeMap_snd f f' g g' h U).symm).inv.app F) q y)
  have hrectangle :
      (relativeCohomologyTransfer.{u, e} ((inverseImage g').obj F) q
        (geometricFibrePointedMap Ω ζ f'
          { obj := (siteBaseChange g).obj U
            val := CoefficientStalkBaseChange.pulledBackPoint g ζ U p })
        (cohomologyTransfer.{u, e} (fibreProductBaseChangeMap f f' g g' h U)
          ((inverseImageSquareIso (pullback.snd U.hom f)
            (pullback.snd ((siteBaseChange g).obj U).hom f')
            g' (fibreProductBaseChangeMap f f' g g' h U)
            (fibreProductBaseChangeMap_snd f f' g g' h U).symm).inv.app F) q y)) =
      geometricFibreCohomologyTransfer.{u, e} f f' g g' h ζ F q
        (relativeCohomologyTransfer.{u, e} F q
          (geometricFibrePointedMap Ω (ζ ≫ g) f { obj := U, val := p }) y) :=
    rawGroupSquare_apply.{e}
      (cohomologyTransfer.{u, e} (fibreProductBaseChangeMap f f' g g' h U)
        ((inverseImageSquareIso (pullback.snd U.hom f)
          (pullback.snd ((siteBaseChange g).obj U).hom f')
          g' (fibreProductBaseChangeMap f f' g g' h U)
          (fibreProductBaseChangeMap_snd f f' g g' h U).symm).inv.app F) q)
      (relativeCohomologyTransfer.{u, e} ((inverseImage g').obj F) q
        (geometricFibrePointedMap Ω ζ f'
          { obj := (siteBaseChange g).obj U
            val := CoefficientStalkBaseChange.pulledBackPoint g ζ U p }))
      (relativeCohomologyTransfer.{u, e} F q
        (geometricFibrePointedMap Ω (ζ ≫ g) f { obj := U, val := p }))
      (geometricFibreCohomologyTransfer.{u, e} f f' g g' h ζ F q)
      (geometricCohomologyComparison_neighborhood_whole.{u, e} f f' g g' h ζ
        (hZU := hZU) (hZV := hZV) (hFiber := hFiber) (hFiber' := hFiber')
        F q U p) y
  have hfinish :
      geometricFibreCohomologyTransfer.{u, e} f f' g g' h ζ F q
        (relativeCohomologyTransfer.{u, e} F q
          (geometricFibrePointedMap Ω (ζ ≫ g) f { obj := U, val := p }) y) =
      geometricFibreCohomologyTransfer.{u, e} f f' g g' h ζ F q
        (b
          (@fibreProductCohomologyGerm.{u, w, s, e} X S f U
            hXExt (hSourceSlice U) (hZU U) F q Ω hΩField hΩSep (ζ ≫ g) p y)) :=
    congrArg
      (fun t : Sheaf.H.{e} ((inverseImage (pullback.snd (ζ ≫ g) f)).obj F) q =>
        geometricFibreCohomologyTransfer.{u, e} f f' g g' h ζ F q t)
      (hb U p y).symm
  have hsource :
      b' (((pointSmallEtale ζ).sheafFiber (A := AddCommGrpCat.{u + 1})).map β
          ((StalkInverseImage.stalkUnitNatIso g ζ).hom.app
            ((higherDirectImage f q).obj F) z)) =
      b' (((pointSmallEtale ζ).sheafFiber (A := AddCommGrpCat.{u + 1})).map β
          ((StalkInverseImage.stalkUnitNatIso g ζ).hom.app
            ((higherDirectImage f q).obj F)
            (@fibreProductCohomologyGerm.{u, w, s, e} X S f U
              hXExt (hSourceSlice U) (hZU U) F q Ω hΩField hΩSep (ζ ≫ g) p y))) :=
    congrArg
      (fun t : ((pointSmallEtale (ζ ≫ g)).sheafFiber
          (A := AddCommGrpCat.{u + 1})).obj ((higherDirectImage f q).obj F) =>
        b' (((pointSmallEtale ζ).sheafFiber (A := AddCommGrpCat.{u + 1})).map β
          ((StalkInverseImage.stalkUnitNatIso g ζ).hom.app
            ((higherDirectImage f q).obj F) t))) hy.symm
  have hresult :
      geometricFibreCohomologyTransfer.{u, e} f f' g g' h ζ F q
        (b (@fibreProductCohomologyGerm.{u, w, s, e} X S f U
          hXExt (hSourceSlice U) (hZU U) F q Ω hΩField hΩSep (ζ ≫ g) p y)) =
      geometricFibreCohomologyTransfer.{u, e} f f' g g' h ζ F q (b z) :=
    congrArg
      (fun t : ((pointSmallEtale (ζ ≫ g)).sheafFiber
          (A := AddCommGrpCat.{u + 1})).obj ((higherDirectImage f q).obj F) =>
        geometricFibreCohomologyTransfer.{u, e} f f' g g' h ζ F q (b t)) hy
  exact hsource.trans
    (hstart.trans (htarget.trans (hrectangle.trans (hfinish.trans hresult))))

/-- Original neighborhood representatives and the literal geometric rectangle
compare any actual sheaf morphism satisfying the stated original germ formula.
No derived-category data is present in this native specialization. -/
theorem geometricCohomologyComparison_of_hom_neighborhoodGerms
    (β : (inverseImage g).obj ((higherDirectImage f q).obj F) ⟶
      (higherDirectImage f' q).obj ((inverseImage g').obj F))
    (hN : ∀ (U : S.Etale) (p : (pointSmallEtale (ζ ≫ g)).fiber.obj U)
      (y : Sheaf.H.{e} ((inverseImage (pullback.snd U.hom f)).obj F) q),
      (pointSmallEtale ζ).sheafFiber.map β
          ((StalkInverseImage.stalkUnitNatIso g ζ).hom.app ((higherDirectImage f q).obj F)
            (@fibreProductCohomologyGerm.{u, w, s, e} X S f U
              hXExt (hSourceSlice U) (hZU U) F q Ω hΩField hΩSep (ζ ≫ g) p y)) =
        @fibreProductCohomologyGerm.{u, w', s', e} X' S' f' ((siteBaseChange g).obj U)
          hX'Ext (hTargetSlice ((siteBaseChange g).obj U)) (hZV ((siteBaseChange g).obj U))
          ((inverseImage g').obj F) q Ω hΩField hΩSep ζ
          (CoefficientStalkBaseChange.pulledBackPoint g ζ U p)
          (Continuity.cohomologyTransfer.{u, e} (fibreProductBaseChangeMap f f' g g' h U)
            ((inverseImageSquareIso (pullback.snd U.hom f)
              (pullback.snd ((siteBaseChange g).obj U).hom f')
              g' (fibreProductBaseChangeMap f f' g g' h U)
              (fibreProductBaseChangeMap_snd f f' g g' h U).symm).inv.app F) q y))
    (b : ((pointSmallEtale (ζ ≫ g)).sheafFiber (A := AddCommGrpCat.{u + 1})).obj
      ((higherDirectImage f q).obj F) →+
        Sheaf.H.{e} ((inverseImage (pullback.snd (ζ ≫ g) f)).obj F) q)
    (b' : ((pointSmallEtale ζ).sheafFiber (A := AddCommGrpCat.{u + 1})).obj
      ((higherDirectImage f' q).obj ((inverseImage g').obj F)) →+
        Sheaf.H.{e} ((inverseImage (pullback.snd ζ f')).obj ((inverseImage g').obj F)) q)
    (hb : ∀ (U : S.Etale) (p : (pointSmallEtale (ζ ≫ g)).fiber.obj U)
      (y : Sheaf.H.{e} ((inverseImage (pullback.snd U.hom f)).obj F) q),
      b (@fibreProductCohomologyGerm.{u, w, s, e} X S f U
              hXExt (hSourceSlice U) (hZU U) F q Ω hΩField hΩSep (ζ ≫ g) p y) =
        relativeCohomologyTransfer.{u, e} F q
          (geometricFibrePointedMap Ω (ζ ≫ g) f { obj := U, val := p }) y)
    (hb' : ∀ (V : S'.Etale) (p : (pointSmallEtale ζ).fiber.obj V)
      (y : Sheaf.H.{e} ((inverseImage (pullback.snd V.hom f')).obj
        ((inverseImage g').obj F)) q),
      b' (@fibreProductCohomologyGerm.{u, w', s', e} X' S' f' V
        hX'Ext (hTargetSlice V) (hZV V) ((inverseImage g').obj F) q Ω hΩField hΩSep ζ p y) =
        relativeCohomologyTransfer.{u, e} ((inverseImage g').obj F) q
          (geometricFibrePointedMap Ω ζ f' { obj := V, val := p }) y)
    : geometricCohomologyComparisonEquationOfHom.{u, e} f f' g g' h ζ
      (hFiber := hFiber) (hFiber' := hFiber') F q β b b' :=
  (geometricCohomologyComparisonEquationOfHom_iff_original.{u, e}
    f f' g g' h ζ (hFiber := hFiber) (hFiber' := hFiber') F q β b b').2
    (geometricCohomologyComparison_pointwise_of_hom_neighborhoodGerms.{u, w, w', s, s', e}
      f f' g g' h ζ
      (hXExt := hXExt) (hX'Ext := hX'Ext)
      (hSourceSlice := hSourceSlice) (hTargetSlice := hTargetSlice)
      (hZU := hZU) (hZV := hZV) (hFiber := hFiber) (hFiber' := hFiber') F q
      β hN b b' hb hb')

end ActualMap

variable
  [hDX : HasDerivedCategory.{dX} (AbelianSheaf.{u, u + 1} X)]
  [hDS : HasDerivedCategory.{dS} (AbelianSheaf.{u, u + 1} S)]
  [hDX' : HasDerivedCategory.{dX'} (AbelianSheaf.{u, u + 1} X')]
  [hDS' : HasDerivedCategory.{dS'} (AbelianSheaf.{u, u + 1} S')]
  (F : AbelianSheaf.{u, u + 1} X) (q : ℕ)

/-- The original stalk unit followed by the stalk of the original higher
exchange, shared before its application to a representative. -/
def higherBaseChangeStalkMap :
    ((pointSmallEtale (ζ ≫ g)).sheafFiber (A := AddCommGrpCat.{u + 1})).obj
      ((higherDirectImage f q).obj F) →+
    ((pointSmallEtale ζ).sheafFiber (A := AddCommGrpCat.{u + 1})).obj
      ((higherDirectImage f' q).obj ((inverseImage g').obj F)) :=
  higherDirectImageStalkMapOfHom.{u} f f' g g' ζ F q
    ((@higherBaseChangeMapFromDerived.{u, dX, dS, dX', dS'} X S X' S'
      hDX hDS hDX' hDS' f f' g g' h q).app F)

omit hXExt hX'Ext hSourceSlice hTargetSlice hZU hZV hFiber hFiber' in
/-- The shared map is literally the original stalk-unit/exchange composite. -/
theorem higherBaseChangeStalkMap_apply
    (z : ((pointSmallEtale (ζ ≫ g)).sheafFiber (A := AddCommGrpCat.{u + 1})).obj
      ((higherDirectImage f q).obj F)) :
    higherBaseChangeStalkMap.{u, dX, dS, dX', dS'} f f' g g' h ζ
      (hDX := hDX) (hDS := hDS) (hDX' := hDX') (hDS' := hDS') F q z =
      ((pointSmallEtale ζ).sheafFiber (A := AddCommGrpCat.{u + 1})).map
        ((@higherBaseChangeMapFromDerived.{u, dX, dS, dX', dS'} X S X' S'
        hDX hDS hDX' hDS' f f' g g' h q).app F)
        ((StalkInverseImage.stalkUnitNatIso g ζ).hom.app
          ((higherDirectImage f q).obj F) z) := rfl

/-- The literal common-point square for the original stalk exchange and
geometric coefficient transfer, retained through its producer and consumer. -/
def geometricCohomologyComparisonEquation
    (b : ((pointSmallEtale (ζ ≫ g)).sheafFiber (A := AddCommGrpCat.{u + 1})).obj
      ((higherDirectImage f q).obj F) →+
        Sheaf.H.{e} ((inverseImage (pullback.snd (ζ ≫ g) f)).obj F) q)
    (b' : ((pointSmallEtale ζ).sheafFiber (A := AddCommGrpCat.{u + 1})).obj
      ((higherDirectImage f' q).obj ((inverseImage g').obj F)) →+
        Sheaf.H.{e} ((inverseImage (pullback.snd ζ f')).obj ((inverseImage g').obj F)) q) : Prop :=
  geometricCohomologyComparisonEquationOfHom.{u, e} f f' g g' h ζ
    (hFiber := hFiber) (hFiber' := hFiber') F q
    ((@higherBaseChangeMapFromDerived.{u, dX, dS, dX', dS'} X S X' S'
      hDX hDS hDX' hDS' f f' g g' h q).app F) b b'

omit hXExt hX'Ext hSourceSlice hTargetSlice hZU hZV in
/-- Expanding the shared equation recovers the original scalar formula. -/
theorem geometricCohomologyComparisonEquation_iff_original
    (b : ((pointSmallEtale (ζ ≫ g)).sheafFiber (A := AddCommGrpCat.{u + 1})).obj
      ((higherDirectImage f q).obj F) →+
        Sheaf.H.{e} ((inverseImage (pullback.snd (ζ ≫ g) f)).obj F) q)
    (b' : ((pointSmallEtale ζ).sheafFiber (A := AddCommGrpCat.{u + 1})).obj
      ((higherDirectImage f' q).obj ((inverseImage g').obj F)) →+
        Sheaf.H.{e} ((inverseImage (pullback.snd ζ f')).obj ((inverseImage g').obj F)) q) :
    geometricCohomologyComparisonEquation.{u, e, dX, dS, dX', dS'} f f' g g' h ζ
      (hFiber := hFiber) (hFiber' := hFiber')
      (hDX := hDX) (hDS := hDS) (hDX' := hDX') (hDS' := hDS') F q b b' ↔
      ∀ z, b' (((pointSmallEtale ζ).sheafFiber (A := AddCommGrpCat.{u + 1})).map
          ((@higherBaseChangeMapFromDerived.{u, dX, dS, dX', dS'} X S X' S'
        hDX hDS hDX' hDS' f f' g g' h q).app F)
          ((StalkInverseImage.stalkUnitNatIso g ζ).hom.app
            ((higherDirectImage f q).obj F) z)) =
        geometricFibreCohomologyTransfer.{u, e} f f' g g' h ζ F q (b z) :=
  geometricCohomologyComparisonEquationOfHom_iff_original.{u, e} f f' g g' h ζ
    (hFiber := hFiber) (hFiber' := hFiber') F q
    ((@higherBaseChangeMapFromDerived.{u, dX, dS, dX', dS'} X S X' S'
      hDX hDS hDX' hDS' f f' g g' h q).app F) b b'

/-- Comparisons with the original pointed-germ formulas commute with the
original stalk unit and higher exchange over the same geometric point. -/
theorem geometricCohomologyComparison_exchange_of_neighborhoodGerms
    (hN : ∀ (U : S.Etale) (p : (pointSmallEtale (ζ ≫ g)).fiber.obj U)
      (y : Sheaf.H.{e} ((inverseImage (pullback.snd U.hom f)).obj F) q),
      (pointSmallEtale ζ).sheafFiber.map
        ((@higherBaseChangeMapFromDerived.{u, dX, dS, dX', dS'} X S X' S'
          hDX hDS hDX' hDS' f f' g g' h q).app F)
          ((StalkInverseImage.stalkUnitNatIso g ζ).hom.app ((higherDirectImage f q).obj F)
            (@fibreProductCohomologyGerm.{u, w, s, e} X S f U
              hXExt (hSourceSlice U) (hZU U) F q Ω hΩField hΩSep (ζ ≫ g) p y)) =
        @fibreProductCohomologyGerm.{u, w', s', e} X' S' f' ((siteBaseChange g).obj U)
          hX'Ext (hTargetSlice ((siteBaseChange g).obj U)) (hZV ((siteBaseChange g).obj U))
          ((inverseImage g').obj F) q Ω hΩField hΩSep ζ
          (CoefficientStalkBaseChange.pulledBackPoint g ζ U p)
          (Continuity.cohomologyTransfer.{u, e} (fibreProductBaseChangeMap f f' g g' h U)
            ((inverseImageSquareIso (pullback.snd U.hom f)
              (pullback.snd ((siteBaseChange g).obj U).hom f')
              g' (fibreProductBaseChangeMap f f' g g' h U)
              (fibreProductBaseChangeMap_snd f f' g g' h U).symm).inv.app F) q y))
    (b : ((pointSmallEtale (ζ ≫ g)).sheafFiber (A := AddCommGrpCat.{u + 1})).obj
      ((higherDirectImage f q).obj F) →+
        Sheaf.H.{e} ((inverseImage (pullback.snd (ζ ≫ g) f)).obj F) q)
    (b' : ((pointSmallEtale ζ).sheafFiber (A := AddCommGrpCat.{u + 1})).obj
      ((higherDirectImage f' q).obj ((inverseImage g').obj F)) →+
        Sheaf.H.{e} ((inverseImage (pullback.snd ζ f')).obj ((inverseImage g').obj F)) q)
    (hb : ∀ (U : S.Etale) (p : (pointSmallEtale (ζ ≫ g)).fiber.obj U)
      (y : Sheaf.H.{e} ((inverseImage (pullback.snd U.hom f)).obj F) q),
      b (@fibreProductCohomologyGerm.{u, w, s, e} X S f U
              hXExt (hSourceSlice U) (hZU U) F q Ω hΩField hΩSep (ζ ≫ g) p y) =
        relativeCohomologyTransfer.{u, e} F q
          (geometricFibrePointedMap Ω (ζ ≫ g) f { obj := U, val := p }) y)
    (hb' : ∀ (V : S'.Etale) (p : (pointSmallEtale ζ).fiber.obj V)
      (y : Sheaf.H.{e} ((inverseImage (pullback.snd V.hom f')).obj
        ((inverseImage g').obj F)) q),
      b' (@fibreProductCohomologyGerm.{u, w', s', e} X' S' f' V
        hX'Ext (hTargetSlice V) (hZV V) ((inverseImage g').obj F) q Ω hΩField hΩSep ζ p y) =
        relativeCohomologyTransfer.{u, e} ((inverseImage g').obj F) q
          (geometricFibrePointedMap Ω ζ f' { obj := V, val := p }) y)
    : geometricCohomologyComparisonEquation.{u, e, dX, dS, dX', dS'} f f' g g' h ζ
      (hFiber := hFiber) (hFiber' := hFiber')
      (hDX := hDX) (hDS := hDS) (hDX' := hDX') (hDS' := hDS') F q b b' :=
  geometricCohomologyComparison_of_hom_neighborhoodGerms.{u, w, w', s, s', e}
    f f' g g' h ζ
    (hXExt := hXExt) (hX'Ext := hX'Ext)
    (hSourceSlice := hSourceSlice) (hTargetSlice := hTargetSlice)
    (hZU := hZU) (hZV := hZV) (hFiber := hFiber) (hFiber' := hFiber') F q
    ((@higherBaseChangeMapFromDerived.{u, dX, dS, dX', dS'} X S X' S'
      hDX hDS hDX' hDS' f f' g g' h q).app F) hN b b' hb hb'

end AlgebraicGeometry.Scheme.EtaleCohomology.Stalk
