/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.GeometricFibreNeighborhood
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.RelativeCohomologySquare
public import Aglib.AlgebraicGeometry.EtaleCohomology.PullbackEquivalence
public import Aglib.AlgebraicGeometry.EtaleCohomology.PullbackIsomorphism

/-! # Original cohomology transfer between the fibres over one point

The transfer keeps the original square coefficient isomorphism. It commutes
with restriction from the original pointed neighborhoods and is bijective
when the original geometric square is Cartesian.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Stalk

universe u e

attribute [local instance] hasSheafifyLarge

open Continuity

private theorem transfer_bijective_of_iso_coefficients
    {A B : Scheme.{u}}
    [HasExt.{e} (AbelianSheaf.{u, u + 1} A)]
    [HasExt.{e} (AbelianSheaf.{u, u + 1} B)]
    (r : A ⟶ B) [IsIso r] (F : AbelianSheaf.{u, u + 1} B)
    (G : AbelianSheaf.{u, u + 1} A) (E : (inverseImage r).obj F ≅ G) (q : ℕ) :
    Function.Bijective (cohomologyTransfer r E.hom q) :=
  (cohomologyMapIso_bijective E q).comp
    (cohomologyPullback_bijective_of_isEquivalence r F q)

private theorem transfer_family_bijective_of_iso
    {C : Type*} [Category* C] {A B : Scheme.{u}}
    [HasExt.{e} (AbelianSheaf.{u, u + 1} A)]
    [HasExt.{e} (AbelianSheaf.{u, u + 1} B)]
    (r : A ⟶ B) [IsIso r]
    (P : C ⥤ AbelianSheaf.{u, u + 1} B) (Q : C ⥤ AbelianSheaf.{u, u + 1} A)
    (E : P ⋙ inverseImage r ≅ Q) (F : C) (q : ℕ) :
    Function.Bijective (cohomologyTransfer r (E.hom.app F) q) :=
  transfer_bijective_of_iso_coefficients r (P.obj F) (Q.obj F) (E.app F) q

/-- The original cohomology transfer with its original square coefficient,
kept at one shared construction before geometric specialization. -/
def cohomologySquareTransfer
    {X X' A B : Scheme.{u}}
    [HasExt.{e} (AbelianSheaf.{u, u + 1} A)]
    [HasExt.{e} (AbelianSheaf.{u, u + 1} B)]
    (a : B ⟶ X) (a' : A ⟶ X') (g : X' ⟶ X) (r : A ⟶ B)
    (h : a' ≫ g = r ≫ a) (F : AbelianSheaf.{u, u + 1} X) (q : ℕ) :
    AddCommGrpCat.of (Sheaf.H.{e} ((inverseImage a).obj F) q) ⟶
      AddCommGrpCat.of (Sheaf.H.{e} ((inverseImage a').obj ((inverseImage g).obj F)) q) :=
  cohomologyTransfer r ((inverseImageSquareIso a a' g r h).inv.app F) q

private theorem squareTransfer_bijective
    {X X' A B : Scheme.{u}}
    [HasExt.{e} (AbelianSheaf.{u, u + 1} A)]
    [HasExt.{e} (AbelianSheaf.{u, u + 1} B)]
    (a : B ⟶ X) (a' : A ⟶ X') (g : X' ⟶ X) (r : A ⟶ B) [IsIso r]
    (h : a' ≫ g = r ≫ a) (F : AbelianSheaf.{u, u + 1} X) (q : ℕ) :
    Function.Bijective (cohomologySquareTransfer a a' g r h F q) :=
  transfer_family_bijective_of_iso r (inverseImage a) (inverseImage g ⋙ inverseImage a')
    (inverseImageSquareIso a a' g r h).symm F q

/-- The original triangle and square transfers form one rectangle over
explicit schemes, with the same four Ext witnesses throughout. -/
def cohomologySquareTriangleEquation
    {X X' A B A' B' : Scheme.{u}}
    [hA : HasExt.{e} (AbelianSheaf.{u, u + 1} A)]
    [hB : HasExt.{e} (AbelianSheaf.{u, u + 1} B)]
    [hA' : HasExt.{e} (AbelianSheaf.{u, u + 1} A')]
    [hB' : HasExt.{e} (AbelianSheaf.{u, u + 1} B')]
    (p : B ⟶ X) (p' : B' ⟶ X') (a : A ⟶ X) (a' : A' ⟶ X')
    (v : A ⟶ B) (v' : A' ⟶ B') (r : B' ⟶ B) (σ : A' ⟶ A) (g : X' ⟶ X)
    (hv : v ≫ p = a) (hv' : v' ≫ p' = a')
    (hR : p' ≫ g = r ≫ p) (hS : a' ≫ g = σ ≫ a)
    (F : AbelianSheaf.{u, u + 1} X) (q : ℕ) : Prop :=
  @cohomologyTransfer.{u, e} B B' hB hB' r
      ((inverseImage p).obj F) ((inverseImage p').obj ((inverseImage g).obj F))
      ((inverseImageSquareIso p p' g r hR).inv.app F) q ≫
      @cohomologyTriangleTransfer.{u, e} X' A' B' hA' hB'
        a' p' v' hv' ((inverseImage g).obj F) q =
    @cohomologyTriangleTransfer.{u, e} X A B hA hB a p v hv F q ≫
      @cohomologySquareTransfer.{u, e} X X' A' A hA' hA a a' g σ hS F q

/-- The original coefficient rectangle proves the shared equation for the
actual triangle and square transfers over explicit schemes. -/
theorem cohomologySquareTriangleEquation_of_rectangle
    {X X' A B A' B' : Scheme.{u}}
    [hA : HasExt.{e} (AbelianSheaf.{u, u + 1} A)]
    [hB : HasExt.{e} (AbelianSheaf.{u, u + 1} B)]
    [hA' : HasExt.{e} (AbelianSheaf.{u, u + 1} A')]
    [hB' : HasExt.{e} (AbelianSheaf.{u, u + 1} B')]
    (p : B ⟶ X) (p' : B' ⟶ X') (a : A ⟶ X) (a' : A' ⟶ X')
    (v : A ⟶ B) (v' : A' ⟶ B') (r : B' ⟶ B) (σ : A' ⟶ A) (g : X' ⟶ X)
    (hv : v ≫ p = a) (hv' : v' ≫ p' = a')
    (hR : p' ≫ g = r ≫ p) (hS : a' ≫ g = σ ≫ a)
    (hRect : v' ≫ r = σ ≫ v) (F : AbelianSheaf.{u, u + 1} X) (q : ℕ) :
    @cohomologySquareTriangleEquation.{u, e} X X' A B A' B' hA hB hA' hB'
      p p' a a' v v' r σ g hv hv' hR hS F q :=
  @cohomologyTransfer_relative_square.{u, e} X X' A B A' B' hA hB hA' hB'
    p p' a a' v v' r σ g hv hv' hR hS hRect F q

/-- The literal original relative rectangle, kept as one regular equation
through its generic producer and concrete geometric consumer. -/
def cohomologySquareTransferRelativeEquation
    {X X' : Scheme.{u}} {A B : Over X} {A' B' : Over X'}
    [HasExt.{e} (AbelianSheaf.{u, u + 1} A.left)]
    [HasExt.{e} (AbelianSheaf.{u, u + 1} B.left)]
    [HasExt.{e} (AbelianSheaf.{u, u + 1} A'.left)]
    [HasExt.{e} (AbelianSheaf.{u, u + 1} B'.left)]
    (v : A ⟶ B) (v' : A' ⟶ B') (r : B'.left ⟶ B.left)
    (σ : A'.left ⟶ A.left) (g : X' ⟶ X)
    (hR : B'.hom ≫ g = r ≫ B.hom) (hS : A'.hom ≫ g = σ ≫ A.hom)
    (F : AbelianSheaf.{u, u + 1} X) (q : ℕ) : Prop :=
  @cohomologySquareTriangleEquation.{u, e} X X' A.left B.left A'.left B'.left
    ‹HasExt.{e} (AbelianSheaf.{u, u + 1} A.left)›
    ‹HasExt.{e} (AbelianSheaf.{u, u + 1} B.left)›
    ‹HasExt.{e} (AbelianSheaf.{u, u + 1} A'.left)›
    ‹HasExt.{e} (AbelianSheaf.{u, u + 1} B'.left)›
    B.hom B'.hom A.hom A'.hom v.left v'.left r σ g
    (Over.w v) (Over.w v') hR hS F q

private theorem squareTransfer_relative
    {X X' : Scheme.{u}} {A B : Over X} {A' B' : Over X'}
    [HasExt.{e} (AbelianSheaf.{u, u + 1} A.left)]
    [HasExt.{e} (AbelianSheaf.{u, u + 1} B.left)]
    [HasExt.{e} (AbelianSheaf.{u, u + 1} A'.left)]
    [HasExt.{e} (AbelianSheaf.{u, u + 1} B'.left)]
    (v : A ⟶ B) (v' : A' ⟶ B') (r : B'.left ⟶ B.left)
    (σ : A'.left ⟶ A.left) (g : X' ⟶ X)
    (hR : B'.hom ≫ g = r ≫ B.hom) (hS : A'.hom ≫ g = σ ≫ A.hom)
    (hRect : v'.left ≫ r = σ ≫ v.left)
    (F : AbelianSheaf.{u, u + 1} X) (q : ℕ) :
    cohomologySquareTransferRelativeEquation v v' r σ g hR hS F q :=
  @cohomologySquareTriangleEquation_of_rectangle.{u, e} X X' A.left B.left A'.left B'.left
    ‹HasExt.{e} (AbelianSheaf.{u, u + 1} A.left)›
    ‹HasExt.{e} (AbelianSheaf.{u, u + 1} B.left)›
    ‹HasExt.{e} (AbelianSheaf.{u, u + 1} A'.left)›
    ‹HasExt.{e} (AbelianSheaf.{u, u + 1} B'.left)›
    B.hom B'.hom A.hom A'.hom v.left v'.left r σ g
    (Over.w v) (Over.w v') hR hS hRect F q

private theorem groupSquare_apply {A B C D : AddCommGrpCat.{e}}
    (r : A ⟶ B) (v : B ⟶ D) (w : A ⟶ C) (σ : C ⟶ D)
    (h : r ≫ v = w ≫ σ) (x : A) : v (r x) = σ (w x) :=
  ConcreteCategory.congr_hom h x

/-- Evaluate the shared rectangle after fixing its four actual schemes,
structural maps and original Ext witnesses. -/
theorem cohomologySquareTriangleEquation_apply
    {X X' A B A' B' : Scheme.{u}}
    [hA : HasExt.{e} (AbelianSheaf.{u, u + 1} A)]
    [hB : HasExt.{e} (AbelianSheaf.{u, u + 1} B)]
    [hA' : HasExt.{e} (AbelianSheaf.{u, u + 1} A')]
    [hB' : HasExt.{e} (AbelianSheaf.{u, u + 1} B')]
    (p : B ⟶ X) (p' : B' ⟶ X') (a : A ⟶ X) (a' : A' ⟶ X')
    (v : A ⟶ B) (v' : A' ⟶ B') (r : B' ⟶ B) (σ : A' ⟶ A) (g : X' ⟶ X)
    (hv : v ≫ p = a) (hv' : v' ≫ p' = a')
    (hR : p' ≫ g = r ≫ p) (hS : a' ≫ g = σ ≫ a)
    (F : AbelianSheaf.{u, u + 1} X) (q : ℕ)
    (h : @cohomologySquareTriangleEquation.{u, e} X X' A B A' B' hA hB hA' hB'
      p p' a a' v v' r σ g hv hv' hR hS F q)
    (x : Sheaf.H.{e} ((inverseImage p).obj F) q) :
    (@cohomologyTriangleTransfer.{u, e} X' A' B' hA' hB'
      a' p' v' hv' ((inverseImage g).obj F) q)
      ((@cohomologyTransfer.{u, e} B B' hB hB' r
        ((inverseImage p).obj F) ((inverseImage p').obj ((inverseImage g).obj F))
        ((inverseImageSquareIso p p' g r hR).inv.app F) q) x) =
      (@cohomologySquareTransfer.{u, e} X X' A' A hA' hA a a' g σ hS F q)
        ((@cohomologyTriangleTransfer.{u, e} X A B hA hB a p v hv F q) x) :=
  groupSquare_apply
    (@cohomologyTransfer.{u, e} B B' hB hB' r
      ((inverseImage p).obj F) ((inverseImage p').obj ((inverseImage g).obj F))
      ((inverseImageSquareIso p p' g r hR).inv.app F) q)
    (@cohomologyTriangleTransfer.{u, e} X' A' B' hA' hB'
      a' p' v' hv' ((inverseImage g).obj F) q)
    (@cohomologyTriangleTransfer.{u, e} X A B hA hB a p v hv F q)
    (@cohomologySquareTransfer.{u, e} X X' A' A hA' hA a a' g σ hS F q) h x

/-- Evaluate the completed original rectangle only after its construction
and transport have been normalized at variable relative schemes. -/
theorem cohomologySquareTransferRelativeEquation_apply
    {X X' : Scheme.{u}} {A B : Over X} {A' B' : Over X'}
    [HasExt.{e} (AbelianSheaf.{u, u + 1} A.left)]
    [HasExt.{e} (AbelianSheaf.{u, u + 1} B.left)]
    [HasExt.{e} (AbelianSheaf.{u, u + 1} A'.left)]
    [HasExt.{e} (AbelianSheaf.{u, u + 1} B'.left)]
    (v : A ⟶ B) (v' : A' ⟶ B') (r : B'.left ⟶ B.left)
    (σ : A'.left ⟶ A.left) (g : X' ⟶ X)
    (hR : B'.hom ≫ g = r ≫ B.hom) (hS : A'.hom ≫ g = σ ≫ A.hom)
    (F : AbelianSheaf.{u, u + 1} X) (q : ℕ)
    (h : cohomologySquareTransferRelativeEquation v v' r σ g hR hS F q)
    (x : Sheaf.H.{e} ((inverseImage B.hom).obj F) q) :
    relativeCohomologyTransfer ((inverseImage g).obj F) q v'
        (cohomologyTransfer r ((inverseImageSquareIso B.hom B'.hom g r hR).inv.app F) q x) =
      cohomologySquareTransfer A.hom A'.hom g σ hS F q
        (relativeCohomologyTransfer F q v x) :=
  @cohomologySquareTriangleEquation_apply.{u, e} X X' A.left B.left A'.left B'.left
    ‹HasExt.{e} (AbelianSheaf.{u, u + 1} A.left)›
    ‹HasExt.{e} (AbelianSheaf.{u, u + 1} B.left)›
    ‹HasExt.{e} (AbelianSheaf.{u, u + 1} A'.left)›
    ‹HasExt.{e} (AbelianSheaf.{u, u + 1} B'.left)›
    B.hom B'.hom A.hom A'.hom v.left v'.left r σ g
    (Over.w v) (Over.w v') hR hS F q h x

variable {X S X' S' : Scheme.{u}}
  (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
  (h : f' ≫ g = g' ≫ f) {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  (ζ : Spec (.of Ω) ⟶ S')
  [HasExt.{e} (AbelianSheaf.{u, u + 1} (pullback (ζ ≫ g) f))]
  [HasExt.{e} (AbelianSheaf.{u, u + 1} (pullback ζ f'))]
  (F : AbelianSheaf.{u, u + 1} X) (q : ℕ)

local instance geometricTransfer_sourceApexExt :
    HasExt.{e} (AbelianSheaf.{u, u + 1} (Over.mk (pullback.snd (ζ ≫ g) f)).left) :=
  inferInstanceAs (HasExt.{e} (AbelianSheaf.{u, u + 1} (pullback (ζ ≫ g) f)))

local instance geometricTransfer_targetApexExt :
    HasExt.{e} (AbelianSheaf.{u, u + 1} (Over.mk (pullback.snd ζ f')).left) :=
  inferInstanceAs (HasExt.{e} (AbelianSheaf.{u, u + 1} (pullback ζ f')))

/-- The actual fibre map and its original inverse-image square coefficient. -/
def geometricFibreCohomologyTransfer :
    AddCommGrpCat.of (Sheaf.H.{e} ((inverseImage (pullback.snd (ζ ≫ g) f)).obj F) q) ⟶
      AddCommGrpCat.of (Sheaf.H.{e}
        ((inverseImage (pullback.snd ζ f')).obj ((inverseImage g').obj F)) q) :=
  cohomologySquareTransfer (pullback.snd (ζ ≫ g) f) (pullback.snd ζ f')
    g' (geometricFibreBaseChangeMap f f' g g' h ζ)
    (geometricFibreBaseChangeMap_snd f f' g g' h ζ).symm F q

omit [IsSepClosed Ω] in
/-- For a Cartesian square this exact cohomology transfer is bijective. -/
theorem geometricFibreCohomologyTransfer_bijective (H : IsPullback g' f' f g) :
    Function.Bijective (geometricFibreCohomologyTransfer f f' g g' h ζ F q) := by
  let σ := geometricFibreBaseChangeMap f f' g g' h ζ
  let : IsIso σ := geometricFibreBaseChangeMap_isIso f f' g g' h ζ H
  exact squareTransfer_bijective (pullback.snd (ζ ≫ g) f) (pullback.snd ζ f')
    g' σ (geometricFibreBaseChangeMap_snd f f' g g' h ζ).symm F q

/-- The original geometric neighborhood supplies the literal triangle/square
predicate before scalar evaluation. The point is the actual stalk-fibre point. -/
theorem geometricFibreCohomologyTransfer_neighborhood_triangle
    (U : S.Etale)
    [hU : HasExt.{e} (AbelianSheaf.{u, u + 1} (pullback U.hom f))]
    [hV : HasExt.{e}
      (AbelianSheaf.{u, u + 1} (pullback ((siteBaseChange g).obj U).hom f'))]
    (p : (pointSmallEtale (ζ ≫ g)).fiber.obj U)
    (r : pullback ((siteBaseChange g).obj U).hom f' ⟶ pullback U.hom f)
    (hr₁ : r ≫ pullback.fst U.hom f =
      pullback.fst ((siteBaseChange g).obj U).hom f' ≫ pullback.fst U.hom g)
    (hr₂ : r ≫ pullback.snd U.hom f = pullback.snd ((siteBaseChange g).obj U).hom f' ≫ g') :
    @cohomologySquareTriangleEquation.{u, e} X X'
      (pullback (ζ ≫ g) f) (pullback U.hom f)
      (pullback ζ f') (pullback ((siteBaseChange g).obj U).hom f')
      ‹HasExt.{e} (AbelianSheaf.{u, u + 1} (pullback (ζ ≫ g) f))› hU
      ‹HasExt.{e} (AbelianSheaf.{u, u + 1} (pullback ζ f'))› hV
      (pullback.snd U.hom f) (pullback.snd ((siteBaseChange g).obj U).hom f')
      (pullback.snd (ζ ≫ g) f) (pullback.snd ζ f')
      (geometricFibrePointedMap Ω (ζ ≫ g) f { obj := U, val := p }).left
      (geometricFibrePointedMap Ω ζ f'
        { obj := (siteBaseChange g).obj U
          val := CoefficientStalkBaseChange.pulledBackPoint g ζ U p }).left
      r (geometricFibreBaseChangeMap f f' g g' h ζ) g'
      (Over.w (geometricFibrePointedMap Ω (ζ ≫ g) f { obj := U, val := p }))
      (Over.w (geometricFibrePointedMap Ω ζ f'
        { obj := (siteBaseChange g).obj U
          val := CoefficientStalkBaseChange.pulledBackPoint g ζ U p }))
      hr₂.symm (geometricFibreBaseChangeMap_snd f f' g g' h ζ).symm F q :=
  @cohomologySquareTriangleEquation_of_rectangle.{u, e} X X'
    (pullback (ζ ≫ g) f) (pullback U.hom f)
    (pullback ζ f') (pullback ((siteBaseChange g).obj U).hom f')
    ‹HasExt.{e} (AbelianSheaf.{u, u + 1} (pullback (ζ ≫ g) f))› hU
    ‹HasExt.{e} (AbelianSheaf.{u, u + 1} (pullback ζ f'))› hV
    (pullback.snd U.hom f) (pullback.snd ((siteBaseChange g).obj U).hom f')
    (pullback.snd (ζ ≫ g) f) (pullback.snd ζ f')
    (geometricFibrePointedMap Ω (ζ ≫ g) f { obj := U, val := p }).left
    (geometricFibrePointedMap Ω ζ f'
      { obj := (siteBaseChange g).obj U
        val := CoefficientStalkBaseChange.pulledBackPoint g ζ U p }).left
    r (geometricFibreBaseChangeMap f f' g g' h ζ) g'
    (Over.w (geometricFibrePointedMap Ω (ζ ≫ g) f { obj := U, val := p }))
    (Over.w (geometricFibrePointedMap Ω ζ f'
      { obj := (siteBaseChange g).obj U
        val := CoefficientStalkBaseChange.pulledBackPoint g ζ U p }))
    hr₂.symm (geometricFibreBaseChangeMap_snd f f' g g' h ζ).symm
    (geometricFibrePointedMap_baseChange.{u} f f' g g' h ζ U p r hr₁ hr₂) F q

variable (U : S.Etale)
  [HasExt.{e} (AbelianSheaf.{u, u + 1} (pullback U.hom f))]
  [HasExt.{e} (AbelianSheaf.{u, u + 1} (pullback ((siteBaseChange g).obj U).hom f'))]
  (p : Over.mk (ζ ≫ g) ⟶ (Scheme.Etale.forget S).obj U)

local instance geometricTransfer_sourceStageExt :
    HasExt.{e} (AbelianSheaf.{u, u + 1}
      ((pointedNeighborhoodBaseChangedDiagram Ω (ζ ≫ g) f).obj
        { obj := U, val := p }).left) :=
  inferInstanceAs (HasExt.{e} (AbelianSheaf.{u, u + 1} (pullback U.hom f)))

local instance geometricTransfer_targetStageExt :
    HasExt.{e} (AbelianSheaf.{u, u + 1}
      ((pointedNeighborhoodBaseChangedDiagram Ω ζ f').obj
        { obj := (siteBaseChange g).obj U,
          val := CoefficientStalkBaseChange.pulledBackPoint g ζ U p }).left) :=
  inferInstanceAs (HasExt.{e} (AbelianSheaf.{u, u + 1}
    (pullback ((siteBaseChange g).obj U).hom f')))

/-- The literal original neighborhood transfer commutes with the geometric
restriction, including both original coefficient comparisons. -/
theorem geometricFibreCohomologyTransfer_neighborhood
    (r : pullback ((siteBaseChange g).obj U).hom f' ⟶ pullback U.hom f)
    (hr₁ : r ≫ pullback.fst U.hom f =
      pullback.fst ((siteBaseChange g).obj U).hom f' ≫ pullback.fst U.hom g)
    (hr₂ : r ≫ pullback.snd U.hom f = pullback.snd ((siteBaseChange g).obj U).hom f' ≫ g') :
    cohomologySquareTransferRelativeEquation
      (geometricFibrePointedMap Ω (ζ ≫ g) f { obj := U, val := p })
      (geometricFibrePointedMap Ω ζ f'
        { obj := (siteBaseChange g).obj U,
          val := CoefficientStalkBaseChange.pulledBackPoint g ζ U p })
      r (geometricFibreBaseChangeMap f f' g g' h ζ) g'
      hr₂.symm (geometricFibreBaseChangeMap_snd f f' g g' h ζ).symm F q :=
  squareTransfer_relative
    (geometricFibrePointedMap Ω (ζ ≫ g) f { obj := U, val := p })
    (geometricFibrePointedMap Ω ζ f'
      { obj := (siteBaseChange g).obj U,
        val := CoefficientStalkBaseChange.pulledBackPoint g ζ U p })
    r (geometricFibreBaseChangeMap f f' g g' h ζ) g'
    hr₂.symm (geometricFibreBaseChangeMap_snd f f' g g' h ζ).symm
    (geometricFibrePointedMap_baseChange f f' g g' h ζ U p r hr₁ hr₂) F q

end AlgebraicGeometry.Scheme.EtaleCohomology.Stalk
