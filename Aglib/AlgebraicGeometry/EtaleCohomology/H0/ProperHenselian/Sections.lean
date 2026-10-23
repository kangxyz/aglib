/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.SchemeTorsorBaseChange
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.DegreeZeroPullback
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.CoverLimits

/-! # Original sections of finite represented coefficients under pullback -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.Scheme.EtaleCohomology.ProperHenselianH0

universe u v

private theorem eval_composite_of_eq {P Q R : AddCommGrpCat.{v}}
    (p : P ⟶ Q) (q : Q ⟶ R) (r : P ⟶ R) (h : p ≫ q = r)
    (x : P) (y : R) (hr : r x = y) : q (p x) = y :=
  (ConcreteCategory.congr_hom h x).trans hr

attribute [local instance] hasSheafifyLarge Over.cartesianMonoidalCategory

variable {X S : Scheme.{u}} (f : S ⟶ X)

/-- The finite-cover terminal comparison is the original small-site terminal comparison. -/
def terminalIso :
    (Scheme.FiniteEtale.baseChange f).obj (Scheme.FiniteEtale.terminalCover X) ≅
      Scheme.FiniteEtale.terminalCover S :=
  ObjectProperty.isoMk _ ((Scheme.Etale.forget S).mapIso (siteBaseChangeTerminalIso f))

/-- Pullback of actual sections, with the original terminal-object transport. -/
def sectionsPullback (Y : Scheme.FiniteEtale X)
    (s : Over.mk (𝟙 X) ⟶ Y.obj) :
    Over.mk (𝟙 S) ⟶ ((Scheme.FiniteEtale.baseChange f).obj Y).obj :=
  (terminalIso f).inv.hom ≫ (Over.pullback f).map s

/-- Full faithfulness of the actual finite-cover functor gives a section bijection. -/
theorem sectionsPullback_bijective
    [(Scheme.FiniteEtale.baseChange f).Full]
    [(Scheme.FiniteEtale.baseChange f).Faithful] (Y : Scheme.FiniteEtale X) :
    Function.Bijective (sectionsPullback f Y) := by
  let F := Scheme.FiniteEtale.baseChange f
  let e : (Scheme.FiniteEtale.terminalCover X ⟶ Y) ≃
      (Scheme.FiniteEtale.terminalCover S ⟶ F.obj Y) :=
    ((Functor.FullyFaithful.ofFullyFaithful F).homEquiv).trans
      (Iso.homCongr (terminalIso f) (Iso.refl _))
  constructor
  · intro a b hab
    have h : e (ObjectProperty.homMk a) = e (ObjectProperty.homMk b) := by
      apply ObjectProperty.hom_ext
      exact hab
    exact congrArg (fun k => k.hom) (e.injective h)
  · intro b
    obtain ⟨a, ha⟩ := e.surjective (ObjectProperty.homMk b)
    exact ⟨a.hom, congrArg (fun k => k.hom) ha⟩

variable (A : Grp (Over X)) [IsCommMonObj A.X] [IsFinite A.X.hom] [Etale A.X.hom]

/-- The native represented coefficient comparison retains the original section map. -/
theorem represented_sectionsPullback
    (s : Over.mk (𝟙 X) ⟶ A.X) :
    (globalSections S).map (representedSheafBaseChangeIso f A).hom
        (globalSectionsPullback f (representedSheaf A) (ULift.up (Additive.ofMul s))) =
      ULift.up (Additive.ofMul (sectionsPullback f (Scheme.FiniteEtale.mk A.X.hom) s)) := by
  have h : globalSectionsPullback f (representedSheaf A) ≫
      (globalSections S).map (representedSheafBaseChangeIso f A).hom =
      (globalSections X).map (SchemeTorsorBaseChange.representedCoefficientUnit f A) ≫
        (directImageGlobalSectionsIso f).hom.app (representedSheaf (baseChangedGroup f A)) := by
    dsimp only [globalSectionsPullback]
    rw [Category.assoc, ← (directImageGlobalSectionsIso f).hom.naturality,
      ← Category.assoc, Functor.comp_map, ← Functor.map_comp,
      SchemeTorsorBaseChange.representedSheafBaseChangeIso_unit]
  exact eval_composite_of_eq
    (globalSectionsPullback f (representedSheaf A))
    ((globalSections S).map (representedSheafBaseChangeIso f A).hom)
    ((globalSections X).map (SchemeTorsorBaseChange.representedCoefficientUnit f A) ≫
      (directImageGlobalSectionsIso f).hom.app (representedSheaf (baseChangedGroup f A)))
    h (ULift.up (Additive.ofMul s))
    (ULift.up (Additive.ofMul (sectionsPullback f (Scheme.FiniteEtale.mk A.X.hom) s))) rfl

/-- Actual global-section pullback is bijective for every finite represented coefficient. -/
theorem represented_globalSectionsPullback_bijective
    [(Scheme.FiniteEtale.baseChange f).Full]
    [(Scheme.FiniteEtale.baseChange f).Faithful] :
    Function.Bijective (globalSectionsPullback f (representedSheaf A)) := by
  have hb : Function.Bijective (fun s : (globalSections X).obj (representedSheaf A) =>
      (globalSections S).map (representedSheafBaseChangeIso f A).hom
        (globalSectionsPullback f (representedSheaf A) s)) := by
    constructor
    · intro s t h
      apply ULift.ext
      apply Additive.toMul.injective
      apply (sectionsPullback_bijective f (Scheme.FiniteEtale.mk A.X.hom)).injective
      exact congrArg (fun x => x.down.toMul)
        ((represented_sectionsPullback f A s.down.toMul).symm.trans
          (h.trans (represented_sectionsPullback f A t.down.toMul)))
    · intro t
      obtain ⟨s, hs⟩ := (sectionsPullback_bijective f
        (Scheme.FiniteEtale.mk A.X.hom)).surjective t.down.toMul
      refine ⟨ULift.up (Additive.ofMul s), ?_⟩
      dsimp only
      exact (represented_sectionsPullback f A s).trans (congrArg
        (fun q => ULift.up (Additive.ofMul q)) hs)
  constructor
  · exact hb.injective.of_comp
  · intro t
    obtain ⟨s, hs⟩ := hb.surjective
      ((globalSections S).map (representedSheafBaseChangeIso f A).hom t)
    exact ⟨s, (Functor.mapIso (globalSections S)
      (representedSheafBaseChangeIso f A)).addCommGroupIsoToAddEquiv.injective hs⟩

end AlgebraicGeometry.Scheme.EtaleCohomology.ProperHenselianH0
