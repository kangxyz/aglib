/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.PullbackCohomologySystem
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.EtaleRestrictionUnit

/-! # Actual sections on an étale chart and original sheaf evaluation -/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite

private theorem paste_two_squares {C : Type*} [Category C]
    {A B C₀ D E H : C} (a : A ⟶ B) (b : A ⟶ C₀) (c : B ⟶ D)
    (d : C₀ ⟶ D) (e : D ⟶ E) (f : C₀ ⟶ H) (g : H ⟶ E)
    (h₁ : a ≫ c = b ≫ d) (h₂ : d ≫ e = f ≫ g) :
    a ≫ (c ≫ e) = (b ≫ f) ≫ g := by
  rw [← Category.assoc, h₁, Category.assoc, h₂, Category.assoc]

private theorem paste_unit_square {C : Type*} [Category C]
    {A B C₀ D E H : C} (a : A ⟶ B) (b : B ⟶ C₀) (c : C₀ ⟶ D)
    (d : B ⟶ E) (e : E ⟶ D) (f : D ⟶ H) (r : A ⟶ E)
    (h : b ≫ c = d ≫ e) (hu : a ≫ d = r) :
    (a ≫ b) ≫ (c ≫ f) = r ≫ e ≫ f := by
  rw [Category.assoc, ← Category.assoc b, h]
  simp only [Category.assoc]
  rw [← Category.assoc a, hu]

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Continuity

universe u

attribute [local instance] hasSheafifyLarge

/-- The terminal test scheme of an étale chart, regarded over the original base. -/
def siteEtalePostcomposeTerminalIso {X : Scheme.{u}} (U : X.Etale) :
    (siteEtalePostcompose U.hom).obj (etaleTerminal U.left) ≅ U :=
  MorphismProperty.Over.isoMk (Iso.refl _) (by
    change 𝟙 U.left ≫ U.hom = 𝟙 U.left ≫ U.hom
    rfl)

/-- Original pullback sections on an étale chart are the original value of the sheaf. -/
def pullbackSectionsEtaleEvaluationIso {X : Scheme.{u}}
    (F : AbelianSheaf.{u, u + 1} X) (U : X.Etale) :
    (globalSections U.left).obj ((inverseImage U.hom).obj F) ≅ F.obj.obj (op U) :=
  (globalSections U.left).mapIso ((inverseImageEtaleIso U.hom).app F) ≪≫
    F.obj.mapIso (siteEtalePostcomposeTerminalIso U).symm.op

/-- The chart identification is natural in the actual coefficient sheaf. -/
@[reassoc]
theorem pullbackSectionsEtaleEvaluationIso_naturality {X : Scheme.{u}}
    {F G : AbelianSheaf.{u, u + 1} X} (q : F ⟶ G) (U : X.Etale) :
    (globalSections U.left).map ((inverseImage U.hom).map q) ≫
        (pullbackSectionsEtaleEvaluationIso G U).hom =
      (pullbackSectionsEtaleEvaluationIso F U).hom ≫ q.hom.app (op U) := by
  let Γ := globalSections U.left
  have h₁ := (Γ.map_comp ((inverseImage U.hom).map q)
    ((inverseImageEtaleIso U.hom).hom.app G)).symm.trans
    ((congrArg Γ.map ((inverseImageEtaleIso U.hom).hom.naturality q)).trans
      (Γ.map_comp ((inverseImageEtaleIso U.hom).hom.app F)
        ((etaleRestriction U.hom).map q)))
  exact paste_two_squares _ _ _ _ _ _ _ h₁
    (q.hom.naturality (siteEtalePostcomposeTerminalIso U).symm.hom.op).symm

/-- The chart comparison identifies the original unit pullback with restriction
along the original structural map to the terminal étale object. -/
@[reassoc]
theorem globalSectionsPullback_etaleEvaluation {X : Scheme.{u}}
    (F : AbelianSheaf.{u, u + 1} X) (U : X.Etale) :
    globalSectionsPullback U.hom F ≫ (pullbackSectionsEtaleEvaluationIso F U).hom =
      F.obj.map ((etaleTerminalIsTerminal X).from U).op := by
  let t := siteBaseChangeTerminalIso U.hom
  let s := siteEtalePostcomposeTerminalIso U
  let e := (inverseImageEtaleIso U.hom).hom.app F
  have hn : ((inverseImage U.hom).obj F).obj.map t.inv.op ≫
      e.hom.app (op (etaleTerminal U.left)) =
    e.hom.app (op ((siteBaseChange U.hom).obj (etaleTerminal X))) ≫
      F.obj.map ((siteEtalePostcompose U.hom).map t.inv).op :=
    e.hom.naturality t.inv.op
  have hsite : (s.inv ≫ (siteEtalePostcompose U.hom).map t.inv) ≫
      (siteEtalePostcomposeAdj U.hom).counit.app (etaleTerminal X) =
    (etaleTerminalIsTerminal X).from U :=
    (etaleTerminalIsTerminal X).hom_ext _ _
  have hp := paste_unit_square
    (((inverseImageAdjunction U.hom).unit.app F).hom.app (op (etaleTerminal X)))
    (((inverseImage U.hom).obj F).obj.map t.inv.op)
    (e.hom.app (op (etaleTerminal U.left)))
    (e.hom.app (op ((siteBaseChange U.hom).obj (etaleTerminal X))))
    (F.obj.map ((siteEtalePostcompose U.hom).map t.inv).op)
    (F.obj.map s.inv.op)
    (F.obj.map ((siteEtalePostcomposeAdj U.hom).counit.app (etaleTerminal X)).op)
    hn (inverseImageEtaleIso_unit_app U.hom F (etaleTerminal X))
  refine hp.trans ?_
  exact (congrArg
    (fun k => F.obj.map ((siteEtalePostcomposeAdj U.hom).counit.app
      (etaleTerminal X)).op ≫ k)
    (F.obj.map_comp ((siteEtalePostcompose U.hom).map t.inv).op s.inv.op).symm).trans
    ((F.obj.map_comp ((siteEtalePostcomposeAdj U.hom).counit.app (etaleTerminal X)).op
      (((siteEtalePostcompose U.hom).map t.inv).op ≫ s.inv.op)).symm.trans
      (congrArg (fun a => F.obj.map a.op) hsite))

end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
