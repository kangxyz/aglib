/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.PullbackEtaleEvaluation
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.EtaleRestrictionCoherence

/-! # Chart-variable naturality of original pullback sections -/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite

private theorem map_inverse_square {C D : Type*} [Category C] [Category D]
    (Γ : C ⥤ D) {A B E H M : C} (K : A ≅ B) (R : E ≅ H)
    (e : A ⟶ E) (l : B ⟶ M) (m : M ⟶ H)
    (h : K.hom ≫ l ≫ m = e ≫ R.hom) :
    Γ.map K.inv ≫ Γ.map e = Γ.map l ≫ Γ.map m ≫ Γ.map R.inv := by
  have hr : K.inv ≫ e = l ≫ m ≫ R.inv := by
    apply (cancel_epi K.hom).1
    simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id] using
      (congrArg (fun k => k ≫ R.inv) h).symm
  simpa only [Functor.map_comp] using congrArg Γ.map hr

private theorem paste_chart_square {C : Type*} [Category C]
    {A B C₀ D E F G H J : C}
    (p : A ⟶ B) (k : B ⟶ C₀) (e : C₀ ⟶ D) (s : D ⟶ E)
    (l : B ⟶ F) (m : F ⟶ G) (r : G ⟶ D)
    (n : A ⟶ H) (q : H ⟶ F) (t : G ⟶ E) (v : H ⟶ E)
    (sg : H ⟶ J) (fa : J ⟶ E)
    (hC : k ≫ e = l ≫ m ≫ r) (hn : p ≫ l = n ≫ q)
    (hr : r ≫ s = t) (hu : q ≫ m ≫ t = v) (hs : v = sg ≫ fa) :
    (p ≫ k) ≫ (e ≫ s) = (n ≫ sg) ≫ fa := by
  simp only [Category.assoc]
  rw [← Category.assoc k, hC]
  simp only [Category.assoc]
  rw [hr, ← Category.assoc p, hn]
  simp only [Category.assoc]
  rw [hu, hs]

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Continuity

universe u

attribute [local instance] hasSheafifyLarge

/-- The relative morphism attached to two composable étale morphisms. -/
def etaleCompositeToChart {X S T : Scheme.{u}} (f : S ⟶ X) (g : T ⟶ S)
    [Etale f] [Etale g] : Scheme.Etale.mk (g ≫ f) ⟶ Scheme.Etale.mk f :=
  MorphismProperty.Over.homMk g rfl (by trivial)

/-- The native restriction-composition comparison is normalized at the terminal chart. -/
theorem restrictionComp_terminal {X S T : Scheme.{u}} (f : S ⟶ X) (g : T ⟶ S)
    [Etale f] [Etale g] (F : AbelianSheaf.{u, u + 1} X) :
    (globalSections T).map ((etaleRestrictionComp f g).inv.app F) ≫
        F.obj.map (siteEtalePostcomposeTerminalIso (Scheme.Etale.mk (g ≫ f))).inv.op =
      ((etaleRestriction f).obj F).obj.map
        (siteEtalePostcomposeTerminalIso (Scheme.Etale.mk g)).inv.op := by
  have hsite : (siteEtalePostcomposeTerminalIso (Scheme.Etale.mk (g ≫ f))).inv ≫
      (siteEtalePostcomposeComp f g).hom.app (etaleTerminal T) =
    (siteEtalePostcompose f).map
      (siteEtalePostcomposeTerminalIso (Scheme.Etale.mk g)).inv := by
    apply MorphismProperty.Over.Hom.ext
    change 𝟙 T ≫ 𝟙 T = 𝟙 T
    exact Category.id_comp _
  change F.obj.map ((siteEtalePostcomposeComp f g).hom.app (etaleTerminal T)).op ≫
      F.obj.map (siteEtalePostcomposeTerminalIso (Scheme.Etale.mk (g ≫ f))).inv.op =
    F.obj.map ((siteEtalePostcompose f).map
      (siteEtalePostcomposeTerminalIso (Scheme.Etale.mk g)).inv).op
  exact (F.obj.map_comp _ _).symm.trans (congrArg (fun a => F.obj.map a.op) hsite)

/-- Restriction in the original sheaf is the original chart structural morphism. -/
theorem restriction_terminal_map {X S T : Scheme.{u}} (f : S ⟶ X) (g : T ⟶ S)
    [Etale f] [Etale g] (F : AbelianSheaf.{u, u + 1} X) :
    ((etaleRestriction f).obj F).obj.map ((etaleTerminalIsTerminal S).from
      (Scheme.Etale.mk g)).op =
    F.obj.map (siteEtalePostcomposeTerminalIso (Scheme.Etale.mk f)).inv.op ≫
      F.obj.map (etaleCompositeToChart f g).op := by
  have hw := MorphismProperty.Over.w ((etaleTerminalIsTerminal S).from (Scheme.Etale.mk g))
  change ((etaleTerminalIsTerminal S).from (Scheme.Etale.mk g)).left ≫ 𝟙 S = g at hw
  have hw' := (Category.comp_id _).symm.trans hw
  have hsite : (siteEtalePostcompose f).map ((etaleTerminalIsTerminal S).from
      (Scheme.Etale.mk g)) =
    etaleCompositeToChart f g ≫ (siteEtalePostcomposeTerminalIso (Scheme.Etale.mk f)).inv := by
    apply MorphismProperty.Over.Hom.ext
    change ((etaleTerminalIsTerminal S).from (Scheme.Etale.mk g)).left = g ≫ 𝟙 S
    exact hw'.trans (Category.comp_id _).symm
  exact (congrArg (fun a => F.obj.map a.op) hsite).trans (F.obj.map_comp _ _)

/-- Composable étale chart pullbacks agree with literal sheaf restriction. -/
@[reassoc]
theorem pullbackSections_comp_etaleEvaluation {X S T : Scheme.{u}}
    (f : S ⟶ X) (g : T ⟶ S) [Etale f] [Etale g]
    (F : AbelianSheaf.{u, u + 1} X) :
    (globalSectionsPullback g ((inverseImage f).obj F) ≫
        (globalSections T).map ((inverseImageComp f g).inv.app F)) ≫
      (pullbackSectionsEtaleEvaluationIso F (Scheme.Etale.mk (g ≫ f))).hom =
    (pullbackSectionsEtaleEvaluationIso F (Scheme.Etale.mk f)).hom ≫
      F.obj.map (etaleCompositeToChart f g).op := by
  have hc := map_inverse_square (globalSections T) ((inverseImageComp f g).app F)
    ((etaleRestrictionComp f g).app F) ((inverseImageEtaleIso (g ≫ f)).hom.app F)
    ((inverseImage g).map ((inverseImageEtaleIso f).hom.app F))
    ((inverseImageEtaleIso g).hom.app ((etaleRestriction f).obj F))
    (inverseImageEtaleIso_comp f g F)
  have hn := (globalSectionsPullback_naturality g ((inverseImageEtaleIso f).hom.app F)).symm
  have hr := restrictionComp_terminal f g F
  have hu := globalSectionsPullback_etaleEvaluation ((etaleRestriction f).obj F)
    (Scheme.Etale.mk g)
  have hs := restriction_terminal_map f g F
  exact paste_chart_square _ _ _ _ _ _ _ _ _ _ _ _ _ hc hn hr hu hs
/-- The literal étale morphism in a commuting triangle. -/
def etaleTriangleToChart {X S T : Scheme.{u}} (f : S ⟶ X) (g : T ⟶ X)
    (a : S ⟶ T) [Etale f] [Etale g] (h : a ≫ g = f) :
    Scheme.Etale.mk f ⟶ Scheme.Etale.mk g :=
  MorphismProperty.Over.homMk a h (by trivial)

/-- Evaluation respects the native coefficient comparison of any étale triangle. -/
@[reassoc]
theorem pullbackSections_triangle_etaleEvaluation {X S T : Scheme.{u}}
    (f : S ⟶ X) (g : T ⟶ X) (a : S ⟶ T) [Etale f] [Etale g] [Etale a]
    (h : a ≫ g = f) (F : AbelianSheaf.{u, u + 1} X) :
    (globalSectionsPullback a ((inverseImage g).obj F) ≫
        (globalSections S).map ((pullbackTriangleIso f g a h).inv.app F)) ≫
      (pullbackSectionsEtaleEvaluationIso F (Scheme.Etale.mk f)).hom =
    (pullbackSectionsEtaleEvaluationIso F (Scheme.Etale.mk g)).hom ≫
      F.obj.map (etaleTriangleToChart f g a h).op := by
  subst f
  simpa only [pullbackTriangleIso, eqToIso_refl, Iso.refl_trans,
    etaleTriangleToChart, etaleCompositeToChart] using
    pullbackSections_comp_etaleEvaluation g a F

/-- Relative section transport restricts to the original presheaf restriction map. -/
@[reassoc]
theorem pullbackSectionsMap_etaleEvaluation {X : Scheme.{u}}
    (F : AbelianSheaf.{u, u + 1} X) {U V : X.Etale} (a : U ⟶ V) :
    pullbackSectionsMap F ((Scheme.Etale.forget X).map a) ≫
        (pullbackSectionsEtaleEvaluationIso F U).hom =
      (pullbackSectionsEtaleEvaluationIso F V).hom ≫ F.obj.map a.op :=
  pullbackSections_triangle_etaleEvaluation U.hom V.hom a.left
    (MorphismProperty.Over.w a) F

/-- On the original small étale site the relative section system is the original sheaf. -/
def pullbackSectionsEtaleNatIso {X : Scheme.{u}} (F : AbelianSheaf.{u, u + 1} X) :
    (Scheme.Etale.forget X).op ⋙ pullbackSectionsFunctor F ≅ F.obj :=
  NatIso.ofComponents (fun U => pullbackSectionsEtaleEvaluationIso F U.unop)
    (fun a => pullbackSectionsMap_etaleEvaluation F a.unop)

end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
