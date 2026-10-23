/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Sites.EtaleAffineBasis.InverseImageSections
public import Aglib.AlgebraicGeometry.Sites.EtaleAffineBasis.RepresentativeSections
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.PullbackScalarTransport

/-! # Finite affine representatives of original relative global sections -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleAffineBasis

universe u

open EtaleCohomology EtaleCohomology.Continuity
attribute [local instance] hasSheafifyLarge

private theorem representative_section_apply {X : Scheme.{u}}
    (F : AbelianSheaf.{u, u + 1} X) (Y : Over X) (U : X.Etale)
    (a : Y ⟶ (Etale.forget X).obj U) (t : F.obj.obj (op U)) :
    ((pullbackSectionsEtaleEvaluationIso F U).inv ≫ pullbackSectionsMap F a) t =
      etaleRepresentativeSection F Y U a t := by
  change ((pullbackSectionsEtaleEvaluationIso F U).inv ≫
    (pullbackSectionsFunctor F).map a.op) t = _
  exact ConcreteCategory.comp_apply _ _ _

private theorem unit_section_apply {X S : Scheme.{u}} (f : S ⟶ X)
    (F : AbelianSheaf.{u, u + 1} X) {W : S.Etale} {U : X.Etale}
    (a : W ⟶ (siteBaseChange f).obj U) (t : F.obj.obj (op U)) :
    unitSectionMap f F a t = ((inverseImage f).obj F).obj.map a.op
      (((inverseImageAdjunction f).unit.app F).hom.app (op U) t) :=
  ConcreteCategory.comp_apply _ _ _

private theorem section_of_native_unit_eq {X S : Scheme.{u}} (f : S ⟶ X)
    (F : AbelianSheaf.{u, u + 1} X) (W : S.Etale) (U : X.Etale)
    (a : W ⟶ (siteBaseChange f).obj U) (g : W ⟶ etaleTerminal S)
    (s : (globalSections S).obj ((inverseImage f).obj F)) (t : F.obj.obj (op U))
    (ht : unitSectionMap f F a t = ((inverseImage f).obj F).obj.map g.op s) :
    pullbackSectionsMap F
      (Over.homMk W.hom (U := Over.mk (W.hom ≫ f)) (V := Over.mk f)) s =
        ((pullbackSectionsEtaleEvaluationIso F U).inv ≫
          pullbackSectionsMap F (unitRepresentativeArrow f a)) t := by
  exact (pullbackSectionTransport_restriction f F W g s).symm.trans
    ((congrArg (pullbackSectionTransport f F W) ht).symm.trans
      (pullbackSectionTransport_unit f F a t))


/-- A local original unit equality is the literal relative section restriction
formula for the same representative. -/
theorem pullbackSectionsMap_eq_representative_of_unit_eq
    {X S : Scheme.{u}} (f : S ⟶ X)
    (F : AbelianSheaf.{u, u + 1} X) (W : S.Etale) (U : X.Etale)
    (a : W ⟶ (siteBaseChange f).obj U) (g : W ⟶ etaleTerminal S)
    (s : (globalSections S).obj ((inverseImage f).obj F)) (t : F.obj.obj (op U))
    (ht : ((inverseImage f).obj F).obj.map a.op
      (((inverseImageAdjunction f).unit.app F).hom.app (op U) t) =
        ((inverseImage f).obj F).obj.map g.op s) :
    pullbackSectionsMap F
      (Over.homMk W.hom (U := Over.mk (W.hom ≫ f)) (V := Over.mk f)) s =
        etaleRepresentativeSection F (Over.mk (W.hom ≫ f)) U
          (unitRepresentativeArrow f a) t :=
  (section_of_native_unit_eq f F W U a g s t ((unit_section_apply f F a t).trans ht)).trans
    (representative_section_apply F _ U (unitRepresentativeArrow f a) t)

/-- Every original relative global section has finitely many affine local
representatives in the original coefficient sheaf. The equality uses the
literal relative section restriction, not a replacement presentation. -/
theorem exists_finite_affine_section_representatives
    {X S : Scheme.{u}} [CompactSpace S] (f : S ⟶ X)
    (F : AbelianSheaf.{u, u + 1} X)
    (s : (globalSections S).obj ((inverseImage f).obj F)) :
    ∃ (J : Type u) (_ : Finite J) (W : J → S.Etale),
      (∀ j, IsAffine (W j).left) ∧
      (Sieve.ofArrows W (fun j ↦ (etaleTerminalIsTerminal S).from (W j)) ∈
        S.smallEtaleTopology (etaleTerminal S)) ∧
      ∀ j, ∃ (U : X.Etale)
        (a : Over.mk ((W j).hom ≫ f) ⟶ (Etale.forget X).obj U)
        (t : F.obj.obj (op U)),
        pullbackSectionsMap F
          (Over.homMk (W j).hom (U := Over.mk ((W j).hom ≫ f)) (V := Over.mk f)) s =
            etaleRepresentativeSection F (Over.mk ((W j).hom ≫ f)) U a t := by
  have : CompactSpace (etaleTerminal S).left := inferInstanceAs (CompactSpace S)
  obtain ⟨J, hJ, W, g, hW, hcov, hrep⟩ :=
    exists_finite_affine_inverseImage_unit_representatives f F (etaleTerminal S) s
  have hg (j : J) : g j = (etaleTerminalIsTerminal S).from (W j) :=
    (etaleTerminalIsTerminal S).hom_ext _ _
  refine ⟨J, hJ, W, hW, ?_, fun j ↦ ?_⟩
  · have hg' : g = fun j ↦ (etaleTerminalIsTerminal S).from (W j) := funext hg
    exact hg' ▸ hcov
  obtain ⟨U, a, t, ht⟩ := hrep j
  refine ⟨U, unitRepresentativeArrow f a, t, ?_⟩
  exact pullbackSectionsMap_eq_representative_of_unit_eq f F (W j) U a (g j) s t ht

end AlgebraicGeometry.Scheme.EtaleAffineBasis
