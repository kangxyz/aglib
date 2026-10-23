/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.EtaleRestrictionComposition
public import Aglib.AlgebraicGeometry.Sites.EtaleAffineBasis.InverseImageUnitComposition

/-! # Native inverse-image coherence for étale chart restriction -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite

universe u

private theorem compose_units {C : Type*} [Category* C]
    {A B C₀ D E H B' G : C}
    (u₁ : A ⟶ B) (u₂ : B ⟶ C₀) (d : C₀ ⟶ D)
    (u : A ⟶ E) (c : E ⟶ D) (l : D ⟶ H) (l' : C₀ ⟶ G)
    (d' : G ⟶ H) (e : B ⟶ B') (v : B' ⟶ G) (j : A ⟶ B') (r : A ⟶ H)
    (hc : u₁ ≫ u₂ ≫ d = u ≫ c) (hn : d ≫ l = l' ≫ d')
    (hu : u₂ ≫ l' = e ≫ v) (he : u₁ ≫ e = j) (hg : j ≫ v ≫ d' = r) :
    u ≫ c ≫ l = r := by
  rw [← Category.assoc, ← hc]
  simp only [Category.assoc]
  rw [hn, ← Category.assoc u₂, hu]
  simp only [Category.assoc]
  rw [← Category.assoc u₁ e, he, hg]

private theorem unit_naturality_comp {C : Type*} [Category* C]
    {A B D E H : C} (e : A ⟶ B) (v : B ⟶ D) (u : A ⟶ E) (k : E ⟶ D)
    (t : D ⟶ H) (z : B ⟶ H) (h₀ : e ≫ v = u ≫ k) (h₁ : v ≫ t = z) :
    u ≫ k ≫ t = e ≫ z := by
  rw [← Category.assoc, ← h₀, Category.assoc, h₁]

namespace AlgebraicGeometry.Scheme.EtaleCohomology

attribute [local instance] hasSheafifyLarge

variable {X S T : Scheme.{u}} (f : S ⟶ X) (g : T ⟶ S) [Etale f] [Etale g]

/-- The chosen inverse-image comparison agrees with literal chart restriction composition. -/
theorem inverseImageEtaleIso_comp (F : AbelianSheaf.{u, u + 1} X) :
    (inverseImageComp f g).hom.app F ≫
        (inverseImage g).map ((inverseImageEtaleIso f).hom.app F) ≫
        (inverseImageEtaleIso g).hom.app ((etaleRestriction f).obj F) =
      (inverseImageEtaleIso (g ≫ f)).hom.app F ≫
        (etaleRestrictionComp f g).hom.app F := by
  let L := (inverseImage g).map ((inverseImageEtaleIso f).hom.app F) ≫
    (inverseImageEtaleIso g).hom.app ((etaleRestriction f).obj F)
  apply ((inverseImageAdjunction (g ≫ f)).homEquiv F _).injective
  change (inverseImageAdjunction (g ≫ f)).unit.app F ≫
      (directImage (g ≫ f)).map ((inverseImageComp f g).hom.app F ≫ L) =
    (inverseImageAdjunction (g ≫ f)).unit.app F ≫
      (directImage (g ≫ f)).map ((inverseImageEtaleIso (g ≫ f)).hom.app F ≫
        (etaleRestrictionComp f g).hom.app F)
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext V
  let U := V.unop
  let δ := (siteBaseChangeComp f g).hom.app U
  have hc := EtaleAffineBasis.inverseImageUnit_comp f g F U
  have hn := L.hom.naturality δ.op
  have he := inverseImageEtaleIso_unit_app f F U
  have hg₀ := inverseImageEtaleIso_unit_app (g ≫ f) F U
  have hu₀ := congrArg (fun h => h.hom.app (op ((siteBaseChange f).obj U)))
    ((inverseImageAdjunction g).unit.naturality ((inverseImageEtaleIso f).hom.app F))
  have hu₁ := inverseImageEtaleIso_unit_app g ((etaleRestriction f).obj F)
    ((siteBaseChange f).obj U)
  have hu : ((inverseImageAdjunction g).unit.app ((inverseImage f).obj F)).hom.app
        (op ((siteBaseChange f).obj U)) ≫ L.hom.app
          (op ((siteBaseChange g).obj ((siteBaseChange f).obj U))) =
      ((inverseImageEtaleIso f).hom.app F).hom.app (op ((siteBaseChange f).obj U)) ≫
        ((etaleRestriction f).obj F).obj.map
          ((siteEtalePostcomposeAdj g).counit.app ((siteBaseChange f).obj U)).op := by
    have hu₀' :
        ((inverseImageEtaleIso f).hom.app F).hom.app (op ((siteBaseChange f).obj U)) ≫
          ((inverseImageAdjunction g).unit.app ((etaleRestriction f).obj F)).hom.app
            (op ((siteBaseChange f).obj U)) =
        ((inverseImageAdjunction g).unit.app ((inverseImage f).obj F)).hom.app
          (op ((siteBaseChange f).obj U)) ≫
          ((inverseImage g).map ((inverseImageEtaleIso f).hom.app F)).hom.app
            (op ((siteBaseChange g).obj ((siteBaseChange f).obj U))) := hu₀
    exact unit_naturality_comp _ _ _ _ _ _ hu₀' hu₁
  have hsite := siteEtalePostcomposeComp_counit f g U
  have hsite' :
      (siteEtalePostcompose f).map ((siteEtalePostcompose g).map δ) ≫
          (siteEtalePostcompose f).map
            ((siteEtalePostcomposeAdj g).counit.app ((siteBaseChange f).obj U)) ≫
          (siteEtalePostcomposeAdj f).counit.app U =
        (siteEtalePostcomposeComp f g).inv.app ((siteBaseChange (g ≫ f)).obj U) ≫
          (siteEtalePostcomposeAdj (g ≫ f)).counit.app U := by
    exact (Iso.eq_inv_comp _).mpr hsite
  have hg := congrArg (fun k => F.obj.map k.op) hsite'
  simp only [op_comp, Functor.map_comp, Category.assoc] at hg
  have hgr := congrArg
    (fun k => k ≫ ((etaleRestrictionComp f g).hom.app F).hom.app
      (op ((siteBaseChange (g ≫ f)).obj U))) hg₀
  simp only [Category.assoc] at hgr
  exact (compose_units _ _ _ _ _ _ _ _ _ _ _ _ hc hn hu he hg).trans hgr.symm

end AlgebraicGeometry.Scheme.EtaleCohomology
