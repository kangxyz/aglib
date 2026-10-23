/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.QuasiCoherent.ZariskiModuleNaturality
public import Aglib.CategoryTheory.Sites.SheafCohomology.BasisAcyclicity.ValueLift

/-! # Identification with the original Zariski module coefficient -/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory Opposite TopologicalSpace
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent

/-- Four restrictions and two restrictions with the same endpoints agree on a thin site. -/
theorem additivePresheaf_restriction_chain {C : Type*} [Category* C] [Quiver.IsThin C]
    (P : C ⥤ AddCommGrpCat.{u}) {A B D E T H : C}
    (a : A ⟶ B) (b : B ⟶ D) (c : D ⟶ E) (d : E ⟶ T)
    (e : A ⟶ H) (f : H ⟶ T) (s : P.obj A) :
    P.map d (P.map c (P.map b (P.map a s))) = P.map f (P.map e s) := by
  have h : a ≫ b ≫ c ≫ d = e ≫ f := Subsingleton.elim _ _
  have hp := congrArg P.map h
  simp only [CategoryTheory.Functor.map_comp] at hp
  exact ConcreteCategory.congr_hom hp s

/-- The native open-section component respects every original open restriction. -/
theorem openPullbackSectionsIso_naturality (X : Scheme.{u}) (F : X.Modules)
    [F.IsQuasicoherent] {U V : X.Opens} (f : V ⟶ U)
    (s : Γ((pullback U.ι).obj F, ⊤)) :
    (openPullbackSectionsIso X F V).hom
        ((sectionsPresheaf X F).map (X.restrictFunctor.map f).op s) =
      F.presheaf.map f.op ((openPullbackSectionsIso X F U).hom s) := by
  rw [openPullbackSectionsIso_hom_apply, openPullbackSectionsIso_hom_apply]
  let : IsOpenImmersion (X.restrictFunctor.obj U).hom :=
    inferInstanceAs (IsOpenImmersion U.ι)
  let : IsOpenImmersion (X.restrictFunctor.obj V).hom :=
    inferInstanceAs (IsOpenImmersion V.ι)
  let : IsOpenImmersion (X.restrictFunctor.map f).left :=
    inferInstanceAs (IsOpenImmersion (X.homOfLE f.le))
  have h := openOverSections_naturality X F (X.restrictFunctor.map f) s
  simp only [Scheme.restrictFunctor_obj_hom, Scheme.restrictFunctor_map_left] at h
  refine (congrArg (fun t : Γ(F.restrict V.ι, ⊤) =>
    F.presheaf.map (eqToHom V.ι_image_top.symm).op t) h).trans ?_
  simp only [Scheme.Modules.Hom.comp_app, restrictFunctorComp_inv_app_app,
    restrictFunctorCongr_hom_app_app, restrictAdjunction_unit_app_app]
  rw [restrict_map]
  exact additivePresheaf_restriction_chain F.presheaf _ _ _ _ _ _
    (Scheme.Modules.Hom.app ((restrictFunctorIsoPullback U.ι).inv.app F) ⊤ s)

/-- The original big section coefficient restricted to opens is the lifted original module sheaf. -/
def zariskiModulePresheafIso (X : Scheme.{u}) (F : X.Modules) [F.IsQuasicoherent] :
    X.restrictFunctor.op ⋙ additiveSectionsPresheaf X F ≅
      F.presheaf ⋙ AddCommGrpCat.uliftFunctor.{u+1,u} :=
  liftTransportNativeIso (homPresheaf X F)
    (fun T => AddCommGrpCat.of Γ((pullback T.hom).obj F, ⊤))
    (sectionsEquiv X F) (fun f => sectionsAddHom X F f)
    (fun f s => sectionsAddHom_apply X F f s)
    X.restrictFunctor F.presheaf
    (fun U => (openPullbackSectionsIso X F U).addCommGroupIsoToAddEquiv)
    (fun f s => openPullbackSectionsIso_naturality X F f s)

/-- The actual quasi-coherent étale coefficient restricts to the literal value lift
of the original Zariski additive module sheaf. -/
def zariskiModuleIso (X : Scheme.{u}) (F : X.Modules) [F.IsQuasicoherent] :
    (zariskiRestriction X).obj (additiveCoefficient X F) ≅
      (Sheaf.BasisAcyclicity.valueLift.{u,u,u,u+1}
        (Opens.grothendieckTopology X)).obj (Scheme.Cohomology.moduleAddSheaf X F) :=
  (fullyFaithfulSheafToPresheaf _ _).preimageIso
    ((Functor.associator (opensToEtale X).op (Scheme.Etale.forget X).op
      (additiveSectionsPresheaf X F)).symm ≪≫
      Functor.isoWhiskerRight
        ((Functor.opComp (opensToEtale X) (Scheme.Etale.forget X)).symm ≪≫
          NatIso.op (opensToEtaleForgetIso X).symm)
        (additiveSectionsPresheaf X F) ≪≫ zariskiModulePresheafIso X F)

end AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent
