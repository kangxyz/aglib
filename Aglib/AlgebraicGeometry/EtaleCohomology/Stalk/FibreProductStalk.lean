/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.FibreProductPresheaf

/-! # Original higher-image stalks as the actual fibre-product cohomology colimit -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite

private theorem unit_transport {C D : Type*} [Category* C] [Category* D]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) {P Q : C} {M : D}
    (a : P ≅ Q) (b : L.obj Q ≅ M) (c : Q ⟶ R.obj M)
    (hc : adj.unit.app Q ≫ R.map b.hom = c) :
    adj.unit.app P ≫ R.map ((L.mapIso a) ≪≫ b).hom = a.hom ≫ c := by
  change adj.unit.app P ≫ R.map (L.map a.hom ≫ b.hom) = _
  have hn : a.hom ≫ adj.unit.app Q =
      adj.unit.app P ≫ R.map (L.map a.hom) := adj.unit.naturality a.hom
  rw [R.map_comp, ← Category.assoc]
  exact (congrArg (fun k => k ≫ R.map b.hom) hn.symm).trans
    ((Category.assoc _ _ _).trans (congrArg (fun k => a.hom ≫ k) hc))

universe u w s t

namespace AlgebraicGeometry.Scheme.EtaleCohomology

attribute [local instance] hasSheafifyLarge

variable {X S : Scheme.{u}} (f : X ⟶ S)
  [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
  [∀ U : S.Etale, HasExt.{s} (Sheaf ((Scheme.smallEtaleTopology X).over
    ((siteBaseChange f).obj U)) AddCommGrpCat.{u + 1})]
  [∀ U : S.Etale, HasExt.{t} (AbelianSheaf.{u, u + 1} (pullback U.hom f))]
  (F : AbelianSheaf.{u, u + 1} X) (q : ℕ)

/-- Sheafification of the actual scheme-cohomology diagram is the native higher direct image. -/
def fibreProductCohomologySheafificationIso :
    (presheafToSheaf (Scheme.smallEtaleTopology S) AddCommGrpCat.{u + 1}).obj
        (smallFibreProductCohomologyPresheaf f F q) ≅ (higherDirectImage f q).obj F :=
  (presheafToSheaf (Scheme.smallEtaleTopology S) AddCommGrpCat.{u + 1}).mapIso
    (smallFibreProductOriginalIso f F q) ≪≫ originalCohomologySheafificationIso f F q

/-- The map from actual fibre-product cohomology is fixed by the original represented comparison. -/
def fibreProductCohomologyToHigherDirectImage :
    smallFibreProductCohomologyPresheaf f F q ⟶ ((higherDirectImage f q).obj F).obj :=
  (smallFibreProductOriginalIso f F q).hom ≫ originalCohomologyToHigherDirectImage f F q

/-- The actual fibre-product comparison uses the original sheafification unit. -/
theorem fibreProductCohomologyToHigherDirectImage_unit :
    toSheafify (Scheme.smallEtaleTopology S) (smallFibreProductCohomologyPresheaf f F q) ≫
      (fibreProductCohomologySheafificationIso f F q).hom.hom =
        fibreProductCohomologyToHigherDirectImage f F q := by
  exact unit_transport (sheafificationAdjunction (Scheme.smallEtaleTopology S)
    AddCommGrpCat.{u + 1}) (smallFibreProductOriginalIso f F q)
    (originalCohomologySheafificationIso f F q)
    (originalCohomologyToHigherDirectImage f F q)
    (originalCohomologyToHigherDirectImage_unit f F q)

variable {Ω : Type u} [Field Ω] [IsSepClosed Ω] (η : Spec (.of Ω) ⟶ S)

/-- The actual neighbourhood colimit of original scheme cohomology is the native stalk.
No continuity theorem for a strict-local inverse limit is used in this statement. -/
def fibreProductCohomologyStalkIso :
    ((pointSmallEtale η).presheafFiber (A := AddCommGrpCat.{u + 1})).obj
        (smallFibreProductCohomologyPresheaf f F q) ≅
      ((pointSmallEtale η).sheafFiber (A := AddCommGrpCat.{u + 1})).obj
        ((higherDirectImage f q).obj F) :=
  ((pointSmallEtale η).presheafFiber (A := AddCommGrpCat.{u + 1})).mapIso
    (smallFibreProductOriginalIso f F q) ≪≫ originalCohomologyStalkIso f F q η

/-- Each actual unresized scheme-cohomology class has its original higher-image germ. -/
theorem germ_fibreProductCohomologyStalkIso_apply (U : S.Etale)
    (p : (pointSmallEtale η).fiber.obj U)
    (x : Sheaf.H.{t} ((inverseImage (pullback.snd U.hom f)).obj F) q) :
    (fibreProductCohomologyStalkIso f F q η).hom
      ((pointSmallEtale η).toPresheafFiber U p
        (smallFibreProductCohomologyPresheaf f F q) (Shrink.addEquiv.symm x)) =
      fibreProductCohomologyGerm f U F q η p x := by
  have h := ConcreteCategory.congr_hom
    ((pointSmallEtale η).toPresheafFiber_naturality
      (smallFibreProductOriginalIso f F q).hom U p) (Shrink.addEquiv.symm x)
  refine (congrArg (originalCohomologyStalkIso f F q η).hom h).trans ?_
  change (originalCohomologyStalkIso f F q η).hom
    ((pointSmallEtale η).toPresheafFiber U p (smallOriginalCohomologyPresheaf f F q)
      (Shrink.addEquiv.symm ((fibreProductCohomologyEquiv f U F q).symm
        (Shrink.addEquiv (Shrink.addEquiv.symm x))))) = _
  rw [AddEquiv.apply_symm_apply]
  exact germ_originalCohomologyStalkIso_apply f F q η U p
    ((fibreProductCohomologyEquiv f U F q).symm x)

end AlgebraicGeometry.Scheme.EtaleCohomology
