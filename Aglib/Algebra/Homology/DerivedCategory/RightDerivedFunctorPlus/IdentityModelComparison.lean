/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.ChangeTargetUnit
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Identity

/-! # Original identity-derived comparison between independent native models -/

@[expose] public noncomputable section
open CategoryTheory DerivedCategory.Plus
namespace CategoryTheory.Functor

private theorem identityModel_unit_transport
    {C D₀ D₁ : Type*} [Category* C] [Category* D₀] [Category* D₁]
    (Q₀ : C ⥤ D₀) (Q₁ : C ⥤ D₁) (L : C ⥤ C)
    (E : D₀ ⥤ D₁) (R₀ : D₀ ⥤ D₀) (R₁ : D₀ ⥤ D₁)
    (q : Q₀ ⋙ E ≅ Q₁) (i : R₀ ≅ 𝟭 D₀) (θ : R₀ ⋙ E ≅ R₁)
    (ψ : R₁ ≅ E) (hψ : ψ = θ.symm ≪≫ isoWhiskerRight i E ≪≫ leftUnitor E)
    (a₀ : L ⋙ Q₀ ⟶ Q₀ ⋙ R₀) (a₁ : L ⋙ Q₁ ⟶ Q₀ ⋙ R₁)
    (ε : L ≅ 𝟭 C) (K : C)
    (hθ : E.map (a₀.app K) ≫ θ.hom.app (Q₀.obj K) =
      q.hom.app (L.obj K) ≫ a₁.app K)
    (hi : a₀.app K ≫ i.hom.app (Q₀.obj K) = Q₀.map (ε.hom.app K)) :
    a₁.app K ≫ ψ.hom.app (Q₀.obj K) ≫ q.hom.app K = Q₁.map (ε.hom.app K) := by
  subst ψ
  apply (cancel_epi (q.hom.app (L.obj K))).mp
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, isoWhiskerRight_hom,
    whiskerRight_app, leftUnitor_hom_app]
  calc
    _ = E.map (a₀.app K) ≫ θ.hom.app (Q₀.obj K) ≫ θ.inv.app (Q₀.obj K) ≫
        E.map (i.hom.app (Q₀.obj K)) ≫ q.hom.app K := by
      rw [← Category.assoc, ← hθ]
      simp only [Category.assoc]
      exact congrArg (fun z => E.map (a₀.app K) ≫ θ.hom.app (Q₀.obj K) ≫
        θ.inv.app (Q₀.obj K) ≫ E.map (i.hom.app (Q₀.obj K)) ≫ z)
        (Category.id_comp (q.hom.app K))
    _ = E.map (a₀.app K ≫ i.hom.app (Q₀.obj K)) ≫ q.hom.app K := by
      simp only [Iso.hom_inv_id_app_assoc, map_comp, Category.assoc]
    _ = E.map (Q₀.map (ε.hom.app K)) ≫ q.hom.app K := by rw [hi]
    _ = _ := q.hom.naturality (ε.hom.app K)

universe u v d₀ d₁
variable {A : Type u} [Category.{v} A] [Abelian A] [EnoughInjectives A]
  (h₀ : HasDerivedCategory.{d₀} A) (h₁ : HasDerivedCategory.{d₁} A)
  (F : A ⥤ A) [F.Additive] (e : F ≅ 𝟭 A)

/-- Change the native target model, then contract by the original same-model identity. -/
def rightDerivedFunctorPlusIdentityModelIso :
    (@Functor.rightDerivedFunctorPlus _ _ _ _ _ _ h₀ h₁ F _ _) ≅ (canonicalEquivalence h₀
      h₁).functor := by
  letI := h₀
  exact (rightDerivedFunctorPlusChangeTarget h₀ h₀ h₁ F).symm ≪≫
    isoWhiskerRight (F.rightDerivedFunctorPlusIso e ≪≫ rightDerivedFunctorPlusIdIso A)
      (canonicalEquivalence h₀ h₁).functor ≪≫ leftUnitor _

/-- Both the original derived unit and the actual quotient comparison are retained. -/
@[reassoc]
theorem rightDerivedFunctorPlusIdentityModelIso_unit (K : CochainComplex.Plus A) :
    ((@Functor.rightDerivedFunctorPlusUnit _ _ _ _ _ _ h₀ h₁ F _ _)).app K ≫
        (rightDerivedFunctorPlusIdentityModelIso h₀ h₁ F e).hom.app (((@DerivedCategory.Plus.Q _ _
          _ h₀)).obj K) ≫
        (quotientCompCanonicalEquivalenceIso h₀ h₁).hom.app K =
      ((@DerivedCategory.Plus.Q _ _ _ h₁)).map ((NatIso.mapCochainComplexPlus e).hom.app K ≫
        (mapCochainComplexPlusIdIso A).hom.app K) := by
  let := h₀
  have hi : F.rightDerivedFunctorPlusUnit.app K ≫
      (F.rightDerivedFunctorPlusIso e ≪≫ rightDerivedFunctorPlusIdIso A).hom.app
        (DerivedCategory.Plus.Q.obj K) =
      DerivedCategory.Plus.Q.map ((NatIso.mapCochainComplexPlus e).hom.app K ≫
        (mapCochainComplexPlusIdIso A).hom.app K) := by
    simp only [Iso.trans_hom, NatTrans.comp_app]
    rw [← Category.assoc, rightDerivedFunctorPlusIso_hom_app,
      Category.assoc, rightDerivedFunctorPlusIdIso_unit, ← map_comp]
  exact identityModel_unit_transport ((@DerivedCategory.Plus.Q _ _ _ h₀))
    ((@DerivedCategory.Plus.Q _ _ _ h₁)) F.mapCochainComplexPlus
    (canonicalEquivalence h₀ h₁).functor ((@Functor.rightDerivedFunctorPlus _ _ _ _ _ _ h₀ h₀ F _
      _))
    ((@Functor.rightDerivedFunctorPlus _ _ _ _ _ _ h₀ h₁ F _ _))
      (quotientCompCanonicalEquivalenceIso h₀ h₁)
    (F.rightDerivedFunctorPlusIso e ≪≫ rightDerivedFunctorPlusIdIso A)
    (rightDerivedFunctorPlusChangeTarget h₀ h₀ h₁ F)
    (rightDerivedFunctorPlusIdentityModelIso h₀ h₁ F e) rfl
    ((@Functor.rightDerivedFunctorPlusUnit _ _ _ _ _ _ h₀ h₀ F _ _))
      ((@Functor.rightDerivedFunctorPlusUnit _ _ _ _ _ _ h₀ h₁ F _ _))
    (NatIso.mapCochainComplexPlus e ≪≫ mapCochainComplexPlusIdIso A) K
    (rightDerivedFunctorPlusChangeTarget_unit h₀ h₀ h₁ F K) hi

end CategoryTheory.Functor
