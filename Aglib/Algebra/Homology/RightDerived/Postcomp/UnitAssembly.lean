/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.ModuleCoefficients.DerivedPostcompResolution
public import Aglib.CategoryTheory.Sites.SheafCohomology.ModuleCoefficients.DerivedGammaZero

/-! # The original postcomposition transpose and its whole zero unit

The original ordinary counit comparison constructs the derived comparison.
Its actual adjunction transpose retains the whole zero unit by the original
right triangle. This is proved before any sheaf, section, germ or point value.
No preservation of injectives by the left functor or right forgetful functor
is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory.Limits

namespace CategoryTheory.Functor

universe uC vC uD vD uE vE

section OriginalUnitIso

variable {D : Type uD} [Category.{vD} D] {E : Type uE} [Category.{vE} E]
  (L : D ⥤ E) (R : E ⥤ D) (adj : L ⊣ R)
  (ε : 𝟭 E ≅ R ⋙ L)
  (hε : Functor.whiskerRight ε.hom R = Functor.whiskerLeft R adj.unit)

include hε in
/-- The inverse of the actual unit isomorphism is the actual adjunction counit. -/
theorem unitIso_inv_eq_counit : ε.inv = adj.counit := by
  apply NatTrans.ext
  funext Y
  apply (adj.homEquiv (R.obj Y) Y).injective
  simp only [Adjunction.homEquiv_unit]
  have h := NatTrans.congr_app hε Y
  change R.map (ε.hom.app Y) = adj.unit.app (R.obj Y) at h
  have hi : adj.unit.app (R.obj Y) ≫ R.map (ε.inv.app Y) = 𝟙 _ := by
    rw [← h, ← R.map_comp, ε.hom_inv_id_app, R.map_id]
    simp only [Functor.id_obj]
  exact hi.trans (adj.right_triangle_components Y).symm

include hε in
/-- The original comparison built from that unit Iso is the original counit comparison. -/
theorem postcompUnitIso_comparison_hom {C : Type uC} [Category.{vC} C] (Q : C ⥤ E) :
    ((Functor.associator Q R L) ≪≫ Functor.isoWhiskerLeft Q ε.symm ≪≫
      Functor.rightUnitor Q).hom =
      (Functor.associator Q R L).hom ≫ Functor.whiskerLeft Q adj.counit ≫
        (Functor.rightUnitor Q).hom := by
  simp only [Iso.trans_hom, Functor.isoWhiskerLeft_hom, Iso.symm_hom]
  rw [unitIso_inv_eq_counit L R adj ε hε]

end OriginalUnitIso

section Ordinary

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  {E : Type uE} [Category.{vE} E] (Q : C ⥤ E) (L : D ⥤ E) (R : E ⥤ D)
  (adj : L ⊣ R) (α : (Q ⋙ R) ⋙ L ≅ Q)
  (hα : α.hom = (Functor.associator Q R L).hom ≫
    Functor.whiskerLeft Q adj.counit ≫ (Functor.rightUnitor Q).hom)

include hα in
/-- The original underived counit comparison cancels the original unit. -/
theorem postcompCounit_unit (M : C) :
    adj.unit.app (R.obj (Q.obj M)) ≫ R.map (α.hom.app M) = 𝟙 _ := by
  have ha : α.hom.app M = adj.counit.app (Q.obj M) := by
    rw [hα]
    change 𝟙 _ ≫ adj.counit.app (Q.obj M) ≫ 𝟙 _ = _
    simp only [Category.id_comp, Category.comp_id]
  rw [ha]
  exact adj.right_triangle_components (Q.obj M)

end Ordinary

section OrdinaryUnitIso

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  {E : Type uE} [Category.{vE} E] (Q : C ⥤ E) (L : D ⥤ E) (R : E ⥤ D)
  (adj : L ⊣ R) (ε : 𝟭 E ≅ R ⋙ L)
  (hε : Functor.whiskerRight ε.hom R = Functor.whiskerLeft R adj.unit)

include hε in
/-- The original unit Iso comparison has its original underived unit value. -/
theorem postcompUnitIso_unit (M : C) :
    let α := Functor.associator Q R L ≪≫ Functor.isoWhiskerLeft Q ε.symm ≪≫ Functor.rightUnitor Q
    adj.unit.app (R.obj (Q.obj M)) ≫ R.map (α.hom.app M) = 𝟙 _ :=
  postcompCounit_unit Q L R adj
    (Functor.associator Q R L ≪≫ Functor.isoWhiskerLeft Q ε.symm ≪≫ Functor.rightUnitor Q)
    (postcompUnitIso_comparison_hom L R adj ε hε Q) M

end OrdinaryUnitIso

section Derived

variable {C : Type uC} [Category.{vC} C] [Abelian C] [EnoughInjectives C]
  {D : Type uD} [Category.{vD} D] [Abelian D]
  {E : Type uE} [Category.{vE} E] [Abelian E]
  (P : C ⥤ D) (L : D ⥤ E) (Q : C ⥤ E)
  [P.Additive] [L.Additive] [L.PreservesHomology] [Q.Additive]
  (α : P ⋙ L ≅ Q)

/-- The existing postcomposition/ordinary comparison retains the actual zero unit. -/
@[reassoc]
theorem rightDerivedPostcompIso_comparison_zero_unit (M : C) :
    L.map (P.toRightDerivedZero.app M) ≫
        ((Functor.rightDerivedPostcompIso P L 0).symm ≪≫
          Functor.rightDerivedNatIsoOfAdditive α 0).hom.app M =
      α.hom.app M ≫ Q.toRightDerivedZero.app M := by
  let d := (Sheaf.ModuleCoefficients.rightDerivedPostcompIso P L 0).app M
  have hp : (P ⋙ L).toRightDerivedZero.app M ≫ d.hom =
      L.map (P.toRightDerivedZero.app M) :=
    Sheaf.ModuleCoefficients.toRightDerivedZero_postcomp P L M
  change L.map (P.toRightDerivedZero.app M) ≫
    d.inv ≫ (NatTrans.rightDerived α.hom 0).app M = _
  have hc : ((P ⋙ L).toRightDerivedZero.app M ≫ d.hom) ≫
      d.inv ≫ (NatTrans.rightDerived α.hom 0).app M =
      (P ⋙ L).toRightDerivedZero.app M ≫ (NatTrans.rightDerived α.hom 0).app M :=
    (Category.assoc _ _ _).trans
      (congrArg (fun k => (P ⋙ L).toRightDerivedZero.app M ≫ k)
        (d.hom_inv_id_assoc ((NatTrans.rightDerived α.hom 0).app M)))
  exact (congrArg (fun k => k ≫ d.inv ≫ (NatTrans.rightDerived α.hom 0).app M)
    hp.symm).trans (hc.trans (Sheaf.ModuleCoefficients.toRightDerivedZero_naturality α.hom M))

end Derived

section CounitTranspose

variable {C : Type uC} [Category.{vC} C] [Abelian C] [EnoughInjectives C]
  {D : Type uD} [Category.{vD} D] [Abelian D]
  {E : Type uE} [Category.{vE} E] [Abelian E]
  (Q : C ⥤ E) (L : D ⥤ E) (R : E ⥤ D)
  [Q.Additive] [(Q ⋙ R).Additive] [L.Additive] [L.PreservesHomology]
  (adj : L ⊣ R) (α : (Q ⋙ R) ⋙ L ≅ Q)
  (hα : α.hom = (Functor.associator Q R L).hom ≫
    Functor.whiskerLeft Q adj.counit ≫ (Functor.rightUnitor Q).hom)

include hα in
/-- The whole actual derived transpose retains the original zero unit before evaluation. -/
theorem rightDerivedPostcompIso_transpose_zero_unit :
    let β := (Functor.rightDerivedPostcompIso (Q ⋙ R) L 0).symm ≪≫
      Functor.rightDerivedNatIsoOfAdditive α 0
    (Q ⋙ R).toRightDerivedZero ≫
        (Adjunction.whiskerRight C adj).homEquiv ((Q ⋙ R).rightDerived 0) (Q.rightDerived 0) β.hom =
      Functor.whiskerRight Q.toRightDerivedZero R := by
  dsimp only
  rw [Sheaf.ModuleCoefficients.rightDerivedPostcompIso_transpose_eq]
  apply NatTrans.ext
  funext M
  let β := (Functor.rightDerivedPostcompIso (Q ⋙ R) L 0).symm ≪≫
    Functor.rightDerivedNatIsoOfAdditive α 0
  have hz := rightDerivedPostcompIso_comparison_zero_unit (Q ⋙ R) L Q α M
  have hpaste : (Q ⋙ R).toRightDerivedZero.app M ≫
      adj.unit.app (((Q ⋙ R).rightDerived 0).obj M) ≫ R.map (β.hom.app M) =
      adj.unit.app ((Q ⋙ R).obj M) ≫ R.map (α.hom.app M) ≫
        R.map (Q.toRightDerivedZero.app M) := by
    rw [← Category.assoc, ← adj.unit_naturality, Category.assoc,
      ← R.map_comp, hz, R.map_comp]
  have hcancel : adj.unit.app ((Q ⋙ R).obj M) ≫ R.map (α.hom.app M) ≫
      R.map (Q.toRightDerivedZero.app M) = R.map (Q.toRightDerivedZero.app M) := by
    simp only [Functor.comp_obj]
    rw [← Category.assoc, postcompCounit_unit Q L R adj α hα M, Category.id_comp]
  exact hpaste.trans hcancel

end CounitTranspose

section OriginalUnitTranspose

variable {C : Type uC} [Category.{vC} C] [Abelian C] [EnoughInjectives C]
  {D : Type uD} [Category.{vD} D] [Abelian D]
  {E : Type uE} [Category.{vE} E] [Abelian E]
  (Q : C ⥤ E) (L : D ⥤ E) (R : E ⥤ D)
  [Q.Additive] [(Q ⋙ R).Additive] [L.Additive] [L.PreservesHomology]
  (adj : L ⊣ R) (ε : 𝟭 E ≅ R ⋙ L)
  (hε : Functor.whiskerRight ε.hom R = Functor.whiskerLeft R adj.unit)

include hε in
/-- The complete original unit-Iso construction gives the whole derived transpose zero unit. -/
theorem rightDerivedPostcompUnitIso_transpose_zero_unit :
    let α := Functor.associator Q R L ≪≫ Functor.isoWhiskerLeft Q ε.symm ≪≫ Functor.rightUnitor Q
    let β := (Functor.rightDerivedPostcompIso (Q ⋙ R) L 0).symm ≪≫
      Functor.rightDerivedNatIsoOfAdditive α 0
    (Q ⋙ R).toRightDerivedZero ≫
        (Adjunction.whiskerRight C adj).homEquiv ((Q ⋙ R).rightDerived 0) (Q.rightDerived 0) β.hom =
      Functor.whiskerRight Q.toRightDerivedZero R :=
  rightDerivedPostcompIso_transpose_zero_unit Q L R adj
    (Functor.associator Q R L ≪≫ Functor.isoWhiskerLeft Q ε.symm ≪≫ Functor.rightUnitor Q)
    (postcompUnitIso_comparison_hom L R adj ε hε Q)

end OriginalUnitTranspose

end CategoryTheory.Functor
