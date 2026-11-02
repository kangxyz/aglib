/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.CategoryTheory.Adjunction.TripleLocalization
public import Mathlib.CategoryTheory.Adjunction.Mates

/-! # Original conjugate comparisons preserve the canonical outer-adjoint map -/
@[expose] public noncomputable section
open CategoryTheory.Functor
namespace CategoryTheory.Adjunction
variable {A B : Type*} [Category* A] [Category* B]
  {J S J' S' : A ⥤ B} {U U' : B ⥤ A}
  (t : Triple J U S) (t' : Triple J' U' S')
  [J.Full] [J.Faithful] [J'.Full] [J'.Faithful]

/-- The complete original outer-adjoint square under specified comparisons. -/
def TripleTransportEquation (eJ : J ≅ J') (eS : S ≅ S') : Prop :=
  eJ.hom ≫ t'.leftToRight = t.leftToRight ≫ eS.hom

/-- Both original adjunction conjugacies preserve the same canonical triple map. -/
theorem Triple.leftToRight_transport (eJ : J ≅ J') (eU : U ≅ U') (eS : S ≅ S')
    (hJ : conjugateEquiv t'.adj₁ t.adj₁ eJ.hom = eU.inv)
    (hU : conjugateEquiv t'.adj₂ t.adj₂ eU.hom = eS.inv) :
    TripleTransportEquation t t' eJ eS := by
  have h₁ (X : A) : t'.adj₁.unit.app X =
      t.adj₁.unit.app X ≫ eU.hom.app (J.obj X) ≫ U'.map (eJ.hom.app X) := by
    have h := unit_conjugateEquiv t'.adj₁ t.adj₁ eJ.hom X
    rw [hJ] at h
    have h' := congrArg (fun z => z ≫ eU.hom.app (J'.obj X)) h
    simp only [Category.assoc, Iso.inv_hom_id_app] at h'
    rw [eU.hom.naturality] at h'
    exact (Category.comp_id _).symm.trans h'
  have h₂ (Y : B) : t'.adj₂.unit.app Y =
      t.adj₂.unit.app Y ≫ eS.hom.app (U.obj Y) ≫ S'.map (eU.hom.app Y) := by
    have h := unit_conjugateEquiv t'.adj₂ t.adj₂ eU.hom Y
    rw [hU] at h
    have h' := congrArg (fun z => z ≫ eS.hom.app (U'.obj Y)) h
    simp only [Category.assoc, Iso.inv_hom_id_app] at h'
    rw [eS.hom.naturality] at h'
    exact (Category.comp_id _).symm.trans h'
  apply NatTrans.ext
  funext X
  exact Triple.leftToRight_normalized t t' (𝟭 A) (𝟭 B)
    eJ.hom eU.hom eS.hom h₁ h₂ t.leftToRight t.leftToRight_app_map_adj₁_unit_app X
end CategoryTheory.Adjunction
