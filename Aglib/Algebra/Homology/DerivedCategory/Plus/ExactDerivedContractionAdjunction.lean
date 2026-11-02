/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.Plus.ExactDerivedContractionModels
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Adjunction
public import
  Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Adjunction.ComparisonSquares

/-! # The original derived contraction is the inverse adjunction unit

The endpoint and middle derived models remain independent. The normalization
hypothesis concerns the original ordinary adjunction, not a new derived equivalence.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Functor
namespace DerivedCategory.Plus
universe u v d u' v' d'
variable {A : Type u} [Category.{v} A] [Abelian A] [EnoughInjectives A]
  [HasDerivedCategory.{d} A]
  {B : Type u'} [Category.{v'} B] [Abelian B] [EnoughInjectives B]
  [HasDerivedCategory.{d'} B]
  (F : A ⥤ B) (G : B ⥤ A) [F.Additive] [G.Additive]
  [F.PreservesHomology] [G.PreservesHomology]
  (adj : F ⊣ G) (e : F ⋙ G ≅ 𝟭 A)
  (he : ∀ M, adj.unit.app M ≫ e.hom.app M = 𝟙 M)

include he

omit [EnoughInjectives A] [HasDerivedCategory A] [EnoughInjectives B]
  [HasDerivedCategory B] [F.PreservesHomology] [G.PreservesHomology] in
/-- The original ordinary unit-contraction equation holds degreewise on bounded-below complexes. -/
theorem exactContraction_complex_unit (K : CochainComplex.Plus A) :
    adj.mapCochainComplexPlus.unit.app K ≫
      (NatIso.mapCochainComplexPlus e).hom.app K ≫
      (mapCochainComplexPlusIdIso A).hom.app K = 𝟙 K := by
  apply ObjectProperty.hom_ext
  ext n
  change adj.unit.app (K.obj.X n) ≫ e.hom.app (K.obj.X n) ≫ 𝟙 _ = 𝟙 _
  simpa only [Category.comp_id, Functor.id_obj] using he (K.obj.X n)

/-- The original derived adjunction unit contracts through the original derived comparison. -/
theorem exactDerivedContractionViaIso_adjunction_unit :
    adj.rightDerivedFunctorPlus.unit ≫ (exactDerivedContractionViaIso F G e).hom =
      𝟙 (𝟭 (DerivedCategory.Plus A)) := by
  apply Localization.natTrans_ext DerivedCategory.Plus.Q (CochainComplex.Plus.quasiIso A)
  intro K
  change adj.rightDerivedFunctorPlus.unit.app (DerivedCategory.Plus.Q.obj K) ≫
    (exactDerivedContractionViaIso F G e).hom.app (DerivedCategory.Plus.Q.obj K) = _
  have h := congrArg
    (fun z => z ≫ G.rightDerivedFunctorPlus.map
      (F.rightDerivedFunctorPlusExactComparison.inv.app K) ≫
      (exactDerivedContractionViaIso F G e).hom.app (DerivedCategory.Plus.Q.obj K))
    (adj.rightDerivedFunctorPlus_unit_fac K)
  simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id_app] at h
  have hm := G.rightDerivedFunctorPlus.map_id
    ((DerivedCategory.Plus.Q (C := A) ⋙ F.rightDerivedFunctorPlus).obj K)
  rw [hm] at h
  have hid := Category.id_comp
    ((exactDerivedContractionViaIso F G e).hom.app (DerivedCategory.Plus.Q.obj K))
  dsimp only [Functor.comp_obj] at h hid
  rw [hid] at h
  rw [rightDerivedFunctorPlusExactComparison_inv_app] at h
  have hc := exactDerivedContractionViaIso_unit F G e K
  rw [rightDerivedFunctorPlusCompUnit_app] at hc
  rw [Category.assoc] at hc
  rw [hc] at h
  rw [← Functor.map_comp] at h
  rw [exactContraction_complex_unit F G adj e he K,
    (DerivedCategory.Plus.Q (C := A)).map_id K] at h
  exact h

/-- The same comparison identifies the inverse of the original derived adjunction unit. -/
theorem exactDerivedContractionViaIso_adjunction_unit_eq_inv :
    adj.rightDerivedFunctorPlus.unit = (exactDerivedContractionViaIso F G e).inv := by
  apply (cancel_mono (exactDerivedContractionViaIso F G e).hom).1
  simpa only [Iso.inv_hom_id] using
    exactDerivedContractionViaIso_adjunction_unit F G adj e he

end DerivedCategory.Plus
