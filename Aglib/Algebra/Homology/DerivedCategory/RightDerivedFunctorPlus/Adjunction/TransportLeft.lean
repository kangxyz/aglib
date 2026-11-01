/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Adjunction
public import
  Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Adjunction.ComparisonSquares

/-! # Original derived adjunction units under left-functor transport -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Functor
namespace CategoryTheory.Adjunction
universe u v d u' v' d'
variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{d} A]
  [EnoughInjectives A] {B : Type u'} [Category.{v'} B] [Abelian B]
  [HasDerivedCategory.{d'} B] [EnoughInjectives B]
  {F F' : A ⥤ B} {G : B ⥤ A} [F.Additive] [F'.Additive] [G.Additive]
  [F.PreservesHomology] [F'.PreservesHomology] (adj : F ⊣ G) (e : F ≅ F')

/-- Deriving the transported original adjunction preserves its actual transported unit. -/
theorem rightDerivedFunctorPlus_ofNatIsoLeft_unit :
    (adj.ofNatIsoLeft e).rightDerivedFunctorPlus.unit =
      adj.rightDerivedFunctorPlus.unit ≫
        whiskerRight (F.rightDerivedFunctorPlusIso e).hom G.rightDerivedFunctorPlus := by
  apply Localization.natTrans_ext DerivedCategory.Plus.Q (CochainComplex.Plus.quasiIso A)
  intro K
  dsimp only [NatTrans.comp_app, whiskerRight_app]
  have hs : (F.rightDerivedFunctorPlusIso e).hom.app (DerivedCategory.Plus.Q.obj K) ≫
      F'.rightDerivedFunctorPlusExactComparison.hom.app K =
    F.rightDerivedFunctorPlusExactComparison.hom.app K ≫
      DerivedCategory.Plus.Q.map ((NatIso.mapCochainComplexPlus e).hom.app K) := by
    apply (cancel_epi (F.rightDerivedFunctorPlusExactComparison.inv.app K)).1
    have h := F.rightDerivedFunctorPlusIso_hom_app e K
    rw [← rightDerivedFunctorPlusExactComparison_inv_app] at h
    rw [← Category.assoc, h]
    simp only [Category.assoc, ← rightDerivedFunctorPlusExactComparison_inv_app,
      Iso.inv_hom_id_app, Iso.inv_hom_id_app_assoc]
    simpa only [Functor.comp_obj] using
      (Category.comp_id (DerivedCategory.Plus.Q.map
        ((NatIso.mapCochainComplexPlus e).hom.app K)))
  apply (cancel_mono (G.rightDerivedFunctorPlus.map
    (F'.rightDerivedFunctorPlusExactComparison.hom.app K))).1
  rw [(adj.ofNatIsoLeft e).rightDerivedFunctorPlus_unit_fac]
  rw [Category.assoc, ← Functor.map_comp, hs, Functor.map_comp,
    ← Category.assoc, adj.rightDerivedFunctorPlus_unit_fac, Category.assoc]
  have hn := G.rightDerivedFunctorPlusUnit.naturality
    ((NatIso.mapCochainComplexPlus e).hom.app K)
  dsimp only [Functor.comp_map] at hn
  rw [← hn, ← Category.assoc, ← Functor.map_comp]
  congr 2

end CategoryTheory.Adjunction
