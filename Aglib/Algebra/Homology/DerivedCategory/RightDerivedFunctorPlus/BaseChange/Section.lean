/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.SingleCoherence
public import Aglib.Algebra.Homology.DerivedCategory.Plus.ExtTransport
public import Aglib.CategoryTheory.Adjunction.SectionTrace

/-! Original single comparison transport of a complete coefficient section law. -/

@[expose] public noncomputable section

open CategoryTheory

namespace CategoryTheory.Functor

variable {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
  [HasDerivedCategory A] [HasDerivedCategory B] [EnoughInjectives A] [EnoughInjectives B]
  (F : A ⥤ B) (G : B ⥤ A) (H : A ⥤ A)
  [F.Additive] [G.Additive] [H.Additive]
  [F.PreservesHomology] [G.PreservesHomology] [H.PreservesHomology]

/-- The same native composite comparison transports a complete original coefficient loop. -/
theorem rightDerivedFunctorPlusSingleIsoOfIso_section
    (c : H ≅ F ⋙ G) (e : H ≅ 𝟭 A) {M : A} {N : B}
    (a : F.obj M ≅ N) (b : G.obj N ≅ M)
    (h : c.hom.app M ≫ G.map a.hom ≫ b.hom = e.hom.app M) :
    (H.rightDerivedFunctorPlusIso c ≪≫
        rightDerivedFunctorPlusCompIsoOfPreservesHomology F G).hom.app
          ((DerivedCategory.Plus.singleFunctor A 0).obj M) ≫
      G.rightDerivedFunctorPlus.map (F.rightDerivedFunctorPlusSingleIsoOfIso 0 a).hom ≫
      (G.rightDerivedFunctorPlusSingleIsoOfIso 0 b).hom =
    (H.rightDerivedFunctorPlusIso e ≪≫ rightDerivedFunctorPlusIdIso A).hom.app
      ((DerivedCategory.Plus.singleFunctor A 0).obj M) := by
  let SA := DerivedCategory.Plus.singleFunctor A 0
  let SB := DerivedCategory.Plus.singleFunctor B 0
  let aF := (F.rightDerivedFunctorPlusSingleIso 0).hom.app M
  let aG := (G.rightDerivedFunctorPlusSingleIso 0).hom.app (F.obj M)
  let bG := (G.rightDerivedFunctorPlusSingleIso 0).hom.app N
  let aH := (H.rightDerivedFunctorPlusSingleIso 0).hom.app M
  let d := H.rightDerivedFunctorPlusIso c ≪≫
    rightDerivedFunctorPlusCompIsoOfPreservesHomology F G
  let i := H.rightDerivedFunctorPlusIso e ≪≫ rightDerivedFunctorPlusIdIso A
  have hn := (G.rightDerivedFunctorPlusSingleIso 0).hom.naturality a.hom
  change G.rightDerivedFunctorPlus.map (SB.map a.hom) ≫ bG =
    aG ≫ SA.map (G.map a.hom) at hn
  have hc := rightDerivedFunctorPlusSingleIso_comp F G H c M
  change d.hom.app (SA.obj M) ≫ G.rightDerivedFunctorPlus.map aF ≫ aG =
    aH ≫ SA.map (c.hom.app M) at hc
  have hi := rightDerivedFunctorPlusSingleIso_id H e M
  change i.hom.app (SA.obj M) = aH ≫ SA.map (e.hom.app M) at hi
  change d.hom.app (SA.obj M) ≫
    G.rightDerivedFunctorPlus.map (aF ≫ SB.map a.hom) ≫ bG ≫ SA.map b.hom =
      i.hom.app (SA.obj M)
  rw [G.rightDerivedFunctorPlus.map_comp]
  simp only [Category.assoc]
  rw [reassoc_of% hn, reassoc_of% hc]
  simp only [← SA.map_comp]
  rw [h]
  exact hi.symm

end CategoryTheory.Functor

namespace CategoryTheory.Functor

variable {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
  [HasDerivedCategory A] [HasDerivedCategory B] [EnoughInjectives A] [EnoughInjectives B]
  (F : A ⥤ B) (G : B ⥤ A) [F.Additive] [G.Additive]
  [F.PreservesHomology] [G.PreservesHomology]
  {J : Type*} (P : J → A ⥤ A)
  [∀ j, (P j).Additive] [∀ j, (P j).PreservesHomology]


/-- Consume the original coefficient family before specializing its section index. -/
theorem rightDerivedFunctorPlusSingleIsoOfIso_section_of_original_family
    {j k : J} (hjk : j = k) (c : P j ≅ F ⋙ G) (e : P k ≅ 𝟭 A)
    {M : A} {N : B} (a : F.obj M ≅ N) (b : G.obj N ≅ M)
    (q : ∀ j, (P j).obj M ≅ M)
    (hc : c.hom.app M ≫ G.map a.hom ≫ b.hom = (q j).hom)
    (hi : (q k).hom = e.hom.app M) :
    ((P j).rightDerivedFunctorPlusIso c ≪≫
        rightDerivedFunctorPlusCompIsoOfPreservesHomology F G).hom.app
          ((DerivedCategory.Plus.singleFunctor A 0).obj M) ≫
      G.rightDerivedFunctorPlus.map (F.rightDerivedFunctorPlusSingleIsoOfIso 0 a).hom ≫
      (G.rightDerivedFunctorPlusSingleIsoOfIso 0 b).hom =
    (eqToIso (congrArg (fun j => (P j).rightDerivedFunctorPlus) hjk) ≪≫
      (P k).rightDerivedFunctorPlusIso e ≪≫ rightDerivedFunctorPlusIdIso A).hom.app
        ((DerivedCategory.Plus.singleFunctor A 0).obj M) := by
  cases hjk
  simpa only [eqToIso_refl, Iso.refl_trans] using
    rightDerivedFunctorPlusSingleIsoOfIso_section F G (P j) c e a b (hc.trans hi)

/-- Retain actual comparison and coefficient aliases while deriving the original section law. -/
theorem rightDerivedSingle_sectionValue_of_original_family
    {j k : J} (hjk : j = k) (c : P j ≅ F ⋙ G) (e : P k ≅ 𝟭 A)
    {M : A} {N : B} (a : F.obj M ≅ N) (b : G.obj N ≅ M)
    (q : ∀ j, (P j).obj M ≅ M)
    (hc : c.hom.app M ≫ G.map a.hom ≫ b.hom = (q j).hom)
    (hi : (q k).hom = e.hom.app M)
    (cD : (P j).rightDerivedFunctorPlus ≅ F.rightDerivedFunctorPlus ⋙ G.rightDerivedFunctorPlus)
    (iD : (P j).rightDerivedFunctorPlus ≅ 𝟭 (DerivedCategory.Plus A))
    (aD : F.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor A 0).obj M) ≅
      (DerivedCategory.Plus.singleFunctor B 0).obj N)
    (bD : G.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor B 0).obj N) ≅
      (DerivedCategory.Plus.singleFunctor A 0).obj M)
    (hcD : cD = (P j).rightDerivedFunctorPlusIso c ≪≫
      rightDerivedFunctorPlusCompIsoOfPreservesHomology F G)
    (hiD : iD = eqToIso (congrArg (fun j => (P j).rightDerivedFunctorPlus) hjk) ≪≫
      (P k).rightDerivedFunctorPlusIso e ≪≫ rightDerivedFunctorPlusIdIso A)
    (haD : aD = F.rightDerivedFunctorPlusSingleIsoOfIso 0 a)
    (hbD : bD = G.rightDerivedFunctorPlusSingleIsoOfIso 0 b) :
    SectionCoefficientValue F.rightDerivedFunctorPlus G.rightDerivedFunctorPlus cD iD aD bD := by
  subst cD
  subst iD
  subst aD
  subst bD
  exact rightDerivedFunctorPlusSingleIsoOfIso_section_of_original_family
    F G P hjk c e a b q hc hi

end CategoryTheory.Functor
