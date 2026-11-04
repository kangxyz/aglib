/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Adjunction.SingleCounit

/-! The original adjunct of maps between original degree-zero singles. -/

@[expose] public noncomputable section

open CategoryTheory

namespace CategoryTheory.Adjunction

variable {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
  [HasDerivedCategory A] [HasDerivedCategory B] [EnoughInjectives A] [EnoughInjectives B]
  {L : A ⥤ B} {R : B ⥤ A} [L.Additive] [R.Additive] [L.PreservesHomology]
  (adj : L ⊣ R)

/-- The adjunct on the original singles uses the original underived
adjunct and the original right-derived single unit. -/
theorem rightDerivedFunctorPlus_homEquiv_single {U : A} {M : B} (f : L.obj U ⟶ M) :
    let A₀ := (DerivedCategory.Plus.singleFunctor A 0).obj U
    let B₀ := (DerivedCategory.Plus.singleFunctor B 0).obj M
    adj.rightDerivedFunctorPlus.homEquiv A₀ B₀
        ((L.rightDerivedFunctorPlusSingleIso 0).hom.app U ≫
          (DerivedCategory.Plus.singleFunctor B 0).map f) =
      (DerivedCategory.Plus.singleFunctor A 0).map (adj.homEquiv U M f) ≫
        R.rightDerivedSingleUnit M := by
  intro A₀ B₀
  let S := DerivedCategory.Plus.singleFunctor A 0
  let T := DerivedCategory.Plus.singleFunctor B 0
  let a := L.rightDerivedFunctorPlusSingleIso 0
  let d := adj.rightDerivedFunctorPlus
  let g := adj.homEquiv U M f
  have h : L.map g ≫ adj.counit.app M = f :=
    (adj.homEquiv_counit U M g).symm.trans ((adj.homEquiv U M).symm_apply_apply f)
  have hn : L.rightDerivedFunctorPlus.map (S.map g) ≫ a.hom.app (R.obj M) =
      a.hom.app U ≫ T.map (L.map g) := a.hom.naturality g
  change d.homEquiv A₀ B₀ (a.hom.app U ≫ T.map f) = S.map g ≫ R.rightDerivedSingleUnit M
  apply (d.homEquiv A₀ B₀).symm.injective
  rw [Equiv.symm_apply_apply, d.homEquiv_counit, L.rightDerivedFunctorPlus.map_comp,
    Category.assoc, adj.rightDerivedSingleUnit_counit M,
    reassoc_of% hn]
  change a.hom.app U ≫ T.map f = a.hom.app U ≫ T.map (L.map g) ≫ T.map (adj.counit.app M)
  have ht : T.map (L.map g) ≫ T.map (adj.counit.app M) = T.map f :=
    (T.map_comp _ _).symm.trans (congrArg T.map h)
  exact (congrArg (fun z => a.hom.app U ≫ z) ht).symm

end CategoryTheory.Adjunction
