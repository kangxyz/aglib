/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.DirectImage
public import Aglib.AlgebraicGeometry.EtaleCohomology.H0.UnitEndRestriction
public import Mathlib.CategoryTheory.Functor.FullyFaithful
public import Mathlib.CategoryTheory.NatIso

/-! Detection of original derived unit endomorphisms by inverse image. -/

open CategoryTheory

@[expose] public noncomputable section

namespace CategoryTheory.Functor

/-- A comparison on a full source detects its original endomorphisms
whenever the original coefficient functor detects their preimages. -/
private theorem map_injective_end_of_comparison
    {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
    (S : A ⥤ B) (T : C ⥤ D) (F : B ⥤ D) (G : A ⥤ C)
    [S.Full] [T.Faithful] (i : S ⋙ F ≅ G ⋙ T) (M : A)
    (hG : Function.Injective (fun f : M ⟶ M => G.map f)) :
    Function.Injective (fun f : S.obj M ⟶ S.obj M => F.map f) := by
  intro a b h
  let x := S.preimage a
  let y := S.preimage b
  have hx : F.map a ≫ i.hom.app M = i.hom.app M ≫ T.map (G.map x) := by
    have e := i.hom.naturality x
    change F.map (S.map x) ≫ i.hom.app M = i.hom.app M ≫ T.map (G.map x) at e
    rw [S.map_preimage] at e
    exact e
  have hy : F.map b ≫ i.hom.app M = i.hom.app M ≫ T.map (G.map y) := by
    have e := i.hom.naturality y
    change F.map (S.map y) ≫ i.hom.app M = i.hom.app M ≫ T.map (G.map y) at e
    rw [S.map_preimage] at e
    exact e
  have hg : G.map x = G.map y := T.map_injective <| (cancel_epi (i.hom.app M)).mp <|
    hx.symm.trans ((congrArg (fun f => f ≫ i.hom.app M) h).trans hy)
  exact (S.map_preimage a).symm.trans ((congrArg S.map (hG hg)).trans (S.map_preimage b))

end CategoryTheory.Functor

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients

universe u wX wT

attribute [local instance] hasSheafifyLarge hasSheafifyModules
  CategoryTheory.TorsionZMod.Ringed.abWEqualsLocallyBijectiveStandard

variable {X T : Scheme.{u}}
  [ConnectedSpace X] [CompactSpace X] [QuasiSeparatedSpace X]
  [ConnectedSpace T] [CompactSpace T] [QuasiSeparatedSpace T] (f : T ⟶ X)
  (Λ : Type (u + 1)) [Ring Λ]
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wT} (ModuleSheaf T Λ)]

/-- The original inverse image detects endomorphisms of the original derived torsion unit. -/
theorem moduleDerivedInverseImage_map_injective_singleUnit_end
    (hΛ : IsAddTorsion (AddCommGrpCat.of Λ)) :
    let U := (DerivedCategory.Plus.singleFunctor (ModuleSheaf X Λ) 0).obj (moduleUnit X Λ)
    Function.Injective (fun a : U ⟶ U => (moduleDerivedInverseImage Λ f).map a) := by
  let : (DerivedCategory.Plus.singleFunctor (ModuleSheaf X Λ) 0).Full :=
    Functor.Full.of_comp_faithful_iso (DerivedCategory.Plus.singleFunctorιIso (ModuleSheaf X Λ) 0)
  let : (DerivedCategory.Plus.singleFunctor (ModuleSheaf T Λ) 0).Faithful :=
    Functor.Faithful.of_comp_iso (DerivedCategory.Plus.singleFunctorιIso (ModuleSheaf T Λ) 0)
  exact Functor.map_injective_end_of_comparison
    (DerivedCategory.Plus.singleFunctor (ModuleSheaf X Λ) 0)
    (DerivedCategory.Plus.singleFunctor (ModuleSheaf T Λ) 0)
    (moduleDerivedInverseImage Λ f) (moduleInverseImage f Λ)
    ((moduleInverseImage f Λ).rightDerivedFunctorPlusSingleIso 0)
    (moduleUnit X Λ) (moduleInverseImage_map_injective_unit_end f Λ hΛ)

end AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients
