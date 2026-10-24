/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.ZeroComparison
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.TStructure
public import Aglib.Algebra.Homology.DerivedCategory.Plus.SingleTriangleNaturality

/-!
# The original derived single unit on short exact coefficient diagrams

The actual single coefficient maps followed by the installed native single
unit form a morphism of the original short-exact triangles. A third-arrow
completion is unique because the target derived single is nonnegative and
the source first single shifted by one is strictly negative. No exactness
or preservation of injective objects by the original functor is assumed.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open HomologicalComplex

universe u v w u' v' w'

namespace CategoryTheory.Functor

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
  [EnoughInjectives A]
  {B : Type u'} [Category.{v'} B] [Abelian B] [HasDerivedCategory.{w'} B]
  (G : A ⥤ B) [G.Additive]

/-- Naturality of the existing native single unit, without constructing another unit. -/
@[reassoc]
theorem rightDerivedSingleUnit_naturality {M N : A} (f : M ⟶ N) :
    (DerivedCategory.Plus.singleFunctor B 0).map (G.map f) ≫ G.rightDerivedSingleUnit N =
      G.rightDerivedSingleUnit M ≫
        G.rightDerivedFunctorPlus.map ((DerivedCategory.Plus.singleFunctor A 0).map f) := by
  let SA := CochainComplex.singleFunctorPlus A 0
  let SB := CochainComplex.singleFunctorPlus B 0
  let Q : CochainComplex.Plus B ⥤ DerivedCategory.Plus B := DerivedCategory.Plus.Q
  let τ (P : A) : SB.obj (G.obj P) ⟶ G.mapCochainComplexPlus.obj (SA.obj P) :=
    ObjectProperty.homMk ((singleMapHomologicalComplex G (.up ℤ) 0).inv.app P)
  have hτ : SB.map (G.map f) ≫ τ N = τ M ≫ G.mapCochainComplexPlus.map (SA.map f) := by
    apply ObjectProperty.hom_ext
    exact (singleMapHomologicalComplex G (.up ℤ) 0).inv.naturality f
  have hη := G.rightDerivedFunctorPlusUnit.naturality (SA.map f)
  change Q.map (G.mapCochainComplexPlus.map (SA.map f)) ≫
      G.rightDerivedFunctorPlusUnit.app (SA.obj N) =
    G.rightDerivedFunctorPlusUnit.app (SA.obj M) ≫
      G.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map (SA.map f)) at hη
  change Q.map (SB.map (G.map f)) ≫
      (Q.map (τ N) ≫ G.rightDerivedFunctorPlusUnit.app (SA.obj N)) =
    (Q.map (τ M) ≫ G.rightDerivedFunctorPlusUnit.app (SA.obj M)) ≫
      G.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map (SA.map f))
  rw [← Category.assoc, ← Q.map_comp, hτ, Q.map_comp, Category.assoc, hη]
  simp only [Category.assoc]

/-- A commuting original coefficient square remains commuting after the actual single unit. -/
theorem rightDerivedSingleUnit_coefficient_naturality
    {M M' : B} {N N' : A}
    (φ : M ⟶ G.obj N) (φ' : M' ⟶ G.obj N')
    (f : M ⟶ M') (g : N ⟶ N') (h : f ≫ φ' = φ ≫ G.map g) :
    (DerivedCategory.Plus.singleFunctor B 0).map f ≫
        ((DerivedCategory.Plus.singleFunctor B 0).map φ' ≫ G.rightDerivedSingleUnit N') =
      ((DerivedCategory.Plus.singleFunctor B 0).map φ ≫ G.rightDerivedSingleUnit N) ≫
        G.rightDerivedFunctorPlus.map ((DerivedCategory.Plus.singleFunctor A 0).map g) := by
  let S := DerivedCategory.Plus.singleFunctor B 0
  rw [← Category.assoc, ← S.map_comp, h, S.map_comp, Category.assoc,
    G.rightDerivedSingleUnit_naturality g]
  simp only [Category.assoc, S]

variable (S : ShortComplex B) (T : ShortComplex A)
  (hS : S.ShortExact) (hT : T.ShortExact) (φ : S ⟶ T.map G)

/-- The three actual coefficient units satisfy the original third-arrow equation.
The triangulated completion is identified with the specified third unit. -/
theorem rightDerivedSingleUnit_singleTriangle_comm₃ :
    hS.singleTrianglePlus.mor₃ ≫
        ((DerivedCategory.Plus.singleFunctor B 0).map φ.τ₁ ≫
          G.rightDerivedSingleUnit T.X₁)⟦(1 : ℤ)⟧' =
      ((DerivedCategory.Plus.singleFunctor B 0).map φ.τ₃ ≫
        G.rightDerivedSingleUnit T.X₃) ≫
          (G.rightDerivedFunctorPlus.mapTriangle.obj hT.singleTrianglePlus).mor₃ := by
  let TS := hS.singleTrianglePlus
  let TT := G.rightDerivedFunctorPlus.mapTriangle.obj hT.singleTrianglePlus
  let d₁ : TS.obj₁ ⟶ TT.obj₁ := (DerivedCategory.Plus.singleFunctor B 0).map φ.τ₁ ≫
    G.rightDerivedSingleUnit T.X₁
  let d₂ : TS.obj₂ ⟶ TT.obj₂ := (DerivedCategory.Plus.singleFunctor B 0).map φ.τ₂ ≫
    G.rightDerivedSingleUnit T.X₂
  let d₃ : TS.obj₃ ⟶ TT.obj₃ := (DerivedCategory.Plus.singleFunctor B 0).map φ.τ₃ ≫
    G.rightDerivedSingleUnit T.X₃
  have hTS : TS ∈ distTriang _ := hS.singleTrianglePlus_distinguished
  have hTT : TT ∈ distTriang _ :=
    G.rightDerivedFunctorPlus.map_distinguished hT.singleTrianglePlus
      hT.singleTrianglePlus_distinguished
  have h₁₂ : TS.mor₁ ≫ d₂ = d₁ ≫ TT.mor₁ :=
    G.rightDerivedSingleUnit_coefficient_naturality φ.τ₁ φ.τ₂ S.f T.f φ.comm₁₂.symm
  have h₂₃ : TS.mor₂ ≫ d₃ = d₂ ≫ TT.mor₂ :=
    G.rightDerivedSingleUnit_coefficient_naturality φ.τ₂ φ.τ₃ S.g T.g φ.comm₂₃.symm
  obtain ⟨c, hc₂, hc₃⟩ :=
    complete_distinguished_triangle_morphism TS TT hTS hTT d₁ d₂ h₁₂
  have hz : TS.mor₂ ≫ (c - d₃) = 0 := by
    rw [Preadditive.comp_sub, hc₂, h₂₃, sub_self]
  obtain ⟨b, hb⟩ := TS.yoneda_exact₃ hTS (c - d₃) hz
  let : TS.obj₁.IsLE 0 := by
    change ((DerivedCategory.Plus.singleFunctor B 0).obj S.X₁).IsLE 0
    infer_instance
  let : (TS.obj₁⟦(1 : ℤ)⟧).IsLE (-1) :=
    DerivedCategory.Plus.TStructure.t.isLE_shift TS.obj₁ 0 1 (-1) (by omega)
  let : TT.obj₃.IsGE 0 :=
    G.rightDerivedFunctorPlus_isGE ((DerivedCategory.Plus.singleFunctor A 0).obj T.X₃) 0
  have hb₀ : b = 0 := DerivedCategory.Plus.TStructure.t.zero b (-1) 0 (by omega)
  have hc : c = d₃ := sub_eq_zero.mp (hb.trans (by rw [hb₀, comp_zero]))
  exact hc₃.trans (congrArg (fun k => k ≫ TT.mor₃) hc)

/-- The original single coefficient arrows and native units give the actual triangle morphism. -/
def rightDerivedSingleUnitTriangleMap :
    hS.singleTrianglePlus ⟶
      G.rightDerivedFunctorPlus.mapTriangle.obj hT.singleTrianglePlus where
  hom₁ := (DerivedCategory.Plus.singleFunctor B 0).map φ.τ₁ ≫
    G.rightDerivedSingleUnit T.X₁
  hom₂ := (DerivedCategory.Plus.singleFunctor B 0).map φ.τ₂ ≫
    G.rightDerivedSingleUnit T.X₂
  hom₃ := (DerivedCategory.Plus.singleFunctor B 0).map φ.τ₃ ≫
    G.rightDerivedSingleUnit T.X₃
  comm₁ := G.rightDerivedSingleUnit_coefficient_naturality φ.τ₁ φ.τ₂ S.f T.f φ.comm₁₂.symm
  comm₂ := G.rightDerivedSingleUnit_coefficient_naturality φ.τ₂ φ.τ₃ S.g T.g φ.comm₂₃.symm
  comm₃ := G.rightDerivedSingleUnit_singleTriangle_comm₃ S T hS hT φ

@[simp]
theorem rightDerivedSingleUnitTriangleMap_hom₁ :
    (G.rightDerivedSingleUnitTriangleMap S T hS hT φ).hom₁ =
      (DerivedCategory.Plus.singleFunctor B 0).map φ.τ₁ ≫ G.rightDerivedSingleUnit T.X₁ := rfl

@[simp]
theorem rightDerivedSingleUnitTriangleMap_hom₂ :
    (G.rightDerivedSingleUnitTriangleMap S T hS hT φ).hom₂ =
      (DerivedCategory.Plus.singleFunctor B 0).map φ.τ₂ ≫ G.rightDerivedSingleUnit T.X₂ := rfl

@[simp]
theorem rightDerivedSingleUnitTriangleMap_hom₃ :
    (G.rightDerivedSingleUnitTriangleMap S T hS hT φ).hom₃ =
      (DerivedCategory.Plus.singleFunctor B 0).map φ.τ₃ ≫ G.rightDerivedSingleUnit T.X₃ := rfl

end CategoryTheory.Functor
