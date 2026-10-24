/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.SingleUnit.ShortExact
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Composition.Shift
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.TransformationShift
public import Aglib.Algebra.Homology.CochainComplexPlus.QuasiIsoShift
public import Aglib.AlgebraicGeometry.Cohomology.Functoriality.GlobalSectionsComposition

/-!
# The original global-sections composition on native single units

The existing geometric composition isomorphism retains the original
single units and the original identity on section values. Its same unit
factorization also transports the native triangles, with the unchanged
comparison on all three objects.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor HomologicalComplex
open CategoryTheory.Pretriangulated
open AlgebraicGeometry AlgebraicGeometry.Scheme.Modules Opposite

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

variable {R : Type u} [CommRing R] {X Y : Scheme.{u}}
  (g : Y ⟶ X) (α : R →+* Γ(X, ⊤))

/-- The standard derived category of module sheaves for the composition comparison. -/
local instance compositionSingleUnitDerived (Z : Scheme.{u}) :
    HasDerivedCategory.{u + 1} Z.Modules := HasDerivedCategory.standard _

/-- The standard derived category of `R`-modules for derived global sections. -/
local instance compositionSingleUnitTarget : HasDerivedCategory.{u + 1} (ModuleCat.{u} R) :=
  HasDerivedCategory.standard _

/-- The original composition isomorphism carries the two native single units
to the source single unit through the original section comparison. -/
theorem moduleDerivedGlobalSectionsPushforwardCompIso_singleUnit (N : Y.Modules) :
    (moduleGlobalSectionsFunctorOfHom X α).rightDerivedSingleUnit
        ((Scheme.Modules.pushforward g).obj N) ≫
      (moduleGlobalSectionsFunctorOfHom X α).rightDerivedFunctorPlus.map
        ((Scheme.Modules.pushforward g).rightDerivedSingleUnit N) =
      (DerivedCategory.Plus.singleFunctor (ModuleCat.{u} R) 0).map
          ((modulePushforwardGlobalSectionsIso g α).hom.app N) ≫
        (moduleGlobalSectionsFunctorOfHom Y (g.appTop.hom.comp α)).rightDerivedSingleUnit N ≫
        (moduleDerivedGlobalSectionsPushforwardCompIso g α).hom.app
          ((DerivedCategory.Plus.singleFunctor Y.Modules 0).obj N) := by
  let G := Scheme.Modules.pushforward g
  let F := moduleGlobalSectionsFunctorOfHom X α
  let H := moduleGlobalSectionsFunctorOfHom Y (g.appTop.hom.comp α)
  let S := CochainComplex.singleFunctorPlus (ModuleCat.{u} R) 0
  let K := (CochainComplex.singleFunctorPlus Y.Modules 0).obj N
  let L := (CochainComplex.singleFunctorPlus X.Modules 0).obj (G.obj N)
  let Q : CochainComplex.Plus (ModuleCat.{u} R) ⥤ DerivedCategory.Plus (ModuleCat.{u} R) :=
    DerivedCategory.Plus.Q
  let τG : L ⟶ G.mapCochainComplexPlus.obj K :=
    (exactSingleComplexNatIso G).inv.app N
  let τF : S.obj (F.obj (G.obj N)) ⟶ F.mapCochainComplexPlus.obj L :=
    ObjectProperty.homMk ((singleMapHomologicalComplex F (.up ℤ) 0).inv.app (G.obj N))
  let τH : S.obj (H.obj N) ⟶ H.mapCochainComplexPlus.obj K :=
    ObjectProperty.homMk ((singleMapHomologicalComplex H (.up ℤ) 0).inv.app N)
  let c : G ⋙ F ≅ H := modulePushforwardGlobalSectionsIso g α
  let e := (NatIso.mapCochainComplexPlus c).app K
  let C := moduleDerivedGlobalSectionsPushforwardCompIso g α
  have hτ : τF ≫ F.mapCochainComplexPlus.map τG ≫ e.hom = S.map (c.hom.app N) ≫ τH := by
    apply ObjectProperty.hom_ext
    change (singleMapHomologicalComplex F (.up ℤ) 0).inv.app (G.obj N) ≫
        (F.mapHomologicalComplex (.up ℤ)).map
          ((singleMapHomologicalComplex G (.up ℤ) 0).inv.app N) ≫
        (c.hom.mapHomologicalComplex (.up ℤ)).app
          ((CochainComplex.singleFunctor Y.Modules 0).obj N) =
      (CochainComplex.singleFunctor (ModuleCat.{u} R) 0).map (c.hom.app N) ≫
        (singleMapHomologicalComplex H (.up ℤ) 0).inv.app N
    rw [← Category.assoc, ← singleMapHomologicalComplex_comp_inv_app,
      natTransMapHomologicalComplex_app_single_obj]
    change (singleMapHomologicalComplex (G ⋙ F) (.up ℤ) 0).inv.app N ≫
        (singleMapHomologicalComplex (G ⋙ F) (.up ℤ) 0).hom.app N ≫
        (CochainComplex.singleFunctor (ModuleCat.{u} R) 0).map (c.hom.app N) ≫
        (singleMapHomologicalComplex H (.up ℤ) 0).inv.app N = _
    rw [Iso.inv_hom_id_app_assoc]
  have hη := F.rightDerivedFunctorPlusUnit.naturality τG
  change Q.map (F.mapCochainComplexPlus.map τG) ≫
      F.rightDerivedFunctorPlusUnit.app (G.mapCochainComplexPlus.obj K) =
    F.rightDerivedFunctorPlusUnit.app L ≫
      F.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map τG) at hη
  have hC : Q.map e.hom ≫ H.rightDerivedFunctorPlusUnit.app K ≫ C.hom.app
      (DerivedCategory.Plus.Q.obj K) =
      F.rightDerivedFunctorPlusUnit.app (G.mapCochainComplexPlus.obj K) ≫
        F.rightDerivedFunctorPlus.map (G.rightDerivedFunctorPlusUnit.app K) := by
    calc
      _ = Q.map e.hom ≫ (Q.map e.inv ≫
          (Functor.rightDerivedFunctorPlusCompUnit G F).app K) :=
        congrArg (fun k => Q.map e.hom ≫ k)
          (moduleDerivedGlobalSectionsPushforwardCompIso_unit g α K)
      _ = (Functor.rightDerivedFunctorPlusCompUnit G F).app K := by
        rw [← Category.assoc, ← Q.map_comp, e.hom_inv_id, Q.map_id, Category.id_comp]
      _ = _ := Functor.rightDerivedFunctorPlusCompUnit_app G F K
  change (Q.map τF ≫ F.rightDerivedFunctorPlusUnit.app L) ≫
      F.rightDerivedFunctorPlus.map
        (DerivedCategory.Plus.Q.map τG ≫ G.rightDerivedFunctorPlusUnit.app K) =
    Q.map (S.map (c.hom.app N)) ≫
      (Q.map τH ≫ H.rightDerivedFunctorPlusUnit.app K) ≫
      C.hom.app (DerivedCategory.Plus.Q.obj K)
  rw [Functor.map_comp]
  calc
    _ = Q.map τF ≫ (F.rightDerivedFunctorPlusUnit.app L ≫
          F.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map τG)) ≫
        F.rightDerivedFunctorPlus.map (G.rightDerivedFunctorPlusUnit.app K) := by
      simp only [Category.assoc]
    _ = Q.map τF ≫ Q.map (F.mapCochainComplexPlus.map τG) ≫
        (F.rightDerivedFunctorPlusUnit.app (G.mapCochainComplexPlus.obj K) ≫
          F.rightDerivedFunctorPlus.map (G.rightDerivedFunctorPlusUnit.app K)) := by
      rw [← hη]
      simp only [Category.assoc]
    _ = Q.map τF ≫ Q.map (F.mapCochainComplexPlus.map τG) ≫
        (Q.map e.hom ≫ H.rightDerivedFunctorPlusUnit.app K ≫
          C.hom.app (DerivedCategory.Plus.Q.obj K)) := by rw [hC]
    _ = Q.map (τF ≫ F.mapCochainComplexPlus.map τG ≫ e.hom) ≫
        H.rightDerivedFunctorPlusUnit.app K ≫ C.hom.app (DerivedCategory.Plus.Q.obj K) := by
      simp only [Functor.map_comp, Category.assoc]
    _ = Q.map (S.map (c.hom.app N) ≫ τH) ≫ H.rightDerivedFunctorPlusUnit.app K ≫
        C.hom.app (DerivedCategory.Plus.Q.obj K) :=
      congrArg (fun k => Q.map k ≫ H.rightDerivedFunctorPlusUnit.app K ≫
        C.hom.app (DerivedCategory.Plus.Q.obj K)) hτ
    _ = _ := by simp only [Functor.map_comp, Category.assoc]

/-- An arbitrary original coefficient arrow retains the same actual section
map through the existing composite-derived comparison. -/
theorem moduleDerivedGlobalSectionsPushforwardCompIso_coefficientUnit
    {M : X.Modules} {N : Y.Modules} (φ : M ⟶ (Scheme.Modules.pushforward g).obj N) :
    (moduleGlobalSectionsFunctorOfHom X α).rightDerivedSingleUnit M ≫
        (moduleGlobalSectionsFunctorOfHom X α).rightDerivedFunctorPlus.map
          ((DerivedCategory.Plus.singleFunctor X.Modules 0).map φ ≫
            (Scheme.Modules.pushforward g).rightDerivedSingleUnit N) ≫
        (moduleDerivedGlobalSectionsPushforwardCompIso g α).inv.app
          ((DerivedCategory.Plus.singleFunctor Y.Modules 0).obj N) =
      (DerivedCategory.Plus.singleFunctor (ModuleCat.{u} R) 0).map
          ((moduleGlobalSectionsFunctorOfHom X α).map φ ≫
            (modulePushforwardGlobalSectionsIso g α).hom.app N) ≫
        (moduleGlobalSectionsFunctorOfHom Y (g.appTop.hom.comp α)).rightDerivedSingleUnit N := by
  let F := moduleGlobalSectionsFunctorOfHom X α
  let H := moduleGlobalSectionsFunctorOfHom Y (g.appTop.hom.comp α)
  let G := Scheme.Modules.pushforward g
  let S := DerivedCategory.Plus.singleFunctor (ModuleCat.{u} R) 0
  let C := moduleDerivedGlobalSectionsPushforwardCompIso g α
  let K := (DerivedCategory.Plus.singleFunctor Y.Modules 0).obj N
  change F.rightDerivedSingleUnit M ≫ F.rightDerivedFunctorPlus.map
      ((DerivedCategory.Plus.singleFunctor X.Modules 0).map φ ≫ G.rightDerivedSingleUnit N) ≫
      C.inv.app K =
    S.map (F.map φ ≫ (modulePushforwardGlobalSectionsIso g α).hom.app N) ≫
      H.rightDerivedSingleUnit N
  rw [Functor.map_comp]
  calc
    _ = (F.rightDerivedSingleUnit M ≫ F.rightDerivedFunctorPlus.map
          ((DerivedCategory.Plus.singleFunctor X.Modules 0).map φ)) ≫
        F.rightDerivedFunctorPlus.map (G.rightDerivedSingleUnit N) ≫ C.inv.app K := by
      simp only [Category.assoc]
    _ = S.map (F.map φ) ≫ (F.rightDerivedSingleUnit (G.obj N) ≫
        F.rightDerivedFunctorPlus.map (G.rightDerivedSingleUnit N)) ≫ C.inv.app K := by
      rw [← F.rightDerivedSingleUnit_naturality φ]
      simp only [Category.assoc]; rfl
    _ = S.map (F.map φ) ≫ (S.map ((modulePushforwardGlobalSectionsIso g α).hom.app N) ≫
        H.rightDerivedSingleUnit N ≫ C.hom.app K) ≫ C.inv.app K := by
      rw [moduleDerivedGlobalSectionsPushforwardCompIso_singleUnit g α N]
    _ = (S.map (F.map φ) ≫ S.map ((modulePushforwardGlobalSectionsIso g α).hom.app N) ≫
        H.rightDerivedSingleUnit N) ≫ (C.hom.app K ≫ C.inv.app K) := by
      simp only [Category.assoc]
    _ = S.map (F.map φ) ≫ S.map ((modulePushforwardGlobalSectionsIso g α).hom.app N) ≫
        H.rightDerivedSingleUnit N := by
      exact (congrArg (fun k =>
        (S.map (F.map φ) ≫ S.map ((modulePushforwardGlobalSectionsIso g α).hom.app N) ≫
          H.rightDerivedSingleUnit N) ≫ k) (C.hom_inv_id_app K)).trans (Category.comp_id _)
    _ = _ := by rw [S.map_comp]; simp only [Category.assoc]

local instance compositionSingleUnitShift :
    (moduleDerivedGlobalSectionsPushforwardCompIso g α).hom.CommShift ℤ := by
  let F := moduleGlobalSectionsFunctorOfHom Y (g.appTop.hom.comp α)
  let G := Scheme.Modules.pushforward g
  let H := moduleGlobalSectionsFunctorOfHom X α
  let β := whiskerRight
      (NatTrans.mapCochainComplexPlus (modulePushforwardGlobalSectionsIso g α).inv)
        DerivedCategory.Plus.Q ≫
    Functor.rightDerivedFunctorPlusCompUnit G H
  let : β.CommShift ℤ := by
    dsimp only [β]
    infer_instance
  exact Functor.commShift_of_rightDerived_factorization DerivedCategory.Plus.Q
    (CochainComplex.Plus.quasiIso Y.Modules) F.rightDerivedFunctorPlusUnit β
      (moduleDerivedGlobalSectionsPushforwardCompIso g α).hom (by
        apply NatTrans.ext
        funext K
        exact moduleDerivedGlobalSectionsPushforwardCompIso_unit g α K)

/-- The same existing composition comparison transports all three original
triangle objects and their native connecting arrow. -/
def moduleDerivedGlobalSectionsPushforwardCompTriangleIso :
    (moduleGlobalSectionsFunctorOfHom Y (g.appTop.hom.comp α)).rightDerivedFunctorPlus.mapTriangle ≅
      (Scheme.Modules.pushforward g).rightDerivedFunctorPlus.mapTriangle ⋙
        (moduleGlobalSectionsFunctorOfHom X α).rightDerivedFunctorPlus.mapTriangle :=
  Functor.mapTriangleIso (moduleDerivedGlobalSectionsPushforwardCompIso g α) ≪≫
    Functor.mapTriangleCompIso (Scheme.Modules.pushforward g).rightDerivedFunctorPlus
      (moduleGlobalSectionsFunctorOfHom X α).rightDerivedFunctorPlus

@[simp]
theorem moduleDerivedGlobalSectionsPushforwardCompTriangleIso_inv_hom₁
    (T : Triangle (DerivedCategory.Plus Y.Modules)) :
    ((moduleDerivedGlobalSectionsPushforwardCompTriangleIso g α).inv.app T).hom₁ =
      (moduleDerivedGlobalSectionsPushforwardCompIso g α).inv.app T.obj₁ := by
  simp [moduleDerivedGlobalSectionsPushforwardCompTriangleIso,
    Functor.mapTriangleIso, Functor.mapTriangleCompIso]

@[simp]
theorem moduleDerivedGlobalSectionsPushforwardCompTriangleIso_inv_hom₂
    (T : Triangle (DerivedCategory.Plus Y.Modules)) :
    ((moduleDerivedGlobalSectionsPushforwardCompTriangleIso g α).inv.app T).hom₂ =
      (moduleDerivedGlobalSectionsPushforwardCompIso g α).inv.app T.obj₂ := by
  simp [moduleDerivedGlobalSectionsPushforwardCompTriangleIso,
    Functor.mapTriangleIso, Functor.mapTriangleCompIso]

@[simp]
theorem moduleDerivedGlobalSectionsPushforwardCompTriangleIso_inv_hom₃
    (T : Triangle (DerivedCategory.Plus Y.Modules)) :
    ((moduleDerivedGlobalSectionsPushforwardCompTriangleIso g α).inv.app T).hom₃ =
      (moduleDerivedGlobalSectionsPushforwardCompIso g α).inv.app T.obj₃ := by
  simp [moduleDerivedGlobalSectionsPushforwardCompTriangleIso,
    Functor.mapTriangleIso, Functor.mapTriangleCompIso]

end AlgebraicGeometry.Scheme.Cohomology
