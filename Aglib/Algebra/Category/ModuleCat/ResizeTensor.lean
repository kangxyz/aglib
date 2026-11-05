/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aglib contributors
-/
module

public import Aglib.Algebra.Category.ModuleCat.Resize
public import Aglib.Algebra.Category.ModuleCat.FunctorTensorRightScalars

/-! # Tensor comparisons after resizing only their original factors

The original additive tensor equivalence and its right-factor scalar action
are constructed once, before specializing to any cohomology diagram.
-/

@[expose] public noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace ModuleCat
universe u r e uI vI

section TensorResize

variable (R : Type) [Field R] (Λ : Type r) [Ring Λ]
  (M : ModuleCat.{u + 1} R) [Module Λ M] [SMulCommClass Λ R M]

/-- The existing tensor congruence with its original scalar structure. -/
def tensorShrinkAddEquiv (V : ModuleCat.{max (u + 1) e} R)
    [Small.{u + 1} V] : Shrink.{u + 1} V ⊗[R] M ≃+ V ⊗[R] M :=
  (TensorProduct.congr (Shrink.linearEquiv.{u + 1} R V)
    (LinearEquiv.refl R M)).toAddEquiv

private theorem tensorShrinkAddEquiv_tmul (V : ModuleCat.{max (u + 1) e} R)
    [Small.{u + 1} V] (x : Shrink.{u + 1} V) (m : M) :
    tensorShrinkAddEquiv R M V (x ⊗ₜ[R] m) =
      Shrink.linearEquiv.{u + 1} R V x ⊗ₜ[R] m :=
  TensorProduct.congr_tmul (Shrink.linearEquiv.{u + 1} R V)
    (LinearEquiv.refl R M) x m

/-- The native tensor congruence is linear for the same right-factor action. -/
def tensorShrinkEquiv (V : ModuleCat.{max (u + 1) e} R)
    [Small.{u + 1} V] :
    letI := TensorProduct.rightModule R Λ (Shrink.{u + 1} V) M
    letI := TensorProduct.rightModule R Λ V M
    Shrink.{u + 1} V ⊗[R] M ≃ₗ[Λ] V ⊗[R] M := by
  letI := TensorProduct.rightModule R Λ (Shrink.{u + 1} V) M
  letI := TensorProduct.rightModule R Λ V M
  exact
    { tensorShrinkAddEquiv R M V with
      map_smul' := by
        intro a z
        induction z using TensorProduct.inductionOn with
        | tmul x m =>
            change tensorShrinkAddEquiv R M V (a • (x ⊗ₜ[R] m)) =
              a • tensorShrinkAddEquiv R M V (x ⊗ₜ[R] m)
            rw [TensorProduct.rightModule_smul_tmul, tensorShrinkAddEquiv_tmul,
              tensorShrinkAddEquiv_tmul, TensorProduct.rightModule_smul_tmul]
        | add z t hz ht =>
            change tensorShrinkAddEquiv R M V (a • (z + t)) =
              a • tensorShrinkAddEquiv R M V (z + t)
            change tensorShrinkAddEquiv R M V (a • z) =
              a • tensorShrinkAddEquiv R M V z at hz
            change tensorShrinkAddEquiv R M V (a • t) =
              a • tensorShrinkAddEquiv R M V t at ht
            rw [smul_add, map_add, map_add, hz, ht, smul_add] }

private theorem tensorShrinkEquiv_tmul (V : ModuleCat.{max (u + 1) e} R)
    [Small.{u + 1} V] (x : Shrink.{u + 1} V) (m : M) :
    tensorShrinkEquiv R Λ M V (x ⊗ₜ[R] m) =
      Shrink.linearEquiv.{u + 1} R V x ⊗ₜ[R] m := by
  exact TensorProduct.congr_tmul (Shrink.linearEquiv.{u + 1} R V)
    (LinearEquiv.refl R M) x m

end TensorResize

variable {I : Type uI} [Category.{vI} I]
  (R : Type) [Field R] (Λ : Type r) [Ring Λ]
  (M : ModuleCat.{u + 1} R) [Module Λ M] [SMulCommClass Λ R M]
  (F : I ⥤ ModuleCat.{max (u + 1) e} R)
  (G : I ⥤ ModuleCat.{max (u + 1) e} Λ)
  [∀ i, Small.{u + 1} (F.obj i)] [∀ i, Small.{u + 1} (G.obj i)]
  (α : F ⋙ tensorRightScalarsFunctor R Λ M ⟶ G)

/-- The same original comparison, conjugated only on its original factors. -/
def resizeTensorComparisonApp (i : I) :
    (resizeDiagram.{u + 1} R F ⋙ tensorRightScalarsFunctor R Λ M).obj i ⟶
      (resizeDiagram.{u + 1} Λ G).obj i := by
  letI := TensorProduct.rightModule R Λ (Shrink.{u + 1} (F.obj i)) M
  letI := TensorProduct.rightModule R Λ (F.obj i) M
  let T : Shrink.{u + 1} (F.obj i) ⊗[R] M ≃ₗ[Λ] (F.obj i) ⊗[R] M :=
    tensorShrinkEquiv R Λ M (F.obj i)
  exact ConcreteCategory.ofHom (C := ModuleCat.{u + 1} Λ)
    (X := (resizeDiagram.{u + 1} R F ⋙ tensorRightScalarsFunctor R Λ M).obj i)
    (Y := (resizeDiagram.{u + 1} Λ G).obj i)
    ((Shrink.linearEquiv.{u + 1} Λ (G.obj i)).symm.toLinearMap.comp
      ((α.app i).hom.comp T.toLinearMap))

/-- All original restrictions commute with this conjugated comparison. -/
def resizeTensorComparison :
    resizeDiagram.{u + 1} R F ⋙ tensorRightScalarsFunctor R Λ M ⟶
      resizeDiagram.{u + 1} Λ G where
  app i := resizeTensorComparisonApp R Λ M F G α i
  naturality U V g := by
    let A := F
    let B := G
    let E (W : I) := Shrink.linearEquiv.{u + 1} Λ (B.obj W)
    let T (W : I) := tensorShrinkEquiv R Λ M (A.obj W)
    let mg : Shrink.{u + 1} (A.obj U) →ₗ[R] Shrink.{u + 1} (A.obj V) :=
      (Shrink.linearEquiv.{u + 1} R (A.obj V)).symm.toLinearMap.comp
        ((A.map g).hom.comp (Shrink.linearEquiv.{u + 1} R (A.obj U)).toLinearMap)
    have ht (z : Shrink.{u + 1} (A.obj U) ⊗[R] M) :
        T V (TensorProduct.map mg
          LinearMap.id z) =
        TensorProduct.map (A.map g).hom LinearMap.id (T U z) := by
      induction z using TensorProduct.inductionOn with
      | tmul x m =>
          calc
            T V (TensorProduct.map mg
                LinearMap.id (x ⊗ₜ[R] m)) =
                T V ((mg x) ⊗ₜ[R] m) :=
              congrArg (T V) (TensorProduct.map_tmul _ _ x m)
            _ = (A.map g (Shrink.linearEquiv.{u + 1} R (A.obj U) x)) ⊗ₜ[R] m := by
              change tensorShrinkEquiv R Λ M (A.obj V) (mg x ⊗ₜ[R] m) = _
              exact (tensorShrinkEquiv_tmul R Λ M (A.obj V) (mg x) m).trans
                (congrArg (fun y => y ⊗ₜ[R] m)
                  ((Shrink.linearEquiv.{u + 1} R (A.obj V)).apply_symm_apply _))
            _ = TensorProduct.map (A.map g).hom LinearMap.id (T U (x ⊗ₜ[R] m)) := by
              exact (TensorProduct.map_tmul (A.map g).hom (LinearMap.id : M →ₗ[R] M)
                ((Shrink.linearEquiv.{u + 1} R (A.obj U)) x) m).symm.trans
                  (congrArg (TensorProduct.map (A.map g).hom (LinearMap.id : M →ₗ[R] M))
                    (tensorShrinkEquiv_tmul R Λ M (A.obj U) x m).symm)
      | add z t hz ht =>
          calc
            T V (TensorProduct.map mg
                LinearMap.id (z + t)) =
                T V (TensorProduct.map mg
                  LinearMap.id z) +
                T V (TensorProduct.map mg
                  LinearMap.id t) := by
              exact (congrArg (T V) ((TensorProduct.map mg
                (LinearMap.id : M →ₗ[R] M)).map_add z t)).trans
                  ((T V).map_add _ _)
            _ = TensorProduct.map (A.map g).hom LinearMap.id (T U z) +
                TensorProduct.map (A.map g).hom LinearMap.id (T U t) :=
              congrArg₂ (· + ·) hz ht
            _ = TensorProduct.map (A.map g).hom LinearMap.id (T U (z + t)) := by
              exact ((TensorProduct.map (A.map g).hom
                (LinearMap.id : M →ₗ[R] M)).map_add (T U z) (T U t)).symm.trans
                  (congrArg (TensorProduct.map (A.map g).hom (LinearMap.id : M →ₗ[R] M))
                    ((T U).map_add z t).symm)
    ext z
    change Shrink.{u + 1} (A.obj U) ⊗[R] M at z
    change (E V).symm
        ((α.app V).hom
          (T V (TensorProduct.map
            mg LinearMap.id z))) =
      (E V).symm (B.map g
        (E U ((E U).symm ((α.app U).hom (T U z)))))
    have hn : (α.app V).hom
        (TensorProduct.map (A.map g).hom LinearMap.id (T U z)) =
        B.map g ((α.app U).hom (T U z)) :=
      ConcreteCategory.congr_hom (α.naturality g) (T U z)
    exact (congrArg (fun y => (E V).symm ((α.app V).hom y)) (ht z)).trans
      ((congrArg (E V).symm hn).trans
        (congrArg (fun y => (E V).symm (B.map g y))
          ((E U).apply_symm_apply ((α.app U).hom (T U z))).symm))


/-- Actual bijectivity is preserved by the two actual equivalences. -/
theorem resizeTensorComparison_bijective (i : I) (h : Function.Bijective (α.app i)) :
    Function.Bijective ((resizeTensorComparison R Λ M F G α).app i) := by
  exact (Shrink.linearEquiv.{u + 1} Λ (G.obj i)).symm.bijective.comp
    (h.comp (tensorShrinkEquiv R Λ M (F.obj i)).bijective)

end ModuleCat
