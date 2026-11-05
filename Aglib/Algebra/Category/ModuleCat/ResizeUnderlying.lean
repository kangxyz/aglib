/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aglib contributors
-/
module

public import Aglib.Algebra.Category.ModuleCat.ResizeNaturality

/-! # Coefficient-natural underlying comparisons for module resizing

Original additive equivalences commute with the actual diagram and coefficient
maps. Their existing Shrink conjugates give the complete underlying comparison
before specializing any coefficient. A coefficient-change functor is retained
literally, and source and target value universes remain independent.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace ModuleCat

universe r l e e' uI vI uC vC uD vD

variable {I : Type uI} [Category.{vI} I]
  {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  (Λ : Type l) [Ring Λ]
  (P : C ⥤ I ⥤ ModuleCat.{e} Λ) (K : C ⥤ D)
  (Q : D ⥤ I ⥤ AddCommGrpCat.{e'})
  [hP : ∀ c i, Small.{r} ((P.obj c).obj i)]
  [hQ : ∀ d i, Small.{r} ((Q.obj d).obj i)]
  (a : ∀ c i, (P.obj c).obj i ≃+ (Q.obj (K.obj c)).obj i)
  (hi : ∀ c {i j : I} (b : i ⟶ j) (x : (P.obj c).obj i),
    a c j ((P.obj c).map b x) = (Q.obj (K.obj c)).map b (a c i x))
  (hc : ∀ {c d : C} (g : c ⟶ d) (i : I) (x : (P.obj c).obj i),
    a d i ((P.map g).app i x) = (Q.map (K.map g)).app i (a c i x))

/-- Original compatible additive equivalences give the complete underlying
coefficient comparison on the same resized module and additive diagrams. -/
def resizeDiagramFunctorUnderlyingIsoOfAddEquiv :
    resizeDiagramFunctor.{r} Λ P ⋙
        (Functor.whiskeringRight I _ _).obj
          (forget₂ (ModuleCat.{r} Λ) AddCommGrpCat.{r}) ≅
      K ⋙ resizeAdditiveDiagramFunctor.{r} Q :=
  NatIso.ofComponents
    (fun c => resizeDiagramUnderlyingIso.{r} Λ (P.obj c) ≪≫
      @resizeAdditiveDiagramIsoOfAddEquiv.{r, e, e'} I _
        (P.obj c ⋙ forget₂ (ModuleCat.{e} Λ) AddCommGrpCat.{e})
        (Q.obj (K.obj c)) (fun i => hP c i) (fun i => hQ (K.obj c) i)
        (a c) (hi c)) (by
      intro c d g
      apply NatTrans.ext
      funext i
      apply ConcreteCategory.ext_apply
      intro x
      change Shrink.addEquiv.symm
          (a d i (Shrink.addEquiv (Shrink.addEquiv.symm
            ((P.map g).app i (Shrink.addEquiv x))))) =
        Shrink.addEquiv.symm
          ((Q.map (K.map g)).app i (Shrink.addEquiv
            (Shrink.addEquiv.symm (a c i (Shrink.addEquiv x)))))
      simp only [AddEquiv.apply_symm_apply]
      exact congrArg Shrink.addEquiv.symm (hc g i (Shrink.addEquiv x)))

/-- The complete comparison retains the original additive equivalence on
every original value, using precisely the existing Shrink realization. -/
theorem resizeDiagramFunctorUnderlyingIsoOfAddEquiv_hom_app_shrink
    (c : C) (i : I) (x : (P.obj c).obj i) :
    ((resizeDiagramFunctorUnderlyingIsoOfAddEquiv.{r} Λ P K Q a hi hc).hom.app c).app i
        (Shrink.addEquiv.symm x) = Shrink.addEquiv.symm (a c i x) := by
  change Shrink.addEquiv.symm (a c i (Shrink.addEquiv (Shrink.addEquiv.symm x))) = _
  rw [AddEquiv.apply_symm_apply]

end ModuleCat
