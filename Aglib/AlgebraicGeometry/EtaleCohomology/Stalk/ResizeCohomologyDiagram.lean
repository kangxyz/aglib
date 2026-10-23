/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.FibreProductOriginalDiagram

/-! # Group-only resizing of whole original cohomology diagrams -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.EtaleCohomology.Stalk
universe r e uI vI uJ vJ

variable {I : Type uI} [Category.{vI} I]

/-- Resize only groups of an additive diagram with small values. -/
def resizeAdditiveDiagram (F : I ⥤ AddCommGrpCat.{e}) [∀ i, Small.{r} (F.obj i)] :
    I ⥤ AddCommGrpCat.{r} where
  obj i := AddCommGrpCat.of (Shrink.{r} (F.obj i))
  map a := AddCommGrpCat.ofHom
    (Shrink.addEquiv.symm.toAddMonoidHom.comp ((F.map a).hom.comp Shrink.addEquiv.toAddMonoidHom))
  map_id i := by
    apply ConcreteCategory.ext_apply
    intro x
    change Shrink.addEquiv.symm (F.map (𝟙 i) (Shrink.addEquiv x)) = x
    exact (congrArg Shrink.addEquiv.symm
      (ConcreteCategory.congr_hom (F.map_id i) (Shrink.addEquiv x))).trans
        (Shrink.addEquiv.symm_apply_apply x)
  map_comp a b := by
    apply ConcreteCategory.ext_apply
    intro x
    change Shrink.addEquiv.symm (F.map (a ≫ b) (Shrink.addEquiv x)) =
      Shrink.addEquiv.symm (F.map b (Shrink.addEquiv
        (Shrink.addEquiv.symm (F.map a (Shrink.addEquiv x)))))
    simp only [Functor.map_comp, ConcreteCategory.comp_apply, AddEquiv.apply_symm_apply]

/-- An original whole-diagram isomorphism induces a group-only resized isomorphism. -/
def resizeAdditiveDiagramIso {F G : I ⥤ AddCommGrpCat.{e}}
    [∀ i, Small.{r} (F.obj i)] [∀ i, Small.{r} (G.obj i)] (α : F ≅ G) :
    resizeAdditiveDiagram.{r} F ≅ resizeAdditiveDiagram.{r} G :=
  NatIso.ofComponents (fun i =>
    (((Shrink.addEquiv : Shrink.{r} (F.obj i) ≃+ F.obj i).trans
      (α.app i).addCommGroupIsoToAddEquiv).trans
      (Shrink.addEquiv : Shrink.{r} (G.obj i) ≃+ G.obj i).symm).toAddCommGrpIso) (by
    intro i j a
    apply ConcreteCategory.ext_apply
    intro x
    change Shrink.addEquiv.symm ((α.hom.app j)
      (Shrink.addEquiv (Shrink.addEquiv.symm (F.map a (Shrink.addEquiv x))))) =
      Shrink.addEquiv.symm (G.map a
        (Shrink.addEquiv (Shrink.addEquiv.symm ((α.hom.app i) (Shrink.addEquiv x)))))
    simp only [AddEquiv.apply_symm_apply]
    exact congrArg Shrink.addEquiv.symm
      (ConcreteCategory.congr_hom (α.hom.naturality a) (Shrink.addEquiv x)))

/-- Group-only resizing commutes with actual reindexing. -/
def resizeAdditiveDiagramWhiskerIso
    {J : Type uJ} [Category.{vJ} J] (K : J ⥤ I)
    (F : I ⥤ AddCommGrpCat.{e}) [h : ∀ i, Small.{r} (F.obj i)] :
    let _ : ∀ j, Small.{r} ((K ⋙ F).obj j) := fun j => h (K.obj j)
    resizeAdditiveDiagram.{r} (K ⋙ F) ≅ K ⋙ resizeAdditiveDiagram.{r} F :=
  Iso.refl _

section NativeCohomology
universe u w s t
attribute [local instance] hasSheafifyLarge
variable {X S : Scheme.{u}} (f : X ⟶ S)
  [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
  [∀ U : S.Etale, HasExt.{s} (Sheaf ((Scheme.smallEtaleTopology X).over
    ((siteBaseChange f).obj U)) AddCommGrpCat.{u + 1})]
  [∀ U : S.Etale, HasExt.{t} (AbelianSheaf.{u, u + 1} (pullback U.hom f))]
  (F : AbelianSheaf.{u, u + 1} X) (q : ℕ)

instance originalFibreProductCohomologyPresheaf_small (U : S.Etaleᵒᵖ) :
    Small.{u + 1} ((originalFibreProductCohomologyPresheaf f F q).obj U) :=
  inferInstanceAs (Small.{u + 1}
    (Sheaf.H.{t} ((inverseImage (pullback.snd U.unop.hom f)).obj F) q))

/-- Resizing the original whole diagram recovers the actual small cohomology presheaf. -/
def resizeOriginalFibreProductIso :
    resizeAdditiveDiagram.{u + 1} (originalFibreProductCohomologyPresheaf f F q) ≅
      smallFibreProductCohomologyPresheaf f F q :=
  Iso.refl _
end NativeCohomology

end AlgebraicGeometry.Scheme.EtaleCohomology.Stalk
