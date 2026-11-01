/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.ConstantRing.InternalHom
public import Aglib.Algebra.Category.ModuleCat.Sheaf.ConstantSections

/-!
# The original internal-Hom comparison on an actual constant source chart

An actual constant chart of the original module-valued source is restricted
by the existing constantOverIso. The whole slice-Hom comparison, original
chart precomposition and original constant-sheaf adjunction then identify
internal-Hom sections with linear maps to the original target sections.
The forward equation retains the original constant-unit map of that chart.
No freeness, finiteness or alternative coefficient object is used here.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe c h r

namespace ModuleCat.Sheaf.ConstantRing

variable {C : Type c} [Category.{h} C] (J : GrothendieckTopology C)
  (Λ : Type r) [CommRing Λ] (U : C)
  [HasWeakSheafify J RingCat.{r}] [HasWeakSheafify (J.over U) RingCat.{r}]
  [J.WEqualsLocallyBijective RingCat.{r}] [(J.over U).WEqualsLocallyBijective RingCat.{r}]
  [J.HasSheafCompose (CategoryTheory.forget RingCat.{r})]
  [(J.over U).HasSheafCompose (CategoryTheory.forget RingCat.{r})]
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [HasWeakSheafify J AddCommGrpCat.{max c h}]
  [HasWeakSheafify (J.over U) AddCommGrpCat.{max c h}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c h}]
  [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{max c h}]
  [J.HasSheafCompose (forget₂ (ModuleCat.{max c h} Λ) AddCommGrpCat.{max c h})]
  [(J.over U).HasSheafCompose (forget₂ (ModuleCat.{max c h} Λ) AddCommGrpCat.{max c h})]

attribute [local instance] ModuleCat.Sheaf.hasSheafify

/-- The source chart is the original constant-over map followed by the chart inverse. -/
def constantFrameSourceIso (M : ModuleSheaf.{c, h, r, max c h} J Λ)
    (M₀ : ModuleCat.{max c h} Λ)
    (e : (moduleSheafEquivalence J Λ).inverse.obj M ≅
      (constantSheaf J (ModuleCat.{max c h} Λ)).obj M₀) :
    (constantSheaf (J.over U) (ModuleCat.{max c h} Λ)).obj M₀ ≅
      (J.overPullback (ModuleCat.{max c h} Λ) U).obj
        ((moduleSheafEquivalence J Λ).inverse.obj M) :=
  ModuleCat.Sheaf.constantOverIso J U M₀ ≪≫
    ((J.overPullback (ModuleCat.{max c h} Λ) U).mapIso e).symm

/-- The whole target-variable Hom comparison through an actual constant chart on the slice. -/
def sliceFrameHomNatIso (M : ModuleSheaf.{c, h, r, max c h} J Λ)
    (M₀ : ModuleCat.{max c h} Λ)
    (a : (constantSheaf (J.over U) (ModuleCat.{max c h} Λ)).obj M₀ ≅
      (J.overPullback (ModuleCat.{max c h} Λ) U).obj
        ((moduleSheafEquivalence J Λ).inverse.obj M)) :
    SheafOfModules.overFunctor (constantRing J Λ) U ⋙
        preadditiveCoyoneda.obj (op (M.over U)) ≅
      (moduleSheafEquivalence J Λ).inverse ⋙
        (sheafSections J (ModuleCat.{max c h} Λ)).obj (op U) ⋙
          preadditiveCoyoneda.obj (op M₀) := by
  let G := (moduleSheafEquivalence J Λ).inverse
  let P := J.overPullback (ModuleCat.{max c h} Λ) U
  let H := preadditiveCoyoneda.obj (op (P.obj (G.obj M)))
  let H₀ := preadditiveCoyoneda.obj
    (op ((constantSheaf (J.over U) (ModuleCat.{max c h} Λ)).obj M₀))
  exact overHomValuedNatIso J Λ U M ≪≫ (Functor.associator G P H).symm ≪≫
    Functor.isoWhiskerLeft (G ⋙ P)
      (preadditiveCoyoneda.mapIso a.op) ≪≫
    Functor.associator G P H₀ ≪≫
    Functor.isoWhiskerLeft G (ModuleCat.Sheaf.constantSliceHomNatIso J U M₀)

/-- The global chart specializes the same whole slice-chart construction. -/
def constantFrameHomNatIso (M : ModuleSheaf.{c, h, r, max c h} J Λ)
    (M₀ : ModuleCat.{max c h} Λ)
    (e : (moduleSheafEquivalence J Λ).inverse.obj M ≅
      (constantSheaf J (ModuleCat.{max c h} Λ)).obj M₀) :
    SheafOfModules.overFunctor (constantRing J Λ) U ⋙
        preadditiveCoyoneda.obj (op (M.over U)) ≅
      (moduleSheafEquivalence J Λ).inverse ⋙
        (sheafSections J (ModuleCat.{max c h} Λ)).obj (op U) ⋙
          preadditiveCoyoneda.obj (op M₀) :=
  sliceFrameHomNatIso J Λ U M M₀ (constantFrameSourceIso J Λ U M M₀ e)

/-- The original section comparison for an actual constant chart on this slice. -/
def sliceFrameSectionAddEquiv (M N : ModuleSheaf.{c, h, r, max c h} J Λ)
    (M₀ : ModuleCat.{max c h} Λ)
    (a : (constantSheaf (J.over U) (ModuleCat.{max c h} Λ)).obj M₀ ≅
      (J.overPullback (ModuleCat.{max c h} Λ) U).obj
        ((moduleSheafEquivalence J Λ).inverse.obj M)) :
    (SheafOfModules.InternalHom.sheaf (commutativeSheaf J Λ) M N).val.obj (op U) ≃+
      (M₀ ⟶ ((moduleSheafEquivalence J Λ).inverse.obj N).obj.obj (op U)) :=
  (SheafOfModules.InternalHom.sectionHomAddEquiv (commutativeSheaf J Λ) M N U).trans
    ((sliceFrameHomNatIso J Λ U M M₀ a).app N).addCommGroupIsoToAddEquiv

/-- The slice-chart equation retains its original constant unit and source isomorphism. -/
theorem sliceFrameSectionAddEquiv_apply (M N : ModuleSheaf.{c, h, r, max c h} J Λ)
    (M₀ : ModuleCat.{max c h} Λ)
    (a : (constantSheaf (J.over U) (ModuleCat.{max c h} Λ)).obj M₀ ≅
      (J.overPullback (ModuleCat.{max c h} Λ) U).obj
        ((moduleSheafEquivalence J Λ).inverse.obj M))
    (s : (SheafOfModules.InternalHom.sheaf (commutativeSheaf J Λ) M N).val.obj (op U)) :
    sliceFrameSectionAddEquiv J Λ U M N M₀ a s =
      (ModuleCat.Sheaf.constantUnit (J.over U) M₀).app (op (Over.mk (𝟙 U))) ≫
        a.hom.hom.app (op (Over.mk (𝟙 U))) ≫
          (sectionValuedHomAddEquiv J Λ U M N s).hom.app (op (Over.mk (𝟙 U))) := by
  change ModuleCat.Sheaf.constantSliceHomAddEquiv J U M₀
      ((moduleSheafEquivalence J Λ).inverse.obj N)
      (a.hom ≫ sectionValuedHomAddEquiv J Λ U M N s) = _
  rw [ModuleCat.Sheaf.constantSliceHomAddEquiv_apply]
  rfl

/-- Original internal-Hom sections through the whole chart Hom comparison. -/
def constantFrameSectionAddEquiv (M N : ModuleSheaf.{c, h, r, max c h} J Λ)
    (M₀ : ModuleCat.{max c h} Λ)
    (e : (moduleSheafEquivalence J Λ).inverse.obj M ≅
      (constantSheaf J (ModuleCat.{max c h} Λ)).obj M₀) :
    (SheafOfModules.InternalHom.sheaf (commutativeSheaf J Λ) M N).val.obj (op U) ≃+
      (M₀ ⟶ ((moduleSheafEquivalence J Λ).inverse.obj N).obj.obj (op U)) :=
  (SheafOfModules.InternalHom.sectionHomAddEquiv (commutativeSheaf J Λ) M N U).trans
    ((constantFrameHomNatIso J Λ U M M₀ e).app N).addCommGroupIsoToAddEquiv

-- Identify the original over-restriction value at its terminal object.
set_option backward.isDefEq.respectTransparency false in
/-- The forward chart equation uses the original constant unit and chart inverse. -/
theorem constantFrameSectionAddEquiv_apply (M N : ModuleSheaf.{c, h, r, max c h} J Λ)
    (M₀ : ModuleCat.{max c h} Λ)
    (e : (moduleSheafEquivalence J Λ).inverse.obj M ≅
      (constantSheaf J (ModuleCat.{max c h} Λ)).obj M₀)
    (s : (SheafOfModules.InternalHom.sheaf (commutativeSheaf J Λ) M N).val.obj (op U)) :
    constantFrameSectionAddEquiv J Λ U M N M₀ e s =
      (ModuleCat.Sheaf.constantUnit J M₀).app (op U) ≫ e.inv.hom.app (op U) ≫
        (sectionValuedHomAddEquiv J Λ U M N s).hom.app (op (Over.mk (𝟙 U))) := by
  change ModuleCat.Sheaf.constantSliceHomAddEquiv J U M₀
      ((moduleSheafEquivalence J Λ).inverse.obj N)
      ((constantFrameSourceIso J Λ U M M₀ e).hom ≫
        sectionValuedHomAddEquiv J Λ U M N s) = _
  rw [ModuleCat.Sheaf.constantSliceHomAddEquiv_apply]
  have hu := congrArg (fun α => α.app (op (Over.mk (𝟙 U))))
    (ModuleCat.Sheaf.constantOverMap_unit J U M₀)
  change (ModuleCat.Sheaf.constantUnit (J.over U) M₀).app (op (Over.mk (𝟙 U))) ≫
      (ModuleCat.Sheaf.constantOverMap J U M₀).hom.app (op (Over.mk (𝟙 U))) =
    (ModuleCat.Sheaf.constantUnit J M₀).app (op U) at hu
  change (ModuleCat.Sheaf.constantUnit (J.over U) M₀).app (op (Over.mk (𝟙 U))) ≫
      ((ModuleCat.Sheaf.constantOverMap J U M₀).hom.app (op (Over.mk (𝟙 U))) ≫
        e.inv.hom.app (op U)) ≫
      (sectionValuedHomAddEquiv J Λ U M N s).hom.app (op (Over.mk (𝟙 U))) = _
  simp only [← Category.assoc, hu]

end ModuleCat.Sheaf.ConstantRing
