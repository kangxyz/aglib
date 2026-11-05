/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.PointedTransferZero
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.SmoothAffineStageSystem

/-! # Pointed local zero ascends from the original smooth stages

The actual bounded stage representative is produced internally by continuity.
A local zero theorem at each stage is then used once, at that representative
and at the image of the original mark. The literal pullback chart retains the
mark and kills the original class, using the same mate, projection and counit.
The stage zero theorem is an explicit mathematical input, not a conclusion
of continuity. Genuine coefficient injectivity belongs to its stage supplier.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Continuity.SmoothAffineStageSystem

universe u e
attribute [local instance] hasSheafifyLarge HasExt.standard

/-- Ascend pointed target-local vanishing from stage coefficients to an
original bounded class. No class representative or return equation is input. -/
theorem exists_pointed_zero_of_stage_zero
    {I : Type u} [Category.{u} I] [IsFiltered I]
    (D : SmoothAffineStageSystem I)
    [hstage : ∀ i, HasExt.{e} (AbelianSheaf.{u, u + 1} (D.diagram.obj i).unop)]
    [hapex : HasExt.{e} (AbelianSheaf.{u, u + 1} D.cone.pt.unop)]
    [HasColimitsOfShape I AddCommGrpCat.{e}] [UnivLE.{u, e}]
    {X P : Scheme.{u}} (a : D.cone.pt.unop ⟶ X)
    (Xi : I → Scheme.{u}) (p : ∀ i, X ⟶ Xi i)
    (ai : ∀ i, (D.diagram.obj i).unop ⟶ Xi i)
    (h : ∀ i, a ≫ p i = (D.cone.ι.app i).unop ≫ ai i)
    (n : ℕ) (hn : 0 < n)
    (F : (boundedCoefficientProperty D.base n).FullSubcategory)
    (q : ℕ) (x : P ⟶ X)
    (hzero : ∀ (i : I)
      (ci : Sheaf.H.{e} ((boundedBaseChangeSource (D.baseLeg i)
        (D.stageProjection i) n).obj F) q),
      ∃ (U : (Xi i).Etale) (xi : P ⟶ U.left), xi ≫ U.hom = x ≫ p i ∧
        cohomologyPullback.{u, e, u + 2} (pullback.snd U.hom (ai i)) _ q ci = 0)
    (c : Sheaf.H.{e} (((boundedCoefficientProperty D.base n).ι ⋙
      inverseImage D.projection).obj F) q) :
    ∃ (V : X.Etale) (xV : P ⟶ V.left), xV ≫ V.hom = x ∧
      cohomologyPullback.{u, e, u + 2} (pullback.snd V.hom a) _ q c = 0 := by
  obtain ⟨i, ci, hci⟩ := D.exists_stage_class n hn F q c
  obtain ⟨U, xi, hx, hz⟩ := hzero i ci
  let γ := (boundedBaseChangeMap (D.baseLeg i) (D.cone.ι.app i).unop
    (D.stageProjection i) D.projection (D.cartesian i).w.symm n).app F
  have hz' : cohomologyPullback.{u, e, u + 2} (pullback.snd U.hom (ai i)) _ q
      (Sheaf.H.map γ q ci) = 0 := by
    rw [cohomologyPullback_coefficientMap, hz, map_zero]
  obtain ⟨V, xV, hxV, hV⟩ := exists_pointed_etale_zero_of_stage_transfer
    (p i) a (ai i) (D.cone.ι.app i).unop (h i) _ _
    ((inverseImageAdjunction (D.cone.ι.app i).unop).counit.app
      (((boundedCoefficientProperty D.base n).ι ⋙ inverseImage D.projection).obj F))
    q (Sheaf.H.map γ q ci) x U xi hx hz'
  refine ⟨V, xV, hxV, ?_⟩
  rw [hci] at hV
  exact hV

end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity.SmoothAffineStageSystem
