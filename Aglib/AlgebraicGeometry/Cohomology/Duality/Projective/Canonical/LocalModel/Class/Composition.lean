/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.LocalModel.Class.Open

/-!
# The original class-one section under composed open restrictions

The original restriction-composition comparison preserves the inverse
unit-frame section. Applied to the original top-homology frame, it
preserves the same original class-one section.
-/

@[expose] public section
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Opposite

universe u w
namespace AlgebraicGeometry.Scheme.Modules

private theorem restrictionComp_unit_one
    {X V W : Scheme.{u}} (f : W ⟶ V) (g : V ⟶ X)
    [IsOpenImmersion f] [IsOpenImmersion g] (U : W.Opens) :
    ((restrictFunctorComp f g).hom.app (SheafOfModules.unit X.ringCatSheaf)).val.app (op U)
        (1 : Γ(X, (f ≫ g) ''ᵁ U)) = (1 : Γ(X, g ''ᵁ (f ''ᵁ U))) := by
  change (X.presheaf.map (eqToHom (by simp)).op).hom (1 : Γ(X, (f ≫ g) ''ᵁ U)) = _
  exact map_one _

private theorem restrictionComp_inverseUnitSection
    {X V W : Scheme.{u}} (f : W ⟶ V) (g : V ⟶ X)
    [IsOpenImmersion f] [IsOpenImmersion g]
    {M : X.Modules} (e : M ≅ SheafOfModules.unit X.ringCatSheaf) (U : W.Opens) :
    ((restrictFunctorComp f g).hom.app M).val.app (op U)
        (e.inv.val.app (op ((f ≫ g) ''ᵁ U)) (1 : Γ(X, (f ≫ g) ''ᵁ U))) =
      e.inv.val.app (op (g ''ᵁ (f ''ᵁ U))) (1 : Γ(X, g ''ᵁ (f ''ᵁ U))) := by
  have hn := congrArg (fun a => a.val.app (op U) (1 : Γ(X, (f ≫ g) ''ᵁ U)))
    ((restrictFunctorComp f g).hom.naturality e.inv)
  exact hn.trans (congrArg (e.inv.val.app (op (g ''ᵁ (f ''ᵁ U))))
    (restrictionComp_unit_one f g U))

variable {A : CommRingCat.{u}} (s : List A)
  (hs : RingTheory.Sequence.IsWeaklyRegular A s)
  {L : (Spec A).Modules} [L.IsQuasicoherent]
  (J : InjectiveResolution L) (e : moduleSpecΓFunctor.obj L ≅ ModuleCat.of A A)
  [HasExt.{w} (ModuleCat.{u} A)]

/-- The original class one is the inverse of the original unit-frame section one. -/
theorem regularListModelTopClass_eq_inverseFrame_one
    (U : (Spec (regularListQuotientRing s)).Opens) :
    regularListModelTopClass s hs J e (1 : A) U =
      (closedImmersionRightAdjointRegularListResolutionTopHomologyIso s hs J e).inv.val.app
        (op U) (1 : Γ(Spec (regularListQuotientRing s), U)) := by
  let F := closedImmersionRightAdjointRegularListResolutionTopHomologyIso s hs J e
  let z := regularListModelTopClass s hs J e (1 : A) U
  exact ((congrArg (F.inv.val.app (op U))
    (regularListModelTopClass_one s hs J e U)).symm.trans
      (congrArg (fun k => k.val.app (op U) z) F.hom_inv_id)).symm

/-- The actual composition comparison preserves the original class-one section. -/
theorem regularListModelTopClass_restrictFunctorComp_one
    {V W : Scheme.{u}} (f : W ⟶ V) (g : V ⟶ Spec (regularListQuotientRing s))
    [IsOpenImmersion f] [IsOpenImmersion g] (U : W.Opens) :
    ((restrictFunctorComp f g).hom.app
      ((closedImmersionRightAdjointRegularListResolutionComplex s J).homology
        (s.length : ℤ))).val.app (op U)
      (regularListModelTopClass s hs J e (1 : A) ((f ≫ g) ''ᵁ U)) =
      regularListModelTopClass s hs J e (1 : A) (g ''ᵁ (f ''ᵁ U)) := by
  have hS := regularListModelTopClass_eq_inverseFrame_one s hs J e ((f ≫ g) ''ᵁ U)
  have hT := regularListModelTopClass_eq_inverseFrame_one s hs J e (g ''ᵁ (f ''ᵁ U))
  exact (congrArg
    (((restrictFunctorComp f g).hom.app
      ((closedImmersionRightAdjointRegularListResolutionComplex s J).homology
        (s.length : ℤ))).val.app (op U)) hS).trans
    ((restrictionComp_inverseUnitSection f g
      (closedImmersionRightAdjointRegularListResolutionTopHomologyIso s hs J e) U).trans
        hT.symm)

end AlgebraicGeometry.Scheme.Modules
