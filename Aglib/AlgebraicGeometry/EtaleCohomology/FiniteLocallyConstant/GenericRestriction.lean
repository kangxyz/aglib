/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.GenericFiber
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.FiniteEtaleRigidity

/-!
Native migration from
`R5Lab.Aglib.AlgebraicGeometry.Cohomology.FiniteLocallyConstant.GenericRestriction` at R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`24a8ccc759eba16d71c512eb706664f6727b8ce273c2d19e8e591d4dad57565d`.
Original objects, maps, universes and explicit hypotheses are retained.
Native providers replace duplicate implementations.
-/

@[expose] public section

open _root_.AlgebraicGeometry.Scheme.EtaleCohomology

noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj
open AlgebraicGeometry.Scheme.FiniteEtale
open AlgebraicGeometry.Scheme.EtaleCohomology
open AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.Scheme.EtaleCohomology.GenericRestriction
universe u w wK
section ArbitraryClassUniqueness
variable (X : Scheme.{u}) [IsIntegral X]
  [∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)]
  [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
  [HasExt.{wK} (AbelianSheaf.{u, u + 1} (Spec X.functionField))]
  (H : Grp (Over X)) [IsCommMonObj H.X] [IsFinite H.X.hom] [Etale H.X.hom]
  (hAX : Stacks03AJ.{u, w} X) (hRX : Stacks03RV X)
  (hAK : Stacks03AJ.{u, wK} (Spec X.functionField))
  (hH : IsFiniteLocallyConstant (representedSheaf H))

include hAX hRX hAK hH in
theorem generic_h1Pullback_injective :
    Function.Injective (h1Pullback ((X.fromSpecStalk (genericPoint X))) (representedSheaf H)) :=
  AlgebraicGeometry.Scheme.EtaleCohomology.FiniteEtaleRigidity.h1Pullback_injective_of_full
      ((X.fromSpecStalk (genericPoint X))) hAX hRX hAK H hH

include hAX hRX hAK hH in
theorem generic_representedH1Pullback_injective :
    Function.Injective (representedH1Pullback ((X.fromSpecStalk (genericPoint X))) H) :=
  (coefficientIso (representedSheafBaseChangeIso ((X.fromSpecStalk (genericPoint X)))
      H)).injective.comp
    (generic_h1Pullback_injective X H hAX hRX hAK hH)

end ArbitraryClassUniqueness
section GenericOriginDetection
universe wB wBG
variable {Base X : Scheme.{u}} [IsIntegral Base]
  [∀ x : Base, IsIntegrallyClosed (Base.presheaf.stalk x)]
  [HasExt.{wB} (AbelianSheaf.{u, u + 1} Base)]
  [HasExt.{wBG} (AbelianSheaf.{u, u + 1} (Spec Base.functionField))]
  [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
  (o : Base ⟶ X) (L : AbelianSheaf.{u, u + 1} X)
  (hAB : Stacks03AJ.{u, wB} Base) (hRB : Stacks03RV Base)
  (hAG : Stacks03AJ.{u, wBG} (Spec Base.functionField))
  (hL : IsFiniteLocallyConstant L)

include hAB hRB hAG hL in
/-- The lower origin-detection step uses actual Ext composition and normal-base
generic full faithfulness. To apply it to a pointed original curve class still
requires identifying the displayed generic-origin pullback with that class's
literal origin evaluation, including coefficient transport. -/
theorem origin_zero_iff_generic_origin_zero (c : H1Etale X L) :
    h1Pullback o L c = 0 ↔ h1Pullback ((Base.fromSpecStalk (genericPoint Base)) ≫ o) L c = 0 := by
  constructor
  · intro hc
    apply (coefficientIso ((inverseImageComp o ((Base.fromSpecStalk (genericPoint Base)))).app
        L)).injective
    change coefficientMap ((inverseImageComp o ((Base.fromSpecStalk (genericPoint
        Base)))).hom.app L) _ = _
    rw [h1Pullback_comp, hc, map_zero, map_zero]
  · intro hc
    apply Scheme.EtaleCohomology.FiniteEtaleRigidity.h1Pullback_injective_finite_of_full
      ((Base.fromSpecStalk (genericPoint Base))) hAB hRB hAG ((inverseImage o).obj L)
      (isFiniteLocallyConstant_pullback o hL)
    rw [map_zero, ← h1Pullback_comp, hc, map_zero]

end GenericOriginDetection
end AlgebraicGeometry.Scheme.EtaleCohomology.GenericRestriction
