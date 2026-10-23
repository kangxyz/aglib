/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Finite.ExactImageComparison.AffineOrdinaryBaseChange
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.EtaleDirectImageMate

/-! # Original chart comparison on geometric direct-image stalks -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u

open CoefficientStalkBaseChange
attribute [local instance] hasSheafifyLarge

variable {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S) [Etale g]
  {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  (s' : Spec (.of Ω) ⟶ T) (s : Spec (.of Ω) ⟶ S) (hs : s' ≫ g = s)
  (F : AbelianSheaf.{u, u + 1} X)

/-- Original chart stalk unit followed by the original canonical ordinary mate. -/
def directImageChartStalkIso :
    coefficientFiber s ((directImage f).obj F) ≅
      coefficientFiber s' ((directImage (pullback.fst g f)).obj
        ((inverseImage (pullback.snd g f)).obj F)) := by
  subst s
  exact (StalkInverseImage.nativeStalkIso g s').app ((directImage f).obj F) ≪≫
    (pointSmallEtale s').sheafFiber.mapIso ((etaleBaseChangeIso f g).app F)

/-- Normalize the explicit native comparison only at its complete hom boundary. -/
theorem directImageChartStalkIso_hom :
    (directImageChartStalkIso f g s' s hs F).hom =
      pointedStalkUnit g s' ((directImage f).obj F) s hs ≫
        (pointSmallEtale s').sheafFiber.map
          ((baseChangeMap f (pullback.fst g f) g (pullback.snd g f)
            pullback.condition).app F) := by
  subst s
  change (StalkInverseImage.nativeStalkIso g s').hom.app ((directImage f).obj F) ≫
    (pointSmallEtale s').sheafFiber.map ((etaleBaseChangeIso f g).hom.app F) = _
  rw [StalkInverseImage.nativeStalkIso_hom, etaleBaseChangeIso_hom]
  rfl

/-- The chart comparison preserves the literal evaluation at an original point. -/
theorem directImageChartStalkIso_evaluation
    (x : Spec (.of Ω) ⟶ X) (x' : Spec (.of Ω) ⟶ pullback g f)
    (hx : x ≫ f = s) (hx' : x' ≫ pullback.fst g f = s')
    (hm : x' ≫ pullback.snd g f = x) :
    (directImageChartStalkIso f g s' s hs F).hom ≫
        pointedDirectImageEvaluation (pullback.fst g f) x' s' hx'
          ((inverseImage (pullback.snd g f)).obj F) =
      pointedDirectImageEvaluation f x s hx F ≫
        pointedStalkUnit (pullback.snd g f) x' F x hm := by
  rw [directImageChartStalkIso_hom]
  exact pointedDirectImageEvaluation_baseChange f (pullback.fst g f) g
    (pullback.snd g f) pullback.condition x s x' s' hx hs hx' hm F

end AlgebraicGeometry.Scheme.EtaleCohomology
