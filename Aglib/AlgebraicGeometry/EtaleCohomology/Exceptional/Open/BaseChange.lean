/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Open.AbelianAdjunction
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.EtaleDirectImageMate

/-!
# Arbitrary base change of étale lower shriek

The comparison is the adjunction mate of the actual direct-image/chart
restriction isomorphism on the original pullback square. Both sides are
left adjoints to the identified right adjoints, so the comparison is
invertible without proper base change. Its normalization records the
actual composite adjunction unit.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology

variable {U X Y : Scheme.{u}} (j : U ⟶ X) (f : Y ⟶ X) [Etale j]

/-- Arbitrary base change of the actual lower-shriek functor on the native pullback. -/
def etaleLowerShriekBaseChangeIso :
    etaleLowerShriek j ⋙ inverseImage f ≅
      inverseImage (pullback.fst j f) ⋙ etaleLowerShriek (pullback.snd j f) :=
  (((etaleLowerShriekAdjunction j).comp (inverseImageAdjunction f)).ofNatIsoRight
    (etaleBaseChangeIso f j)).leftAdjointUniq
      ((inverseImageAdjunction (pullback.fst j f)).comp
        (etaleLowerShriekAdjunction (pullback.snd j f)))

/-- The base-change map is normalized by the actual adjunctions and right-adjoint exchange. -/
@[reassoc]
theorem etaleLowerShriekBaseChangeIso_homEquiv (F : AbelianSheaf.{u, u + 1} U) :
    ((etaleLowerShriekAdjunction j).comp (inverseImageAdjunction f)).homEquiv _ _
        ((etaleLowerShriekBaseChangeIso j f).hom.app F) ≫
          (etaleBaseChangeIso f j).hom.app
            ((etaleLowerShriek (pullback.snd j f)).obj
              ((inverseImage (pullback.fst j f)).obj F)) =
      ((inverseImageAdjunction (pullback.fst j f)).comp
        (etaleLowerShriekAdjunction (pullback.snd j f))).unit.app F := by
  simpa only [Adjunction.homEquiv_ofNatIsoRight_apply, etaleLowerShriekBaseChangeIso,
    Functor.comp_obj] using
    Adjunction.homEquiv_leftAdjointUniq_hom_app
      (((etaleLowerShriekAdjunction j).comp (inverseImageAdjunction f)).ofNatIsoRight
        (etaleBaseChangeIso f j))
      ((inverseImageAdjunction (pullback.fst j f)).comp
        (etaleLowerShriekAdjunction (pullback.snd j f))) F

/-- The right-adjoint exchange used by lower shriek is the original ordinary base-change map. -/
@[reassoc]
theorem etaleLowerShriekBaseChangeIso_originalMap (F : AbelianSheaf.{u, u + 1} U) :
    ((etaleLowerShriekAdjunction j).comp (inverseImageAdjunction f)).homEquiv _ _
        ((etaleLowerShriekBaseChangeIso j f).hom.app F) ≫
          (baseChangeMap f (pullback.fst j f) j (pullback.snd j f)
            pullback.condition).app
              ((etaleLowerShriek (pullback.snd j f)).obj
                ((inverseImage (pullback.fst j f)).obj F)) =
      ((inverseImageAdjunction (pullback.fst j f)).comp
        (etaleLowerShriekAdjunction (pullback.snd j f))).unit.app F := by
  rw [← etaleBaseChangeIso_hom]
  exact etaleLowerShriekBaseChangeIso_homEquiv j f F

end AlgebraicGeometry.Scheme.EtaleCohomology
