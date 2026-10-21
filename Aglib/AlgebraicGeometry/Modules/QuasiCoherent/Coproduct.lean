/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Limits

/-!
# Arbitrary coproducts of quasicoherent module sheaves

The ambient sheaf coproduct remains quasicoherent. This is proved on actual
open affine charts using the tilde adjunction, rather than replacing the
ambient coproduct with an unrelated quasicoherent object.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules.QuasiCoherent

/-- Module sheaves admit colimits indexed in a smaller universe. -/
instance (priority := 100) moduleSheaf_hasSmallerColimits (X : Scheme.{max u v}) :
    HasColimitsOfSize.{v, v} X.Modules :=
  hasColimitsOfSizeShrink X.Modules

instance affineQuasicoherent_hasColimits (R : CommRingCat.{u}) :
    HasColimitsOfSize.{u, u} (AffineQuasicoherent R) where
  has_colimits_of_shape _ _ :=
    Adjunction.hasColimitsOfShape_of_equivalence (tildeEquiv (R := R)).inverse

instance affineQuasicoherentToSheaves_preservesColimits (R : CommRingCat.{u}) :
    PreservesColimitsOfSize.{u, u}
      (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).ι := by
  have : PreservesColimitsOfSize.{u, u}
      ((tildeEquiv (R := R)).inverse ⋙ tilde.functor R) := inferInstance
  exact preservesColimits_of_natIso (affineQuasicoherentToSheavesIso R)

instance affineQuasicoherent_colimitsOfShape (R : CommRingCat.{max u v})
    (J : Type v) [Category.{v} J] :
    (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).IsClosedUnderColimitsOfShape J := by
  let P := SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf
  let : HasColimitsOfSize.{v, v} (AffineQuasicoherent R) :=
    hasColimitsOfSizeShrink (AffineQuasicoherent R)
  let : PreservesColimitsOfSize.{v, v} P.ι := preservesColimitsOfSize_shrink P.ι
  exact P.isClosedUnderColimitsOfShape_of_preservesColimitsOfShape_ι J

instance quasicoherent_colimitsOfShape (X : Scheme.{max u v})
    (J : Type v) [Category.{v} J] :
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).IsClosedUnderColimitsOfShape J where
  colimitsOfShape_le := by
    rintro M ⟨p⟩
    apply quasicoherent_of_affineCharts M
    intro R j _
    exact (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).prop_of_isColimit
      (isColimitOfPreserves (Scheme.Modules.restrictFunctor j) p.isColimit)
      (fun i => by
        have : (p.diag.obj i).IsQuasicoherent := p.prop_diag_obj i
        change ((Scheme.Modules.restrictFunctor j).obj (p.diag.obj i)).IsQuasicoherent
        infer_instance)

/-- The actual ambient coproduct of quasicoherent coefficients is quasicoherent. -/
theorem quasicoherent_coproduct {X : Scheme.{max u v}} {ι : Type v}
    (M : ι → X.Modules) [∀ i, (M i).IsQuasicoherent] :
    (∐ M).IsQuasicoherent := by
  apply (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_isColimit
    (coproductIsCoproduct M)
  intro i
  exact inferInstanceAs (M i.as).IsQuasicoherent

end AlgebraicGeometry.Scheme.Modules.QuasiCoherent
