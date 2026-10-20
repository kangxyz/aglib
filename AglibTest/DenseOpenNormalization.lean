module

import Aglib.AlgebraicGeometry.Normalization.DenseOpen
import Aglib.RingTheory.RegularLocalRing.Normal

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

-- The source's exact universal interface has a proved supplier.
example : Scheme.DenseOpenNormalNormalization.{u} := Scheme.denseOpenNormalNormalization

-- The companion ring predicate is supplied directly by its existing native owner.
example : ∀ (A : Type u) [CommRing A] [IsRegularLocalRing A],
    IsIntegrallyClosed A := by
  intro A _ _
  exact IsRegularLocalRing.isIntegrallyClosed_of_regularLocal A

variable {X Y T X' : Scheme.{u}} (j : X ⟶ Y)
  [QuasiCompact j] [QuasiSeparated j] [IsIntegral Y]
  [IsOpenImmersion j] [IsDominant j] (hY : Scheme.NormalStalks Y)

-- Both arrows are the literal Mathlib normalization arrows.
example : IsIso j.fromNormalization :=
  j.isIso_fromNormalization_of_isOpenImmersion hY

example : (j.denseOpenNormalizationIso hY).hom = j.fromNormalization := rfl

example : j.toNormalization ≫ (j.denseOpenNormalizationIso hY).hom = j := by simp

example : j ≫ (j.denseOpenNormalizationIso hY).inv = j.toNormalization := by simp

-- This is the exact smooth-square normalization comparison used by local models.
example (g : T ⟶ Y) (p : X' ⟶ X) (j' : X' ⟶ T)
    [QuasiCompact j'] [QuasiSeparated j'] [Smooth g] (hp : IsPullback p j' j g) :
    IsIso j'.fromNormalization := by
  have := j.isIso_fromNormalization_of_isOpenImmersion hY
  exact Scheme.Hom.normalizationFrom_isIso_of_smooth_pullback j g p j' hp

-- The canonical comparison to an actual integral final factor is an isomorphism.
example {Z : Scheme.{u}} (g : Y ⟶ Z) [IsIntegralHom g] :
    IsIso ((j ≫ g).normalizationDesc j g rfl) := by
  have := j.isIso_fromNormalization_of_isOpenImmersion hY
  exact Scheme.Hom.normalizationDesc_isIso (j ≫ g) j g rfl

-- On a nonempty affine chart, the coefficient map is the actual algebraMap.
example (U : Y.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    letI := (j.app U).hom.toAlgebra
    Function.Bijective (algebraMap Γ(Y, U) (integralClosure Γ(Y, U) Γ(X, j ⁻¹ᵁ U))) :=
  j.integralClosure_algebraMap_bijective_of_isOpenImmersion hY U hU
