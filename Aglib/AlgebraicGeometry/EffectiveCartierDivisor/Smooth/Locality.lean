/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EffectiveCartierDivisor.Smooth.Field
public import Aglib.AlgebraicGeometry.EffectiveCartierDivisor.FinitePresentation
public import Aglib.AlgebraicGeometry.IdealSheaf.BaseChange.Fibre
public import Aglib.AlgebraicGeometry.IdealSheaf.BaseChange.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite

/-!
# Local quasi-finiteness of flat Cartier subschemes in smooth relative curves

## Extraction basis

Existing proofs transferred from frozen dirty R5 revision
`79307ff88f07d34fd5c3edb859f799c55e38f290`. Source identities:

- `R5Lab/AlgebraicGeometry/Curves/RelativeDivisors/CartierLocality.lean`, SHA-256
  `d11c4ffb39327cd751cb517541e51344ca708630381facd0620868347b548718`.

Actual objects, maps, universes and stated conditions are retained.
Native validation coverage is recorded separately in `doc/WORK_PLAN.md` and
the migration records; the source hashes above identify extraction inputs.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w t

open CategoryTheory Limits AlgebraicGeometry Opposite TopologicalSpace
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.Scheme.Modules
open LinearMap
open AlgebraicGeometry.Scheme.Modules.Invertible

section
namespace AlgebraicGeometry.Scheme.Hom

open scoped nonZeroDivisors
variable {D X : Scheme.{u}} (i : D ⟶ X)

/-- Relative Cartier locality follows from the original quotient-flat ideal base-change
family. This is an explicit conditional deduction, not a supplier for either family. -/
theorem locallyQuasiFinite_and_locallyOfFinitePresentation_of_idealBaseChange
    (hbase : (∀ (S T X Y D D' : Scheme.{u}) (p : X ⟶ S) (q : T ⟶ S) (p' : Y ⟶ T)
    (b : Y ⟶ X) (i : D ⟶ X) (i' : D' ⟶ Y) (a : D' ⟶ D)
    (h : a ≫ i = i' ≫ b),
    IsPullback b p' p q → IsPullback a i' i b → IsClosedImmersion i →
      IsLocallyRankOne X (idealModule i) → Flat (i ≫ p) →
        IsIso (idealPullbackMap i i' b a h))) : (∀ (S X D : Scheme.{u}) (p : X ⟶ S) (i : D ⟶ X),
    SmoothOfRelativeDimension 1 p → IsClosedImmersion i →
      IsLocallyRankOne X (idealModule i) → Flat (i ≫ p) →
        LocallyQuasiFinite (i ≫ p) ∧ LocallyOfFinitePresentation (i ≫ p)) := by
  intro S X D p i hp hi hI hf
  let : SmoothOfRelativeDimension 1 p := hp
  let : Smooth p := SmoothOfRelativeDimension.smooth 1 p
  let : IsClosedImmersion i := hi
  let : Flat (i ≫ p) := hf
  let : LocallyOfFinitePresentation (i ≫ p) := relativeCartier_locallyOfFinitePresentation i p hI
  refine ⟨?_, inferInstance⟩
  apply LocallyQuasiFinite.of_fiberToSpecResidueField (i ≫ p)
  intro s
  let t := S.fromSpecResidueField s
  let : SmoothOfRelativeDimension 1 (pullback.snd p t) :=
    MorphismProperty.pullback_snd p t hp
  have hIfibre : IsLocallyRankOne (pullback p t) (idealModule (fibreInclusion p i t)) :=
    (fibreIdealLineBundle p i t hbase hI).property
  let : IsLocallyArtinian ((i ≫ p).fiber s) :=
    smoothFieldCartier_isLocallyArtinian (S.residueField s) (pullback.snd p t)
      (fibreInclusion p i t) hIfibre
  let : LocallyOfFiniteType ((i ≫ p).fiberToSpecResidueField s) :=
    MorphismProperty.pullback_snd (i ≫ p) t inferInstance
  exact locallyQuasiFinite_iff_isDiscrete_preimage_singleton.mpr
    fun _ ↦ isDiscrete_iff_discreteTopology.mpr inferInstance

/-- The unchanged arbitrary-base smooth relative Cartier locality interface. -/
theorem locallyQuasiFinite_and_locallyOfFinitePresentation_of_smooth_cartier : (∀ (S X D :
  Scheme.{u}) (p : X ⟶ S) (i : D ⟶ X),
    SmoothOfRelativeDimension 1 p → IsClosedImmersion i →
      IsLocallyRankOne X (idealModule i) → Flat (i ≫ p) →
        LocallyQuasiFinite (i ≫ p) ∧ LocallyOfFinitePresentation (i ≫ p)) :=
  locallyQuasiFinite_and_locallyOfFinitePresentation_of_idealBaseChange
    idealPullbackMap_isIso_of_relativeCartier

end AlgebraicGeometry.Scheme.Hom
end
