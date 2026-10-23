/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Basic
public import Aglib.AlgebraicGeometry.Morphisms.Etale.QuasiFinite
public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-!
# Finite etale objects form a basis over a locally Artinian base

Every actual affine etale test is finite over a quasi-separated locally Artinian
base. Thus the existing inclusion of finite etale objects is cover dense in the
original small etale site. Non-quasi-compact etale objects are not claimed finite.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.FiniteEtale

universe u

variable (X : Scheme.{u}) [IsLocallyArtinian X] [QuasiSeparatedSpace X]

private theorem isFinite_of_isAffine_etale {Y : Scheme.{u}} [IsAffine Y]
    (f : Y ⟶ X) [Etale f] : IsFinite f := by
  let : QuasiCompact f := quasiCompact_of_compactSpace f
  exact IsFinite.of_locallyQuasiFinite f

/-- An actual affine etale test over this base is finite. -/
theorem affineEtale_isFinite (A : X.AffineEtale) :
    IsFinite ((AffineEtale.Spec X).obj A).hom := by
  let f : Spec A.left.unop ⟶ X := A.hom
  let : Etale f := A.prop
  exact isFinite_of_isAffine_etale X f

/-- The original finite-etale inclusion is a basis for the original small site. -/
instance toEtale_isCoverDense_of_isLocallyArtinian :
    (toEtale X).IsCoverDense X.smallEtaleTopology where
  is_cover U := by
    apply X.smallEtaleTopology.superset_covering ?_
      ((AffineEtale.Spec X).is_cover_of_isCoverDense X.smallEtaleTopology U)
    intro V f hf
    obtain ⟨⟨A, l, m, h⟩⟩ := hf
    let : IsFinite ((AffineEtale.Spec X).obj A).hom := affineEtale_isFinite X A
    refine ⟨⟨mk ((AffineEtale.Spec X).obj A).hom, l, m, ?_⟩⟩
    exact h

/-- The native induced topology on finite etale objects. -/
def artinTopology : GrothendieckTopology (FiniteEtale X) :=
  (toEtale X).inducedTopology X.smallEtaleTopology

/-- The existing inclusion exhibits the actual finite-etale dense subsite. -/
instance toEtale_isDenseSubsite_of_isLocallyArtinian :
    (toEtale X).IsDenseSubsite (artinTopology X) X.smallEtaleTopology := by
  dsimp [artinTopology]
  infer_instance

end AlgebraicGeometry.Scheme.FiniteEtale
