/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Projective.EmbeddedFibers.Family.Core
public import Aglib.AlgebraicGeometry.Cohomology.Projective.EmbeddedFibers.Basic

/-! # General field-point comparison and proper-family reexports -/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Cohomology

open AlgebraicGeometry.ProjectiveSpace

variable {A : Type u} [CommRing A] {ι : Type u} {X : Scheme.{u}}
  (i : X ⟶ ProjectiveSpace A ι)

/-- Field-point base change with an arbitrary base point equal to `Spec σ ≫ k`: twisted fibre
dimensions are unchanged (`embeddedFiberTwistDim_fieldBaseChange`). -/
theorem embeddedFiberTwistDim_pullbackMap_of_eq [QuasiCompact (i ≫ toSpec A ι)]
    [QuasiSeparated (i ≫ toSpec A ι)] {K K' : Type u} [Field K] [Field K']
    (k : Spec (.of K) ⟶ Spec (.of A)) (φ : CommRingCat.of K ⟶ CommRingCat.of K')
    (k' : Spec (.of K') ⟶ Spec (.of A)) (hk : Spec.map φ ≫ k = k')
    (M : (pullback (i ≫ toSpec A ι) k).Modules) (n : ℤ)
    [(pulledTwist (pullback.fst (i ≫ toSpec A ι) k ≫ i) n M).IsQuasicoherent] (q : ℕ) :
    embeddedFiberTwistDim i k'
        ((Scheme.Modules.pullback (pullback.map (i ≫ toSpec A ι) k' (i ≫ toSpec A ι) k (𝟙 X)
          (Spec.map φ) (𝟙 _) (by simp) (by simp [hk]))).obj M) n q =
      embeddedFiberTwistDim i k M n q := by
  subst hk
  exact embeddedFiberTwistDim_fieldBaseChange i k φ.hom M n q


end AlgebraicGeometry.Scheme.Cohomology
