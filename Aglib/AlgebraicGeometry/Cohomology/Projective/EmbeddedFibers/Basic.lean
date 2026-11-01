/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Projective.EmbeddedFibers.FieldComparison
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Modules.Qcqs

/-! # Geometric producers for the original twisted field comparison -/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Cohomology

variable {A : Type u} [CommRing A] {ι : Type u} {X : Scheme.{u}}
  (i : X ⟶ ProjectiveSpace A ι)

/-- **Twisted fibre dimensions are unchanged by field extension**, for a quasicoherent twist
and a quasi-compact quasi-separated `f = i ≫ toSpec A ι` (Kleiman, arXiv:math/0504020v1, p. 28:
cohomology commutes with flat base change). -/
theorem embeddedFiberTwistDim_fieldBaseChange [QuasiCompact (i ≫ ProjectiveSpace.toSpec A ι)]
    [QuasiSeparated (i ≫ ProjectiveSpace.toSpec A ι)] {K K' : Type u} [Field K] [Field K']
    (k : Spec (.of K) ⟶ Spec (.of A)) (σ : K →+* K')
    (M : (pullback (i ≫ ProjectiveSpace.toSpec A ι) k).Modules) (n : ℤ)
    [(pulledTwist (pullback.fst (i ≫ ProjectiveSpace.toSpec A ι) k ≫ i) n M).IsQuasicoherent]
    (q : ℕ) :
    embeddedFiberTwistDim i (Spec.map (CommRingCat.ofHom σ) ≫ k)
        ((Scheme.Modules.pullback (fieldExtensionBaseChange i k σ)).obj M) n q =
      embeddedFiberTwistDim i k M n q := by
  let := moduleCohomologyBaseChangeMap_isIso_of_quasiSeparated
    (pullback.snd (i ≫ ProjectiveSpace.toSpec A ι) k) σ
    (RingHom.Flat.of_isField (Field.toIsField K) σ)
    (pulledTwist (pullback.fst (i ≫ ProjectiveSpace.toSpec A ι) k ≫ i) n M) q
  exact embeddedFiberTwistDim_fieldBaseChange_of_isIso i k σ M n q

end AlgebraicGeometry.Scheme.Cohomology
