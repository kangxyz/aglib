/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Aglib.AlgebraicGeometry.Normalization.GenericFiniteEtale.RegularBase

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.FiniteEtale.GenericNormalization

universe u

namespace AglibTest.RegularNormalizationPurity

/-- The original target-local hypothesis gives the original structural morphism,
without any purity, dimension-comparison, localization or base-normality input. -/
example (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    [∀ x : X, IsRegularLocalRing (X.presheaf.stalk x)]
    (C : Scheme.FiniteEtale (Spec X.functionField))
    (hlocal : ∀ x : Scheme.CodimensionOnePoint X,
      Etale (pullback.snd (C.obj.hom ≫ X.fromSpecStalk (genericPoint X)).fromNormalization
        (X.fromSpecStalk x.1))) :
    Etale (C.obj.hom ≫ X.fromSpecStalk (genericPoint X)).fromNormalization :=
  etale_of_regularStalks X C hlocal

/-- The admitted empty cover needs no invented generic or normalization point. -/
example (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    [∀ x : X, IsRegularLocalRing (X.presheaf.stalk x)]
    (hlocal : ∀ x : Scheme.CodimensionOnePoint X,
      Etale (pullback.snd
        (Scheme.emptyTo (Spec X.functionField) ≫ X.fromSpecStalk (genericPoint X)).fromNormalization
        (X.fromSpecStalk x.1))) :
    Etale (Scheme.emptyTo (Spec X.functionField) ≫
      X.fromSpecStalk (genericPoint X)).fromNormalization :=
  etale_of_regularStalks X (Scheme.FiniteEtale.mk (Scheme.emptyTo _)) hlocal

/-- A concrete disconnected finite etale cover in the original universe. -/
def splitCover (K : Type u) [Field K] : Scheme.FiniteEtale (Spec (.of K)) := by
  let f := Spec.map (CommRingCat.ofHom (algebraMap K (Fin 2 → K)))
  let : IsFinite f := IsFinite.SpecMap_iff _ |>.mpr
    (RingHom.finite_algebraMap.mpr inferInstance)
  let : Etale f := HasRingHomProperty.Spec_iff.mpr
    (RingHom.etale_algebraMap.mpr inferInstance)
  exact Scheme.FiniteEtale.mk f

/-- The split generic algebra is kept as a product, with no domain premise on it. -/
example (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    [∀ x : X, IsRegularLocalRing (X.presheaf.stalk x)]
    (hlocal : ∀ x : Scheme.CodimensionOnePoint X,
      Etale (pullback.snd
        ((splitCover X.functionField).obj.hom ≫
          X.fromSpecStalk (genericPoint X)).fromNormalization (X.fromSpecStalk x.1))) :
    Etale ((splitCover X.functionField).obj.hom ≫
      X.fromSpecStalk (genericPoint X)).fromNormalization :=
  etale_of_regularStalks X (splitCover X.functionField) hlocal

end AglibTest.RegularNormalizationPurity
