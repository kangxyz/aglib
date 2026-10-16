/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.ChangeOfRings.Additive
public import Aglib.Algebra.Homology.ShortComplex.Adjunction
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
# The canonical scalar-extension map on actual homology

The native extension/restriction adjunction gives a canonical map on
short-complex and complex homology for every ring homomorphism. Its unit and
naturality equations identify the original map, which agrees with the inverse
of the native homology comparison when scalar extension preserves homology.

In a rightmost degree, arbitrary scalar extension commutes with homology
without a flatness assumption. No finite-projective hypothesis is needed for
these constructions.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ChangeOfRings

namespace ModuleCat

universe u v w

variable {R : Type u} {S : Type w} [CommRing R] [CommRing S]
  (φ : R →+* S) (T : ShortComplex (ModuleCat.{max v w} R))

/-- Canonical scalar extension on actual short-complex homology, using the
existing extension/restriction adjunction and its original unit. -/
abbrev homologyBaseChangeMap :
    (extendScalars φ).obj T.homology ⟶ (T.map (extendScalars φ)).homology :=
  (extendRestrictScalarsAdj φ).homologyComparison T

/-- The canonical map retains the scalar-extension adjunction-unit equation. -/
theorem homologyBaseChangeMap_unit :
    (extendRestrictScalarsAdj φ).unit.app T.homology ≫
      (restrictScalars φ).map (homologyBaseChangeMap φ T) =
        (extendRestrictScalarsAdj φ).homologyUnit T :=
  (extendRestrictScalarsAdj φ).homologyComparison_unit T

/-- On the unit pure tensor, base change is the original normalized unit on homology. -/
theorem homologyBaseChangeMap_one_tmul (x : T.homology) :
    homologyBaseChangeMap φ T ((1 : S) ⊗ₜ[R,φ] x) =
      (extendRestrictScalarsAdj φ).homologyUnit T x :=
  congrArg (fun q => q x) (homologyBaseChangeMap_unit φ T)

/-- Canonical scalar extension on homology is natural in the actual short complex. -/
@[reassoc]
theorem homologyBaseChangeMap_naturality {T U : ShortComplex (ModuleCat.{max v w} R)}
    (f : T ⟶ U) :
    (extendScalars φ).map (ShortComplex.homologyMap f) ≫ homologyBaseChangeMap φ U =
      homologyBaseChangeMap φ T ≫
        ShortComplex.homologyMap ((extendScalars φ).mapShortComplex.map f) :=
  (extendRestrictScalarsAdj φ).homologyComparison_naturality f

/-- Exact scalar extension identifies the canonical mate with the native
homology-comparison isomorphism, in its original direction. -/
theorem homologyBaseChangeMap_eq_mapHomologyIso_inv
    [(extendScalars φ).PreservesHomology] :
    homologyBaseChangeMap φ T = (T.mapHomologyIso (extendScalars φ)).inv := by
  let : PreservesFiniteLimits (extendScalars φ) :=
    Functor.preservesFiniteLimits_of_preservesHomology _
  let : PreservesFiniteColimits (extendScalars φ) :=
    Functor.preservesFiniteColimits_of_preservesHomology _
  exact (extendRestrictScalarsAdj φ).homologyComparison_eq_mapHomologyIso_inv T

/-- Arbitrary scalar extension commutes canonically with rightmost homology:
only the zero outgoing differential is assumed. -/
theorem homologyBaseChangeMap_isIso_of_g_eq_zero (hg : T.g = 0) :
    IsIso (homologyBaseChangeMap φ T) := by
  let F := extendScalars φ
  let G := restrictScalars φ
  let : F.PreservesLeftHomologyOf T := F.preservesLeftHomology_of_zero_g T hg
  let : F.PreservesRightHomologyOf T := F.preservesRightHomology_of_zero_g T hg
  let : (F ⋙ G).PreservesLeftHomologyOf T :=
    (F ⋙ G).preservesLeftHomology_of_zero_g T hg
  let : (F ⋙ G).PreservesRightHomologyOf T :=
    (F ⋙ G).preservesRightHomology_of_zero_g T hg
  change IsIso ((extendRestrictScalarsAdj φ).homologyComparison T)
  rw [(extendRestrictScalarsAdj φ).homologyComparison_eq_mapHomologyIso_inv T]
  infer_instance

end ModuleCat

namespace HomologicalComplex

universe u v w

variable {R : Type u} {S : Type w} [CommRing R] [CommRing S]
  {ι : Type*} {c : ComplexShape ι} (φ : R →+* S)

/-- The canonical scalar-extension map on the actual homology of a complex. -/
abbrev extendScalarsHomologyMap (K : HomologicalComplex (ModuleCat.{max v w} R) c) (n : ι) :
    (ModuleCat.extendScalars φ).obj (K.homology n) ⟶
      (((ModuleCat.extendScalars φ).mapHomologicalComplex c).obj K).homology n :=
  ModuleCat.homologyBaseChangeMap φ (K.sc n)

/-- A zero outgoing differential suffices for arbitrary base change in the
rightmost degree of the actual complex. -/
theorem extendScalarsHomologyMap_isIso_of_d_eq_zero
    (K : HomologicalComplex (ModuleCat.{max v w} R) c) (n : ι)
    (h : K.d n (c.next n) = 0) : IsIso (extendScalarsHomologyMap φ K n) :=
  ModuleCat.homologyBaseChangeMap_isIso_of_g_eq_zero φ (K.sc n) h

end HomologicalComplex
