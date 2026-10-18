/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.Proper.BaseChange
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Data.ZMod.Basic

/-! Concrete general-base proper base-change consumers. The new base can be a
nonflat infinite-variable polynomial algebra; the original base can be nonreduced.
The endpoints use the actual comparison and actual residue-map epimorphism. -/

@[expose] public section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open AlgebraicGeometry.Scheme.Cohomology

noncomputable section

private abbrev TargetRing := MvPolynomial ℕ (ZMod 2)

private abbrev integerBaseChange :
    Spec (CommRingCat.of TargetRing) ⟶ Spec (CommRingCat.of ℤ) :=
  Spec.map (CommRingCat.ofHom (Int.castRingHom TargetRing))

-- The new base is the infinite-variable polynomial ring over Z/2.
-- This consumer supplies neither target Noetherianity nor flatness of the base map.
example {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of ℤ)) [IsProper f]
    (M : X.Modules) (hM : affineLocallyFiniteType X M) (hflat : relativeFlat f M)
    (q : ℕ) (hdim : IsLocallyConstant (modulePointFiberCohomologyDimension f M q)) :
    letI : M.IsQuasicoherent := quasicoherent_of_affineCharts M (fun A j _ => (hM A j).1)
    IsIso (higherDirectImageBaseChangeMap
      (Limits.pullback.fst f integerBaseChange) (Limits.pullback.snd f integerBaseChange)
      f integerBaseChange (IsPullback.of_hasPullback f integerBaseChange) q M) :=
  higherDirectImageBaseChangeMap_isIso_of_isLocallyConstant_of_proper
    _ _ f integerBaseChange (IsPullback.of_hasPullback f integerBaseChange)
    M hM hflat q hdim

-- The base Z/4 supplies no reducedness instance; the residue condition is the actual map.
example {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of (ZMod 4))) [IsProper f]
    (M : X.Modules) (hM : affineLocallyFiniteType X M) (hflat : relativeFlat f M)
    (q : ℕ) (y : Spec (CommRingCat.of (ZMod 4)))
    (hres : letI : M.IsQuasicoherent :=
        quasicoherent_of_affineCharts M (fun A j _ => (hM A j).1)
      Epi (higherDirectImageResidueBaseChangeMap f M q y)) :
    letI : M.IsQuasicoherent := quasicoherent_of_affineCharts M (fun A j _ => (hM A j).1)
    ∃ U : (Spec (CommRingCat.of (ZMod 4))).Opens, y ∈ U ∧
      ∀ (Z : Scheme.{0}) (g : Z ⟶ U.toScheme),
        IsIso (higherDirectImageBaseChangeMap
          (Limits.pullback.fst f (g ≫ U.ι)) (Limits.pullback.snd f (g ≫ U.ι))
          f (g ≫ U.ι) (IsPullback.of_hasPullback f (g ≫ U.ι)) q M) :=
  exists_open_higherDirectImageBaseChangeMap_isIso_of_epi_residue_of_proper
    f M hM hflat q y hres
