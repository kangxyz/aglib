/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Cohomology.Proper.Semicontinuity
public import Aglib.AlgebraicGeometry.Cohomology.Proper.Finiteness
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.Pullback

/-!
# Openness of vanishing for actual proper fibre H⁰

This generic corollary uses `moduleCohomology_finite_of_proper` and
`upperSemicontinuous_modulePointFiberCohomologyDimension_of_proper` from
`Aglib.AlgebraicGeometry.Cohomology.Proper.Finiteness` and
`Aglib.AlgebraicGeometry.Cohomology.Proper.Semicontinuity` at Aglib revision
`197ca0728db3cdf1552a6bcefeeda901e3377862`.

The fibre is the native pullback over the actual residue field, the coefficient
is the ordinary pullback of the original module sheaf, and cohomology retains
the structural residue-field action. Proper finiteness is proved before using
zero `finrank` to characterize vanishing.
-/


/-!
Native migration from `R5Lab.Aglib.AlgebraicGeometry.Cohomology.Proper.H0Vanishing` at R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`5f9e4403474fc4e76b704564f6eb7a8d9c28432da65ee3340c18d8a472fc2ad0`.
Original objects, maps, universes and explicit hypotheses are retained.
Native providers replace duplicate implementations.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent

namespace AlgebraicGeometry.Scheme.Cohomology

universe u

/-- Every degree of actual point-fibre cohomology is finite over the original
residue field, by native proper finiteness after coherent pullback. -/
theorem modulePointFiberCohomology_finite_of_proper
    {X Y : Scheme.{u}} [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [IsProper f] (M : X.Modules)
    (hM : affineLocallyFiniteType X M) (q : ℕ) (y : Y) :
    Module.Finite (Y.residueField y) (modulePointFiberCohomology f M q y) := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let : IsProper (f.fiberToSpecResidueField y) :=
    MorphismProperty.pullback_snd _ _ inferInstance
  exact moduleCohomology_finite_of_proper (Y.residueField y)
    (f.fiberToSpecResidueField y) ((Scheme.Modules.pullback (f.fiberι y)).obj M)
    (affineLocallyFiniteType_pullback (f.fiberι y) hM) q

/-- For a proper coherent relatively flat family over a locally Noetherian
target, vanishing of actual fibre H⁰ is an open condition. -/
theorem isOpen_setOf_subsingleton_modulePointFiberH0_of_proper
    {X Y : Scheme.{u}} [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [IsProper f] (M : X.Modules)
    (hM : affineLocallyFiniteType X M) (hflat : Scheme.Modules.relativeFlat f M) :
    IsOpen {y : Y | Subsingleton (modulePointFiberCohomology f M 0 y)} := by
  have hdim := upperSemicontinuous_modulePointFiberCohomologyDimension_of_proper
    f M hM hflat 0
  have he : {y : Y | Subsingleton (modulePointFiberCohomology f M 0 y)} =
      (modulePointFiberCohomologyDimension f M 0) ⁻¹' Set.Iio 1 := by
    ext y
    let := modulePointFiberCohomology_finite_of_proper f M hM 0 y
    change Subsingleton (modulePointFiberCohomology f M 0 y) ↔
      Module.finrank (Y.residueField y) (modulePointFiberCohomology f M 0 y) < 1
    rw [Nat.lt_one_iff, Module.finrank_zero_iff]
  rw [he]
  exact hdim.isOpen_preimage 1

end AlgebraicGeometry.Scheme.Cohomology
