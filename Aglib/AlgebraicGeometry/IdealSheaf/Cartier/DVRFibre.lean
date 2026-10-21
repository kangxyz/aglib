/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.IdealSheaf.Cartier.Interfaces
public import Aglib.AlgebraicGeometry.IdealSheaf.BaseChange.FlatMorphism
public import Aglib.AlgebraicGeometry.IdealSheaf.Affine
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.Free
public import Aglib.RingTheory.Ideal.RegularPrincipal
public import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-!
# Triviality of the actual special-fibre ideal over a DVR

For a flat morphism from an arbitrary scheme to the spectrum of a discrete
valuation ring, the ideal module of the literal residue-field fibre is
isomorphic to the structure module. The construction chooses a singleton basis
of the actual residue kernel, sheafifies it, and applies the canonical ideal
base-change isomorphism along the given flat morphism.

The public theorem inhabits the existing `FlatDVRFibreIdealTrivial` family.
There are no regularity, Noetherianity, properness, or reduced-fibre assumptions.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Hom.Cartier

variable (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- A singleton basis of the original residue kernel, chosen from its actual
nonzero principal ideal. -/
def dvrResidueKernelBasis :
    Module.Basis PUnit.{u + 1} R (RingHom.ker (IsLocalRing.residue R)) :=
  Ideal.principalIdealBasis _ (by
    rw [IsLocalRing.ker_residue]
    exact IsDiscreteValuationRing.not_a_field R)

/-- Sheafification of a basis of the actual residue kernel trivializes the
actual ideal module of the closed point of the DVR spectrum. -/
def dvrResidueIdealIso :
    idealModule (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) ≅
      SheafOfModules.unit (Spec (.of R)).ringCatSheaf :=
  (affineIdealIso (CommRingCat.ofHom (IsLocalRing.residue R))).symm ≪≫
    tildeBasisIso _ (dvrResidueKernelBasis R) ≪≫ coproductUniqueIso _

variable (X : Scheme.{u}) (π : X ⟶ Spec (.of R)) [Flat π]

/-- The canonical ideal comparison for the literal residue-field fibre, with
the projection orientation occurring in `FlatDVRFibreIdealTrivial`. -/
def flatDVRFibreIdealBaseChangeIso :
    (Scheme.Modules.pullback π).obj
        (idealModule (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))) ≅
      idealModule (pullback.fst π
        (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))) := by
  let i := Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))
  have := idealPullbackMap_isIso_of_flat i π (pullback.fst π i)
    (pullback.snd π i) (pullback.condition (f := π) (g := i)).symm
    (IsPullback.of_hasPullback π i).flip
  exact asIso (idealPullbackMap i (pullback.fst π i) π (pullback.snd π i)
    (pullback.condition (f := π) (g := i)).symm)

/-- The base-change isomorphism preserves the original fibre-ideal inclusion. -/
@[reassoc]
theorem flatDVRFibreIdealBaseChangeIso_hom_inclusion :
    (flatDVRFibreIdealBaseChangeIso R X π).hom ≫
        idealInclusion (pullback.fst π
          (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))) =
      (Scheme.Modules.pullback π).map
          (idealInclusion (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))) ≫
        (pullbackUnitIso π).hom := by
  exact idealPullbackMap_inclusion _ _ _ _ _

/-- The actual ideal module of the residue-field fibre of a flat DVR scheme
is trivial, using the chosen basis on the original DVR spectrum. -/
def flatDVRFibreIdealIso :
    idealModule (pullback.fst π
      (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))) ≅
        SheafOfModules.unit X.ringCatSheaf :=
  (flatDVRFibreIdealBaseChangeIso R X π).symm ≪≫
    (Scheme.Modules.pullback π).mapIso (dvrResidueIdealIso R) ≪≫ pullbackUnitIso π

/-- A proof of the existing general flat-DVR fibre-ideal theorem family. -/
theorem flatDVRFibreIdealTrivial : FlatDVRFibreIdealTrivial.{u} := by
  intro R _ _ _ X π hπ
  let := hπ
  exact ⟨flatDVRFibreIdealIso R X π⟩

end AlgebraicGeometry.Scheme.Hom.Cartier
