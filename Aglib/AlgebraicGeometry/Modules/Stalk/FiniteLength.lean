/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.FiniteLength.Support
public import Aglib.AlgebraicGeometry.Modules.Stalk.Basic
public import Aglib.AlgebraicGeometry.Modules.Coherent.Affine.Comparison
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.FiniteTypeComparison
public import Mathlib.AlgebraicGeometry.Stalk
public import Aglib.AlgebraicGeometry.Modules.Support
public import Aglib.AlgebraicGeometry.Modules.Coherent.Affine.Property
public import Aglib.AlgebraicGeometry.Modules.Exact
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.FiniteTypeProperty
public import Aglib.CategoryTheory.SmallModel.Abelian
public import Aglib.AlgebraicGeometry.Modules.FinitePresentation.Noetherian
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.FiniteGenerators
public import Aglib.Algebra.Category.ModuleCat.FiniteLength.Restriction

/-!
# Finite length at actual affine closed stalks

Source-only extraction from `R5Lab.KTheory.Quillen.LocalLengthTransport` at R5Lab revision
`e6d63abca2403f50b6b413101ad7f6a7f2e0e2c7`. Existing objects, maps,
hypotheses, universes, proof bodies and mathematical namespaces are retained.
The original source correspondence remains in the supplying application module.
-/



/-!
Native migration from `R5Lab.Aglib.AlgebraicGeometry.Modules.Stalk.FiniteLength` at R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`58dcf2fd8a29985db51fccffa439b31c82e0a1bdaec3c04f13601572478bf479`.
Original objects, maps, universes and explicit hypotheses are retained.
Native providers replace duplicate implementations.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.Modules.Stalk
universe u v
/-- Over a local ring, the closed-point stalk of a finite-length tilde module
has finite length for the actual stalk-ring scalar action. -/
theorem tilde_closedStalk_finiteLength (R : CommRingCat.{u}) [IsLocalRing R]
    (M : ModuleCat.{u} R) (hM : IsFiniteLength R M) :
    IsFiniteLength ((Spec R).presheaf.stalk (IsLocalRing.closedPoint R))
      ((Scheme.Modules.moduleStalk (Spec R) (IsLocalRing.closedPoint
          R)).obj (tilde M)) := by
  let x := IsLocalRing.closedPoint R
  change IsFiniteLength ((structurePresheafInCommRingCat R).stalk x)
    ↑(TopCat.Presheaf.stalk (moduleStructurePresheaf R M).presheaf x)
  have hs : Function.Surjective (StructureSheaf.toStalkₗ R M x) :=
    ModuleCat.localizedModule_surjective_of_units x.asIdeal.primeCompl (StructureSheaf.toStalkₗ
        R M x)
      (fun s => IsLocalRing.notMem_maximalIdeal.mp s.2)
  have hR := hM.of_surjective hs
  obtain ⟨hn, ha⟩ := isFiniteLength_iff_isNoetherian_isArtinian.mp hR
  exact isFiniteLength_iff_isNoetherian_isArtinian.mpr
    ⟨isNoetherian_of_tower R hn, isArtinian_of_tower R ha⟩

/-- Actual quasicoherent affine comparison transports finite-length sections to
the actual closed-point stalk. -/
-- Retain the original Noetherian local base of the coherent finite-length comparison.
@[nolint unusedArguments]
theorem coherent_closedStalk_finiteLength (R : CommRingCat.{u}) [IsNoetherianRing R]
    [IsLocalRing R] (M :
        Scheme.Modules.QuasiCoherent.FiniteTypeSheaves (Spec R))
    (hM : IsFiniteLength R (moduleSpecΓFunctor.obj M.obj)) :
    IsFiniteLength ((Spec R).presheaf.stalk (IsLocalRing.closedPoint R))
      ((Scheme.Modules.moduleStalk (Spec R) (IsLocalRing.closedPoint
          R)).obj M.obj) := by
  have hcoh :=
      (Scheme.Modules.QuasiCoherent.affineLocallyFiniteType_spec_iff R
      M.obj).mp M.property
  let : M.obj.IsQuasicoherent := hcoh.1
  let e := (Scheme.Modules.moduleStalk (Spec R)
      (IsLocalRing.closedPoint R)).mapIso (asIso M.obj.fromTildeΓ)
  exact e.toLinearEquiv.isFiniteLength (tilde_closedStalk_finiteLength R _ hM)

end AlgebraicGeometry.Scheme.Modules.Stalk
