/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.H0.CyclicSection
public import Aglib.AlgebraicGeometry.EtaleCohomology.H0.CyclicMonomorphism

/-! # The actual cyclic line defined by a nonzero torsion section

The original constant/global-section adjunction defines the map. Its literal
unit-generator equation and the actual geometric value prove monicity.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj
open Scheme.FiniteEtale

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u

attribute [local instance] Over.cartesianMonoidalCategory hasSheafifyLarge

/-- A p-torsion original section with nonzero geometric value defines an actual
monomorphic constant prime-cyclic coefficient map. -/
theorem cyclicSectionMap_mono_of_geometric_value
    {X : Scheme.{u}} {Ω : Type u} [Field Ω] (s : Spec (.of Ω) ⟶ X)
    [GaloisCategory (Scheme.FiniteEtale X)]
    [PreGaloisCategory.FiberFunctor (fiberToFinite s)]
    (H : Grp (Over X)) [IsCommMonObj H.X] [IsFinite H.X.hom] [Etale H.X.hom]
    {p : ℕ} [Fact p.Prime]
    (r : (globalSections X).obj (representedSheaf H)) (hr : p • r = 0)
    (hvalue : (Over.homMk s (by simp) : Over.mk s ⟶ Over.mk (𝟙 X)) ≫
      r.down.toMul ≠ 1) :
    Mono (cyclicSectionMap (representedSheaf H) p r hr) := by
  let A := ConstantFinite.value (ULift.{u} (ZMod p))
  let q := cyclicSectionMap (representedSheaf H) p r hr
  let a : A := ULift.up (ULift.up (1 : ZMod p))
  have hgen : q.hom.app (op (etaleTerminal X))
      (((constantAdjunction X).unit.app A) a) = r := by
    have h := congrArg (fun f : A ⟶ (globalSections X).obj (representedSheaf H) => f a)
      (cyclicSectionMap_adjoint (representedSheaf H) p r hr)
    rw [Adjunction.homEquiv_unit] at h
    exact h.trans (cyclicSectionValues_one (representedSheaf H) p r hr)
  apply cyclic_mono_of_generator_value_ne_zero s H q
  intro hzero
  have he := congrArg
    (fun z : (globalSections X).obj (representedSheaf H) =>
      (Over.homMk s (by simp) : Over.mk s ⟶ Over.mk (𝟙 X)) ≫ z.down.toMul) hgen
  exact hvalue (he.symm.trans hzero)

end AlgebraicGeometry.Scheme.EtaleCohomology
