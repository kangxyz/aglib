/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Galois.FixedPoints
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.RepresentedCoefficients
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.TorsorAction
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.CoverLimits

/-! # Original represented global sections from invariant geometric points

Native finite-etale fibre fullness supplies an actual section of the
coefficient scheme. It is returned as a section of the original represented
additive sheaf, together with its literal restriction to the geometric point.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj
open Scheme.FiniteEtale Scheme.FiniteEtale.FiberTorsorActions

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u

attribute [local instance] Over.cartesianMonoidalCategory

variable {X : Scheme.{u}} {Ω : Type u} [Field Ω]
  (s : Spec (.of Ω) ⟶ X)
  [GaloisCategory (Scheme.FiniteEtale X)]
  [PreGaloisCategory.FiberFunctor (fiberToFinite s)]
  (H : Grp (Over X)) [IsCommMonObj H.X] [IsFinite H.X.hom] [Etale H.X.hom]

/-- An invariant actual geometric point comes from an original global
represented-sheaf section, with its exact scheme-point normalization. -/
theorem exists_represented_globalSection_of_fixed_point
    (a : Over.mk s ⟶ H.X)
    (ha : ∀ g : Aut (fiberToFinite s), g.hom.app (coefficientCover H) a = a) :
    ∃ r : (representedSheaf H).obj.obj (op (Scheme.Etale.mk (𝟙 X))),
      (Over.homMk s (by simp) : Over.mk s ⟶ Over.mk (𝟙 X)) ≫ r.down.toMul = a := by
  obtain ⟨f, hf⟩ := PreGaloisCategory.exists_hom_of_fixed_fiber_point
    (fiberToFinite s) (T := terminalCover X) (A := coefficientCover H) a ha
  refine ⟨ULift.up (Additive.ofMul f.hom), ?_⟩
  exact hf (Over.homMk s (by change s ≫ 𝟙 X = s; exact Category.comp_id s))

end AlgebraicGeometry.Scheme.EtaleCohomology
