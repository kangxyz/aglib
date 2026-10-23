/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.RepresentedKernel
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.CoverPreservation
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.TorsorAction
public import Mathlib.CategoryTheory.Galois.Basic
public import Mathlib.CategoryTheory.Limits.Constructions.EpiMono

/-! # Detecting represented coefficient monomorphisms on the actual fibre

The original finite-etale fibre functor reflects monomorphisms. Forgetting to
the scheme slice preserves finite limits, and the original represented sheaf
map is then pointwise injective. No independent coefficient category is used.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Scheme.FiniteEtale Scheme.FiniteEtale.FiberTorsorActions

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u

attribute [local instance] Over.cartesianMonoidalCategory

/-- Injectivity on the actual geometric coefficient points implies monicity
of the original represented additive sheaf morphism. -/
theorem representedSheafMap_mono_of_fiber_injective
    {X : Scheme.{u}} {Ω : Type u} [Field Ω] (s : Spec (.of Ω) ⟶ X)
    [GaloisCategory (Scheme.FiniteEtale X)]
    [PreGaloisCategory.FiberFunctor (fiberToFinite s)]
    {A B : Grp (Over X)} [IsCommMonObj A.X] [IsCommMonObj B.X]
    [IsFinite A.X.hom] [Etale A.X.hom] [IsFinite B.X.hom] [Etale B.X.hom]
    (q : A ⟶ B) (hq : Function.Injective
      (fun a : Over.mk s ⟶ A.X => a ≫ q.hom.hom)) :
    Mono (representedSheafMap q) := by
  let f : coefficientCover A ⟶ coefficientCover B := ObjectProperty.homMk q.hom.hom
  have hf : Mono ((fiberToFinite s).map f) :=
    ConcreteCategory.mono_of_injective _ hq
  have : Mono f := (fiberToFinite s).mono_of_mono_map hf
  have : Mono q.hom.hom := (Scheme.FiniteEtale.forget X).map_mono f
  exact RepresentedKernel.represented_mono q

end AlgebraicGeometry.Scheme.EtaleCohomology
