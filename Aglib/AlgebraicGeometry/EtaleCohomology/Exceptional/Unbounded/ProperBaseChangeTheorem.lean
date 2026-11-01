/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.GeometricLocality
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.AffineCoverGeometry

/-! # Unbounded proper base change for the original module exchange

Actual affine charts and their original Cartesian pullbacks supply the local
geometry. The proved proper geometric relative bounds discharge the local
vanishing inputs. Thus the same original exchange is invertible on the full
unbounded derived categories, without a quasi-compactness assumption on either
base, a supplied cohomological bound, or invertibility of the torsion exponent.
The four original module derived models remain independently sized; standard
models are chosen only for the auxiliary chart calculation.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Proper

open Coefficients

universe u wX wS wX' wS'

attribute [local instance] hasSheafifyLarge

variable (Λ : Type (u + 1)) [Ring Λ] {X S X' S' : Scheme.{u}}
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
  [HasDerivedCategory.{wX'} (ModuleSheaf X' Λ)]
  [HasDerivedCategory.{wS'} (ModuleSheaf S' Λ)]

/-- The original unbounded proper exchange is an isomorphism for a torsion
coefficient ring. Both bases and the unbounded input are arbitrary. -/
theorem properModuleUnboundedDerivedBaseChange_isIso
    (f : X ⟶ S) [IsProper f] (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (sq : IsPullback g' f' f g) (N : ℕ) (hN : 0 < N) (hΛ : N • (1 : Λ) = 0) :
    IsIso (moduleUnboundedDerivedBaseChangeMap Λ f f' g g' sq.w.symm) := by
  let : ∀ i : AffineCoverGeometry.Index S,
      HasDerivedCategory (ModuleSheaf (AffineCoverGeometry.Y f i) Λ) :=
    fun i => HasDerivedCategory.standard (ModuleSheaf (AffineCoverGeometry.Y f i) Λ)
  let : ∀ i : AffineCoverGeometry.Index S,
      HasDerivedCategory (ModuleSheaf (AffineCoverGeometry.T S i) Λ) :=
    fun i => HasDerivedCategory.standard (ModuleSheaf (AffineCoverGeometry.T S i) Λ)
  let : ∀ i : AffineCoverGeometry.Index S,
      HasDerivedCategory (ModuleSheaf (AffineCoverGeometry.Y' f' g i) Λ) :=
    fun i => HasDerivedCategory.standard (ModuleSheaf (AffineCoverGeometry.Y' f' g i) Λ)
  let : ∀ i : AffineCoverGeometry.Index S,
      HasDerivedCategory (ModuleSheaf (AffineCoverGeometry.U g i).left Λ) :=
    fun i => HasDerivedCategory.standard (ModuleSheaf (AffineCoverGeometry.U g i).left Λ)
  let : ∀ i : AffineCoverGeometry.Index S,
      HasDerivedCategory (AbelianSheaf.{u, u + 1} (AffineCoverGeometry.Y f i)) :=
    fun i => HasDerivedCategory.standard (AbelianSheaf.{u, u + 1} (AffineCoverGeometry.Y f i))
  let : ∀ i : AffineCoverGeometry.Index S,
      HasDerivedCategory (AbelianSheaf.{u, u + 1} (AffineCoverGeometry.T S i)) :=
    fun i => HasDerivedCategory.standard (AbelianSheaf.{u, u + 1} (AffineCoverGeometry.T S i))
  let : ∀ i : AffineCoverGeometry.Index S,
      HasDerivedCategory (AbelianSheaf.{u, u + 1} (AffineCoverGeometry.Y' f' g i)) :=
    fun i => HasDerivedCategory.standard (AbelianSheaf.{u, u + 1} (AffineCoverGeometry.Y' f' g i))
  let : ∀ i : AffineCoverGeometry.Index S,
      HasDerivedCategory (AbelianSheaf.{u, u + 1} (AffineCoverGeometry.U g i).left) :=
    fun i => HasDerivedCategory.standard (AbelianSheaf.{u, u + 1} (AffineCoverGeometry.U g i).left)
  exact properModuleUnboundedDerivedBaseChange_isIso_of_compact_local_charts
    Λ f f' g g' sq (AffineCoverGeometry.U g) (AffineCoverGeometry.hU g)
    (AffineCoverGeometry.Y f) (AffineCoverGeometry.T S) (AffineCoverGeometry.Y' f' g)
    (AffineCoverGeometry.p f) (AffineCoverGeometry.p' f' g)
    (AffineCoverGeometry.q g) (AffineCoverGeometry.q' f f' g g' sq)
    (AffineCoverGeometry.jS S) (AffineCoverGeometry.jX f) (AffineCoverGeometry.jX' f' g)
    (AffineCoverGeometry.sf f) (AffineCoverGeometry.sf' f' g)
    (AffineCoverGeometry.hg g) (AffineCoverGeometry.hg' f f' g g' sq)
    (AffineCoverGeometry.localSq f f' g g' sq) N hN hΛ

end AlgebraicGeometry.Scheme.EtaleCohomology.Proper
