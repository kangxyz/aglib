/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.FinitePresentation
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Limits
public import Aglib.AlgebraicGeometry.Modules.Rees.AffineOpenImage

/-!
# Quotients of quasi-coherent sheaves of finite type

Let `p : E ⟶ Q` be an epimorphism of `𝒪_X`-modules on a scheme `X`, with `Q` and `ker p`
quasi-coherent. If `E` is quasi-coherent of finite type in the chart sense of
`Scheme.Modules.QuasiCoherent.affineLocallyFiniteType`, so is `Q`
(`QuasiCoherent.affineLocallyFiniteType_of_epi`): on an affine chart `Spec R ⟶ X` the global
sections of the restriction of `p` are surjective, since the kernel is quasi-coherent
(`affineRestriction_epi_surjective`), so the sections of `Q` form a quotient of a finite
`R`-module.

In particular the cokernel of a morphism `σ : F ⟶ E` of quasi-coherent sheaves with `E` of finite
type is of finite type (`QuasiCoherent.affineLocallyFiniteType_cokernel`). No Noetherian or
finite-presentation hypothesis is used.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules.QuasiCoherent

variable {X : Scheme.{u}}

/-- **Quotients of sheaves of finite type**: if `p : E ⟶ Q` is an epimorphism with `Q` and `ker p`
quasi-coherent and `E` is quasi-coherent of finite type, then `Q` is quasi-coherent of finite
type. -/
theorem affineLocallyFiniteType_of_epi {E Q : X.Modules} (p : E ⟶ Q) [Epi p]
    [Q.IsQuasicoherent] [(kernel p).IsQuasicoherent] (hE : affineLocallyFiniteType X E) :
    affineLocallyFiniteType X Q := by
  intro R j _
  have : Module.Finite R (moduleSpecΓFunctor.obj ((Scheme.Modules.restrictFunctor j).obj E)) :=
    (hE R j).2
  exact ⟨inferInstance, Module.Finite.of_surjective _ (affineRestriction_epi_surjective j p)⟩

/-- The cokernel of a morphism `σ : F ⟶ E` of quasi-coherent sheaves, with `E` of finite type, is
quasi-coherent of finite type. -/
theorem affineLocallyFiniteType_cokernel {F E : X.Modules} (σ : F ⟶ E) [F.IsQuasicoherent]
    [E.IsQuasicoherent] (hE : affineLocallyFiniteType X E) :
    affineLocallyFiniteType X (cokernel σ) := by
  have := quasicoherent_cokernel σ
  have := quasicoherent_kernel (cokernel.π σ)
  exact affineLocallyFiniteType_of_epi (cokernel.π σ) hE

end AlgebraicGeometry.Scheme.Modules.QuasiCoherent
