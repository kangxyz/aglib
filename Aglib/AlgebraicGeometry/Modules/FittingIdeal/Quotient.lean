/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.FittingIdeal.LocallyFree
public import Aglib.AlgebraicGeometry.Modules.Rees.AffineOpenImage

/-!
# Fitting ideal sheaves of quotients

Let `p : E ⟶ Q` be an epimorphism of `𝒪_X`-modules with quasi-coherent kernel, between
quasi-coherent sheaves of finite type (`Scheme.Modules.QuasiCoherent.affineLocallyFiniteType`).

* `fittingIdealSheaf_le_of_epi`: `Fitt_k(E) ⊆ Fitt_k(Q)` for every `k`. On an affine open `U` the
  map `Γ(E, U) → Γ(Q, U)` is surjective (`affineOpenSections_epi_surjective`), and Fitting ideals
  grow along surjections (`Module.fittingIdeal_le_of_surjective`, Stacks Project, Tag 07ZA (5)).
* `fittingIdealSheaf_eq_top_of_epi_of_sheafHasRank`: if `E` is finite locally free of constant
  rank `d`, then `Fitt_d(Q) = 𝒪_X`, since `Fitt_d(E) = 𝒪_X`
  (`fittingIdealSheaf_eq_of_sheafHasRank`, Stacks Project, Tag 0C3G).

No Noetherian or finite-presentation hypothesis is used. Consumer: the zero scheme of a morphism
into a finite locally free sheaf of constant rank,
`Aglib.AlgebraicGeometry.Modules.ZeroLocus.LocallyFree`.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- **Fitting ideal sheaves grow along epimorphisms** (Stacks Project, Tag 07ZA (5), on every
affine open): for an epimorphism `p : E ⟶ Q` with quasi-coherent kernel between quasi-coherent
sheaves of finite type, `Fitt_k(E) ⊆ Fitt_k(Q)`. -/
theorem fittingIdealSheaf_le_of_epi {E Q : X.Modules} (p : E ⟶ Q) [Epi p]
    [(kernel p).IsQuasicoherent] (hE : QuasiCoherent.affineLocallyFiniteType X E)
    (hQ : QuasiCoherent.affineLocallyFiniteType X Q) (k : ℕ) :
    fittingIdealSheaf E hE k ≤ fittingIdealSheaf Q hQ k := fun U =>
  let g : Γ(E, U) →ₗ[Γ(X, U)] Γ(Q, U) :=
    { toFun := p.app U.1
      map_add' := map_add _
      map_smul' := fun r x => p.app_smul r x }
  Module.fittingIdeal_le_of_surjective (g := g) (affineOpenSections_epi_surjective U p) k

/-- **A quotient of a sheaf of constant rank `d` has unit `d`-th Fitting ideal sheaf**: for an
epimorphism `p : E ⟶ Q` with quasi-coherent kernel, `E` finite locally free of constant rank `d`
and `Q` quasi-coherent of finite type, `Fitt_d(Q) = 𝒪_X`. -/
theorem fittingIdealSheaf_eq_top_of_epi_of_sheafHasRank {E Q : X.Modules} (p : E ⟶ Q) [Epi p]
    [(kernel p).IsQuasicoherent] (hE : QuasiCoherent.affineLocallyFiniteType X E)
    (hQ : QuasiCoherent.affineLocallyFiniteType X Q) {d : ℕ} (h : SheafHasRank E d) :
    fittingIdealSheaf Q hQ d = ⊤ :=
  eq_top_iff.mpr <| (fittingIdealSheaf_eq_of_sheafHasRank E hE h).2.symm.le.trans
    (fittingIdealSheaf_le_of_epi p hE hQ d)

end AlgebraicGeometry.Scheme.Modules
