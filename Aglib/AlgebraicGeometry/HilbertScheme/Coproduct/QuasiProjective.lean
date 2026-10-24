/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.HilbertScheme.Coproduct.Representability
public import Aglib.AlgebraicGeometry.HilbertScheme.Immersed.QuasiProjective
public import Aglib.AlgebraicGeometry.ProjectiveSpace.QuasiProjective.Coproduct

/-!
# The finite disjoint union of Hilbert schemes of an immersed scheme is quasi-projective

* `AlgebraicGeometry.Scheme.LocallyNoetherianOver.isHQuasiProjective_sigma_obj_hom`: the disjoint
  union `Scheme.LocallyNoetherianOver.sigma H` (`Properties/Noetherian/Coproduct`) of finitely many
  locally Noetherian test schemes over `Spec R` that are H-quasi-projective over `Spec R` is
  H-quasi-projective over `Spec R` (`isHQuasiProjective_sigmaDesc`,
  `ProjectiveSpace/QuasiProjective/Coproduct`).
* `AlgebraicGeometry.ProjectiveSpace.isHQuasiProjective_sigmaImmersedHilbertSchemeOver_hom`: hence
  for a Noetherian ring `A`, an immersion `i : Y ⟶ P^n_A` and a finite set `F` of polynomials, the
  disjoint union `H_F = sigmaImmersedHilbertSchemeOver ι n e A r hr φ i` of the Hilbert schemes
  `H^Φ_Y`, `Φ ∈ F` (`HilbertScheme/Coproduct/Representability`), is H-quasi-projective over
  `Spec A`, since every `H^Φ_Y` is (`isHQuasiProjective_immersedHilbertSchemeOver_hom`,
  `HilbertScheme/Immersed/QuasiProjective`). In particular `H_F` is Noetherian, separated and of
  finite type over `Spec A`.

Source: Nitsure, *Construction of Hilbert and Quot schemes*, arXiv:math/0504590v1, proof of
Thm 6.8, p. 33: "Let H be the finite disjoint union of the corresponding open subschemes
Hilb^{Φ,L}_{X/S} of Hilb_{X/S}. Then H is a quasi-projective scheme over S as each
Hilb^{Φ,L}_{X/S} is so by Theorem 6.3"; the step from the pieces to the finite disjoint union is
`isHQuasiProjective_sigmaDesc`. H-quasi-projective is Stacks, Definition 29.41.1 (Tag 01VW), over
the affine base `Spec A` (`ProjectiveSpace/QuasiProjective`).
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped Polynomial

universe v u

namespace AlgebraicGeometry

/-- **A finite disjoint union of H-quasi-projective test schemes is H-quasi-projective**: for a
finite family `H` of locally Noetherian test schemes over `Spec R`, each H-quasi-projective over
`Spec R`, their disjoint union is H-quasi-projective over `Spec R`. -/
instance Scheme.LocallyNoetherianOver.isHQuasiProjective_sigma_obj_hom {R : CommRingCat.{u}}
    {σ : Type v} [Small.{u} σ] [Finite σ] (H : σ → Scheme.LocallyNoetherianOver (Spec R))
    [∀ j, IsHQuasiProjective (H j).obj.hom] :
    IsHQuasiProjective (Scheme.LocallyNoetherianOver.sigma H).obj.hom :=
  isHQuasiProjective_sigmaDesc fun j => (H j).obj.hom

namespace ProjectiveSpace

variable (ι : Type u) (n : ℕ) (e : ι ≃ Fin (n + 1)) (A : Type u) [CommRing A]
  [IsNoetherianRing A] {F : Set ℚ[X]} (r : F → ℕ)
  (hr : ∀ Φ : F, hilbertRegularityBound n Φ ≤ r Φ) {J : F → Type u}
  (φ : ∀ Φ : F, SheafOfModules.free (R := (ProjectiveSpace A ι).ringCatSheaf) (J Φ) ⟶
    twistingSheaf A ι (r Φ : ℤ))
  {Y : Scheme.{u}} (i : Y ⟶ ProjectiveSpace A ι) [IsImmersion i]

/-- **The finite disjoint union of Hilbert schemes of a locally closed subscheme of `P^n_A` is
H-quasi-projective over `Spec A`** (Nitsure, arXiv:math/0504590v1, proof of Thm 6.8, p. 33): for a
finite set `F` of polynomials, `H_F = ∐_{Φ ∈ F} H^Φ_Y` is H-quasi-projective, as a finite disjoint
union of the H-quasi-projective `H^Φ_Y`. -/
instance isHQuasiProjective_sigmaImmersedHilbertSchemeOver_hom [Finite F] :
    IsHQuasiProjective (sigmaImmersedHilbertSchemeOver ι n e A r hr φ i).obj.hom :=
  Scheme.LocallyNoetherianOver.isHQuasiProjective_sigma_obj_hom _

end ProjectiveSpace

end AlgebraicGeometry
