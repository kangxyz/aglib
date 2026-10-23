/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Projective.GlobalSections.Polynomial

/-!
# The section of a homogeneous polynomial in `H^0(P_R, 𝒪(m))`

`Scheme.Cohomology.equiv₀_twistingH0PolynomialLinearEquiv_symm`: under
`Sheaf.H.equiv₀ : H^0 ≃ Γ(𝒪(m), ⊤)`, the element `twistingH0PolynomialLinearEquiv.symm q` of
`H^0(P_R, 𝒪(m))` of a homogeneous polynomial `q` of degree `m` is its section
`ProjectiveSpace.homogeneousSection R ι m q` (`homogeneousSectionLinearEquiv_apply`).
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

-- The polynomial comparison carries the structural action of `Γ(P_R, ⊤)` through `Module.compHom`.
set_option backward.isDefEq.respectTransparency false in
/-- The element of `H^0(P_R, 𝒪(m))` of a homogeneous polynomial is its section over `⊤`. -/
theorem equiv₀_twistingH0PolynomialLinearEquiv_symm (R : Type u) [CommRing R] (ι : Type u)
    [Fintype ι] (j : ι) (m : ℕ) (q : MvPolynomial.homogeneousSubmodule ι R m) :
    Sheaf.H.equiv₀ (moduleAddSheaf _ (ProjectiveSpace.twistingSheaf R ι m)) Limits.isTerminalTop
        ((twistingH0PolynomialLinearEquiv R ι j m).symm q) =
      ProjectiveSpace.homogeneousSection R ι m q := by
  let α : R →+* Γ(ProjectiveSpace R ι, ⊤) :=
    (ProjectiveSpace.toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
  let := Module.compHom Γ(ProjectiveSpace.twistingSheaf R ι (m : ℤ), ⊤) α
  change moduleH0EquivOfHom _ α _ ((moduleH0EquivOfHom _ α _).symm
    ((twistingGlobalSectionsPolynomialLinearEquiv R ι j m).symm q)) = _
  rw [LinearEquiv.apply_symm_apply]
  exact homogeneousSectionLinearEquiv_apply R ι j m q

end AlgebraicGeometry.Scheme.Cohomology
