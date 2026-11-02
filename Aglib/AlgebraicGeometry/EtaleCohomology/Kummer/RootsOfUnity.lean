/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Coefficients.ConstantRing
public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.Coefficients
public import Aglib.CategoryTheory.Sites.Torsion.ZMod.Ringed.Equivalence
public import Aglib.CategoryTheory.Sites.Torsion.ZMod.Sheaf

/-!
# The sheaf of `n`-th roots of unity as a sheaf of `ℤ/n`-modules

The represented étale sheaf `μ_n = GroupCohomology.Kummer.Coefficients.mu X n` of `n`-th roots
of unity is killed by `n` (`mu_killedBy`), so its sections carry their canonical
`ZMod n`-module structure (`TorsionZMod.sheaf`). Transporting the scalars along the ring
isomorphism `ULift (ZMod n) ≃+* ZMod n` (`TorsionZMod.Ringed.scalarSheafEquivalence`) and
through the module-valued/ringed equivalence `moduleSheafEquivalence` gives a sheaf of modules
over the constant ring sheaf `ℤ/n` on the small étale site. Its underlying abelian sheaf is
`μ_n`, by the composite of the three original underlying isomorphisms. This is the coefficient
`μ_n` of the duality pairing of Milne, *Lectures on Étale Cohomology* (v2.21), Thm 14.7, p. 93,
and p. 103, as an object of `Sh(X_et, n)`. Every `n` is allowed, including `0` and `1`; no
invertibility of `n` on `X` is used.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients GroupCohomology.Kummer.Coefficients

variable (X : Scheme.{u}) (n : ℕ)

/-- The sheaf `μ_n` of `n`-th roots of unity as a sheaf of modules over the constant ring sheaf
on `ULift (ZMod n)`. -/
def moduleRootsOfUnity : ModuleSheaf X (ULift.{u + 1} (ZMod n)) :=
  (moduleSheafEquivalence X (ULift.{u + 1} (ZMod n))).functor.obj
    ((TorsionZMod.Ringed.scalarSheafEquivalence.{u + 1, u, u + 1}
        (Scheme.smallEtaleTopology X) n).functor.obj
      (TorsionZMod.sheaf.{u + 1, u, u + 1} (Scheme.smallEtaleTopology X) n (mu X n)
        (mu_killedBy X n)))

/-- The underlying abelian sheaf of the module sheaf `μ_n` is the represented sheaf `μ_n`. -/
def moduleRootsOfUnityUnderlyingIso :
    (SheafOfModules.toSheaf (constantRing X (ULift.{u + 1} (ZMod n)))).obj
        (moduleRootsOfUnity X n) ≅ mu X n :=
  (moduleSheafUnderlyingIso X (ULift.{u + 1} (ZMod n))).app _ ≪≫
    (TorsionZMod.Ringed.scalarSheafUnderlyingIso.{u + 1, u, u + 1}
        (Scheme.smallEtaleTopology X) n).app _ ≪≫
      TorsionZMod.sheafUnderlyingIso.{u + 1, u, u + 1} (Scheme.smallEtaleTopology X) n (mu X n)
        (mu_killedBy X n)

end AlgebraicGeometry.Scheme.EtaleCohomology
