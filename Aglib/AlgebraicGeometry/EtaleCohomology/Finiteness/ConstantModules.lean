/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Finiteness.ArtinSchreier
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.ConstantCoefficients

/-!
# Proper constant modules killed by the characteristic

For a proper scheme over a separably closed characteristic-`p` field, original
cohomology with any constant `Fp`-vector space finite over a commuting
coefficient ring is finite over that same ring. The coefficients need not be
finite as a set or finite-dimensional over `Fp`. This combines the actual
Artin--Schreier theorem with fixed-site coefficient continuity and the canonical
scalar-compatible tensor pairing.
-/

@[expose] public noncomputable section

open CategoryTheory Limits
open AlgebraicGeometry.Scheme.OverField

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u e l

attribute [local instance] hasSheafifyLarge

variable {k : Type u} [Field k] [IsSepClosed k] (Y : FScheme k) [IsProper Y.hom]
  [HasExt.{e} (AbelianSheaf.{u, u + 1} Y.left)]
  (p : ℕ) [Fact p.Prime] [CharP k p]

/-- Actual original constant cohomology is finite for the original commuting
coefficient-ring action. There is no finiteness hypothesis on the underlying
abelian group or on its prime-field dimension. -/
theorem constantModule_cohomology_finite_of_proper
    (q : ℕ) (M : ModuleCat.{u + 1} (ZMod p))
    [HasColimitsOfShape (Finset (Discrete (Module.Free.ChooseBasisIndex (ZMod p) M)))
      AddCommGrpCat.{e}]
    (Λ : Type l) [CommRing Λ] [Module Λ M] [SMulCommClass Λ (ZMod p) M]
    [Module.Finite Λ M] :
    Module.Finite Λ ((ModuleCat.Sheaf.constantCohomology Y.left.smallEtaleTopology Λ q).obj
      (ModuleCat.of Λ M)) := by
  let : CompactSpace Y.left := QuasiCompact.compactSpace_of_compactSpace Y.hom
  let : QuasiSeparatedSpace Y.left := quasiSeparatedSpace_of_quasiSeparated Y.hom
  let := Continuity.qcqsConstantCohomology_preservesCoproducts Y.left (ZMod p)
    (Module.Free.ChooseBasisIndex (ZMod p) M) q
  let : Finite ((ModuleCat.Sheaf.constantCohomology Y.left.smallEtaleTopology (ZMod p) q).obj
      (ModuleCat.liftedUnit.{0, u + 1} (ZMod p))) :=
    primeField_cohomology_finite_of_proper Y p q
  exact ModuleCat.Sheaf.finite_constantCohomology Y.left.smallEtaleTopology (ZMod p)
    q M Λ

end AlgebraicGeometry.Scheme.EtaleCohomology
