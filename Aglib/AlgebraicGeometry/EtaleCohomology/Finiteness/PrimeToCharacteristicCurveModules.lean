/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Finiteness.SeparablyClosedCurveH1
public import Aglib.AlgebraicGeometry.EtaleCohomology.Curves.CharacteristicPrimary
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.ConstantCoefficients
public import Mathlib.Algebra.Module.ZMod

/-!
# Finite original H1 for prime-to-characteristic constant modules on curves

Finite original cyclic H1 supplies the rank-one prime-field value. Fixed-site
coefficient continuity and the canonical scalar-compatible tensor pairing then
give finite generation over the original commuting coefficient ring. The
coefficient module need not have a finite underlying group or finite prime-field
dimension, and the coefficient ring need not be Noetherian.
-/

@[expose] public noncomputable section

open CategoryTheory Limits
open AlgebraicGeometry.Scheme.OverField
open AlgebraicGeometry.Scheme.OverField.Curve

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Finiteness

universe u e l

attribute [local instance] hasSheafifyLarge

variable {k : Type u} [Field k] [IsSepClosed k]
  (X : FScheme k) (hX : Properties X)
  [HasExt.{e} (AbelianSheaf.{u, u + 1} X.left)]
  (p : ℕ) [Fact p.Prime] (hunit : IsUnit (p : k))

include hX hunit

/-- The actual constant prime-field coefficient has finite original H1 when
the prime is invertible on the smooth proper geometrically connected curve. -/
theorem finite_primeField_h1_of_smooth_proper_curve :
    Finite (Sheaf.H.{e} (primeFieldSheaf X.left p) 1) := by
  let : Finite (H1Etale.{u, u + 1, e} X.left
      (ConstantFinite.coefficient (ULift.{u} (ZMod p)) X.left)) :=
    finite_cyclic_h1_of_separably_closed_smooth_proper_curve X hX p
      (Fact.out : p.Prime).pos hunit
  let f : Sheaf.H.{e} (primeFieldSheaf X.left p) 1 ≃+
      Sheaf.H.{e} (ConstantFinite.coefficient (ULift.{u} (ZMod p)) X.left) 1 :=
    ((Sheaf.functorH X.left.smallEtaleTopology 1).mapIso
      (Curves.cyclicPrimeFieldIso X.left p).symm).addCommGroupIsoToAddEquiv
  exact Finite.of_injective f f.injective

/-- Original constant H1 is finite over the original commuting coefficient ring,
even when the coefficient module is infinite-dimensional over the prime field. -/
theorem constantModule_h1_finite_of_smooth_proper_curve
    (M : ModuleCat.{u + 1} (ZMod p))
    [HasColimitsOfShape (Finset (Discrete (Module.Free.ChooseBasisIndex (ZMod p) M)))
      AddCommGrpCat.{e}]
    (Λ : Type l) [CommRing Λ] [Module Λ M] [SMulCommClass Λ (ZMod p) M]
    [Module.Finite Λ M] :
    Module.Finite Λ ((ModuleCat.Sheaf.constantCohomology X.left.smallEtaleTopology Λ 1).obj
      (ModuleCat.of Λ M)) := by
  let : IsProper X.hom := hX.proper
  let : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  let : QuasiSeparatedSpace X.left := quasiSeparatedSpace_of_quasiSeparated X.hom
  let := Continuity.qcqsConstantCohomology_preservesCoproducts X.left (ZMod p)
    (Module.Free.ChooseBasisIndex (ZMod p) M) 1
  let : Finite ((ModuleCat.Sheaf.constantCohomology X.left.smallEtaleTopology (ZMod p) 1).obj
      (ModuleCat.liftedUnit.{0, u + 1} (ZMod p))) :=
    finite_primeField_h1_of_smooth_proper_curve X hX p hunit
  exact ModuleCat.Sheaf.finite_constantCohomology X.left.smallEtaleTopology (ZMod p)
    1 M Λ

/-- A finite literal module killed by an invertible prime has finite original
constant H1. No Noetherian or finite-underlying-group hypothesis is required. -/
theorem constantModule_h1_finite_of_prime_nsmul
    [HasColimitsOfSize.{u + 1, u + 1} AddCommGrpCat.{e}]
    (Λ : Type l) [CommRing Λ] (M : ModuleCat.{u + 1} Λ) [Module.Finite Λ M]
    (hM : ∀ x : M, p • x = 0) :
    Module.Finite Λ ((ModuleCat.Sheaf.constantCohomology X.left.smallEtaleTopology Λ 1).obj M) := by
  have h : ∀ (V : ModuleCat.{u + 1} (ZMod p)), ∀ [Module Λ V],
      ∀ [SMulCommClass Λ (ZMod p) V], ∀ [Module.Finite Λ V],
      Module.Finite Λ ((ModuleCat.Sheaf.constantCohomology
        X.left.smallEtaleTopology Λ 1).obj (ModuleCat.of Λ V)) := by
    intro V _ _ _
    let I : Type (u + 1) := Finset (Discrete (Module.Free.ChooseBasisIndex (ZMod p) V))
    let : HasColimitsOfShape I AddCommGrpCat.{e} :=
      @HasColimitsOfSize.has_colimits_of_shape AddCommGrpCat.{e} inferInstance
        (inferInstance : HasColimitsOfSize.{u + 1, u + 1} AddCommGrpCat.{e}) I
        (inferInstance : SmallCategory I)
    exact constantModule_h1_finite_of_smooth_proper_curve.{u, e, l} X hX p hunit V Λ
  let : Module (ZMod p) M := AddCommGroup.zmodModule hM
  let : SMulCommClass Λ (ZMod p) M :=
    ⟨fun a r x => ZMod.map_smul (DistribSMul.toAddMonoidHom M a) r x⟩
  exact h (ModuleCat.of (ZMod p) M)

end AlgebraicGeometry.Scheme.EtaleCohomology.Finiteness
