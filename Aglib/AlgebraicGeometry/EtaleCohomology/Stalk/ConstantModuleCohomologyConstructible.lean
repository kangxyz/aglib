/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aglib contributors
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.ConstantModuleCoefficientFunctor
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.ConstantModuleTensorSheafification
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.TensorRightScalars
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.ZModComparison
public import Aglib.AlgebraicGeometry.EtaleCohomology.Finiteness.ProperConstructible
public import Mathlib.Algebra.Module.ZMod

/-! # Constructibility of the original constant-module cohomology sheafification

The rank-one prime-field coefficient uses the original proper abelian theorem.
The actual sheafified tensor comparison then keeps the same module action and
strata. This statement concerns the original small-diagram sheafification;
identification with the native module higher direct image is separate.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u r w s e

attribute [local instance] hasSheafifyLarge ModuleCat.Sheaf.hasSheafify

variable {X S : Scheme.{u}} [IsNoetherian S] (f : X ⟶ S) [IsProper f]
  [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
  [∀ U : S.Etale, HasExt.{s} (Sheaf ((Scheme.smallEtaleTopology X).over
    ((siteBaseChange f).obj U)) AddCommGrpCat.{u + 1})]
  [∀ U : S.Etale, HasExt.{max (u + 1) e}
    (AbelianSheaf.{u, u + 1} (pullback U.hom f))]

/-- Rank-one prime-field cohomology is constructible with its original module action. -/
theorem constantPrimeFieldCohomologySheafification_isConstructible
    (p : ℕ) [Fact p.Prime] (q : ℕ) :
    Constructible.Modules.IsConstructible
      ((constantModuleCohomologySheafificationFunctor f (ZMod p) q).obj
        (ModuleCat.liftedUnit.{0, u + 1} (ZMod p))) := by
  let : Finite ((forget₂ (ModuleCat.{u + 1} (ZMod p)) AddCommGrpCat).obj
      (ModuleCat.liftedUnit.{0, u + 1} (ZMod p))) := by
    change Finite (ULift.{u + 1} (ZMod p))
    infer_instance
  apply Constructible.Modules.isConstructible_of_zmodUnderlying p
  apply (Constructible.isConstructible_iff_of_iso
    ((constantModuleCohomologySheafificationUnderlyingIso f (ZMod p) q).app
      (ModuleCat.liftedUnit.{0, u + 1} (ZMod p)))).mpr
  exact higherDirectImage_proper_isConstructible f q _
    (Constructible.isConstructible_constant X _)

/-- A finite-type module with a commuting prime-field action retains its actual
cohomology diagram and actual coefficient action after sheafification. -/
theorem constantPrimeModuleCohomologySheafification_isConstructible
    (p : ℕ) [Fact p.Prime] (Λ : Type r) [Ring Λ]
    (M : ModuleCat.{u + 1} (ZMod p)) [Module Λ M]
    [SMulCommClass Λ (ZMod p) M] [Module.Finite Λ M] (q : ℕ) :
    Constructible.Modules.IsConstructible
      ((constantModuleCohomologySheafificationFunctor f Λ q).obj (ModuleCat.of Λ M)) := by
  apply (Constructible.Modules.isConstructible_iff_of_iso
    (constantModuleTensorSheafificationIso f (ZMod p) Λ M q)).mp
  exact Constructible.Modules.isConstructible_tensorRightScalars (ZMod p) Λ M
    (constantPrimeFieldCohomologySheafification_isConstructible f p q)

/-- A prime-killed original module supplies its commuting prime-field action internally. -/
theorem constantPrimeKilledModuleCohomologySheafification_isConstructible
    (p : ℕ) [Fact p.Prime] (Λ : Type r) [Ring Λ]
    (M : ModuleCat.{u + 1} Λ) [Module.Finite Λ M]
    (hM : ∀ x : M, p • x = 0) (q : ℕ) :
    Constructible.Modules.IsConstructible
      ((constantModuleCohomologySheafificationFunctor f Λ q).obj M) := by
  let : Module (ZMod p) M := AddCommGroup.zmodModule hM
  let : SMulCommClass Λ (ZMod p) M :=
    ⟨fun a r x => ZMod.map_smul (DistribSMul.toAddMonoidHom M a) r x⟩
  exact constantPrimeModuleCohomologySheafification_isConstructible f p Λ
    (ModuleCat.of (ZMod p) M) q

end AlgebraicGeometry.Scheme.EtaleCohomology
