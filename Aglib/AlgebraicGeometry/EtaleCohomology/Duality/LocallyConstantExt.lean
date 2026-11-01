/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.ConstantRing.InternalHomAcyclic
public import Aglib.Algebra.Module.ZMod.Injective
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.FiniteConstantCharts
public import Aglib.AlgebraicGeometry.EtaleCohomology.Duality.ConstantCoefficients
public import Aglib.CategoryTheory.Sites.SheafCohomology.InternalExtComparison

/-!
# Original Ext and internal-Hom cohomology for finite locally constant coefficients

The native finite-lcc charts and self-injectivity of every positive ZMod level
supply actual internal-Hom target acyclicity. The existing constant-root
isomorphism then supplies the roots coefficient over an algebraically closed
field with invertible level. This needs no smoothness, properness, or
projectivity of the scheme. Composite levels and level one are retained.

The comparison uses the already constructed original Ext/right-derived and
module-unit/cohomology maps. Its degree-zero specialization is the existing
unconditional comparison. Source connecting compatibility is a separate
whole-triangle obligation; it is not inferred from this objectwise equivalence.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open CategoryTheory.TorsionZMod.Ringed

universe u eM eA

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

attribute [local instance] hasSheafifyRingStandard hasSheafifyAbStandard
  ringWEqualsLocallyBijectiveStandard abWEqualsLocallyBijectiveStandard
  hasSheafifyLarge abelianSheafEnoughInjectivesLarge

-- Use the literal native internal-Hom category while retaining the same original ring parent.
/-- Enough injectives in the original category at the native internal-Hom header. -/
local instance locallyConstantExt_enoughInjectives (X : Scheme.{u})
    (Λ : Type (u + 1)) [CommRing Λ] :
    EnoughInjectives (SheafOfModulesOfCommRing.{u + 1, u + 1, u}
      (ModuleCat.Sheaf.ConstantRing.commutativeSheaf X.smallEtaleTopology Λ)) :=
  SheafOfModules.enoughInjectivesLarge.{u + 1, u, 0}
    ((sheafCompose X.smallEtaleTopology
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (ModuleCat.Sheaf.ConstantRing.commutativeSheaf X.smallEtaleTopology Λ))

set_option backward.isDefEq.respectTransparency false in
local instance locallyConstantExt_genericEnoughInjectives (X : Scheme.{u})
    (Λ : Type (u + 1)) [CommRing Λ] :
    EnoughInjectives (ModuleCat.Sheaf.ConstantRing.ModuleSheaf.{u + 1, u, u + 1, u + 1}
      X.smallEtaleTopology Λ) :=
  inferInstanceAs (EnoughInjectives (SheafOfModulesOfCommRing.{u + 1, u + 1, u}
    (ModuleCat.Sheaf.ConstantRing.commutativeSheaf X.smallEtaleTopology Λ)))

set_option backward.isDefEq.respectTransparency false in
local instance locallyConstantExt_homFunctor_additive (X : Scheme.{u})
    (Λ : Type (u + 1)) [CommRing Λ] (M : ModuleSheaf X Λ) :
    (SheafOfModules.InternalHom.homFunctor.{u + 1, u, 0}
      (ModuleCat.Sheaf.ConstantRing.commutativeSheaf X.smallEtaleTopology Λ) M).Additive :=
  SheafOfModules.InternalHom.homFunctor_additive.{u + 1, u, 0}
    (ModuleCat.Sheaf.ConstantRing.commutativeSheaf X.smallEtaleTopology Λ) M

set_option backward.isDefEq.respectTransparency false in
/-- The original module unit is internally acyclic for every native finite-lcc ZMod source. -/
theorem moduleUnit_internalHom_rightDerived_isZero (X : Scheme.{u}) (n : ℕ) [NeZero n]
    (M : ModuleSheaf X (ULift.{u + 1} (ZMod n)))
    (hM : Constructible.Modules.IsFiniteTypeLocallyConstant
      ((moduleSheafEquivalence X (ULift.{u + 1} (ZMod n))).inverse.obj M)) (q : ℕ) :
    IsZero (((SheafOfModules.InternalHom.homFunctor.{u + 1, u, 0}
      (ModuleCat.Sheaf.ConstantRing.commutativeSheaf X.smallEtaleTopology
        (ULift.{u + 1} (ZMod n))) M).rightDerived (q + 1)).obj
          (moduleUnit X (ULift.{u + 1} (ZMod n)))) := by
  let : Module.Injective (ZMod n) (ZMod n) := ZMod.injective_self n
  let e : ZMod n ≃+* ULift.{u + 1} (ZMod n) := ULift.ringEquiv.symm
  let : Module.Injective (ULift.{u + 1} (ZMod n)) (ULift.{u + 1} (ZMod n)) :=
    Module.Injective.of_ringEquiv e e.toSemilinearEquiv
  exact ModuleCat.Sheaf.ConstantRing.isZero_rightDerived_moduleUnit
    X.smallEtaleTopology (ULift.{u + 1} (ZMod n)) M
    (Constructible.Modules.hasFiniteTypeConstantCharts_of_isFiniteTypeLocallyConstant _ hM) q

variable (k : Type u) [Field k] [IsAlgClosed k] (n : ℕ)
  (hn : 0 < n) (hunit : IsUnit (n : k)) {X : Scheme.{u}} (p : X ⟶ Spec (.of k))

include hn hunit p in
set_option backward.isDefEq.respectTransparency false in
/-- The original roots coefficient is internally acyclic at every positive invertible level. -/
theorem moduleRoots_internalHom_rightDerived_isZero
    (M : ModuleSheaf X (ULift.{u + 1} (ZMod n)))
    (hM : Constructible.Modules.IsFiniteTypeLocallyConstant
      ((moduleSheafEquivalence X (ULift.{u + 1} (ZMod n))).inverse.obj M)) (q : ℕ) :
    IsZero (((SheafOfModules.InternalHom.homFunctor.{u + 1, u, 0}
      (ModuleCat.Sheaf.ConstantRing.commutativeSheaf X.smallEtaleTopology
        (ULift.{u + 1} (ZMod n))) M).rightDerived (q + 1)).obj (moduleRootsOfUnity X n)) := by
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  exact IsZero.of_iso (moduleUnit_internalHom_rightDerived_isZero X n M hM q)
    (((SheafOfModules.InternalHom.homFunctor.{u + 1, u, 0}
      (ModuleCat.Sheaf.ConstantRing.commutativeSheaf X.smallEtaleTopology
        (ULift.{u + 1} (ZMod n))) M).rightDerived (q + 1)).mapIso
          (moduleUnitRootsIso k n hn hunit p).symm)

variable [HasExt.{eM} (ModuleSheaf X (ULift.{u + 1} (ZMod n)))]
  [HasExt.{eA} (AbelianSheaf.{u, u + 1} X)]

set_option backward.isDefEq.respectTransparency false in
local instance locallyConstantExt_nativeHasExt :
    HasExt.{eM} (SheafOfModulesOfCommRing.{u + 1, u + 1, u}
      (ModuleCat.Sheaf.ConstantRing.commutativeSheaf X.smallEtaleTopology
        (ULift.{u + 1} (ZMod n)))) :=
  inferInstanceAs (HasExt.{eM} (ModuleSheaf X (ULift.{u + 1} (ZMod n))))

/-- Original module Ext equals original cohomology of the same native internal Hom. -/
def locallyConstantExtCohomologyAddEquiv
    (M : ModuleSheaf X (ULift.{u + 1} (ZMod n)))
    (hM : Constructible.Modules.IsFiniteTypeLocallyConstant
      ((moduleSheafEquivalence X (ULift.{u + 1} (ZMod n))).inverse.obj M)) (q : ℕ) :
    Ext.{eM} M (moduleRootsOfUnity X n) q ≃+
      Sheaf.H.{eA} ((SheafOfModules.toSheaf
        (constantRing X (ULift.{u + 1} (ZMod n)))).obj
          (SheafOfModules.InternalHom.sheaf
            (ModuleCat.Sheaf.ConstantRing.commutativeSheaf X.smallEtaleTopology
              (ULift.{u + 1} (ZMod n))) M (moduleRootsOfUnity X n))) q :=
  Sheaf.InternalExt.extCohomologyAddEquivOfAcyclic.{u + 1, u, eM, eA}
    (ModuleCat.Sheaf.ConstantRing.commutativeSheaf X.smallEtaleTopology
      (ULift.{u + 1} (ZMod n))) terminalIsTerminal M (moduleRootsOfUnity X n)
    (moduleRoots_internalHom_rightDerived_isZero k n hn hunit p M hM) q

/-- Degree zero is the existing unconditional original Hom/unit/cohomology comparison. -/
theorem locallyConstantExtCohomologyAddEquiv_zero
    (M : ModuleSheaf X (ULift.{u + 1} (ZMod n)))
    (hM : Constructible.Modules.IsFiniteTypeLocallyConstant
      ((moduleSheafEquivalence X (ULift.{u + 1} (ZMod n))).inverse.obj M)) :
    locallyConstantExtCohomologyAddEquiv k n hn hunit p M hM 0 =
      SheafOfModules.InternalHom.extZeroCohomologyAddEquiv
        (ModuleCat.Sheaf.ConstantRing.commutativeSheaf X.smallEtaleTopology
          (ULift.{u + 1} (ZMod n))) terminalIsTerminal M (moduleRootsOfUnity X n) :=
  Sheaf.InternalExt.extCohomologyAddEquivOfAcyclic_zero.{u + 1, u, eM, eA}
    (ModuleCat.Sheaf.ConstantRing.commutativeSheaf X.smallEtaleTopology
      (ULift.{u + 1} (ZMod n))) terminalIsTerminal M (moduleRootsOfUnity X n)
    (moduleRoots_internalHom_rightDerived_isZero k n hn hunit p M hM)

/-- The canonical cohomology-to-Ext arrow for the original roots coefficient exists
for every module source, before imposing finite local constancy. -/
abbrev internalHomCohomologyExtMap
    (M : ModuleSheaf X (ULift.{u + 1} (ZMod n))) (q : ℕ) :=
  Sheaf.InternalExt.cohomologyExtReverse.{u + 1, u, eM, eA}
    (ModuleCat.Sheaf.ConstantRing.commutativeSheaf X.smallEtaleTopology
      (ULift.{u + 1} (ZMod n))) terminalIsTerminal M (moduleRootsOfUnity X n) q

/-- The finite-lcc forward comparison is the actual inverse of the original canonical
map defined for every source, rather than an independently chosen equivalence. -/
theorem locallyConstantExtCohomologyAddEquiv_symm
    (M : ModuleSheaf X (ULift.{u + 1} (ZMod n)))
    (hM : Constructible.Modules.IsFiniteTypeLocallyConstant
      ((moduleSheafEquivalence X (ULift.{u + 1} (ZMod n))).inverse.obj M)) (q : ℕ) :
    (locallyConstantExtCohomologyAddEquiv k n hn hunit p M hM q).symm.toAddMonoidHom =
      internalHomCohomologyExtMap n M q :=
  (Sheaf.InternalExt.cohomologyExtReverse_eq_symm.{u + 1, u, eM, eA}
    (ModuleCat.Sheaf.ConstantRing.commutativeSheaf X.smallEtaleTopology
      (ULift.{u + 1} (ZMod n))) terminalIsTerminal M (moduleRootsOfUnity X n)
    (moduleRoots_internalHom_rightDerived_isZero k n hn hunit p M hM) q).symm

include hn hunit p in
/-- The exact native instance of the original acyclic-target degree-zero law.
The proposition is retained at the producer's original Ext carrier. -/
theorem locallyConstantInternalHomCohomologyExtMap_zero
    (M : ModuleSheaf X (ULift.{u + 1} (ZMod n)))
    (hM : Constructible.Modules.IsFiniteTypeLocallyConstant
      ((moduleSheafEquivalence X (ULift.{u + 1} (ZMod n))).inverse.obj M)) :
    (fun {P : Prop} (_h : P) => P)
      (Sheaf.InternalExt.cohomologyExtReverse_zero_of_acyclic.{u + 1, u, eM, eA}
        (ModuleCat.Sheaf.ConstantRing.commutativeSheaf X.smallEtaleTopology
          (ULift.{u + 1} (ZMod n))) terminalIsTerminal M (moduleRootsOfUnity X n)
        (moduleRoots_internalHom_rightDerived_isZero k n hn hunit p M hM)) :=
  Sheaf.InternalExt.cohomologyExtReverse_zero_of_acyclic.{u + 1, u, eM, eA}
    (ModuleCat.Sheaf.ConstantRing.commutativeSheaf X.smallEtaleTopology
      (ULift.{u + 1} (ZMod n))) terminalIsTerminal M (moduleRootsOfUnity X n)
    (moduleRoots_internalHom_rightDerived_isZero k n hn hunit p M hM)

include hn hunit p in
/-- The exact native original-coefficient naturality law, with its actual roots
acyclicity discharged. The resulting proposition quantifies over the cohomology input. -/
theorem locallyConstantInternalHomCohomologyExtMap_naturality
    (M : ModuleSheaf X (ULift.{u + 1} (ZMod n)))
    (hM : Constructible.Modules.IsFiniteTypeLocallyConstant
      ((moduleSheafEquivalence X (ULift.{u + 1} (ZMod n))).inverse.obj M))
    (f : moduleRootsOfUnity X n ⟶ moduleRootsOfUnity X n) (q : ℕ) :
    (fun {P : Prop} (_h : P) => P)
      (Sheaf.InternalExt.cohomologyExtReverse_naturality_of_acyclic.{u + 1, u, eM, eA}
        (ModuleCat.Sheaf.ConstantRing.commutativeSheaf X.smallEtaleTopology
          (ULift.{u + 1} (ZMod n))) terminalIsTerminal M f
        (moduleRoots_internalHom_rightDerived_isZero k n hn hunit p M hM)
        (moduleRoots_internalHom_rightDerived_isZero k n hn hunit p M hM) q) :=
  Sheaf.InternalExt.cohomologyExtReverse_naturality_of_acyclic.{u + 1, u, eM, eA}
    (ModuleCat.Sheaf.ConstantRing.commutativeSheaf X.smallEtaleTopology
      (ULift.{u + 1} (ZMod n))) terminalIsTerminal M f
    (moduleRoots_internalHom_rightDerived_isZero k n hn hunit p M hM)
    (moduleRoots_internalHom_rightDerived_isZero k n hn hunit p M hM) q

end AlgebraicGeometry.Scheme.EtaleCohomology
