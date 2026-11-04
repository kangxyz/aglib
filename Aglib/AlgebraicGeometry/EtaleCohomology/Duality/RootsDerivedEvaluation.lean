/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.ConstantRing.Commutative
public import Aglib.Algebra.Category.ModuleCat.Sheaf.InternalHom.LiftedUnit
public import Aglib.Algebra.Category.ModuleCat.Sheaf.Tensor.RightUnit
public import Aglib.Algebra.Homology.DerivedCategory.Ext.AdjunctionAcyclic
public import Aglib.AlgebraicGeometry.EtaleCohomology.Coefficients.ModuleCohomology
public import Aglib.AlgebraicGeometry.EtaleCohomology.Duality.ConstantCoefficients

/-! # Derived evaluation against the original roots module

The original tensor with a fixed roots module is exact at positive invertible levels over
algebraically closed constants. Its action on represented Ext followed by the original tensor–Hom
counit gives the derived evaluation, with the original lifted unit on the Ext source.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
open CategoryTheory.TorsionZMod.Ringed
open SheafOfModules.InternalHom

universe u eM

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] hasSheafifyRingStandard hasSheafifyAbStandard
  ringWEqualsLocallyBijectiveStandard abWEqualsLocallyBijectiveStandard
  hasSheafifyLarge hasSheafifyModules

private def normalizedExtCounit
    {A : Type*} [Category A] [Abelian A] [HasExt.{eM} A]
    {L G : A ⥤ A} [L.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (adj : L ⊣ G) {P F : A} (s : F ⟶ L.obj P) (N : A) (q : ℕ) :
    Ext.{eM} P (G.obj N) q →+ Ext.{eM} F N q :=
  ((Ext.mk₀ s).precomp N (zero_add q)).comp (adj.extCounitMap P N q)

private theorem normalizedExtCounit_mk₀
    {A : Type*} [Category A] [Abelian A] [HasExt.{eM} A]
    {L G : A ⥤ A} [L.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (adj : L ⊣ G) {P F : A} (s : F ⟶ L.obj P) (N : A) (f : P ⟶ G.obj N) :
    normalizedExtCounit adj s N 0 (Ext.mk₀ f) =
      Ext.mk₀ (s ≫ L.map f ≫ adj.counit.app N) := by
  change (Ext.mk₀ s).comp (adj.extCounitMap P N 0 (Ext.mk₀ f)) (zero_add 0) = _
  rw [adj.extCounitMap_mk₀, Ext.mk₀_comp_mk₀, adj.homEquiv_counit]

private theorem finiteLimitsOfIdIso {A : Type*} [Category A] {L : A ⥤ A}
    (β : L ≅ 𝟭 A) : PreservesFiniteLimits L := by
  let : PreservesLimitsOfSize.{0, 0} (𝟭 A) := id_preservesLimitsOfSize
  exact preservesFiniteLimits_of_natIso β.symm

private theorem finiteColimitsOfIdIso {A : Type*} [Category A] {L : A ⥤ A}
    (β : L ≅ 𝟭 A) : PreservesFiniteColimits L := by
  let : PreservesColimitsOfSize.{0, 0} (𝟭 A) := id_preservesColimitsOfSize
  exact preservesFiniteColimits_of_natIso β.symm

private theorem normalizedExtCounit_connecting
    {A : Type*} [Category A] [Abelian A] [HasExt.{eM} A]
    {L G : A ⥤ A} [L.Additive] [G.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (adj : L ⊣ G) {P F : A} (s : F ⟶ L.obj P) {S : ShortComplex A} (hS : S.ShortExact)
    (q : ℕ) (x : Ext.{eM} P (G.obj S.X₃) q) :
    normalizedExtCounit adj s S.X₁ (q + 1) (x.comp (hS.map_of_exact G).extClass rfl) =
      (normalizedExtCounit adj s S.X₃ q x).comp hS.extClass rfl := by
  have h := adj.extEquiv_symm_naturality_right x hS.extClass rfl
  rw [Ext.mapExactFunctor_extClass] at h
  change adj.extCounitMap P S.X₁ (q + 1) (x.comp (hS.map_of_exact G).extClass rfl) =
    (adj.extCounitMap P S.X₃ q x).comp hS.extClass rfl at h
  change (Ext.mk₀ s).comp (adj.extCounitMap P S.X₁ (q + 1)
    (x.comp (hS.map_of_exact G).extClass rfl)) (zero_add (q + 1)) =
    ((Ext.mk₀ s).comp (adj.extCounitMap P S.X₃ q x) (zero_add q)).comp hS.extClass rfl
  rw [h, Ext.comp_assoc _ _ _ (zero_add q) rfl (by simp)]

section Evaluation

universe c v

variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{max c v} RingCat.{max c v})]
  (R : Sheaf J CommRingCat.{max c v}) [HasSheafify J AddCommGrpCat.{max c v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v}]

set_option quotPrecheck false in
set_option hygiene false in
local notation "R₀" =>
  (sheafCompose J (forget₂ CommRingCat.{max c v} RingCat.{max c v})).obj R
set_option quotPrecheck false in
set_option hygiene false in
local notation "U₀" => SheafOfModules.liftedUnit.{c, v, max c v, max c v} R₀

private def rightTensorIsoOfUnitIso {F : SheafOfModulesOfCommRing R}
    (e : F ≅ SheafOfModules.unit R₀) :
    tensorRightFunctor.{c, v, 0} R F ≅ 𝟭 (SheafOfModulesOfCommRing R) :=
  ((SheafOfModulesOfCommRing.tensorFunctor R).flip.mapIso e) ≪≫
    SheafOfModulesOfCommRing.tensorRightUnitIso R

variable [HasExt.{eM} (SheafOfModulesOfCommRing R)]
  (F N : SheafOfModulesOfCommRing R)
  [PreservesFiniteLimits (tensorRightFunctor.{c, v, 0} R F)]
  [PreservesFiniteColimits (tensorRightFunctor.{c, v, 0} R F)]

private def tensorLiftedUnitInv : F ⟶ (tensorRightFunctor.{c, v, 0} R F).obj U₀ :=
  (SheafOfModulesOfCommRing.tensorLeftUnitIso R).inv.app F ≫
    (tensorRightFunctor.{c, v, 0} R F).map (SheafOfModules.liftedUnitIso R₀).inv

private def derivedEvaluation (q : ℕ) : Ext.{eM} U₀ (sheaf R F N) q →+ Ext.{eM} F N q :=
  normalizedExtCounit (tensorHomAdjunction.{c, v, 0} R F)
    (tensorLiftedUnitInv R F) N q

private theorem derivedEvaluation_mk₀ (f : U₀ ⟶ sheaf R F N) :
    let L := tensorRightFunctor.{c, v, 0} R F
    let adj := tensorHomAdjunction.{c, v, 0} R F
    let s : F ⟶ L.obj U₀ := tensorLiftedUnitInv R F
    derivedEvaluation R F N 0 (Ext.mk₀ f) =
      Ext.mk₀ (X := F) (Y := N) (s ≫ L.map f ≫ adj.counit.app N) :=
  normalizedExtCounit_mk₀ (tensorHomAdjunction.{c, v, 0} R F) (tensorLiftedUnitInv R F) N f

end Evaluation

section Roots

variable (k : Type u) [Field k] [IsAlgClosed k] (n : ℕ) (hn : 0 < n)
  (hunit : IsUnit (n : k)) {X : Scheme.{u}} (p : X ⟶ Spec (.of k))

set_option quotPrecheck false in
set_option hygiene false in
local notation "Λ" => ULift.{u + 1} (ZMod n)
local notation "ℛ" => ModuleCat.Sheaf.ConstantRing.commutativeSheaf
  (Scheme.smallEtaleTopology X) Λ
local notation "Fₙ" => moduleRootsOfUnity X n
local notation "Uₙ" => moduleUnit X Λ

private def rootsTensorIso :
    tensorRightFunctor.{u + 1, u, 0} ℛ Fₙ ≅ 𝟭 (ModuleSheaf X Λ) :=
  rightTensorIsoOfUnitIso ℛ ((moduleUnitRootsIso k n hn hunit p).symm ≪≫
    SheafOfModules.liftedUnitIso (constantRing X Λ))

include hn hunit p in
/-- Exactness of tensor with the original roots module, on the limit side. -/
theorem moduleRootsTensorRight_preservesFiniteLimits :
    PreservesFiniteLimits (tensorRightFunctor.{u + 1, u, 0} ℛ Fₙ) :=
  finiteLimitsOfIdIso (rootsTensorIso k n hn hunit p)

include hn hunit p in
/-- Exactness of tensor with the original roots module, on the colimit side. -/
theorem moduleRootsTensorRight_preservesFiniteColimits :
    PreservesFiniteColimits (tensorRightFunctor.{u + 1, u, 0} ℛ Fₙ) :=
  finiteColimitsOfIdIso (rootsTensorIso k n hn hunit p)

include hn hunit p in
/-- The actual roots internal Hom is exact on the original module category. -/
theorem moduleRootsInternalHom_preservesFiniteColimits :
    PreservesFiniteColimits (homFunctor.{u + 1, u, 0} ℛ Fₙ) := by
  let L := tensorRightFunctor.{u + 1, u, 0} ℛ Fₙ
  let G := homFunctor.{u + 1, u, 0} ℛ Fₙ
  let β : L ≅ 𝟭 (ModuleSheaf X Λ) := rootsTensorIso k n hn hunit p
  let adj : L ⊣ G := tensorHomAdjunction.{u + 1, u, 0} ℛ Fₙ
  let idAdj : L ⊣ 𝟭 (ModuleSheaf X Λ) := (Adjunction.id).ofNatIsoLeft β.symm
  exact finiteColimitsOfIdIso (Adjunction.rightAdjointUniq adj idAdj)

/-- The original module Ext universe used in the roots evaluation. -/
local instance rootsEvaluationNativeHasExt [HasExt.{eM} (ModuleSheaf X Λ)] :
    HasExt.{eM} (SheafOfModulesOfCommRing.{u + 1, u + 1, u} ℛ) :=
  inferInstanceAs (HasExt.{eM} (ModuleSheaf X Λ))

variable [HasExt.{eM} (ModuleSheaf X Λ)]

include hn hunit p in
/-- The original exact tensor followed by its original derived counit, on the represented classes
of the internal Hom into the target coefficient. -/
@[no_expose]
def moduleRootsDerivedEvaluation (N : ModuleSheaf X Λ) (q : ℕ) :=
  letI : PreservesFiniteLimits (tensorRightFunctor.{u + 1, u, 0} ℛ Fₙ) :=
    moduleRootsTensorRight_preservesFiniteLimits k n hn hunit p
  letI : PreservesFiniteColimits (tensorRightFunctor.{u + 1, u, 0} ℛ Fₙ) :=
    moduleRootsTensorRight_preservesFiniteColimits k n hn hunit p
  derivedEvaluation.{eM, u + 1, u} ℛ Fₙ N q

/-- In degree zero the derived map is literal tensoring and evaluation after the original unit
identification. -/
theorem moduleRootsDerivedEvaluation_mk₀ (N : ModuleSheaf X Λ)
    (f : Uₙ ⟶ sheaf ℛ Fₙ N) :
    let L := tensorRightFunctor.{u + 1, u, 0} ℛ Fₙ
    let adj := tensorHomAdjunction.{u + 1, u, 0} ℛ Fₙ
    let s : Fₙ ⟶ L.obj Uₙ := (SheafOfModulesOfCommRing.tensorLeftUnitIso ℛ).inv.app Fₙ ≫
      L.map (SheafOfModules.liftedUnitIso (constantRing X Λ)).inv
    moduleRootsDerivedEvaluation k n hn hunit p N 0 (Ext.mk₀ f) =
      Ext.mk₀ (X := Fₙ) (Y := N) (s ≫ L.map f ≫ adj.counit.app N) := by
  let : PreservesFiniteLimits (tensorRightFunctor.{u + 1, u, 0} ℛ Fₙ) :=
    moduleRootsTensorRight_preservesFiniteLimits k n hn hunit p
  let : PreservesFiniteColimits (tensorRightFunctor.{u + 1, u, 0} ℛ Fₙ) :=
    moduleRootsTensorRight_preservesFiniteColimits k n hn hunit p
  exact derivedEvaluation_mk₀.{eM, u + 1, u} ℛ Fₙ N f

/-- The exact tensor evaluation transports the original module boundary by unsigned
postcomposition with the extension class. -/
theorem moduleRootsDerivedEvaluation_connecting {S : ShortComplex (ModuleSheaf X Λ)}
    (hS : S.ShortExact) (q : ℕ) (x : Ext.{eM} Uₙ (sheaf ℛ Fₙ S.X₃) q) :
    let G := homFunctor.{u + 1, u, 0} ℛ Fₙ
    letI : PreservesFiniteLimits G := homFunctor_preservesFiniteLimits.{u + 1, u, 0} ℛ Fₙ
    letI : PreservesFiniteColimits G :=
      moduleRootsInternalHom_preservesFiniteColimits k n hn hunit p
    moduleRootsDerivedEvaluation k n hn hunit p S.X₁ (q + 1)
        (x.comp (hS.map_of_exact G).extClass rfl) =
      (moduleRootsDerivedEvaluation k n hn hunit p S.X₃ q x).comp hS.extClass rfl := by
  intro G
  let : PreservesFiniteLimits G := homFunctor_preservesFiniteLimits.{u + 1, u, 0} ℛ Fₙ
  let : PreservesFiniteColimits G := moduleRootsInternalHom_preservesFiniteColimits k n hn hunit p
  let : PreservesFiniteLimits (tensorRightFunctor.{u + 1, u, 0} ℛ Fₙ) :=
    moduleRootsTensorRight_preservesFiniteLimits k n hn hunit p
  let : PreservesFiniteColimits (tensorRightFunctor.{u + 1, u, 0} ℛ Fₙ) :=
    moduleRootsTensorRight_preservesFiniteColimits k n hn hunit p
  let adj := tensorHomAdjunction.{u + 1, u, 0} ℛ Fₙ
  exact normalizedExtCounit_connecting adj (tensorLiftedUnitInv ℛ Fₙ) hS q x

end Roots

end AlgebraicGeometry.Scheme.EtaleCohomology
