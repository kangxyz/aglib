/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.TensorFiniteFree
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic

/-!
Source: `Quillen/Algebra/Category/ModuleCat/Sheaf/TensorInjectiveRetract.lean` at LOCAL Quillen
`189a8e779f0c68b2dfc6f8195daebb3e684a5905`. Selection: whole_general_prerequisite;
source ranges [[1, 56]]. Actual objects, maps and hypotheses are preserved.
-/

/-!
# Injective tensor with original finite-free retract coefficients

The actual finite-free tensor comparison identifies tensor with a finite
biproduct of the original injective sheaf. An explicit coefficient retraction
then gives injectivity through the original tensor maps. This is a global
finite-projective coefficient statement on a ringed site, with independent
universes and explicit sheafification hypotheses.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v w
open CategoryTheory CategoryTheory.Limits
namespace SheafOfModulesOfCommRing
variable {C : Type v} [Category.{w} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    (R : Sheaf J CommRingCat.{u}) [HasSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
attribute [local instance] Abelian.hasFiniteBiproducts
/-- An actual finite-free coefficient sends an injective sheaf to an injective sheaf. -/
theorem tensorFiniteFree_injective (I : Type u) [Finite I]
    (M : SheafOfModulesOfCommRing R) [Injective M] :
    Injective ((tensorLeftFunctor R (SheafOfModules.free
      (R := ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) I)).obj M) := by
  let e := (tensorFiniteFreeIso R I).app M ≪≫
    PreservesCoproduct.iso ((evaluation _ _).obj M)
      (fun (_ : I) => 𝟭 (SheafOfModulesOfCommRing R)) ≪≫
    (biproduct.isoCoproduct (fun (_ : I) => M)).symm
  exact Injective.of_iso e.symm inferInstance
/-- An original finite-free retraction preserves injectivity under the actual tensor maps. -/
theorem tensor_injective_of_retract_finiteFree
    {E : SheafOfModulesOfCommRing R} (I : Type u) [Finite I]
    (h : Retract E (SheafOfModules.free
      (R := ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) I))
    (M : SheafOfModulesOfCommRing R) [Injective M] :
    Injective ((tensorLeftFunctor R E).obj M) := by
  let hT := (h.map (tensorFunctor R)).map ((evaluation _ _).obj M)
  let : Injective (((evaluation _ _).obj M).obj ((tensorFunctor R).obj
      (SheafOfModules.free
        (R := ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) I))) :=
    tensorFiniteFree_injective R I M
  exact hT.injective
end SheafOfModulesOfCommRing
