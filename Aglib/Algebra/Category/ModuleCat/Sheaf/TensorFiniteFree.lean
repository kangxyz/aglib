/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.TensorAdditive
public import Aglib.CategoryTheory.Abelian.FiniteCoproductFunctor
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.CategoryTheory.Abelian.FunctorCategory

/-!
Source: `Quillen/Algebra/Category/ModuleCat/Sheaf/TensorFiniteFree.lean` at LOCAL Quillen
`189a8e779f0c68b2dfc6f8195daebb3e684a5905`. Selection: whole_general_prerequisite;
source ranges [[1, 80]]. Actual objects, maps and hypotheses are preserved.
-/

/-!
# Tensoring with actual finite free sheaves

Tensoring with the original finite free module sheaf is naturally identified with
the finite coproduct of identity functors. Every original free inclusion is retained
through the original tensor unit comparison. Both finite-limit and finite-colimit
preservation follow from this comparison.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u v w

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
namespace SheafOfModulesOfCommRing

variable {C : Type v} [Category.{w} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    (R : Sheaf J CommRingCat.{u}) [HasSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
attribute [local instance] Abelian.hasFiniteBiproducts

/-- Tensoring by the original finite free sheaf is a finite coproduct of identities. -/
def tensorFiniteFreeIso (I : Type u) [Finite I] :
    tensorLeftFunctor R (SheafOfModules.free
      (R := ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) I) ≅
      ∐ (fun (_ : I) => 𝟭 (SheafOfModulesOfCommRing R)) :=
  PreservesCoproduct.iso (tensorFunctor R) (fun (_ : I) =>
    SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ≪≫
      Sigma.mapIso (fun (_ : I) => tensorLeftUnitIso R)

/-- Each original finite-free inclusion is identified by the original unit comparison. -/
theorem tensorFiniteFreeIso_ι (I : Type u) [Finite I] (i : I) :
    (tensorFunctor R).map (SheafOfModules.ιFree
      (R := ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) i) ≫
        (tensorFiniteFreeIso R I).hom =
      (tensorLeftUnitIso R).hom ≫
        Sigma.ι (fun (_ : I) => 𝟭 (SheafOfModulesOfCommRing R)) i := by
  let U := SheafOfModules.unit
    ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)
  have h : (tensorFunctor R).map (Sigma.ι (fun (_ : I) => U) i) ≫
      (PreservesCoproduct.iso (tensorFunctor R) (fun (_ : I) => U)).hom =
        Sigma.ι (fun (_ : I) => (tensorFunctor R).obj U) i := by
    apply (Iso.eq_comp_inv _).mp
    simp only [PreservesCoproduct.inv_hom, ι_comp_sigmaComparison]
  dsimp only [tensorFiniteFreeIso, Iso.trans_hom, SheafOfModules.ιFree]
  rw [← Category.assoc, h]
  simp

/-- Tensoring by an actual finite free sheaf preserves finite limits. -/
instance tensorFiniteFree_preservesFiniteLimits (I : Type u) [Finite I] :
    PreservesFiniteLimits (tensorLeftFunctor R (SheafOfModules.free
      (R := ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) I)) := by
  have := preservesFiniteLimits_coproduct (fun (_ : I) => 𝟭 (SheafOfModulesOfCommRing R))
  exact preservesFiniteLimits_of_natIso (tensorFiniteFreeIso R I).symm

/-- Tensoring by an actual finite free sheaf preserves finite colimits. -/
instance tensorFiniteFree_preservesFiniteColimits (I : Type u) [Finite I] :
    PreservesFiniteColimits (tensorLeftFunctor R (SheafOfModules.free
      (R := ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) I)) := by
  have := preservesFiniteColimits_coproduct (fun (_ : I) => 𝟭 (SheafOfModulesOfCommRing R))
  exact preservesFiniteColimits_of_natIso (tensorFiniteFreeIso R I).symm

end SheafOfModulesOfCommRing
