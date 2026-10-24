/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.Torsion.Annihilator.AllowedColimit
public import Aglib.AlgebraicGeometry.EtaleCohomology.Torsion.Basic

/-! # Torsion with orders invertible on the entire base

The allowed multiplicative set consists of integers invertible in the global
sections of the specified base. The local condition is equivalent to allowed
annihilators in the original geometric stalks and is presented by the actual
filtered diagram of native annihilator kernels. The base need not be the
scheme carrying the coefficient sheaf.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology

attribute [local instance] hasSheafifyLarge

/-- The multiplicative set of integer orders invertible on the entire specified base. -/
def baseInvertibleOrders (S : Scheme.{u}) : Submonoid ℕ where
  carrier := {n | IsUnit (n : Γ(S, ⊤))}
  one_mem' := by simp
  mul_mem' := by
    intro n m hn hm
    change IsUnit (n : Γ(S, ⊤)) at hn
    change IsUnit (m : Γ(S, ⊤)) at hm
    change IsUnit ((n * m : ℕ) : Γ(S, ⊤))
    rw [Nat.cast_mul]
    exact hn.mul hm

/-- Local positive annihilators are required to be invertible on the whole base `S`. -/
def IsBaseInvertibleTorsion (S : Scheme.{u}) {X : Scheme.{u}}
    (F : AbelianSheaf.{u, u + 1} X) : Prop :=
  Presheaf.IsLocallyAllowedTorsion (baseInvertibleOrders S)
    (Scheme.smallEtaleTopology X) F.obj

/-- Base-invertible torsion implies the existing internal torsion predicate. -/
theorem IsBaseInvertibleTorsion.isTorsion {S X : Scheme.{u}}
    {F : AbelianSheaf.{u, u + 1} X} (hF : IsBaseInvertibleTorsion S F) :
    IsTorsion X F := hF.isLocallyTorsion

/-- Every original geometric-stalk element has an annihilator invertible on the whole base. -/
theorem IsBaseInvertibleTorsion.geometricStalk {S X : Scheme.{u}}
    {F : AbelianSheaf.{u, u + 1} X} (hF : IsBaseInvertibleTorsion S F)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (η : Spec (.of Ω) ⟶ X)
    (z : ((pointSmallEtale η).sheafFiber (A := AddCommGrpCat.{u + 1})).obj F) :
    ∃ n : ℕ, 0 < n ∧ IsUnit (n : Γ(S, ⊤)) ∧ n • z = 0 := by
  let e := (StalkUniverse.sheafFiberIso η).app F
  obtain ⟨n, hn, hm, hs⟩ := hF.fiber (FibrewiseClosed.largePoint η) (e.inv z)
  refine ⟨n, hn, hm, ?_⟩
  have he : e.hom (e.inv z) = z := ConcreteCategory.congr_hom e.inv_hom_id z
  simpa only [map_nsmul, map_zero, he] using congrArg e.hom hs

/-- The original geometric stalks detect the global-base allowed-order condition. -/
theorem isBaseInvertibleTorsion_of_geometricStalks {S X : Scheme.{u}}
    (F : AbelianSheaf.{u, u + 1} X)
    (hF : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (η : Spec (.of Ω) ⟶ X)
      (z : ((pointSmallEtale η).sheafFiber (A := AddCommGrpCat.{u + 1})).obj F),
      ∃ n : ℕ, 0 < n ∧ IsUnit (n : Γ(S, ⊤)) ∧ n • z = 0) :
    IsBaseInvertibleTorsion S F := by
  let : ObjectProperty.Small.{u + 1} (FibrewiseClosed.pointFamily (𝟙 X)) := by
    unfold FibrewiseClosed.pointFamily
    infer_instance
  apply Presheaf.isLocallyAllowedTorsion_of_fibers
    (FibrewiseClosed.pointFamily (𝟙 X)) (FibrewiseClosed.pointFamily_isConservative (𝟙 X))
  rintro ⟨Φ, hΦ⟩ z
  obtain ⟨x⟩ := hΦ
  let η := FibrewiseClosed.geometricPoint x.val
  let e := (StalkUniverse.sheafFiberIso η).app F
  obtain ⟨n, hn, hm, hs⟩ := hF (FibrewiseClosed.pointField x.val) η (e.hom z)
  refine ⟨n, hn, hm, ?_⟩
  have he : e.inv (e.hom z) = z := ConcreteCategory.congr_hom e.hom_inv_id z
  simpa only [map_nsmul, map_zero, he] using congrArg e.inv hs

/-- The condition concerns the original geometric stalks but invertibility on the entire base. -/
theorem isBaseInvertibleTorsion_iff_geometricStalks {S X : Scheme.{u}}
    (F : AbelianSheaf.{u, u + 1} X) :
    IsBaseInvertibleTorsion S F ↔
      ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (η : Spec (.of Ω) ⟶ X)
        (z : ((pointSmallEtale η).sheafFiber (A := AddCommGrpCat.{u + 1})).obj F),
        ∃ n : ℕ, 0 < n ∧ IsUnit (n : Γ(S, ⊤)) ∧ n • z = 0 :=
  ⟨fun h _ _ _ η z => h.geometricStalk η z, isBaseInvertibleTorsion_of_geometricStalks F⟩

/-- The actual allowed-annihilator cocone is a filtered-colimit presentation of `F`. -/
def baseInvertibleAnnihilatorCoconeIsColimit {S X : Scheme.{u}}
    (F : AbelianSheaf.{u, u + 1} X) (hF : IsBaseInvertibleTorsion S F) :
    IsColimit (Sheaf.allowedAnnihilatorCocone (baseInvertibleOrders S) F) :=
  Sheaf.allowedAnnihilatorCoconeIsColimit (baseInvertibleOrders S) F hF

/-- The actual allowed-annihilator colimit identifies with the original coefficient sheaf. -/
def baseInvertibleAnnihilatorColimitIso {S X : Scheme.{u}}
    (F : AbelianSheaf.{u, u + 1} X) (hF : IsBaseInvertibleTorsion S F) :
    colimit (Sheaf.allowedAnnihilatorDiagram (baseInvertibleOrders S) F) ≅ F :=
  Sheaf.allowedAnnihilatorColimitIso (baseInvertibleOrders S) F hF

/-- The isomorphism keeps the original native kernel inclusion at every allowed stage. -/
@[reassoc]
theorem baseInvertibleAnnihilatorColimitIso_ι {S X : Scheme.{u}}
    (F : AbelianSheaf.{u, u + 1} X) (hF : IsBaseInvertibleTorsion S F)
    (n : AllowedAnnihilatorIndex (baseInvertibleOrders S)) :
    colimit.ι (Sheaf.allowedAnnihilatorDiagram (baseInvertibleOrders S) F) n ≫
        (baseInvertibleAnnihilatorColimitIso F hF).hom =
      Sheaf.annihilatorι F n.val :=
  Sheaf.allowedAnnihilatorColimitMap_ι (baseInvertibleOrders S) F n

end AlgebraicGeometry.Scheme.EtaleCohomology
