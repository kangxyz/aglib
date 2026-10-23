/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.Torsion.Sheaf
public import Aglib.AlgebraicGeometry.EtaleCohomology.GeometricPoints.StalkUniverse

/-!
# Torsion of actual abelian etale sheaves

Internal local torsion is equivalent to torsion of the original geometric
stalks. The small conservative family supplied by the identity morphism
discharges the abstract point-family hypothesis for every scheme. No
quasicompactness or Noetherian hypothesis is required.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u

/-- Internal torsion on the actual etale site, allowing varying local annihilators. -/
abbrev IsTorsion (X : Scheme.{u}) (F : AbelianSheaf.{u, u + 1} X) : Prop :=
  Sheaf.IsTorsion F

/-- An internally torsion etale sheaf has torsion at every original geometric stalk. -/
theorem IsTorsion.geometricStalk {X : Scheme.{u}} {F : AbelianSheaf.{u, u + 1} X}
    (hF : IsTorsion X F) {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (η : Spec (.of Ω) ⟶ X) :
    IsAddTorsion ((pointSmallEtale η).sheafFiber (A := AddCommGrpCat.{u + 1}) |>.obj F) := by
  let e := (StalkUniverse.sheafFiberIso η).app F
  have hlarge := Sheaf.IsTorsion.isAddTorsion_fiber hF (FibrewiseClosed.largePoint η)
  apply IsAddTorsion.of_surjective (f := e.hom.hom) ?_ hlarge
  intro z
  refine ⟨e.inv z, ?_⟩
  exact ConcreteCategory.congr_hom e.inv_hom_id z

/-- Torsion of the original canonical geometric stalks detects internal torsion. -/
theorem isTorsion_of_geometricStalks {X : Scheme.{u}}
    (F : AbelianSheaf.{u, u + 1} X)
    (hF : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (η : Spec (.of Ω) ⟶ X),
      IsAddTorsion ((pointSmallEtale η).sheafFiber
        (A := AddCommGrpCat.{u + 1}) |>.obj F)) : IsTorsion X F := by
  let : ObjectProperty.Small.{u + 1} (FibrewiseClosed.pointFamily (𝟙 X)) := by
    unfold FibrewiseClosed.pointFamily
    infer_instance
  apply Presheaf.isLocallyTorsion_of_isAddTorsion_fibers
    (FibrewiseClosed.pointFamily (𝟙 X)) (FibrewiseClosed.pointFamily_isConservative (𝟙 X))
  rintro ⟨Φ, hΦ⟩
  obtain ⟨x⟩ := hΦ
  let η := FibrewiseClosed.geometricPoint x.val
  let e := (StalkUniverse.sheafFiberIso η).app F
  apply IsAddTorsion.of_surjective (f := e.inv.hom) ?_
    (hF (FibrewiseClosed.pointField x.val) η)
  intro z
  refine ⟨e.hom z, ?_⟩
  exact ConcreteCategory.congr_hom e.hom_inv_id z

/-- Internal torsion is exactly torsion of the original geometric stalks. -/
theorem isTorsion_iff_geometricStalks {X : Scheme.{u}}
    (F : AbelianSheaf.{u, u + 1} X) :
    IsTorsion X F ↔
      ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (η : Spec (.of Ω) ⟶ X),
        IsAddTorsion ((pointSmallEtale η).sheafFiber
          (A := AddCommGrpCat.{u + 1}) |>.obj F) :=
  ⟨fun h _ _ _ η => h.geometricStalk η, isTorsion_of_geometricStalks F⟩

end AlgebraicGeometry.Scheme.EtaleCohomology
