/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Stalk.LocalBaseIdeal
public import Aglib.AlgebraicGeometry.Morphisms.Etale.StalkMap
public import Aglib.RingTheory.DiscreteValuationRing.EssentiallyEtale

/-! # Actual essentially étale stalk scalars over a closed local-base point -/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Hom

universe u
section LocalBase

variable {D : Type u} [CommRing D] [IsLocalRing D] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of D)) (x : X)

/-- The original base germ is an isomorphism at the closed point. -/
theorem closedPoint_baseGerm_surjective (hx : f x = IsLocalRing.closedPoint D) :
    Function.Surjective
      (((Spec (.of D)).presheaf.germ ⊤ (f x) trivial).hom.comp
        (Scheme.ΓSpecIso (.of D)).inv.hom) := by
  rw [hx]
  change Function.Surjective (((Scheme.ΓSpecIso (.of D)).inv ≫
    (Spec (.of D)).presheaf.germ ⊤ (IsLocalRing.closedPoint D) trivial).hom)
  rw [← ΓSpecIso_hom_stalkClosedPointIso_inv]
  simp only [Iso.inv_hom_id_assoc]
  intro a
  refine ⟨(stalkClosedPointIso (.of D)).hom a, ?_⟩
  exact ConcreteCategory.congr_hom (stalkClosedPointIso (.of D)).hom_inv_id a

/-- Essential finite type and formal unramifiedness of the original scalar map.
No finite-presentation claim is made for this localized ring map. -/
theorem stalkScalar_essentiallyEtaleProperties [Etale f]
    (hx : f x = IsLocalRing.closedPoint D) :
    (f.stalkScalar x).EssFiniteType ∧ (f.stalkScalar x).Flat ∧
      (f.stalkScalar x).FormallyUnramified := by
  have hsur := closedPoint_baseGerm_surjective f x hx
  refine ⟨?_, stalkScalar_flat f x, ?_⟩
  · rw [stalkScalar_eq_local]
    exact (RingHom.FiniteType.of_surjective _ hsur).essFiniteType.comp
      (LocallyOfFiniteType.stalkMap f x)
  · rw [stalkScalar_eq_local]
    exact (RingHom.FormallyUnramified.of_surjective hsur).comp
      (FormallyUnramified.stalkMap f x)

end LocalBase

/-- The actual stalk above the closed point of a DVR is a DVR, and every original
uniformizer remains irreducible under the canonical scalar map. -/
theorem stalkScalar_dvr_uniformizer {D : Type u} [CommRing D]
    [IsDomain D] [IsDiscreteValuationRing D] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of D)) (x : X) [Etale f] (hx : f x = IsLocalRing.closedPoint D) {t : D}
    (ht : Irreducible t) :
    ∃ hD : IsDomain (X.presheaf.stalk x),
      letI := hD
      IsDiscreteValuationRing (X.presheaf.stalk x) ∧
        Irreducible (f.stalkScalar x t) := by
  let := (f.stalkScalar x).toAlgebra
  have h := stalkScalar_essentiallyEtaleProperties f x hx
  let : Algebra.EssFiniteType D (X.presheaf.stalk x) := h.1
  let : Module.Flat D (X.presheaf.stalk x) := h.2.1
  let : Algebra.FormallyUnramified D (X.presheaf.stalk x) := h.2.2
  let : IsLocalHom (algebraMap D (X.presheaf.stalk x)) :=
    stalkScalar_isLocalHom_of_closedPoint f x hx
  let : IsDomain (X.presheaf.stalk x) :=
    Algebra.FormallyUnramified.isDomain_of_flat_local_dvr D (X.presheaf.stalk x)
  exact ⟨inferInstance,
    Algebra.FormallyUnramified.isDiscreteValuationRing_of_flat_local_dvr
      D (X.presheaf.stalk x),
    Algebra.FormallyUnramified.irreducible_algebraMap_of_flat_local_dvr
      D (X.presheaf.stalk x) ht⟩

end AlgebraicGeometry.Scheme.Hom
