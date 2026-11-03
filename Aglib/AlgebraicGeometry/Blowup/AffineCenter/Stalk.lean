/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Blowup.AffineAtlas
public import Aglib.AlgebraicGeometry.Blowup.BaseChange
public import Aglib.AlgebraicGeometry.IdealSheaf.Colon

/-!
# The original affine centre at an actual scheme stalk

The existing general spectral/local-spectrum ideal comparisons are moved
once from WeakTransform and Principalization. Their original maps and proof
bodies are retained; no surface, regularity, normality or dimension premise
is used. Higher public interfaces remain available through their
same-statement thin wrappers.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Blowup

variable {A : Type u} [CommRing A]

/-- The spectral ideal correspondence returns the original ring ideal. -/
theorem spectrumIdeal_affineCenter_eq (J : Ideal A) :
    spectrumIdeal (affineCenter A J) = J := by
  rw [spectrumIdeal, affineCenter, IdealSheafData.specMap_kernel_top, Ideal.mk_ker]
  exact Ideal.map_comap_of_surjective _
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of A)).hom).surjective _

variable {X : Scheme.{u}}

/-- Extension to the original local spectrum recovers the actual stalk ideal,
through the canonical global-sections isomorphism of that spectrum. -/
theorem spectrumIdeal_comap_fromSpecStalk_eq (J : X.IdealSheafData) (x : X) :
    spectrumIdeal (J.comap (X.fromSpecStalk x)) = J.stalkIdeal x := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have hpre : (⊤ : (Spec (X.presheaf.stalk x)).Opens) ≤ (X.fromSpecStalk x) ⁻¹ᵁ U := by
    intro z _
    exact (Scheme.range_fromSpecStalk.le ⟨z, rfl⟩).mem_open U.isOpen hxU
  have happ : (X.fromSpecStalk x).appLE U ⊤ hpre ≫
      (Scheme.ΓSpecIso (X.presheaf.stalk x)).hom = X.presheaf.germ U x hxU := by
    rw [Scheme.Hom.appLE, Scheme.fromSpecStalk_app hxU]
    have hcomp : (homOfLE (show (X.fromSpecStalk x) ⁻¹ᵁ U ≤ ⊤ from le_top)).op ≫
        (homOfLE hpre).op = 𝟙 (op (⊤ : (Spec (X.presheaf.stalk x)).Opens)) :=
      Subsingleton.elim _ _
    simp only [Category.assoc, ← Functor.map_comp, hcomp]
    rw [CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id, Category.comp_id]
  calc
    spectrumIdeal (J.comap (X.fromSpecStalk x)) =
        ((J.comap (X.fromSpecStalk x)).ideal ⟨⊤, isAffineOpen_top _⟩).map
          (Scheme.ΓSpecIso (X.presheaf.stalk x)).hom.hom := rfl
    _ = ((J.ideal ⟨U, hU⟩).map ((X.fromSpecStalk x).appLE U ⊤ hpre).hom).map
          (Scheme.ΓSpecIso (X.presheaf.stalk x)).hom.hom :=
      congrArg (fun K ↦ K.map (Scheme.ΓSpecIso (X.presheaf.stalk x)).hom.hom)
        (J.ideal_comap_eq_map_appLE (X.fromSpecStalk x)
          ⟨U, hU⟩ ⟨⊤, isAffineOpen_top _⟩ hpre)
    _ = (J.ideal ⟨U, hU⟩).map (((X.fromSpecStalk x).appLE U ⊤ hpre) ≫
          (Scheme.ΓSpecIso (X.presheaf.stalk x)).hom).hom := Ideal.map_map _ _
    _ = (J.ideal ⟨U, hU⟩).map (X.presheaf.germ U x hxU).hom :=
      congrArg (fun φ : Γ(X, U) ⟶ X.presheaf.stalk x ↦ (J.ideal ⟨U, hU⟩).map φ.hom) happ
    _ = J.stalkIdeal x := (J.stalkIdeal_eq_map ⟨U, hU⟩ x hxU).symm

/-- The actual spectral stalk ideal is extension of the original ring ideal
along the canonical ring-to-stalk homomorphism. -/
theorem affineCenter_stalkIdeal {A : Type u} [CommRing A]
    (J : Ideal A) (x : Spec (.of A)) :
    (affineCenter A J).stalkIdeal x = J.map (StructureSheaf.toStalk A x).hom := by
  calc
    _ = spectrumIdeal (A := (Spec (.of A)).presheaf.stalk x)
        ((affineCenter A J).comap ((Spec (.of A)).fromSpecStalk x)) :=
      (spectrumIdeal_comap_fromSpecStalk_eq (affineCenter A J) x).symm
    _ = spectrumIdeal (A := (Spec (.of A)).presheaf.stalk x)
        ((affineCenter A J).comap (Spec.map (StructureSheaf.toStalk A x))) :=
      congrArg (fun f : Spec ((Spec (.of A)).presheaf.stalk x) ⟶ Spec (.of A) ↦
        spectrumIdeal (A := (Spec (.of A)).presheaf.stalk x) ((affineCenter A J).comap f))
        (AlgebraicGeometry.Spec.fromSpecStalk_eq' (.of A) x)
    _ = spectrumIdeal (A := (Spec (.of A)).presheaf.stalk x)
        (affineCenter ((Spec (.of A)).presheaf.stalk x)
          (J.map (StructureSheaf.toStalk A x).hom)) :=
      congrArg (spectrumIdeal (A := (Spec (.of A)).presheaf.stalk x))
        (BaseChange.affineCenter_comap (StructureSheaf.toStalk A x).hom J)
    _ = _ := spectrumIdeal_affineCenter_eq _

end AlgebraicGeometry.Scheme.Blowup
