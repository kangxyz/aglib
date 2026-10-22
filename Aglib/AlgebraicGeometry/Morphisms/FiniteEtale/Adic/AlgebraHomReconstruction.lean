/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Adic.AlgebraHomAffineCharts
public import Aglib.AlgebraicGeometry.Modules.Coherent.Algebra.DirectImageMaps
public import Aglib.AlgebraicGeometry.Modules.Coherent.Algebra.DirectImageSections
public import Aglib.AlgebraicGeometry.Modules.Locality.Sections

/-!
# Original Hom reconstruction for affine structure morphisms

A unit- and multiplication-preserving map between the original direct-image
structure modules gives an actual morphism over the base. Its induced module
map is the specified original map, not a map under an unspecified equivalence.
In particular this applies to arbitrary finite maps, including finite covers
composed with a closed immersion. No étaleness, properness, Noetherianity, or
completeness is needed.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory MonoidalCategory Opposite
open scoped MonObj AlgebraicGeometry.Scheme.Modules.Algebra

namespace AlgebraicGeometry.Scheme.Modules.Algebra

attribute [local instance] inverseImageSectionsAlgebra

variable {X Y Z : Scheme.{u}} {p : Y ⟶ X} {q : Z ⟶ X}

/-- An original algebra-object map induces a map of the original structure rings. -/
def structureSectionRingHom
    (u : Scheme.Modules.Hom (X := X) (pushforwardStructureSheaf q)
      (pushforwardStructureSheaf p)) [IsMonHom (C := X.Modules) u]
    (U : X.Opens) : Γ(Z, q ⁻¹ᵁ U) ⟶ Γ(Y, p ⁻¹ᵁ U) :=
  CommRingCat.ofHom ((pushforwardStructureSectionsAlgEquiv p U).toRingHom.comp
    ((sectionAlgHom u U).toRingHom.comp
      (pushforwardStructureSectionsAlgEquiv q U).symm.toRingHom))

/-- The reconstructed ring map retains the literal original module component. -/
@[simp] theorem structureSectionRingHom_apply
    (u : Scheme.Modules.Hom (X := X) (pushforwardStructureSheaf q)
      (pushforwardStructureSheaf p)) [IsMonHom (C := X.Modules) u]
    (U : X.Opens) (m : Γ(Z, q ⁻¹ᵁ U)) : structureSectionRingHom u U m = u.app U m := by
  change (pushforwardStructureSectionsAlgEquiv p U)
    (sectionAlgHom u U ((pushforwardStructureSectionsAlgEquiv q U).symm m)) = u.app U m
  rw [pushforwardStructureSectionsAlgEquiv_apply, sectionAlgHom_apply]
  congr 1
  apply (pushforwardStructureSectionsAlgEquiv q U).injective
  simp only [AlgEquiv.apply_symm_apply, pushforwardStructureSectionsAlgEquiv_apply]

/-- The original ring maps retain restriction naturality. -/
@[reassoc] theorem structureSectionRingHom_naturality
    (u : Scheme.Modules.Hom (X := X) (pushforwardStructureSheaf q)
      (pushforwardStructureSheaf p)) [IsMonHom (C := X.Modules) u]
    {U V : X.Opens} (i : U ⟶ V) :
    structureSectionRingHom u V ≫ Y.presheaf.map (homOfLE (p.preimage_mono i.le)).op =
      Z.presheaf.map (homOfLE (q.preimage_mono i.le)).op ≫ structureSectionRingHom u U := by
  ext m
  simp only [CommRingCat.comp_apply, structureSectionRingHom_apply]
  exact (PresheafOfModules.naturality_apply u.val i.op m).symm

/-- The original structural ring maps commute with the original module component. -/
@[reassoc] theorem structureSectionRingHom_over
    (u : Scheme.Modules.Hom (X := X) (pushforwardStructureSheaf q)
      (pushforwardStructureSheaf p)) [IsMonHom (C := X.Modules) u]
    (U : X.Opens) : q.app U ≫ structureSectionRingHom u U = p.app U := by
  ext r
  simp only [CommRingCat.comp_apply, structureSectionRingHom_apply]
  exact congrArg (fun f : Scheme.Modules.Hom (X := X) (𝟙_ X.Modules)
      (pushforwardStructureSheaf p) => f.val.app (op U) r)
    (IsMonHom.one_hom (C := X.Modules) u)

/-- The original map over the base identifies the relevant inverse-image opens. -/
theorem over_preimage_le (g : Y ⟶ Z) (w : g ≫ q = p) (U : X.Opens) :
    p ⁻¹ᵁ U ≤ g ⁻¹ᵁ (q ⁻¹ᵁ U) := by subst p; exact le_rfl

/-- On sections the original direct-image map is the native restricted scheme map. -/
theorem structurePullbackMap_appLE (g : Y ⟶ Z) (w : g ≫ q = p)
    (U : X.Opens) (m : Γ(Z, q ⁻¹ᵁ U)) :
    (structurePullbackMap g w).app U m =
      g.appLE (q ⁻¹ᵁ U) (p ⁻¹ᵁ U) (over_preimage_le g w U) m := by
  subst p
  rw [structurePullbackMap_comp_app]
  change g.app (q ⁻¹ᵁ U) m = g.appLE (q ⁻¹ᵁ U) (g ⁻¹ᵁ (q ⁻¹ᵁ U)) le_rfl m
  rw [Scheme.Hom.appLE_eq_app]

/-- Extracting the original ring map from a geometric map gives its native component. -/
theorem structureSectionRingHom_structurePullbackMap (g : Y ⟶ Z) (w : g ≫ q = p)
    (U : X.Opens) :
    structureSectionRingHom (structurePullbackMap g w) U =
      g.appLE (q ⁻¹ᵁ U) (p ⁻¹ᵁ U) (over_preimage_le g w U) := by
  ext m
  rw [structureSectionRingHom_apply, structurePullbackMap_appLE]

variable [IsAffineHom p] [IsAffineHom q]

/-- Original affine coordinates of an existing geometric map. -/
@[reassoc] theorem structurePullbackMap_fromSpec
    (g : Y ⟶ Z) (w : g ≫ q = p) (U : X.affineOpens) :
    (U.property.preimage p).fromSpec ≫ g =
      Spec.map (structureSectionRingHom (structurePullbackMap g w) U.val) ≫
        (U.property.preimage q).fromSpec := by
  rw [structureSectionRingHom_structurePullbackMap]
  exact (IsAffineOpen.SpecMap_appLE_fromSpec g (U.property.preimage q)
    (U.property.preimage p) (over_preimage_le g w U.val)).symm

/-- Affine structure morphisms are determined by their original direct-image module maps. -/
theorem structurePullbackMap_injective (g h : Y ⟶ Z)
    (wg : g ≫ q = p) (wh : h ≫ q = p)
    (e : structurePullbackMap g wg = structurePullbackMap h wh) : g = h := by
  apply (affineInverseImageCover p).hom_ext
  intro U
  apply (cancel_epi (U.property.preimage p).isoSpec.inv).mp
  change (U.property.preimage p).fromSpec ≫ g = (U.property.preimage p).fromSpec ≫ h
  have he : structureSectionRingHom (structurePullbackMap g wg) U.val =
      structureSectionRingHom (structurePullbackMap h wh) U.val := by
    ext m
    simp only [structureSectionRingHom_apply]
    exact congrArg (fun v : Scheme.Modules.Hom (X := X) (pushforwardStructureSheaf q)
      (pushforwardStructureSheaf p) => v.app U.val m) e
  rw [structurePullbackMap_fromSpec g wg, structurePullbackMap_fromSpec h wh, he]

/-- Recovering the original coordinate equations recovers the original module map. -/
theorem structurePullbackMap_eq_of_fromSpec
    (u : Scheme.Modules.Hom (X := X) (pushforwardStructureSheaf q)
      (pushforwardStructureSheaf p)) [IsMonHom (C := X.Modules) u]
    (g : Y ⟶ Z) (w : g ≫ q = p)
    (h : ∀ U : X.affineOpens, (U.property.preimage p).fromSpec ≫ g =
      Spec.map (structureSectionRingHom u U.val) ≫ (U.property.preimage q).fromSpec) :
    structurePullbackMap g w = u := by
  apply moduleHom_ext_affine
  intro U
  have he : structureSectionRingHom (structurePullbackMap g w) U.val =
      structureSectionRingHom u U.val := by
    apply Spec.map_injective
    apply (cancel_mono (U.property.preimage q).fromSpec).mp
    exact (structurePullbackMap_fromSpec g w U).symm.trans (h U)
  ext m
  exact (structureSectionRingHom_apply (structurePullbackMap g w) U.val m).symm.trans
    ((congrArg (fun f => f m) he).trans (structureSectionRingHom_apply u U.val m))

/-- The actual reconstructed over-base morphism and its exact original module-map equation. -/
def structureAlgebraHomData
    (u : Scheme.Modules.Hom (X := X) (pushforwardStructureSheaf q)
      (pushforwardStructureSheaf p)) [IsMonHom (C := X.Modules) u] :
    { g : Over.mk p ⟶ Over.mk q // structurePullbackMap g.left g.w = u } := by
  let d := affineSectionHomData p q (fun U => structureSectionRingHom u U.val)
    (fun {_ _} i => structureSectionRingHom_naturality u (homOfLE i.le))
    (fun U => structureSectionRingHom_over u U.val)
  exact ⟨d.val, structurePullbackMap_eq_of_fromSpec u d.val.left d.val.w d.property⟩

/-- Every original algebra-object map between affine direct images has a unique geometric source. -/
theorem existsUnique_structurePullbackMap
    (u : Scheme.Modules.Hom (X := X) (pushforwardStructureSheaf q)
      (pushforwardStructureSheaf p)) [IsMonHom (C := X.Modules) u] :
    ∃! g : Over.mk p ⟶ Over.mk q, structurePullbackMap g.left g.w = u := by
  refine ⟨(structureAlgebraHomData u).val, (structureAlgebraHomData u).property, ?_⟩
  intro g hg
  apply CostructuredArrow.hom_ext
  exact structurePullbackMap_injective (p := p) (q := q) g.left
    (structureAlgebraHomData u).val.left g.w
    (structureAlgebraHomData u).val.w (hg.trans (structureAlgebraHomData u).property.symm)

/-- The same reconstruction uses the caller's actual objects in the over category. -/
theorem existsUnique_structurePullbackMap_over {P Q : Over X}
    [IsAffineHom P.hom] [IsAffineHom Q.hom]
    (u : Scheme.Modules.Hom (X := X) (pushforwardStructureSheaf Q.hom)
      (pushforwardStructureSheaf P.hom)) [IsMonHom (C := X.Modules) u] :
    ∃! g : P ⟶ Q, structurePullbackMap g.left g.w = u := by
  obtain ⟨g, hg, huniq⟩ := existsUnique_structurePullbackMap u
  refine ⟨Over.homMk g.left g.w, hg, ?_⟩
  intro h hh
  apply CostructuredArrow.hom_ext
  exact congrArg (fun k => k.left) (huniq (Over.homMk h.left h.w) hh)

/-- Equality detection on the caller's original over-category morphisms. -/
theorem structurePullbackMap_over_injective {P Q : Over X}
    [IsAffineHom P.hom] [IsAffineHom Q.hom] (g h : P ⟶ Q)
    (e : structurePullbackMap g.left g.w = structurePullbackMap h.left h.w) : g = h := by
  apply CostructuredArrow.hom_ext
  exact structurePullbackMap_injective g.left h.left g.w h.w e

end AlgebraicGeometry.Scheme.Modules.Algebra
