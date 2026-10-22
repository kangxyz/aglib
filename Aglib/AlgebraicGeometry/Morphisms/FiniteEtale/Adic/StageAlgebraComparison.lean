/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Adic.StageAlgebraEtale
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Adic.AlgebraHomAffineCharts
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.Algebraization.QuotientCoordinates
public import Aglib.AlgebraicGeometry.AffineScheme.TensorPullback

/-!
# Original affine quotient comparisons for finite-etale stage covers

The original quotient algebra coordinates give a Cartesian rectangle with the
actual closed subscheme. The local map is the spectrum of the original section
map, transported only by the original affine-open spectrum isomorphism.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite
open scoped MonObj TensorProduct AlgebraicGeometry.Scheme.Modules.Algebra

namespace AlgebraicGeometry.Scheme.FiniteEtale.Adic

universe u

/-- Assemble the original map, its literal formula and its Cartesian rectangle
before specializing the section rings or closed-subscheme coordinates. -/
def quotientSectionRectangleData
    {R A B B' S' : Type u} [CommRing R] [CommRing A] [CommRing B]
    [CommRing B'] [CommRing S'] [Algebra R A] [Algebra R B]
    (J : Ideal R) (a : A →ₐ[R] B) (c : Modules.Algebra.QuotientAlgebraCoordinates J a)
    (eB : B ≃+* B') (eS : (R ⧸ J) ≃+* S') (s : S' →+* B') (r : R →+* S')
    (hs : eB.toRingHom.comp c.scalar = s.comp eS.toRingHom)
    (hr : eS.toRingHom.comp (Ideal.Quotient.mk J) = r)
    {W V U X Z : Scheme.{u}}
    (eW : W ≅ Spec (.of B')) (eV : V ≅ Spec (.of S')) (eU : U ≅ Spec (.of R))
    (p : W ⟶ V) (k : V ⟶ U) (z : V ⟶ Z) (j : U ⟶ X) (i : Z ⟶ X)
    (hp : Spec.map (CommRingCat.ofHom s) ≫ eV.inv = eW.inv ≫ p)
    (hk : Spec.map (CommRingCat.ofHom r) ≫ eU.inv = eV.inv ≫ k)
    (hopen : IsPullback k z j i) :
    { g : W ⟶ Spec (.of A) //
      g = eW.hom ≫ Spec.map (CommRingCat.ofHom (eB.toRingHom.comp a.toRingHom)) ∧
      IsPullback g (p ≫ z)
        (Spec.map (CommRingCat.ofHom (algebraMap R A)) ≫ eU.inv ≫ j) i } := by
  letI := c.scalar.toAlgebra
  have ht := Spec.isPullback_of_tensorEquiv c.equiv a.toRingHom (by
    ext x
    exact c.one_tmul x)
  have hsections : IsPullback
      (Spec.map (CommRingCat.ofHom (eB.toRingHom.comp a.toRingHom)))
      (Spec.map (CommRingCat.ofHom s))
      (Spec.map (CommRingCat.ofHom (algebraMap R A)))
      (Spec.map (CommRingCat.ofHom r)) := by
    refine ht.of_iso' (Scheme.Spec.mapIso eB.toCommRingCatIso.op) (.refl _)
      (Scheme.Spec.mapIso eS.toCommRingCatIso.op) (.refl _) ?_ ?_ ?_ ?_
    · change Spec.map (CommRingCat.ofHom eB.toRingHom) ≫
        Spec.map (CommRingCat.ofHom a.toRingHom) = _ ≫ 𝟙 _
      rw [Category.comp_id, ← Spec.map_comp]
      rfl
    · change Spec.map (CommRingCat.ofHom eB.toRingHom) ≫
        Spec.map (CommRingCat.ofHom c.scalar) =
        Spec.map (CommRingCat.ofHom s) ≫ Spec.map (CommRingCat.ofHom eS.toRingHom)
      rw [← Spec.map_comp, ← Spec.map_comp]
      congr 1
      exact CommRingCat.hom_ext hs
    · simp
    · change Spec.map (CommRingCat.ofHom eS.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) = _ ≫ 𝟙 _
      rw [Category.comp_id, ← Spec.map_comp]
      congr 1
      exact CommRingCat.hom_ext hr
  have hlocal : IsPullback
      (eW.hom ≫ Spec.map (CommRingCat.ofHom (eB.toRingHom.comp a.toRingHom))) p
      (Spec.map (CommRingCat.ofHom (algebraMap R A)) ≫ eU.inv) k := by
    refine hsections.of_iso' eW (.refl _) eV eU ?_ ?_ ?_ ?_
    · simp
    · apply (cancel_epi eW.inv).mp
      apply (cancel_mono eV.inv).mp
      simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id,
        Category.comp_id] using hp
    · simp
    · apply (cancel_epi eV.inv).mp
      apply (cancel_mono eU.inv).mp
      simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id,
        Category.comp_id] using hk
  refine ⟨_, rfl, ?_⟩
  simpa only [Category.assoc] using hlocal.paste_vert hopen

/-- Native affine coordinates of the original restriction of a morphism. -/
theorem affineOpen_specMap_app_restrict {Y Z : Scheme.{u}} (p : Y ⟶ Z)
    {V : Z.Opens} (hV : IsAffineOpen V) (hW : IsAffineOpen (p ⁻¹ᵁ V)) :
    Spec.map (p.app V) ≫ hV.isoSpec.inv = hW.isoSpec.inv ≫ (p ∣_ V) := by
  apply (cancel_mono V.ι).mp
  simpa only [Scheme.Hom.appLE_eq_app, IsAffineOpen.fromSpec, Category.assoc,
    morphismRestrict_ι] using hV.SpecMap_appLE_fromSpec p hW le_rfl

attribute [local instance] Modules.Algebra.inverseImageSectionsAlgebra

variable {X : Scheme.{u}} (K : X.IdealSheafData) (C : FiniteEtale K.subscheme)
  (M : X.Modules) [MonObj M] [IsCommMonObj M]
  (q : M ⟶ stageCoefficient K C) [IsMonHom q]

/-- The actual stage chart map is the spectrum of the original section map. -/
def stageSectionMap (U : X.affineOpens) :
    ((C.obj.hom ≫ K.subschemeι) ⁻¹ᵁ U.val).toScheme ⟶ Spec (.of Γ(M, U.val)) :=
  (U.property.preimage (C.obj.hom ≫ K.subschemeι)).isoSpec.hom ≫
    Spec.map (CommRingCat.ofHom
      ((Modules.Algebra.pushforwardStructureSectionsAlgEquiv
        (C.obj.hom ≫ K.subschemeι) U.val).toRingHom.comp
          (Modules.Algebra.sectionAlgHom q U.val).toRingHom))

/-- These original chart maps commute with the original section restrictions. -/
theorem stageSectionMap_naturality {U V : X.affineOpens} (j : U.val ⟶ V.val) :
    C.obj.left.homOfLE ((C.obj.hom ≫ K.subschemeι).preimage_mono j.le) ≫
        stageSectionMap K C M q V =
      stageSectionMap K C M q U ≫
        Spec.map (CommRingCat.ofHom (Modules.Algebra.sectionRestriction M j)) := by
  let p := C.obj.hom ≫ K.subschemeι
  let a (W : X.affineOpens) := CommRingCat.ofHom
    ((Modules.Algebra.pushforwardStructureSectionsAlgEquiv p W.val).toRingHom.comp
      (Modules.Algebra.sectionAlgHom q W.val).toRingHom)
  have ha : a V ≫ C.obj.left.presheaf.map (homOfLE (p.preimage_mono j.le)).op =
      CommRingCat.ofHom (Modules.Algebra.sectionRestriction M j) ≫ a U := by
    apply CommRingCat.hom_ext
    ext m
    change (stageCoefficient K C).val.map j.op (q.app V.val m) =
      q.app U.val (M.val.map j.op m)
    exact (PresheafOfModules.naturality_apply q.val j.op m).symm
  have h := Modules.Algebra.affineChartMap_naturality
    (U.property.preimage p).isoSpec (V.property.preimage p).isoSpec
    (C.obj.left.homOfLE (p.preimage_mono j.le))
    (Spec.map (CommRingCat.ofHom (Modules.Algebra.sectionRestriction M j))) (𝟙 _)
    (C.obj.left.presheaf.map (homOfLE (p.preimage_mono j.le)).op)
    (CommRingCat.ofHom (Modules.Algebra.sectionRestriction M j)) (a U) (a V)
    (Modules.Algebra.affineOpen_isoSpec_inv_restriction
      (V.property.preimage p) (U.property.preimage p)
      (homOfLE (p.preimage_mono j.le))).symm (Category.comp_id _) ha
  simpa only [Category.comp_id, stageSectionMap, Category.assoc] using h

/-- The actual quotient coordinates give the rectangle with the original closed
subscheme, not merely an isomorphism between unrelated affine schemes. -/
theorem stageSectionMap_isPullback (U : X.affineOpens)
    (J : Ideal Γ(X, U)) (hJ : J = K.ideal U)
    (c : Modules.Algebra.QuotientAlgebraCoordinates J
      (Modules.Algebra.sectionAlgHom q U.val)) :
    IsPullback (stageSectionMap K C M q U)
      (((C.obj.hom ≫ K.subschemeι) ⁻¹ᵁ U.val).ι ≫ C.obj.hom)
      (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) Γ(M, U.val))) ≫
        U.property.fromSpec) K.subschemeι := by
  let eB := Modules.Algebra.pushforwardStructureSectionsAlgEquiv
    (C.obj.hom ≫ K.subschemeι) U.val
  let eS := stageBaseSectionsEquiv K U J hJ
  have hscalar : c.scalar = stageCoefficientScalar K C U J hJ := by
    apply RingHom.ext
    intro a
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
    exact congrArg (fun g : Γ(X, U) →+* Γ(stageCoefficient K C, U.val) => g r)
      (c.factor.trans (stageCoefficientScalar_factor K C U J hJ).symm)
  have hs : eB.toRingHom.comp c.scalar =
      (C.obj.hom.app (K.subschemeι ⁻¹ᵁ U.val)).hom.comp eS.toRingHom := by
    rw [hscalar]
    ext a
    exact eB.apply_symm_apply _
  have hr : eS.toRingHom.comp (Ideal.Quotient.mk J) = (K.subschemeι.app U.val).hom := by
    ext r
    exact stageBaseSectionsEquiv_mk K U J hJ r
  let d := quotientSectionRectangleData J (Modules.Algebra.sectionAlgHom q U.val) c
    eB.toRingEquiv eS (C.obj.hom.app (K.subschemeι ⁻¹ᵁ U.val)).hom
    (K.subschemeι.app U.val).hom hs hr
    (U.property.preimage (C.obj.hom ≫ K.subschemeι)).isoSpec
    (U.property.preimage K.subschemeι).isoSpec U.property.isoSpec
    (C.obj.hom ∣_ (K.subschemeι ⁻¹ᵁ U.val)) (K.subschemeι ∣_ U.val)
    (K.subschemeι ⁻¹ᵁ U.val).ι U.val.ι K.subschemeι
    (affineOpen_specMap_app_restrict C.obj.hom
      (U.property.preimage K.subschemeι) (U.property.preimage (C.obj.hom ≫ K.subschemeι)))
    (affineOpen_specMap_app_restrict K.subschemeι U.property
      (U.property.preimage K.subschemeι))
    (isPullback_morphismRestrict K.subschemeι U.val)
  have hd := d.property.2
  rw [d.property.1] at hd
  simpa only [stageSectionMap, eB, Scheme.Hom.comp_preimage, morphismRestrict_ι,
    IsAffineOpen.fromSpec] using hd

end AlgebraicGeometry.Scheme.FiniteEtale.Adic
