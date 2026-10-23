/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.IdealSheaf.Modules.Stalk
public import Aglib.AlgebraicGeometry.Modules.StructureSheaf.Hom
public import Aglib.AlgebraicGeometry.Modules.Pullback.LocalSpectrum
public import Aglib.AlgebraicGeometry.Modules.Invertible.LocalRing
public import Aglib.Algebra.Category.ModuleCat.ChangeOfRings.SpanSingleton
public import Aglib.RingTheory.Ideal.RegularPrincipal.BaseChange

/-!
# Original Cartier sections at actual points after pullback

A global function in the original section kernel determines a canonical map
from the structure module to the actual ideal module. Generation of the
original ideal stalk at the image of a point makes the stalk of its actual
pullback invertible, hence makes the pulled section nonzero. Membership in the
maximal ideal times that same original ideal stalk prevents the pulled section
from being an isomorphism.

The source and test schemes are arbitrary. Only local rank one of the original
ideal module and quasi-compactness of the morphism defining it are needed;
closed Cartier immersions satisfy the latter automatically. The current
consumer is `Surfaces.Resolution.VerticalCartier`.
-/

@[expose] public section
noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits AlgebraicGeometry Opposite TopologicalSpace
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Invertible

universe u

private theorem ideal_coefficient_mem_mul {R : Type u} [CommRing R]
    (I J : Ideal R) (e : I ≃ₗ[R] R) (a : I) (ha : a.val ∈ J * I) : e a ∈ J := by
  let g : I := e.symm 1
  have he (m : I) : e m • g = m := by
    dsimp [g]
    rw [← e.symm.map_smul, smul_eq_mul, mul_one, e.symm_apply_apply]
  have hgen : I = Ideal.span {g.val} := by
    apply le_antisymm
    · intro t ht
      exact Ideal.mem_span_singleton'.mpr
        ⟨e ⟨t, ht⟩, congrArg Subtype.val (he ⟨t, ht⟩)⟩
    · exact I.span_singleton_le_iff_mem.mpr g.property
  have ha' : a.val ∈ J * Ideal.span {g.val} :=
    Eq.mp (congrArg (fun K : Ideal R ↦ a.val ∈ J * K) hgen) ha
  obtain ⟨r, hr, hra⟩ := Ideal.mem_mul_span_singleton.mp ha'
  have hsub : r • g = a := Subtype.ext hra
  have hcoef : r = e a := by
    simpa only [_root_.map_smul, g, LinearEquiv.apply_symm_apply, smul_eq_mul, mul_one]
      using congrArg e hsub
  exact hcoef ▸ hr

private theorem ideal_section_isIso_of_generator {R : CommRingCat.{u}}
    (I : Ideal R) (e : I ≃ₗ[R] R) (a : I) (hgen : I = Ideal.span {a.val}) :
    IsIso (ModuleCat.ofHom (LinearMap.toSpanSingleton R I a)) := by
  have hsurj : Function.Surjective (LinearMap.toSpanSingleton R I a) := by
    intro b
    have hb : b.val ∈ Ideal.span {a.val} :=
      Eq.mp (congrArg (fun J : Ideal R ↦ b.val ∈ J) hgen) b.property
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp hb
    exact ⟨r, Subtype.ext hr⟩
  have hunit : IsUnit (e a) := by
    obtain ⟨r, hr⟩ := hsurj (e.symm 1)
    apply IsUnit.of_mul_eq_one_right r
    simpa only [LinearMap.toSpanSingleton_apply, _root_.map_smul,
      LinearEquiv.apply_symm_apply, smul_eq_mul] using congrArg e hr
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  refine ⟨?_, hsurj⟩
  intro r s hrs
  apply hunit.mul_left_injective
  change r • a = s • a at hrs
  simpa only [_root_.map_smul, smul_eq_mul] using congrArg e hrs

private theorem scalarExtension_section_isIso_iff {R S : CommRingCat.{u}}
    (φ : R ⟶ S) (a : R) :
    IsIso ((ModuleCat.extendScalars φ.hom).map
      (ModuleCat.ofHom (LinearMap.toSpanSingleton R R a))) ↔ IsUnit (φ a) := by
  have : IsIso (ModuleCat.scalarExtensionUnit φ) := ModuleCat.scalarExtensionUnit_isIso φ
  have he := ModuleCat.extendScalars_map_toSpanSingleton_comp φ a (φ a)
    (ModuleCat.scalarExtensionUnit φ) (by
      simp only [ModuleCat.scalarExtensionUnit, Equiv.apply_symm_apply]
      rfl)
  have hunit : IsIso (ModuleCat.ofHom (LinearMap.toSpanSingleton S S (φ a))) ↔
      IsUnit (φ a) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    exact IsUnit.isUnit_iff_mulRight_bijective.symm
  constructor
  · intro H
    let := H
    have hc : IsIso (((ModuleCat.extendScalars φ.hom).map
        (ModuleCat.ofHom (LinearMap.toSpanSingleton R R a))) ≫
          ModuleCat.scalarExtensionUnit φ) := inferInstance
    rw [he] at hc
    let := hc
    exact hunit.mp (IsIso.of_isIso_comp_left (ModuleCat.scalarExtensionUnit φ) _)
  · intro H
    have : IsIso (ModuleCat.ofHom (LinearMap.toSpanSingleton S S (φ a))) := hunit.mpr H
    have hc : IsIso (((ModuleCat.extendScalars φ.hom).map
        (ModuleCat.ofHom (LinearMap.toSpanSingleton R R a))) ≫
          ModuleCat.scalarExtensionUnit φ) := by
      rw [he]
      infer_instance
    let := hc
    exact IsIso.of_isIso_comp_right _ (ModuleCat.scalarExtensionUnit φ)

private theorem ideal_section_not_isIso_after_local_extension
    {R S : CommRingCat.{u}} [IsLocalRing R]
    (φ : R ⟶ S) [IsLocalHom φ.hom] (I : Ideal R) (e : I ≃ₗ[R] R)
    (a : I) (ha : a.val ∈ IsLocalRing.maximalIdeal R * I) :
    ¬ IsIso ((ModuleCat.extendScalars φ.hom).map
      (ModuleCat.ofHom (LinearMap.toSpanSingleton R I a))) := by
  intro H
  let := H
  have he : ModuleCat.ofHom (LinearMap.toSpanSingleton R I a) ≫ e.toModuleIso.hom =
      ModuleCat.ofHom (LinearMap.toSpanSingleton R R (e a)) := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro r
    exact e.map_smul r a
  have hc : IsIso ((ModuleCat.extendScalars φ.hom).map
      (ModuleCat.ofHom (LinearMap.toSpanSingleton R R (e a)))) := by
    rw [← he, Functor.map_comp]
    infer_instance
  have hu : IsUnit (e a) := (isUnit_map_iff φ.hom _).mp
    ((scalarExtension_section_isIso_iff φ (e a)).mp hc)
  have hm := ideal_coefficient_mem_mul I (IsLocalRing.maximalIdeal R) e a ha
  exact ((IsLocalRing.mem_maximalIdeal _).mp hm) hu

namespace AlgebraicGeometry.Scheme.Hom

variable {Z X C : Scheme.{u}}

/-- The canonical section of the original ideal module defined by an actual
global function in the original kernel. -/
def idealGlobalSection (i : Z ⟶ X) (a : Γ(X, ⊤))
    (ha : a ∈ RingHom.ker i.appTop.hom) :
    (show X.Modules from SheafOfModules.unit X.ringCatSheaf) ⟶ idealModule i :=
  (unitHomGlobalSectionsEquiv X (idealModule i)).symm
    ((idealSectionsEquiv i ⊤).symm ⟨a, ha⟩)

private def idealGlobalSectionStalkElement (i : Z ⟶ X) [QuasiCompact i]
    (a : Γ(X, ⊤)) (ha : a ∈ RingHom.ker i.appTop.hom) (x : X) : i.ker.stalkIdeal x :=
  idealModuleStalkEquiv i x ((idealModule i).presheaf.germ ⊤ x trivial
    ((idealSectionsEquiv i ⊤).symm ⟨a, ha⟩))

private theorem idealGlobalSectionStalkElement_val (i : Z ⟶ X) [QuasiCompact i]
    (a : Γ(X, ⊤)) (ha : a ∈ RingHom.ker i.appTop.hom) (x : X) :
    (idealGlobalSectionStalkElement i a ha x).val = X.presheaf.germ ⊤ x trivial a := by
  rw [idealGlobalSectionStalkElement, idealModuleStalkEquiv_germ_val]
  have hs := idealSectionsEquiv_val i ⊤ ((idealSectionsEquiv i ⊤).symm ⟨a, ha⟩)
  simp only [LinearEquiv.apply_symm_apply] at hs
  exact congrArg (X.presheaf.germ ⊤ x trivial) hs.symm

/-- A global section of the original section kernel has its original germ
in the original stalk ideal at every point. -/
theorem idealGlobalSection_germ_mem_stalkIdeal (i : Z ⟶ X) [QuasiCompact i]
    (a : Γ(X, ⊤)) (ha : a ∈ RingHom.ker i.appTop.hom) (x : X) :
    X.presheaf.germ ⊤ x trivial a ∈ i.ker.stalkIdeal x := by
  rw [← idealGlobalSectionStalkElement_val i a ha x]
  exact (idealGlobalSectionStalkElement i a ha x).property

private theorem idealGlobalSection_stalk_conjugate (i : Z ⟶ X) [QuasiCompact i]
    (a : Γ(X, ⊤)) (ha : a ∈ RingHom.ker i.appTop.hom) (x : X) :
    (unitModuleStalkEquiv X x).toModuleIso.inv ≫
      (moduleStalk X x).map (idealGlobalSection i a ha) ≫
      (idealModuleStalkEquiv i x).toModuleIso.hom =
        ModuleCat.ofHom (LinearMap.toSpanSingleton (X.presheaf.stalk x)
          (i.ker.stalkIdeal x) (idealGlobalSectionStalkElement i a ha x)) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext_ring
  have hu : (unitModuleStalkEquiv X x).symm 1 =
      (show X.Modules from SheafOfModules.unit X.ringCatSheaf).presheaf.germ
        ⊤ x trivial (1 : Γ(X, ⊤)) := by
    apply (unitModuleStalkEquiv X x).injective
    simp only [LinearEquiv.apply_symm_apply, unitModuleStalkEquiv_germ, map_one]
  change idealModuleStalkEquiv i x
      (((moduleStalk X x).map (idealGlobalSection i a ha))
        ((unitModuleStalkEquiv X x).symm 1)) = _
  rw [hu]
  change idealModuleStalkEquiv i x
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
        (idealGlobalSection i a ha).mapPresheaf
        ((show X.Modules from SheafOfModules.unit X.ringCatSheaf).presheaf.germ
          ⊤ x trivial (1 : Γ(X, ⊤)))) = _
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
  change idealModuleStalkEquiv i x
      ((idealModule i).presheaf.germ ⊤ x trivial
        ((idealGlobalSection i a ha).app ⊤ (1 : Γ(X, ⊤)))) =
    (1 : X.presheaf.stalk x) • idealGlobalSectionStalkElement i a ha x
  have hs : (idealGlobalSection i a ha).app ⊤ (1 : Γ(X, ⊤)) =
      (idealSectionsEquiv i ⊤).symm ⟨a, ha⟩ := by
    change unitHomGlobalSectionsEquiv X (idealModule i)
      ((unitHomGlobalSectionsEquiv X (idealModule i)).symm _) = _
    exact Equiv.apply_symm_apply _ _
  rw [hs, one_smul]
  rfl

private theorem idealStalk_nonempty_equiv_ring (i : Z ⟶ X) [QuasiCompact i]
    (hI : IsLocallyRankOne X (idealModule i)) (x : X) :
    Nonempty (i.ker.stalkIdeal x ≃ₗ[X.presheaf.stalk x] X.presheaf.stalk x) := by
  let R := X.presheaf.stalk x
  let L : LineBundle (Spec R) :=
    ⟨(Scheme.Modules.pullback (X.fromSpecStalk x)).obj (idealModule i),
      pullback_locallyRankOne _ _ hI⟩
  obtain ⟨e⟩ := nonempty_iso_unit_of_isLocalRing R L
  let eM : (moduleStalk X x).obj (idealModule i) ≅ ModuleCat.of R R :=
    stalkFromSpecStalkSectionsIso X x (idealModule i) ≪≫
      moduleSpecΓFunctor.mapIso e ≪≫ (tilde.isoTop (ModuleCat.of R R)).symm
  exact ⟨(idealModuleStalkEquiv i x).symm.trans eM.toLinearEquiv⟩

/-- If the original germ generates the original Cartier ideal stalk, the
original section map on that actual stalk is an isomorphism. -/
theorem idealGlobalSection_stalk_isIso_of_generator (i : Z ⟶ X) [QuasiCompact i]
    (hI : IsLocallyRankOne X (idealModule i)) (a : Γ(X, ⊤))
    (ha : a ∈ RingHom.ker i.appTop.hom) (x : X)
    (hgen : i.ker.stalkIdeal x = Ideal.span {X.presheaf.germ ⊤ x trivial a}) :
    IsIso ((moduleStalk X x).map (idealGlobalSection i a ha)) := by
  obtain ⟨e⟩ := idealStalk_nonempty_equiv_ring i hI x
  have hgen' : i.ker.stalkIdeal x = Ideal.span {(idealGlobalSectionStalkElement i a ha x).val} :=
    (idealGlobalSectionStalkElement_val i a ha x).symm ▸ hgen
  have hc := ideal_section_isIso_of_generator (i.ker.stalkIdeal x) e
    (idealGlobalSectionStalkElement i a ha x) hgen'
  rw [← idealGlobalSection_stalk_conjugate i a ha x] at hc
  let := hc
  have : IsIso ((moduleStalk X x).map (idealGlobalSection i a ha) ≫
      (idealModuleStalkEquiv i x).toModuleIso.hom) :=
    IsIso.of_isIso_comp_left (unitModuleStalkEquiv X x).toModuleIso.inv _
  exact IsIso.of_isIso_comp_right _ (idealModuleStalkEquiv i x).toModuleIso.hom

/-- Generation at the original image point makes the actual pulled section
invertible on the actual stalk of the test scheme. -/
theorem idealGlobalSection_pullback_stalk_isIso_of_generator
    (i : Z ⟶ X) [QuasiCompact i] (hI : IsLocallyRankOne X (idealModule i))
    (j : C ⟶ X) (a : Γ(X, ⊤)) (ha : a ∈ RingHom.ker i.appTop.hom) (c : C)
    (hgen : i.ker.stalkIdeal (j c) = Ideal.span {X.presheaf.germ ⊤ (j c) trivial a}) :
    IsIso ((moduleStalk C c).map
      ((pullbackUnitIso j).inv ≫ (Scheme.Modules.pullback j).map (idealGlobalSection i a ha))) := by
  have hbase : IsIso ((moduleStalk X (j c)).map (idealGlobalSection i a ha)) :=
    idealGlobalSection_stalk_isIso_of_generator i hI a ha (j c) hgen
  have hext : IsIso ((ModuleCat.extendScalars (j.stalkMap c).hom).map
      ((moduleStalk X (j c)).map (idealGlobalSection i a ha))) :=
    (ModuleCat.extendScalars (j.stalkMap c).hom).map_isIso _
  have hp : IsIso ((moduleStalk C c).map
      ((Scheme.Modules.pullback j).map (idealGlobalSection i a ha))) :=
    (NatIso.isIso_map_iff (pullbackModuleStalkIso j c) (idealGlobalSection i a ha)).mpr hext
  rw [Functor.map_comp]
  infer_instance

/-- A generating germ at any actual image point proves that the original
pulled section is nonzero. No integrality assumption on the test scheme is needed. -/
theorem idealGlobalSection_pullback_ne_zero_of_generator
    (i : Z ⟶ X) [QuasiCompact i] (hI : IsLocallyRankOne X (idealModule i))
    (j : C ⟶ X) (a : Γ(X, ⊤)) (ha : a ∈ RingHom.ker i.appTop.hom) (c : C)
    (hgen : i.ker.stalkIdeal (j c) = Ideal.span {X.presheaf.germ ⊤ (j c) trivial a}) :
    (pullbackUnitIso j).inv ≫ (Scheme.Modules.pullback j).map (idealGlobalSection i a ha) ≠ 0 := by
  intro hz
  have := idealGlobalSection_pullback_stalk_isIso_of_generator i hI j a ha c hgen
  let e := unitModuleStalkEquiv C c
  have hinj := (ConcreteCategory.bijective_of_isIso ((moduleStalk C c).map
    ((pullbackUnitIso j).inv ≫ (Scheme.Modules.pullback j).map (idealGlobalSection i a ha)))).1
  have he : e.symm 1 = e.symm 0 := hinj (by rw [hz, Functor.map_zero]; rfl)
  exact one_ne_zero (e.symm.injective he)

/-- A germ in the maximal ideal times the original ideal stalk makes the
same original pulled section fail to be an isomorphism. -/
theorem idealGlobalSection_pullback_not_isIso_of_mem_maximal_mul
    (i : Z ⟶ X) [QuasiCompact i] (hI : IsLocallyRankOne X (idealModule i))
    (j : C ⟶ X) (a : Γ(X, ⊤)) (ha : a ∈ RingHom.ker i.appTop.hom) (c : C)
    (hm : X.presheaf.germ ⊤ (j c) trivial a ∈
      IsLocalRing.maximalIdeal (X.presheaf.stalk (j c)) * i.ker.stalkIdeal (j c)) :
    ¬ IsIso ((pullbackUnitIso j).inv ≫
      (Scheme.Modules.pullback j).map (idealGlobalSection i a ha)) := by
  intro H
  let := H
  have : IsIso ((Scheme.Modules.pullback j).map (idealGlobalSection i a ha)) :=
    IsIso.of_isIso_comp_left (pullbackUnitIso j).inv _
  have hp : IsIso ((moduleStalk C c).map
      ((Scheme.Modules.pullback j).map (idealGlobalSection i a ha))) :=
    (moduleStalk C c).map_isIso _
  have hb : IsIso ((ModuleCat.extendScalars (j.stalkMap c).hom).map
      ((moduleStalk X (j c)).map (idealGlobalSection i a ha))) :=
    (NatIso.isIso_map_iff (pullbackModuleStalkIso j c) (idealGlobalSection i a ha)).mp hp
  have hc : IsIso ((ModuleCat.extendScalars (j.stalkMap c).hom).map
      (ModuleCat.ofHom (LinearMap.toSpanSingleton (X.presheaf.stalk (j c))
        (i.ker.stalkIdeal (j c)) (idealGlobalSectionStalkElement i a ha (j c))))) := by
    rw [← idealGlobalSection_stalk_conjugate i a ha (j c), Functor.map_comp, Functor.map_comp]
    infer_instance
  obtain ⟨e⟩ := idealStalk_nonempty_equiv_ring i hI (j c)
  apply ideal_section_not_isIso_after_local_extension (j.stalkMap c)
    (i.ker.stalkIdeal (j c)) e (idealGlobalSectionStalkElement i a ha (j c)) ?_ hc
  simpa only [idealGlobalSectionStalkElement_val] using hm

end AlgebraicGeometry.Scheme.Hom
