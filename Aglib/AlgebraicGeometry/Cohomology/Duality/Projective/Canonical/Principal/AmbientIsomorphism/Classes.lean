/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.Principal.AmbientIsomorphism
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.Principal.AmbientIsomorphism.Model

/-!
# Literal regular quotients under an ambient ring isomorphism

The quotient map, its Cartesian spectral square, and the scalar-extension
source isomorphism are the original maps. The coefficient frame retains the
native affine restriction comparison and scalar-extension ring unit.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry
open scoped TensorProduct ChangeOfRings

universe u w z

namespace AlgebraicGeometry.Scheme.Modules

variable {A A' : CommRingCat.{u}} (a : A ≃+* A') (s : List A)

/-- The original quotient ring equivalence induced by the ambient ring equivalence. -/
def regularListAmbientQuotientEquiv :
    (A ⧸ Ideal.ofList s) ≃+* (A' ⧸ Ideal.ofList (s.map a.toRingHom)) :=
  Ideal.quotientEquiv (Ideal.ofList s) (Ideal.ofList (s.map a.toRingHom)) a
    (Ideal.map_ofList a.toRingHom s).symm

/-- The literal quotient square retains both original quotient maps. -/
theorem regularListAmbientRingSquare :
    regularListQuotientMap s ≫ (regularListAmbientQuotientEquiv a s).toCommRingCatIso.hom =
      a.toCommRingCatIso.hom ≫ regularListQuotientMap (s.map a.toRingHom) := by
  ext r
  rfl

/-- The original ambient and source isomorphisms form the actual Cartesian square. -/
theorem regularListAmbientSquare :
    IsPullback (Spec.map (regularListAmbientQuotientEquiv a s).toCommRingCatIso.hom)
      (Spec.map (regularListQuotientMap (s.map a.toRingHom)))
      (Spec.map (regularListQuotientMap s)) (Spec.map a.toCommRingCatIso.hom) := by
  apply IsPullback.of_horiz_isIso
  constructor
  rw [← Spec.map_comp, ← Spec.map_comp, regularListAmbientRingSquare]

/-- The same scalar-extension quotient isomorphism, with the native quotient
actions required by the geometric closed-adjoint comparison. -/
def regularListAmbientSourceIso :
    (ModuleCat.extendScalars a.toRingHom).obj
        ((ModuleCat.restrictScalars (regularListQuotientMap s).hom).obj
          (ModuleCat.of (regularListQuotientRing s) (regularListQuotientRing s))) ≅
      (ModuleCat.restrictScalars (regularListQuotientMap (s.map a.toRingHom)).hom).obj
        (ModuleCat.of (regularListQuotientRing (s.map a.toRingHom))
          (regularListQuotientRing (s.map a.toRingHom))) := by
  letI := a.toRingHom.toAlgebra
  exact ChainComplex.Koszul.scalarExtensionQuotientIso (S := A') s

/-- The actual source isomorphism retains the original unit pure tensors. -/
theorem regularListAmbientSourceIso_one_tmul (b : A ⧸ Ideal.ofList s) :
    (regularListAmbientSourceIso a s).hom
        ((1 : A') ⊗ₜ[A,a.toRingHom]
          (show (ModuleCat.restrictScalars (regularListQuotientMap s).hom).obj
            (ModuleCat.of (regularListQuotientRing s) (regularListQuotientRing s)) from b)) =
      regularListAmbientQuotientEquiv a s b := by
  let := a.toRingHom.toAlgebra
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective b
  exact ChainComplex.Koszul.scalarExtensionQuotientIso_one_tmul (S := A') s r

/-- The ambient ring-isomorphism coefficient frame uses the original scalar
extension, chosen coefficient frame, and actual coefficient comparison. -/
def regularListAmbientCoefficientFrame
    {L : ModuleCat.{u} A} {L' : ModuleCat.{u} A'}
    (e : L ≅ ModuleCat.of A A)
    (θ : (ModuleCat.extendScalars a.toRingHom).obj L ≅ L') :
    L' ≅ ModuleCat.of A' A' := by
  letI := a.toRingHom.toAlgebra
  exact θ.symm ≪≫ (ModuleCat.extendScalars a.toRingHom).mapIso e ≪≫
    ModuleCat.extendScalarsAlgebraObjIso A A' (ModuleCat.of A A) ≪≫
    (TensorProduct.AlgebraTensorModule.rid A A' A').toModuleIso

variable [HasExt.{w} (ModuleCat.{u} A)] [HasExt.{z} (ModuleCat.{u} A')]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The original flat scalar-extension top-class formula retains both the
literal same-list quotient and the actual coefficient frame. -/
theorem regularListAmbientTopExtClass_coefficients
    (hs : RingTheory.Sequence.IsWeaklyRegular A s) (x : A)
    {L : ModuleCat.{u} A} {L' : ModuleCat.{u} A'}
    (e : L ≅ ModuleCat.of A A)
    (θ : (ModuleCat.extendScalars a.toRingHom).obj L ≅ L') :
    letI := a.toRingHom.toAlgebra
    letI : Module.Flat A A' :=
      RingHom.flat_algebraMap_iff.mp (RingHom.Flat.of_bijective a.bijective)
    let F : ModuleCat.{u} A ⥤ ModuleCat.{u} A' := ModuleCat.extendScalars a.toRingHom
    letI : PreservesFiniteLimits F :=
      ModuleCat.extendScalars_preservesFiniteLimits_of_flat _
        (RingHom.Flat.of_bijective a.bijective)
    letI : PreservesFiniteColimits F :=
      ModuleCat.extendScalars_preservesFiniteColimits_of_flat _
        (RingHom.Flat.of_bijective a.bijective)
    let e' := regularListAmbientCoefficientFrame a e θ
    ((Ext.mk₀ (regularListAmbientSourceIso a s).inv).comp
      (((ChainComplex.Koszul.topExtClass s hs (ModuleCat.of A A) x).comp
        (Ext.mk₀ e.inv) (add_zero s.length)).mapExactFunctor F) (zero_add s.length)).comp
      (Ext.mk₀ θ.hom) (add_zero s.length) =
    (cast (congrArg (fun k => Ext.{z}
      (ModuleCat.of A' (A' ⧸ Ideal.ofList (s.map a.toRingHom))) (ModuleCat.of A' A') k)
      (List.length_map (as := s) a.toRingHom))
      (ChainComplex.Koszul.topExtClass (s.map a.toRingHom) (hs.of_flat (S := A'))
        (ModuleCat.of A' A') (a x))).comp (Ext.mk₀ e'.inv) (add_zero s.length) := by
  let := a.toRingHom.toAlgebra
  let : Module.Flat A A' :=
    RingHom.flat_algebraMap_iff.mp (RingHom.Flat.of_bijective a.bijective)
  let F : ModuleCat.{u} A ⥤ ModuleCat.{u} A' := ModuleCat.extendScalars a.toRingHom
  let : PreservesFiniteLimits F :=
    ModuleCat.extendScalars_preservesFiniteLimits_of_flat _
      (RingHom.Flat.of_bijective a.bijective)
  let : PreservesFiniteColimits F :=
    ModuleCat.extendScalars_preservesFiniteColimits_of_flat _
      (RingHom.Flat.of_bijective a.bijective)
  let e' := regularListAmbientCoefficientFrame a e θ
  let ε := ModuleCat.extendScalarsAlgebraObjIso A A' (ModuleCat.of A A) ≪≫
    (TensorProduct.AlgebraTensorModule.rid A A' A').toModuleIso
  have hbase := ChainComplex.Koszul.topExtClass_map_of_flat a.toRingHom
    (RingHom.Flat.of_bijective a.bijective) s hs x
  have hvalue : a.toRingHom x = a x := rfl
  rw [hvalue] at hbase
  change ((Ext.mk₀ (regularListAmbientSourceIso a s).inv).comp
      ((ChainComplex.Koszul.topExtClass s hs (ModuleCat.of A A) x).mapExactFunctor F)
      (zero_add s.length)).comp (Ext.mk₀ ε.hom) (add_zero s.length) = _ at hbase
  have he := congrArg (fun ξ => ξ.comp (Ext.mk₀ e'.inv) (add_zero s.length)) hbase
  have hε : ε.hom ≫ e'.inv = F.map e.inv ≫ θ.hom := by
    change ε.hom ≫ (ε.inv ≫ F.map e.inv ≫ θ.hom) = _
    rw [Iso.hom_inv_id_assoc]
  simp only [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, hε] at he
  simpa only [F, e', RingEquiv.coe_toRingHom,
    Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
    Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀] using he

section GeometricClass

variable (hs : RingTheory.Sequence.IsWeaklyRegular A s)
  {L : (Spec A).Modules} [L.IsQuasicoherent]
  (e : moduleSpecΓFunctor.obj L ≅ ModuleCat.of A A) (J : InjectiveResolution L)

local instance : ((restrictFunctor (Spec.map a.toCommRingCatIso.hom)).obj L).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent (Spec A').ringCatSheaf).prop_of_iso
    ((restrictFunctorIsoPullback (Spec.map a.toCommRingCatIso.hom)).symm.app L)
    (isQuasicoherent_pullback a.toCommRingCatIso.hom L)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual geometric ambient-isomorphism homology map sends the original
top Koszul class to the literal image-list class with its original induced
coefficient frame. No source, flatness, or naturality witness is added. -/
theorem regularListAmbientHomologyMap_topClass (x : A) :
    letI := a.toRingHom.toAlgebra
    letI : Module.Flat A A' :=
      RingHom.flat_algebraMap_iff.mp (RingHom.Flat.of_bijective a.bijective)
    let φ := a.toCommRingCatIso.hom
    let σ := regularListQuotientMap s
    let τ := regularListQuotientMap (s.map a.toRingHom)
    let ψ := (regularListAmbientQuotientEquiv a s).toCommRingCatIso.hom
    let J' := affineOpenRestrictedInjectiveResolution φ J
    let θ := affineRestrictGlobalSectionsIso φ L
    let e' := regularListAmbientCoefficientFrame a e θ
    let ξ := (closedImmersionRightAdjointRegularListResolutionSectionsExtAddEquiv s J
      s.length).symm ((ChainComplex.Koszul.topExtClass s hs (ModuleCat.of A A) x).comp
        (Ext.mk₀ e.inv) (add_zero s.length))
    affineClosedRightAdjointResolutionExtAddEquiv τ J' s.length
      (canonicalAmbientHomologyMap φ σ τ ψ (regularListAmbientSquare a s) J
        (s.length : ℤ) ξ) =
      (cast (congrArg (fun k => Ext.{z}
        (ModuleCat.of A' (A' ⧸ Ideal.ofList (s.map a.toRingHom))) (ModuleCat.of A' A') k)
        (List.length_map (as := s) a.toRingHom))
        (ChainComplex.Koszul.topExtClass (s.map a.toRingHom) (hs.of_flat (S := A'))
          (ModuleCat.of A' A') (a x))).comp (Ext.mk₀ e'.inv) (add_zero s.length) := by
  let := a.toRingHom.toAlgebra
  let : Module.Flat A A' :=
    RingHom.flat_algebraMap_iff.mp (RingHom.Flat.of_bijective a.bijective)
  let φ := a.toCommRingCatIso.hom
  let σ := regularListQuotientMap s
  let τ := regularListQuotientMap (s.map a.toRingHom)
  let ψ := (regularListAmbientQuotientEquiv a s).toCommRingCatIso.hom
  let J' := affineOpenRestrictedInjectiveResolution φ J
  let θ := affineRestrictGlobalSectionsIso φ L
  let ξ := (closedImmersionRightAdjointRegularListResolutionSectionsExtAddEquiv s J
    s.length).symm ((ChainComplex.Koszul.topExtClass s hs (ModuleCat.of A A) x).comp
      (Ext.mk₀ e.inv) (add_zero s.length))
  have hξ : closedImmersionRightAdjointRegularListResolutionSectionsExtAddEquiv s J
      s.length ξ =
    (ChainComplex.Koszul.topExtClass s hs (ModuleCat.of A A) x).comp
      (Ext.mk₀ e.inv) (add_zero s.length) :=
    (closedImmersionRightAdjointRegularListResolutionSectionsExtAddEquiv s J
      s.length).apply_symm_apply _
  rw [closedImmersionRightAdjointRegularListResolutionSectionsExtAddEquiv_eq_affine] at hξ
  change affineClosedRightAdjointResolutionExtAddEquiv σ J s.length ξ = _ at hξ
  have hg := canonicalAmbientHomologyMap_ext φ σ τ ψ (regularListAmbientSquare a s) J
    (regularListAmbientSourceIso a s) (regularListAmbientSourceIso_one_tmul a s)
    (RingHom.Flat.of_bijective a.bijective) s.length ξ
  erw [hξ] at hg
  exact hg.trans (regularListAmbientTopExtClass_coefficients a s hs x e θ)

end GeometricClass

end AlgebraicGeometry.Scheme.Modules
