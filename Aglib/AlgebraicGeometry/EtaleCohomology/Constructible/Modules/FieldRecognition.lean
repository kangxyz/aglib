/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.PointFinitePresentation
public import Aglib.CategoryTheory.Sites.Point.Constant
public import Aglib.AlgebraicGeometry.Morphisms.Etale.FieldPoint
public import Aglib.AlgebraicGeometry.EtaleCohomology.GeometricPoints.EtaleRestriction
public import Aglib.AlgebraicGeometry.EtaleCohomology.GeometricPoints.ModuleFieldConservative
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.EtaleRestriction
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.LocallyConstant

/-! # Recognition of finite-type local constancy over a field

Finite presentation of the original chosen geometric stalk lifts its identity
map to an actual pointed chart. A finite separable refinement preserves that
point, and the original constant-adjunction germ equation proves that the
resulting map is an isomorphism. Finite generation alone is used only in the
separate Noetherian-ring corollary. No spreading or global constructibility
statement is asserted.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules

universe u r

attribute [local instance] hasSheafifyLarge ModuleCat.Sheaf.hasSheafify

variable {R : Type r} [CommRing R] (K : Type u) [Field K]
  {Ω : Type u} [Field Ω] [IsSepClosed Ω] (η : Spec (.of Ω) ⟶ Spec (.of K))

/-- A finitely presented chosen geometric stalk over a field yields an actual
finite-type local trivialization of the original module sheaf. -/
theorem isFiniteTypeLocallyConstant_of_finitePresentation_geometricStalk
    (F : ModuleSheaf R (Spec (.of K)))
    [Module.FinitePresentation R
      (((pointSmallEtale η).sheafFiber (A := ModuleCat.{u + 1} R)).obj F)] :
    IsFiniteTypeLocallyConstant F := by
  let : HasProducts.{u} (ModuleCat.{u + 1} R) :=
    fun I => ModuleCat.hasLimitsOfShape.{u, u, u + 1, r} (J := Discrete I)
  let U₀ := forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1}
  let : PreservesColimitsOfSize.{u, u} U₀ :=
    ModuleCat.forget₂PreservesColimitsOfSize.{u + 1, r, u, u} R
  let : PreservesFilteredColimitsOfSize.{u, u} U₀ := ⟨fun _ _ _ => inferInstance⟩
  let : PreservesFilteredColimitsOfSize.{u, u} (CategoryTheory.forget AddCommGrpCat.{u + 1}) :=
    preservesFilteredColimitsOfSize_of_univLE.{u + 1, u + 1}
      (CategoryTheory.forget AddCommGrpCat.{u + 1})
  let : PreservesFilteredColimitsOfSize.{u, u} (CategoryTheory.forget (ModuleCat.{u + 1} R)) :=
    comp_preservesFilteredColimits U₀ (CategoryTheory.forget AddCommGrpCat.{u + 1})
  let Φ := pointSmallEtale η
  let M : ModuleCat.{u + 1} R := Φ.sheafFiber.obj F
  obtain ⟨U, a, b, hb⟩ :=
    ModuleCat.Presheaf.exists_toPresheafFiber_factor_of_finitePresentation
      Φ F.obj M (𝟙 M)
  obtain ⟨L, hL, hKL, hfin, hsep, v, ζ, hv, hp⟩ :=
    Scheme.exists_finite_separable_field_point K U.hom a.left
  let := hL
  let := hKL
  let := hfin
  let := hsep
  let f : Spec (.of L) ⟶ Spec (.of K) := Spec.algebraMap K L
  let : Algebra.FormallyEtale K L := Algebra.FormallyEtale.of_isSeparable K L
  let : Algebra.FinitePresentation K L := Algebra.FinitePresentation.of_finiteType.mp
    (inferInstance : Algebra.FiniteType K L)
  let : Algebra.Etale K L := ⟨inferInstance, inferInstance⟩
  let : Etale f := (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
    (RingHom.etale_algebraMap.mpr inferInstance)
  have hζη : ζ ≫ f = η := by
    rw [show f = v ≫ U.hom from hp.symm, ← Category.assoc, hv]
    exact Over.w a
  let T := etaleTerminal (Spec (.of L))
  let V := (siteEtalePostcompose f).obj T
  let g : V ⟶ U := MorphismProperty.Over.homMk v (by
    change v ≫ U.hom = 𝟙 _ ≫ f
    simpa only [Category.id_comp] using hp)
  let E := (moduleEtaleRestriction R f).obj F
  let b' : M ⟶ E.obj.obj (op T) := b ≫ F.obj.map g.op
  let ψ := pointSmallEtale ζ
  let t : ψ.fiber.obj T := Over.homMk ζ (Category.comp_id ζ)
  let φ : (constantSheaf (Spec (.of L)).smallEtaleTopology
      (ModuleCat.{u + 1} R)).obj M ⟶ E :=
    ((constantSheafAdj (Spec (.of L)).smallEtaleTopology (ModuleCat.{u + 1} R)
      (etaleTerminalIsTerminal (Spec (.of L)))).homEquiv M E).symm b'
  let e : ψ.presheafFiber.obj E.obj ≅ M :=
    etaleRestrictionPresheafFiberIso f ζ F.obj ≪≫
      eqToIso (congrArg (fun q : Spec (.of Ω) ⟶ Spec (.of K) =>
        ((pointSmallEtale q).presheafFiber (A := ModuleCat.{u + 1} R)).obj F.obj) hζη)
  have hbg : b' ≫ ψ.toPresheafFiber T t E.obj ≫ e.hom = 𝟙 M := by
    change (b ≫ F.obj.map g.op) ≫
      (pointSmallEtale ζ).toPresheafFiber T t ((siteEtalePostcompose f).op ⋙ F.obj) ≫
        (etaleRestrictionPresheafFiberIso f ζ F.obj).hom ≫
          (eqToIso (congrArg (fun q : Spec (.of Ω) ⟶ Spec (.of K) =>
            ((pointSmallEtale q).presheafFiber (A := ModuleCat.{u + 1} R)).obj F.obj)
              hζη)).hom = 𝟙 M
    rw [toPresheafFiber_etaleRestrictionPresheafFiberIso_hom_assoc]
    have hpoint :
        Φ.fiber.map g
          (Over.homMk ζ (by
            change ζ ≫ (𝟙 _ ≫ f) = η
            simpa only [Category.id_comp] using hζη)) = a := by
      apply Over.OverMorphism.ext
      exact hv
    subst η
    let p : Φ.fiber.obj V := Over.homMk ζ (by
      change ζ ≫ (𝟙 _ ≫ f) = ζ ≫ f
      exact congrArg (fun q => ζ ≫ q) (Category.id_comp f))
    change (b ≫ F.obj.map g.op) ≫ Φ.toPresheafFiber V p F.obj ≫
      (Iso.refl M).hom = 𝟙 M
    have hw : F.obj.map g.op ≫ Φ.toPresheafFiber V p F.obj =
        Φ.toPresheafFiber U a F.obj :=
      (Φ.toPresheafFiber_w g p F.obj).trans
        (congrArg (fun q => Φ.toPresheafFiber U q F.obj) hpoint)
    let l : M ⟶ M := (b ≫ F.obj.map g.op) ≫ Φ.toPresheafFiber V p F.obj
    have hl : l = 𝟙 M :=
      (Category.assoc b (F.obj.map g.op) (Φ.toPresheafFiber V p F.obj)).trans
        ((congrArg (fun q : F.obj.obj (op U) ⟶ M => b ≫ q) hw).trans hb)
    change l ≫ 𝟙 M = 𝟙 M
    exact (Category.comp_id l).trans hl
  let : IsIso ((b' ≫ ψ.toPresheafFiber T t E.obj) ≫ e.hom) := by
    rw [Category.assoc, hbg]
    infer_instance
  let : IsIso (b' ≫ ψ.toPresheafFiber T t E.obj) :=
    IsIso.of_isIso_comp_right _ e.hom
  let c := (toSheafify (Spec (.of L)).smallEtaleTopology
      ((Functor.const (Spec (.of L)).Etaleᵒᵖ).obj M)).app (op T) ≫
    ψ.toPresheafFiber T t
      ((constantSheaf (Spec (.of L)).smallEtaleTopology (ModuleCat.{u + 1} R)).obj M).obj
  let : IsIso c := ψ.constantSheafGerm_isIso T t M
  have hc : c ≫ ψ.sheafFiber.map φ = b' ≫ ψ.toPresheafFiber T t E.obj :=
    ψ.constantSheafAdj_transpose_germ (etaleTerminalIsTerminal (Spec (.of L))) t M E b'
  let : IsIso (c ≫ ψ.sheafFiber.map φ) :=
    hc.symm ▸ (inferInstance : IsIso (b' ≫ ψ.toPresheafFiber T t E.obj))
  let : IsIso (ψ.sheafFiber.map φ) := IsIso.of_isIso_comp_left c _
  let : IsIso φ := isIso_of_field_moduleGeometricStalk R L ζ φ
  exact ⟨{
    index := PUnit.{u + 1}
    chart := fun _ => Scheme.Etale.mk f
    covers := fun x => ⟨PUnit.unit, (default : Spec (.of L)),
      show f (default : Spec (.of L)) = x from Subsingleton.elim _ _⟩
    value := fun _ => M
    finite_value := fun _ => inferInstance
    trivialization := fun _ => (moduleInverseImageEtaleIso R f).app F ≪≫ (asIso φ).symm }⟩

/-- Over a Noetherian coefficient ring, finite generation supplies the finite
presentation required by the original field recognition theorem. -/
theorem isFiniteTypeLocallyConstant_of_finite_geometricStalk
    [IsNoetherianRing R] (F : ModuleSheaf R (Spec (.of K)))
    [Module.Finite R
      (((pointSmallEtale η).sheafFiber (A := ModuleCat.{u + 1} R)).obj F)] :
    IsFiniteTypeLocallyConstant F := by
  let := Module.finitePresentation_of_finite R
    (((pointSmallEtale η).sheafFiber (A := ModuleCat.{u + 1} R)).obj F)
  exact isFiniteTypeLocallyConstant_of_finitePresentation_geometricStalk K η F

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules
