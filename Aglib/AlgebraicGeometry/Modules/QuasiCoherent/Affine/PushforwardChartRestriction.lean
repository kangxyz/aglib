/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.BaseChange.OpenImmersion.UnitSections
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.ChartRestrictionNaturality

/-! # Whole affine-chart pushforward restriction squares -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.Modules

/-- Additive packaging of the original affine restriction unit on sections. -/
def affineRestrictionUnitSectionAddHom {R S : CommRingCat.{u}} (φ : R ⟶ S)
    [IsOpenImmersion (Spec.map φ)] (M : (Spec R).Modules) :
    moduleSpecΓFunctor.obj M →+
      moduleSpecΓFunctor.obj (M.restrict (Spec.map φ)) :=
  ((pushforwardGlobalSectionsIso φ).hom.app (M.restrict (Spec.map φ))).hom.toAddMonoidHom.comp
    (moduleSpecΓFunctor.map ((restrictAdjunction (Spec.map φ)).unit.app M)).hom.toAddMonoidHom

/-- Coordinates of an original local pushforward comparison, without changing
its source, target, or affine section maps. -/
def PushforwardChartCoordinates
    {X : Scheme.{u}} (U : X.affineOpens) {S : CommRingCat.{u}} (p : Γ(X, U) ⟶ S)
    (M : X.Modules) (Q : (Spec S).Modules)
    (e : (pushforward (Spec.map p)).obj Q ⟶ M.restrict U.property.fromSpec)
    (s : moduleSpecΓFunctor.obj Q →+ Γ(M, U)) : Prop :=
  ∀ x, (affineChartΓIso U M).hom (moduleSpecΓFunctor.map e x) =
    s ((pushforwardGlobalSectionsIso p).hom.app Q x)

/-- Compatibility is expressed using the original source restriction unit and
actual coefficient restriction map. -/
def PushforwardChartCoordinateCompatibility
    {X : Scheme.{u}} (U V : X.affineOpens) (h : V.val ≤ U.val)
    {S T : CommRingCat.{u}} (ψ : S ⟶ T) [IsOpenImmersion (Spec.map ψ)]
    (M : X.Modules) (Q : (Spec S).Modules) (P : (Spec T).Modules)
    (d : Q.restrict (Spec.map ψ) ⟶ P)
    (sU : moduleSpecΓFunctor.obj Q →+ Γ(M, U))
    (sV : moduleSpecΓFunctor.obj P →+ Γ(M, V)) : Prop :=
  ∀ x, sV (moduleSpecΓFunctor.map d (affineRestrictionUnitSection ψ Q x)) =
    M.presheaf.map (homOfLE h).op (sU x)

/-- The original whole pushforward restriction square, with shared native parameters. -/
def PushforwardChartRestrictionSquare
    {X : Scheme.{u}} (U V : X.affineOpens) (h : V.val ≤ U.val)
    {S T : CommRingCat.{u}} (pU : Γ(X, U) ⟶ S) (pV : Γ(X, V) ⟶ T) (ψ : S ⟶ T)
    [IsOpenImmersion (Spec.map (X.presheaf.map (homOfLE h).op))]
    [IsOpenImmersion (Spec.map ψ)]
    (H : IsPullback (Spec.map ψ) (Spec.map pV) (Spec.map pU)
      (Spec.map (X.presheaf.map (homOfLE h).op)))
    (M : X.Modules) (Q : (Spec S).Modules) (P : (Spec T).Modules)
    (d : Q.restrict (Spec.map ψ) ⟶ P)
    (eU : (pushforward (Spec.map pU)).obj Q ⟶ M.restrict U.property.fromSpec)
    (eV : (pushforward (Spec.map pV)).obj P ⟶ M.restrict V.property.fromSpec) : Prop :=
    (restrictFunctor (Spec.map (X.presheaf.map (homOfLE h).op))).map eU ≫
      ((restrictFunctorComp (Spec.map (X.presheaf.map (homOfLE h).op))
        U.property.fromSpec).symm.app M ≪≫
        (restrictFunctorCongr (U.property.map_fromSpec V.property (homOfLE h).op)).app M).hom =
    (cartesianOpenBaseChange (Spec.map ψ) (Spec.map pV) (Spec.map pU)
      (Spec.map (X.presheaf.map (homOfLE h).op)) H).hom.app Q ≫
      (pushforward (Spec.map pV)).map d ≫ eV

/-- Original compatible section coordinates imply the whole native
pushforward comparison square on nested affine charts. -/
theorem pushforwardChart_restriction_of_coordinates
    {X : Scheme.{u}} (U V : X.affineOpens) (h : V.val ≤ U.val)
    {S T : CommRingCat.{u}} (pU : Γ(X, U) ⟶ S) (pV : Γ(X, V) ⟶ T) (ψ : S ⟶ T)
    [IsOpenImmersion (Spec.map (X.presheaf.map (homOfLE h).op))]
    [IsOpenImmersion (Spec.map ψ)]
    (H : IsPullback (Spec.map ψ) (Spec.map pV) (Spec.map pU)
      (Spec.map (X.presheaf.map (homOfLE h).op)))
    (M : X.Modules) (Q : (Spec S).Modules) (P : (Spec T).Modules)
    [((pushforward (Spec.map pU)).obj Q).IsQuasicoherent]
    (d : Q.restrict (Spec.map ψ) ⟶ P)
    (eU : (pushforward (Spec.map pU)).obj Q ⟶ M.restrict U.property.fromSpec)
    (eV : (pushforward (Spec.map pV)).obj P ⟶ M.restrict V.property.fromSpec)
    (sU : moduleSpecΓFunctor.obj Q →+ Γ(M, U))
    (sV : moduleSpecΓFunctor.obj P →+ Γ(M, V))
    (hU : PushforwardChartCoordinates U pU M Q eU sU)
    (hV : PushforwardChartCoordinates V pV M P eV sV)
    (hc : PushforwardChartCoordinateCompatibility U V h ψ M Q P d sU sV) :
    PushforwardChartRestrictionSquare U V h pU pV ψ H M Q P d eU eV := by
  unfold PushforwardChartRestrictionSquare
  apply affineChart_restriction_square_of_unit U V h M
    ((pushforward (Spec.map pU)).obj Q) eU
  intro m
  let x := (pushforwardGlobalSectionsIso pU).hom.app Q m
  have hb := cartesianOpenBaseChange_pushforwardRestrictionUnitSection
    pU pV (X.presheaf.map (homOfLE h).op) ψ H Q P d x
  simp only [x, ← Iso.app_hom, ← Iso.app_inv, Iso.hom_inv_id_apply] at hb
  have hv := hV (pushforwardRestrictionUnitSection pV ψ Q P d x)
  have hu := hU m
  simp only [Functor.map_comp, ConcreteCategory.comp_apply]
  erw [hb, hv, pushforwardRestrictionUnitSection_sections, hc x, hu]

end AlgebraicGeometry.Scheme.Modules
