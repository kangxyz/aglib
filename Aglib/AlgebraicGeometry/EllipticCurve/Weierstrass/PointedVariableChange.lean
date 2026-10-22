/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EllipticCurve.Weierstrass.PointedIsomorphism
public import Aglib.AlgebraicGeometry.EllipticCurve.Weierstrass.ProjectiveVariableChange
public import Aglib.AlgebraicGeometry.EllipticCurve.Weierstrass.Integrality
public import Aglib.AlgebraicGeometry.FunctionField.AffineCharts

/-!
# Recovering the original pointed isomorphism as a native variable change

The native homogeneous change restricts to its existing native affine map.
The existing affine classification now retains both coordinate equations
for its chosen change. Applied to the inverse restriction of the original
pointed isomorphism, these equations recover that same projective Over-iso.
No characteristic, nonsingularity, group or classification premise is added.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open WeierstrassCurve.Projective

universe u

namespace WeierstrassCurve.VariableChange

variable {k : Type u} [Field k]

private theorem projective_z_powers (W : WeierstrassCurve k) (C : VariableChange k) :
    Submonoid.powers (coordinate W 2) ≤
      (Submonoid.powers (coordinate (C • W) 2)).comap (projectiveGraded W C) :=
  Translation.native_powers_le (projectiveGraded W C) _ _ (projectiveHomogeneous_z W C)

/-- The degree-zero localization map of the actual native homogeneous change. -/
private def zChartMap (W : WeierstrassCurve k) (C : VariableChange k) :
    chartRing W 2 →+* chartRing (C • W) 2 :=
  HomogeneousLocalization.map (projectiveGraded W C) (projective_z_powers W C)

private theorem zChartMap_spec (W : WeierstrassCurve k) (C : VariableChange k) :
    chart (C • W) 2 ≫ (projectiveIso W C).hom =
      Spec.map (CommRingCat.ofHom (zChartMap W C)) ≫ chart W 2 :=
  Translation.nativeAwayMap_spec (projectiveGraded W C) (projective_irrelevant W C)
    _ (coordinate_mem W 2) _ (coordinate_mem (C • W) 2) (projectiveHomogeneous_z W C)

private theorem zChartMap_mk (W : WeierstrassCurve k) (C : VariableChange k) (n : ℕ)
    (a : homogeneousCoordinateRing W) (ha : a ∈ grading W (n • 1)) :
    zChartMap W C
      (HomogeneousLocalization.Away.mk (grading W) (coordinate_mem W 2) n a ha) =
      HomogeneousLocalization.Away.mk (grading (C • W)) (coordinate_mem (C • W) 2)
        n (projectiveGraded W C a) ((projectiveGraded W C).map_mem ha) :=
  Translation.nativeAwayMap_mk (projectiveGraded W C) _ (coordinate_mem W 2)
    _ (coordinate_mem (C • W) 2) (projectiveHomogeneous_z W C) n a ha

private theorem dehomogenize_projective (W : WeierstrassCurve k) (C : VariableChange k)
    (a : homogeneousCoordinateRing W) :
    dehomogenize (C • W) (projectiveHomogeneous W C a) =
      affineMap W C (dehomogenize W a) := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  have he : (dehomogenize (C • W)).comp
      ((projectiveHomogeneous W C).toRingHom.comp (Ideal.Quotient.mk _)) =
      (affineMap W C).toRingHom.comp ((dehomogenize W).comp (Ideal.Quotient.mk _)) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      change dehomogenize (C • W) (projectiveHomogeneous W C (algebraMap k _ a)) =
        affineMap W C (dehomogenize W (algebraMap k _ a))
      simp
    · intro i
      change dehomogenize (C • W) (projectiveHomogeneous W C (coordinate W i)) =
        affineMap W C (dehomogenize W (coordinate W i))
      fin_cases i <;> simp [changeX, changeY, VariableChange.map]
  exact DFunLike.congr_fun he p

private theorem zChartMap_dehomogenize (W : WeierstrassCurve k) (C : VariableChange k) :
    (fromProjectiveChart (C • W)).comp (zChartMap W C) =
      (affineMap W C).toRingHom.comp (fromProjectiveChart W) := by
  apply RingHom.ext
  intro a
  obtain ⟨n, b, hb, rfl⟩ := HomogeneousLocalization.Away.mk_surjective
    (grading W) (coordinate_mem W 2) a
  simp only [RingHom.comp_apply, zChartMap_mk, fromProjectiveChart_mk]
  exact dehomogenize_projective W C b

/-- On the actual affine charts, the canonical projective change is the
existing native affine coordinate substitution for that same change. -/
@[reassoc] theorem projectiveIso_affine (W : WeierstrassCurve k) (C : VariableChange k) :
    affineChart (C • W) ≫ (projectiveIso W C).hom =
      Spec.map (CommRingCat.ofHom (affineMap W C :
        affineRing W →+* affineRing (C • W))) ≫ affineChart W := by
  change (Spec.map (CommRingCat.ofHom (fromProjectiveChart (C • W))) ≫
    chart (C • W) 2) ≫ (projectiveIso W C).hom = _
  rw [Category.assoc, zChartMap_spec, ← Category.assoc, ← Spec.map_comp]
  rw [affineChart, ← Category.assoc, ← Spec.map_comp]
  congr 1
  exact congrArg (fun g : chartRing W 2 →+* affineRing (C • W) =>
    Spec.map (CommRingCat.ofHom g)) (zChartMap_dehomogenize W C)

end WeierstrassCurve.VariableChange

namespace WeierstrassCurve.Projective

open AlgebraicGeometry.Scheme.OverField
attribute [local instance] Over.cartesianMonoidalCategory

variable {k : Type u} [Field k]

/-- The literal coefficient cast followed by the canonical native projective
change, with the source and target of the original supplied isomorphism. -/
def variableChangeOverIso (W V : WeierstrassCurve k) (C : VariableChange k)
    (hC : C • W = V) : curveOver V ≅ curveOver W :=
  eqToIso (congrArg curveOver hC.symm) ≪≫ VariableChange.projectiveOverIso W C

/-- The recovered map retains the original structural morphisms. -/
@[reassoc] theorem variableChangeOverIso_over (W V : WeierstrassCurve k)
    (C : VariableChange k) (hC : C • W = V) :
    (variableChangeOverIso W V C hC).hom.left ≫ structureMap W = structureMap V :=
  (variableChangeOverIso W V C hC).hom.w

/-- The recovered native map preserves the literal infinity section. -/
@[reassoc] theorem variableChangeOverIso_infinity (W V : WeierstrassCurve k)
    (C : VariableChange k) (hC : C • W = V) :
    infinitySection V ≫ (variableChangeOverIso W V C hC).hom.left = infinitySection W := by
  subst V
  simp only [variableChangeOverIso, eqToIso_refl, Iso.refl_trans]
  change infinitySection (C • W) ≫ (VariableChange.projectiveIso W C).hom = infinitySection W
  exact VariableChange.projectiveIso_infinity W C

private theorem exists_affine_iso_of_pointed (W V : WeierstrassCurve k)
    (e : curveOver W ≅ curveOver V) (he : originOver W ≫ e.hom = originOver V) :
    ∃ F : (affineOver W).left ≅ (affineOver V).left,
      F.hom ≫ (affineOver V).hom = (affineOver W).hom ∧
      F.inv ≫ affineChart W = affineChart V ≫ e.inv.left := by
  refine ⟨pointedAffineIso (W := W) (V := V) e he, ?_, ?_⟩
  · exact pointedAffineIso_over (W := W) (V := V) e he
  · change pointedAffineInverse (W := W) (V := V) e he ≫ affineChart W =
      affineChart V ≫ e.inv.left
    exact pointedAffineInverse_fac (W := W) (V := V) e he

/-- Keep the actual restriction abstract before applying the fully faithful
spectrum functor to its coordinate rings. -/
private theorem exists_actual_affine_iso (W V : WeierstrassCurve k)
    (E : curveOver V ≅ curveOver W)
    (hE : infinitySection V ≫ E.hom.left = infinitySection W) :
    ∃ F : (affineOver W).left ≅ (affineOver V).left,
      F.hom ≫ (affineOver V).hom = (affineOver W).hom ∧
      F.inv ≫ affineChart W = affineChart V ≫ E.hom.left := by
  have hEo : originOver V ≫ E.hom = originOver W := by
    apply Over.OverMorphism.ext
    exact hE
  have hInv : originOver W ≫ E.inv = originOver V :=
    pointedIso_inv (W := V) (V := W) E hEo
  exact exists_affine_iso_of_pointed W V E.symm hInv

/-- The coordinate-ring equivalence retains the inverse restriction's
original scheme-map triangle. -/
private theorem exists_actual_affine_pullback (W V : WeierstrassCurve k)
    (E : curveOver V ≅ curveOver W)
    (hE : infinitySection V ≫ E.hom.left = infinitySection W) :
    ∃ f : affineRing W ≃ₐ[k] affineRing V,
      Spec.map (CommRingCat.ofHom (f : affineRing W →+* affineRing V)) ≫ affineChart W =
        affineChart V ≫ E.hom.left := by
  obtain ⟨F, hOver, hF⟩ := exists_actual_affine_iso W V E hE
  change F.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap k (affineRing V))) =
    Spec.map (CommRingCat.ofHom (algebraMap k (affineRing W))) at hOver
  refine ⟨AlgebraicGeometry.Spec.algEquivOfIso k F hOver, ?_⟩
  change Spec.map (CommRingCat.ofHom
    (AlgebraicGeometry.Spec.algEquivOfIso k F hOver).toRingHom) ≫ affineChart W = _
  rw [AlgebraicGeometry.Spec.map_algEquivOfIso]
  exact hF

private theorem exists_variableChange_eq_of_affine_pullback (W V : WeierstrassCurve k)
    (E : curveOver V ≅ curveOver W) (f : affineRing W ≃ₐ[k] affineRing V)
    (hOriginal : Spec.map (CommRingCat.ofHom (f : affineRing W →+* affineRing V)) ≫
      affineChart W = affineChart V ≫ E.hom.left) :
    ∃ (C : VariableChange k) (hC : C • W = V), E = variableChangeOverIso W V C hC := by
  obtain ⟨C, hC, hx, hy⟩ := affineAlgEquiv_exists_variableChange_with_coordinates W V f
  refine ⟨C, hC, ?_⟩
  subst V
  have hF : f.toAlgHom = VariableChange.affineMap W C := by
    apply WeierstrassCurve.affine_ext W
    · exact hx.trans (VariableChange.affineMap_x W C).symm
    · exact hy.trans (VariableChange.affineMap_y W C).symm
  have hRing : (f : affineRing W →+* affineRing (C • W)) =
      (VariableChange.affineMap W C : affineRing W →+* affineRing (C • W)) :=
    congrArg AlgHom.toRingHom hF
  have hChart : affineChart (C • W) ≫ E.hom.left =
      affineChart (C • W) ≫ (VariableChange.projectiveOverIso W C).hom.left := by
    rw [← hOriginal, hRing]
    exact (VariableChange.projectiveIso_affine W C).symm
  have hMaps : E.hom.left = (VariableChange.projectiveOverIso W C).hom.left := by
    let : IsIntegral (scheme (C • W)) := scheme_isIntegral_of_isDomain (C • W)
    let : IsIntegral (scheme W) := scheme_isIntegral_of_isDomain W
    let : IsReduced (curveOver (C • W)).left :=
      inferInstanceAs (IsReduced (scheme (C • W)))
    let : IsDominant (affineChart (C • W)) :=
      Scheme.isDominant_of_isOpenImmersion (affineChart (C • W))
    have hBase : E.hom.left ≫ structureMap W = structureMap (C • W) := E.hom.w
    have hCanonical : (VariableChange.projectiveOverIso W C).hom.left ≫ structureMap W =
        structureMap (C • W) := (VariableChange.projectiveOverIso W C).hom.w
    exact ext_of_isDominant_of_isSeparated (structureMap W)
      (hBase.trans hCanonical.symm) (affineChart (C • W)) hChart
  have hIso : E = VariableChange.projectiveOverIso W C :=
    Iso.ext (Over.OverMorphism.ext hMaps)
  simpa only [variableChangeOverIso, eqToIso_refl, Iso.refl_trans] using hIso

/-- Every actual pointed projective Over-isomorphism is the canonical map
of an actual native admissible change, after the proved coefficient cast.
The conclusion identifies the supplied isomorphism itself. -/
theorem pointedIso_exists_variableChange_eq (W V : WeierstrassCurve k)
    (E : curveOver V ≅ curveOver W)
    (hE : infinitySection V ≫ E.hom.left = infinitySection W) :
    ∃ (C : VariableChange k) (hC : C • W = V), E = variableChangeOverIso W V C hC := by
  obtain ⟨f, hf⟩ := exists_actual_affine_pullback W V E hE
  exact exists_variableChange_eq_of_affine_pullback W V E f hf

end WeierstrassCurve.Projective
