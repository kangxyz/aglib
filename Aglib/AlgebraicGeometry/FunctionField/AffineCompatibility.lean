/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.FunctionField.AffineCharts
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
Native extraction from the R5 Aglib source
`AlgebraicGeometry.FunctionField.AffineCharts`.
R5 revision: `f8a3314ddecffcada2ec721d26d56a937bed9690`.
Source SHA-256:
`a84ebc8e511a49c3375dc3d79586117de706a75743f9c4836036da15b5aa68f7`.
Only the five canonical generic/affine triangle and coordinate-naturality helpers from
  source165–273. Existing Scheme.functionFieldMap and FunctionField.affineFieldEquiv objects are
  reused; there is no replacement field comparison.
Conditional blowup families remain explicit inputs.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry
universe u

namespace AlgebraicGeometry.Scheme.FunctionField.AffineCompatibility
section Generic
variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
  (m : X ⟶ Y) [IsDominant m]
  (A : CommRingCat.{u}) [IsDomain A] (jA : Spec A ⟶ X) [IsOpenImmersion jA]

/-- Generic-stalk naturality for an arbitrary dominant map. -/
theorem generic_triangle :
    X.fromSpecStalk (genericPoint X) ≫ m =
      Spec.map (CommRingCat.ofHom (Scheme.functionFieldMap m)) ≫
        Y.fromSpecStalk (genericPoint Y) :=
  Scheme.fromSpecStalk_genericPoint_naturality m

omit m [IsDominant m] in
/-- The affine-chart field identification has its exact generic-point triangle. -/
theorem affine_generic_triangle :
    Spec.map (CommRingCat.ofHom (Scheme.FunctionField.affineFieldEquiv A jA).toRingHom) ≫
      X.fromSpecStalk (genericPoint X) =
    Spec.map (CommRingCat.ofHom (algebraMap A (FractionRing A))) ≫ jA := by
  change Spec.map (CommRingCat.ofHom
    ((FractionRing.algEquiv A (Spec A).functionField).symm.toRingHom.comp
      (Scheme.FunctionField.fieldEquiv jA).toRingHom)) ≫ _ = _
  change Spec.map (CommRingCat.ofHom (Scheme.FunctionField.fieldEquiv jA).toRingHom ≫
    CommRingCat.ofHom (FractionRing.algEquiv A (Spec A).functionField).symm.toRingHom) ≫ _ = _
  rw [Spec.map_comp, Category.assoc, ← Scheme.FunctionField.fieldEquiv_generic_triangle jA,
    ← Category.assoc, Spec.fromSpecStalk_eq', ← Spec.map_comp]
  congr 2
  apply CommRingCat.hom_ext
  ext r
  exact (FractionRing.algEquiv A (Spec A).functionField).symm.commutes r


end Generic

section Coordinates
variable (A B : CommRingCat.{u}) [IsDomain A] [IsDomain B]

/-- Actual affine generic-stalk pullback respects the original ring elements. -/
theorem fieldMap_spec_constants (g : B ⟶ A) [IsDominant (Spec.map g)] :
    (Scheme.functionFieldMap (Spec.map g)).comp
      (algebraMap B (Spec B).functionField) =
    (algebraMap A (Spec A).functionField).comp g.hom := by
  apply CommRingCat.hom_ext_iff.mp
  apply Spec.map_injective
  change Spec.map (CommRingCat.ofHom (algebraMap B (Spec B).functionField) ≫
    CommRingCat.ofHom (Scheme.functionFieldMap (Spec.map g))) =
      Spec.map (g ≫ CommRingCat.ofHom (algebraMap A (Spec A).functionField))
  rw [Spec.map_comp, Spec.map_comp]
  change _ ≫ Spec.map (StructureSheaf.toStalk B (genericPoint (Spec B))) =
    Spec.map (StructureSheaf.toStalk A (genericPoint (Spec A))) ≫ _
  rw [← Spec.fromSpecStalk_eq', ← Spec.fromSpecStalk_eq']
  exact (generic_triangle (Spec.map g)).symm

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
  (m : X ⟶ Y) [IsDominant m]
  (jA : Spec A ⟶ X) [IsOpenImmersion jA]
  (jB : Spec B ⟶ Y) [IsOpenImmersion jB]
  (g : B ⟶ A) (h : jA ≫ m = Spec.map g ≫ jB)

include h

/-- A commuting affine-chart triangle inherits generic-point dominance. -/
theorem spec_dominant_of_chart_triangle : IsDominant (Spec.map g) := by
  have hg : Spec.map g (genericPoint (Spec A)) = genericPoint (Spec B) := by
    apply (Scheme.Hom.isOpenEmbedding jB).injective
    rw [_root_.AlgebraicGeometry.genericPoint_eq_of_isOpenImmersion jB]
    have he := congrArg (fun t : Spec A ⟶ Y => t (genericPoint (Spec A))) h
    simpa only [Scheme.Hom.comp_apply,
      _root_.AlgebraicGeometry.genericPoint_eq_of_isOpenImmersion jA,
      Scheme.map_genericPoint_of_isDominant X m] using he.symm
  constructor
  rw [denseRange_iff_closure_range]
  apply Set.eq_univ_of_univ_subset
  rw [← genericPoint_closure (Spec B), ← hg]
  exact closure_mono (Set.singleton_subset_iff.mpr ⟨genericPoint (Spec A), rfl⟩)

/-- Naturality of the canonical chart comparison on every ring coordinate.
The proof uses only the actual scheme triangle and the generic-stalk maps. -/
theorem affineFieldEquiv_map_coordinate (b : B) :
    Scheme.FunctionField.affineFieldEquiv A jA
      (Scheme.functionFieldMap m
        ((Scheme.FunctionField.affineFieldEquiv B jB).symm (algebraMap B (FractionRing B) b))) =
      algebraMap A (FractionRing A) (g b) := by
  let : IsDominant jA := Scheme.isDominant_of_isOpenImmersion jA
  let : IsDominant jB := Scheme.isDominant_of_isOpenImmersion jB
  let : IsDominant (Spec.map g) := spec_dominant_of_chart_triangle A B m jA jB g h
  have hcomp : (Scheme.functionFieldMap jA).comp
      (Scheme.functionFieldMap m) =
    (Scheme.functionFieldMap (Spec.map g)).comp
      (Scheme.functionFieldMap jB) := by
    rw [← Scheme.functionFieldMap_comp,
      ← Scheme.functionFieldMap_comp]
    congr 1
  have hb : Scheme.functionFieldMap jB
      ((Scheme.FunctionField.affineFieldEquiv B jB).symm (algebraMap B (FractionRing B) b)) =
      algebraMap B (Spec B).functionField b := by
    apply (FractionRing.algEquiv B (Spec B).functionField).symm.injective
    change Scheme.FunctionField.affineFieldEquiv B jB ((Scheme.FunctionField.affineFieldEquiv B
      jB).symm _) = _
    rw [RingEquiv.apply_symm_apply, AlgEquiv.commutes]
  change (FractionRing.algEquiv A (Spec A).functionField).symm
    ((Scheme.functionFieldMap jA)
      (Scheme.functionFieldMap m _)) = _
  have he := DFunLike.congr_fun hcomp
    ((Scheme.FunctionField.affineFieldEquiv B jB).symm (algebraMap B (FractionRing B) b))
  change (Scheme.functionFieldMap jA)
    (Scheme.functionFieldMap m _) = _ at he
  rw [he, RingHom.comp_apply, hb]
  have hc := DFunLike.congr_fun (fieldMap_spec_constants A B g) b
  change Scheme.functionFieldMap (Spec.map g)
    (algebraMap B (Spec B).functionField b) = _ at hc
  rw [hc, RingHom.comp_apply, AlgEquiv.commutes]


end Coordinates
end AlgebraicGeometry.Scheme.FunctionField.AffineCompatibility
