/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Invertible.ZeroLocus.Regular
public import Aglib.AlgebraicGeometry.Modules.Invertible.Nonzero
public import Mathlib.AlgebraicGeometry.Geometrically.Integral

/-!
# Fibrewise regularity of line-bundle maps on integral fibres

Let `f : X ⟶ S` be a morphism, `L` a line bundle on `X` and `φ : L ⟶ O_X` a map, that is, a
section of `L^∨` in the sense of Kleiman, *The Picard scheme*, arXiv:math/0504020v1, 3.1,
p. 22 (Stacks Project, Tag 01WY, Definition 31.15.6). On an integral scheme a nonzero such map
is injective (`nonzero_lineBundleMap_mono`), so the section is regular. In family form:

* `isIntegral_pullback_of_geometricallyIntegral`: the fibres of a geometrically integral
  morphism over field-valued points are integral;
* `fibreLineBundleMap_ne_zero_iff`: the fibre map `fibreLineBundleMap` of `GeometricFibre` is
  nonzero exactly when the pulled-back map is;
* `geometricFibreRegular_of_isIntegral_of_fibre_ne_zero`: if every algebraically closed
  geometric fibre `X_t` is integral and the pulled-back map is nonzero on it, then `φ` is
  `GeometricFibreRegular`.

For a section `σ : O ⟶ M` of a line bundle, `sectionContraction M σ : M^∨ ⟶ O` is the dual map
`M^∨ ≅ M^∨ ⊗ O → M^∨ ⊗ M → O`, whose image is the ideal of the zero scheme of `σ` (Stacks
Project, Tag 02OQ, Definition 31.15.8). It is nonzero after any pullback along which `σ` is
nonzero (`pullback_map_sectionContraction_ne_zero`).

This is the regularity step of the inverse map in the proof of Kleiman, Thm 3.13, p. 26:
"`σ_t ≠ 0`. But `X_t` is integral since the geometric fibers of `X/S` are integral by
hypothesis. Hence `σ_t` is regular". The divisor statements built on it are in
`EffectiveCartierDivisor/Relative/ZeroScheme`. The base `S` is arbitrary.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom
open AlgebraicGeometry.Scheme.Modules.Invertible

namespace AlgebraicGeometry.Scheme.Modules.Invertible

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- The fibre of a geometrically integral morphism over any field-valued point is integral. -/
theorem isIntegral_pullback_of_geometricallyIntegral [GeometricallyIntegral f] {K : Type u}
    [Field K] (t : Spec (.of K) ⟶ S) : IsIntegral (Limits.pullback f t) :=
  GeometricallyIntegral.geometrically_isIntegral t _ _ (IsPullback.of_hasPullback f t)

variable (L : LineBundle X)
  (φ : (show X.Modules from L.val) ⟶ (show X.Modules from SheafOfModules.unit X.ringCatSheaf))

/-- The fibre map `fibreLineBundleMap` is nonzero exactly when the pulled back map is nonzero:
they differ by the unit comparison isomorphism. -/
theorem fibreLineBundleMap_ne_zero_iff (K : Type u) [Field K] (t : Spec (.of K) ⟶ S) :
    fibreLineBundleMap f L φ K t ≠ 0 ↔
      (Scheme.Modules.pullback (Limits.pullback.fst f t)).map φ ≠ 0 := by
  unfold fibreLineBundleMap
  constructor
  · intro h h0
    exact h (by rw [h0, zero_comp])
  · intro h h0
    exact h ((cancel_mono (pullbackUnitIso (Limits.pullback.fst f t)).hom).mp
      (h0.trans zero_comp.symm))

/-- If every algebraically closed geometric fibre is integral and the map is nonzero on it, then
the map is monic on every geometric fibre (Kleiman, Thm 3.13, proof, p. 26). -/
theorem geometricFibreRegular_of_isIntegral_of_fibre_ne_zero
    (hint : ∀ (K : Type u) [Field K] [IsAlgClosed K] (t : Spec (.of K) ⟶ S),
      IsIntegral (Limits.pullback f t))
    (hφ : ∀ (K : Type u) [Field K] [IsAlgClosed K] (t : Spec (.of K) ⟶ S),
      (Scheme.Modules.pullback (Limits.pullback.fst f t)).map φ ≠ 0) :
    GeometricFibreRegular f L φ := by
  intro K _ _ t
  have := hint K t
  exact nonzero_lineBundleMap_mono (pullbackLineBundle (Limits.pullback.fst f t) L)
    (fibreLineBundleMap f L φ K t) ((fibreLineBundleMap_ne_zero_iff f L φ K t).mpr (hφ K t))

/-- The map `M^∨ ⟶ O` dual to a section `σ : O ⟶ M` of a line bundle:
`M^∨ ≅ M^∨ ⊗ O → M^∨ ⊗ M → O`, by the unit, the braiding, `𝟙 ⊗ σ` and dual evaluation. Its
image is the ideal of the zero scheme of `σ` (Kleiman, 3.1, p. 22; Stacks Project, Tag 02OQ). -/
def sectionContraction {Y : Scheme.{u}} (M : LineBundle Y)
    (σ : (show Y.Modules from SheafOfModules.unit Y.ringCatSheaf) ⟶ (show Y.Modules from M.val)) :
    (show Y.Modules from (dualLineBundle Y M).val) ⟶
      (show Y.Modules from SheafOfModules.unit Y.ringCatSheaf) :=
  (tensorSheafLeftUnit Y (dualLineBundle Y M).val).inv ≫
    (tensorSheafBraiding Y (SheafOfModules.unit Y.ringCatSheaf) (dualLineBundle Y M).val).hom ≫
      tensorSheafMap Y (𝟙 (dualLineBundle Y M).val) σ ≫ (dualEvaluationIso Y M).hom

/-- The dual map of a section is nonzero after any pullback along which the section is
nonzero. -/
theorem pullback_map_sectionContraction_ne_zero {Y Z : Scheme.{u}} (g : Z ⟶ Y) (M : LineBundle Y)
    (σ : (show Y.Modules from SheafOfModules.unit Y.ringCatSheaf) ⟶ (show Y.Modules from M.val))
    (hσ : (Scheme.Modules.pullback g).map σ ≠ 0) :
    (Scheme.Modules.pullback g).map (sectionContraction M σ) ≠ 0 := by
  intro h
  apply hσ
  have hC : tensorSheafMap Y (𝟙 (dualLineBundle Y M).val) σ =
      (tensorSheafBraiding Y (SheafOfModules.unit Y.ringCatSheaf) (dualLineBundle Y M).val).inv ≫
        (tensorSheafLeftUnit Y (dualLineBundle Y M).val).hom ≫ sectionContraction M σ ≫
          (dualEvaluationIso Y M).inv := by
    simp only [sectionContraction, Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc,
      Iso.hom_inv_id, Category.comp_id]
  have hzero : (Scheme.Modules.pullback g).map
      (tensorSheafMap Y (𝟙 (dualLineBundle Y M).val) σ) = 0 := by
    rw [hC, Functor.map_comp, Functor.map_comp, Functor.map_comp, h, zero_comp, comp_zero,
      comp_zero]
  have he := pullbackTensorMap_naturality g (𝟙 (dualLineBundle Y M).val) σ
  have hid : (Scheme.Modules.pullback g).map (𝟙 (dualLineBundle Y M).val) =
      𝟙 ((Scheme.Modules.pullback g).obj (dualLineBundle Y M).val) :=
    (Scheme.Modules.pullback g).map_id _
  rw [hid] at he
  have := Scheme.Modules.Invertible.PullbackTensor.Local.pullbackTensorMap_isIso g
    (dualLineBundle Y M).val (SheafOfModules.unit Y.ringCatSheaf) (dualLineBundle Y M).property
  have ht : tensorSheafMap Z (𝟙 ((Scheme.Modules.pullback g).obj (dualLineBundle Y M).val))
      ((Scheme.Modules.pullback g).map σ) = 0 := by
    apply (cancel_epi (pullbackTensorMap g (dualLineBundle Y M).val
      (SheafOfModules.unit Y.ringCatSheaf))).mp
    simpa only [hzero, zero_comp, comp_zero] using he.symm
  exact tensorSheafMap_lineBundle_detects_zero Z (pullbackLineBundle g (dualLineBundle Y M)) _ ht

end AlgebraicGeometry.Scheme.Modules.Invertible
