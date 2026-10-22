/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.Proper.Chow.FiniteProductMap
public import Aglib.AlgebraicGeometry.Morphisms.Proper.GraphClosure.TargetChart

/-!
# The immersive target map of a separated graph product

Closed embeddings of the original graph domains into target opens identify
the actual target-chart preimages. On those charts the target map is both
proper and immersive, hence closed. Target locality then gives an immersion
into the original finite target product. The original source need not be proper.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Chow.GraphProduct

variable {X S : Scheme.{u}} (f : X ⟶ S) {n : ℕ} (P : Fin n → Over S)
  (U : Fin n → X.Opens) (h : ∀ i, (U i).toScheme ⟶ (P i).left)
  (w : ∀ i, (U i).ι ≫ f = h i ≫ (P i).hom)
  [IsSeparated f] [∀ i, IsProper (P i).hom] [∀ i, QuasiCompact (U i).ι]
  (W : ∀ i, (P i).left.Opens) (j : ∀ i, (U i).toScheme ⟶ (W i).toScheme)
  (hj : ∀ i, j i ≫ (W i).ι = h i) [∀ i, IsClosedImmersion (j i)]

include hj in
/-- The inverse image of an original target coordinate chart is exactly the
inverse image of its original graph domain. -/
theorem toTarget_preimage_targetChart (i : Fin n) :
    toTarget f P U h w ⁻¹ᵁ ((finiteProductOverπ P i).left ⁻¹ᵁ W i) =
      toSource f P U h w ⁻¹ᵁ U i := by
  rw [← Hom.comp_preimage, toTarget_π, Hom.comp_preimage,
    GraphClosure.targetPreimage_eq_sourcePreimage f (P i).hom (U i) (h i) (w i)
      (W i) (j i) (hj i), ← Hom.comp_preimage, toComponent_toSource]

include hj in
/-- The original target map is closed on each of the specified target charts. -/
theorem toTarget_targetChart_isClosedImmersion (i : Fin n) :
    IsClosedImmersion
      (toTarget f P U h w ∣_ ((finiteProductOverπ P i).left ⁻¹ᵁ W i)) := by
  have (k : Fin n) : IsImmersion (h k) := by
    rw [← hj k]
    infer_instance
  let V := (finiteProductOverπ P i).left ⁻¹ᵁ W i
  let e := (model f P U h w).isoOfEq
    (toTarget_preimage_targetChart f P U h w W j hj i)
  have hcoord :
      (toTarget f P U h w ∣_ V) ≫ ((finiteProductOverπ P i).left ∣_ W i) =
        e.hom ≫ (toSource f P U h w ∣_ U i) ≫ j i := by
    apply (cancel_mono (W i).ι).mp
    simp only [Category.assoc, morphismRestrict_ι, hj]
    rw [← toTarget_π_restrict, Scheme.isoOfEq_hom_ι_assoc]
    exact morphismRestrict_ι_assoc (toTarget f P U h w) V (finiteProductOverπ P i).left
  have : IsProper (targetOver P).hom := isProper_finiteProductOver P
  have : IsProper ((finiteProductOverπ P i).left) := by
    have : IsProper ((finiteProductOverπ P i).left ≫ (P i).hom) := by
      rw [(finiteProductOverπ P i).w]
      exact isProper_finiteProductOver P
    exact IsProper.of_comp _ (P i).hom
  have : IsProper
      ((toTarget f P U h w ∣_ V) ≫ ((finiteProductOverπ P i).left ∣_ W i)) := by
    rw [hcoord]
    infer_instance
  have : IsProper (toTarget f P U h w ∣_ V) :=
    IsProper.of_comp _ ((finiteProductOverπ P i).left ∣_ W i)
  have : IsImmersion (((toSource f P U h w) ⁻¹ᵁ U i).ι ≫ toTarget f P U h w) :=
    toTarget_restrict_isImmersion f P U h w i
  have hrestrict : (toTarget f P U h w ∣_ V) ≫ V.ι =
      e.hom ≫ (((toSource f P U h w) ⁻¹ᵁ U i).ι ≫ toTarget f P U h w) := by
    rw [morphismRestrict_ι, ← Category.assoc, Scheme.isoOfEq_hom_ι]
  have : IsImmersion ((toTarget f P U h w ∣_ V) ≫ V.ι) := by
    rw [hrestrict]
    infer_instance
  have : IsImmersion (toTarget f P U h w ∣_ V) := IsImmersion.of_comp _ V.ι
  exact IsClosedImmersion.of_isPreimmersion _
    (toTarget f P U h w ∣_ V).isClosedMap.isClosed_range

include hj in
/-- A covering family of original graph domains makes the original target map
an immersion when those domains are closed in specified target opens. -/
theorem toTarget_isImmersion (hcover : (⨆ i, U i) = ⊤) :
    IsImmersion (toTarget f P U h w) := by
  let V := fun i => (finiteProductOverπ P i).left ⁻¹ᵁ W i
  let : MorphismProperty.RespectsRight (@IsImmersion) (@IsOpenImmersion) := {
    postcomp := fun i hi g hg => by
      have := hi
      have := hg
      infer_instance }
  apply IsZariskiLocalAtTarget.of_range_subset_iSup (P := @IsImmersion) V
  · rintro _ ⟨x, rfl⟩
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp
      (((toSource f P U h w).iSup_preimage_eq_top hcover).ge (Set.mem_univ x))
    apply Opens.mem_iSup.mpr
    refine ⟨i, ?_⟩
    change x ∈ toTarget f P U h w ⁻¹ᵁ V i
    rw [toTarget_preimage_targetChart f P U h w W j hj i]
    exact hi
  · intro i
    have := toTarget_targetChart_isClosedImmersion f P U h w W j hj i
    infer_instance

end AlgebraicGeometry.Scheme.Chow.GraphProduct
