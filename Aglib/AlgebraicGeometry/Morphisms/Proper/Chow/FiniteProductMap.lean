/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.Proper.Chow.GraphProduct.Restriction
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-!
# The finite target map of a proper graph product

On the inverse image of each original graph domain, the original target map
is an immersion. A covering family therefore makes it locally quasi-finite.
For a proper original source it is also proper, hence finite by the native
Zariski Main Theorem. No reducedness or Noetherian hypothesis enters this step.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Chow.GraphProduct

variable {X S : Scheme.{u}} (f : X ⟶ S) {n : ℕ} (P : Fin n → Over S)
  (U : Fin n → X.Opens) (h : ∀ i, (U i).toScheme ⟶ (P i).left)
  (w : ∀ i, (U i).ι ≫ f = h i ≫ (P i).hom)
  [∀ i, IsProper (P i).hom]

/-- Properness of the original source makes the original map to the target product proper. -/
theorem toTarget_isProper [IsProper f] : IsProper (toTarget f P U h w) := by
  have : IsProper (targetOver P).hom := isProper_finiteProductOver P
  have : IsProper (toTarget f P U h w ≫ (targetOver P).hom) := by
    rw [← toSource_comp]
    infer_instance
  exact IsProper.of_comp (toTarget f P U h w) (targetOver P).hom

variable [∀ i, QuasiCompact (U i).ι] [∀ i, IsImmersion (h i)]

/-- Over each original graph domain, the original map to the full target product is
an immersion. -/
theorem toTarget_restrict_isImmersion (i : Fin n) :
    IsImmersion (((toSource f P U h w) ⁻¹ᵁ U i).ι ≫ toTarget f P U h w) := by
  let V := (toSource f P U h w) ⁻¹ᵁ U i
  let pU := toSource f P U h w ∣_ U i
  let qU := V.ι ≫ toTarget f P U h w
  have hwU : pU ≫ ((U i).ι ≫ f) = qU ≫ (targetOver P).hom := by
    dsimp only [pU, qU, V]
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc, toSource_comp]
    exact (Category.assoc _ _ _).symm
  let jU := pullback.lift pU qU hwU
  let incl := pullback.map ((U i).ι ≫ f) (targetOver P).hom f (targetOver P).hom
    (U i).ι (𝟙 _) (𝟙 _) (by simp) (by simp)
  have hj : jU ≫ incl = V.ι ≫ pair f P U h w := by
    apply pullback.hom_ext
    · simp [jU, incl, pullback.map, pair, pU, V]
    · simp [jU, incl, pullback.map, pair, qU]
  have : IsImmersion (jU ≫ incl) := by
    rw [hj]
    infer_instance
  have : IsImmersion jU := IsImmersion.of_comp jU incl
  let emb := pullback.map ((U i).ι ≫ f) (targetOver P).hom (P i).hom (targetOver P).hom
    (h i) (𝟙 _) (𝟙 _) ((Category.comp_id _).trans (w i)) (by simp)
  have : IsImmersion emb :=
    MorphismProperty.pullbackMap (P := @IsImmersion.{u}) inferInstance inferInstance
      (w i) (Category.id_comp _).symm
  let graph : (targetOver P).left ⟶ pullback (P i).hom (targetOver P).hom :=
    pullback.lift (finiteProductOverπ P i).left (𝟙 (targetOver P).left)
      (by simpa only [Category.id_comp] using (finiteProductOverπ P i).w)
  have he : qU ≫ graph = jU ≫ emb := by
    apply pullback.hom_ext
    · simp only [graph, jU, emb, pullback.map, Category.assoc, pullback.lift_fst,
        pullback.lift_fst_assoc]
      exact toTarget_π_restrict f P U h w i
    · simp [graph, jU, emb, pullback.map]
  have : IsImmersion (qU ≫ graph) := by
    rw [he]
    infer_instance
  exact IsImmersion.of_comp qU graph

/-- The original target map is locally quasi-finite when the original graph domains cover. -/
theorem toTarget_locallyQuasiFinite (hcover : (⨆ i, U i) = ⊤) :
    LocallyQuasiFinite (toTarget f P U h w) := by
  apply IsZariskiLocalAtSource.of_iSup_eq_top
    (fun i => (toSource f P U h w) ⁻¹ᵁ U i)
    ((toSource f P U h w).iSup_preimage_eq_top hcover)
  intro i
  have := toTarget_restrict_isImmersion f P U h w i
  infer_instance

/-- The original target map of the constructed graph product is finite. -/
theorem toTarget_isFinite [IsProper f] (hcover : (⨆ i, U i) = ⊤) :
    IsFinite (toTarget f P U h w) := by
  have := toTarget_isProper f P U h w
  have := toTarget_locallyQuasiFinite f P U h w hcover
  exact IsFinite.of_isProper_of_locallyQuasiFinite (toTarget f P U h w)

end AlgebraicGeometry.Scheme.Chow.GraphProduct
