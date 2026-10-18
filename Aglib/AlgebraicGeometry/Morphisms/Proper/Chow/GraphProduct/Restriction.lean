/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.Proper.Chow.GraphProduct

/-!
# The original graph-product projection over the common open

When every target is proper over the base and every graph domain is
quasi-compact, each open contained in all original graph domains is an
isomorphism locus of the original graph-product projection. The proof uses
native pullback pasting and the canonical base-change comparison of the same
finite product.
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

/-- The original component projection restricted to the inverse image of its graph domain. -/
def toComponentRestrict (i : Fin n) :
    ((toSource f P U h w) ⁻¹ᵁ U i).toScheme ⟶
      ((GraphClosure.toSource f (P i).hom (U i) (h i) (w i)) ⁻¹ᵁ U i).toScheme :=
  (toComponent f P U h w i).resLE _ _
    (by rw [← Hom.comp_preimage, toComponent_toSource])

@[reassoc (attr := simp)]
theorem toComponentRestrict_ι (i : Fin n) :
    toComponentRestrict f P U h w i ≫
        ((GraphClosure.toSource f (P i).hom (U i) (h i) (w i)) ⁻¹ᵁ U i).ι =
      ((toSource f P U h w) ⁻¹ᵁ U i).ι ≫ toComponent f P U h w i := by
  simp [toComponentRestrict]

@[reassoc (attr := simp)]
theorem toComponentRestrict_toSource (i : Fin n) :
    toComponentRestrict f P U h w i ≫
        (GraphClosure.toSource f (P i).hom (U i) (h i) (w i) ∣_ U i) =
      toSource f P U h w ∣_ U i := by
  apply (cancel_mono (U i).ι).mp
  simp only [Category.assoc, morphismRestrict_ι, toComponentRestrict_ι_assoc,
    toComponent_toSource]

variable [∀ i, IsProper (P i).hom] [∀ i, QuasiCompact (U i).ι]

/-- On the inverse image of a graph domain, the original target coordinate is the original
local map composed with the original source projection. -/
@[reassoc (attr := simp)]
private theorem toComponent_toTarget_restrict (i : Fin n) :
    ((toSource f P U h w) ⁻¹ᵁ U i).ι ≫ toComponent f P U h w i ≫
        GraphClosure.toTarget f (P i).hom (U i) (h i) (w i) =
      (toSource f P U h w ∣_ U i) ≫ h i := by
  have hc : (GraphClosure.toSource f (P i).hom (U i) (h i) (w i) ∣_ U i) ≫ h i =
      ((GraphClosure.toSource f (P i).hom (U i) (h i) (w i)) ⁻¹ᵁ U i).ι ≫
        GraphClosure.toTarget f (P i).hom (U i) (h i) (w i) := by
    have : IsIso (GraphClosure.fromOpenToPreimage f (P i).hom (U i) (h i) (w i)) := by
      rw [← GraphClosure.toSourceRestrictIso_inv]
      infer_instance
    apply (cancel_epi (GraphClosure.fromOpenToPreimage f (P i).hom (U i) (h i) (w i))).mp
    simp [← Category.assoc]
  rw [← toComponentRestrict_ι_assoc, ← hc, toComponentRestrict_toSource_assoc]

/-- The original graph-product coordinate formula. -/
@[reassoc]
theorem toTarget_π_restrict (i : Fin n) :
    ((toSource f P U h w) ⁻¹ᵁ U i).ι ≫ toTarget f P U h w ≫
        (finiteProductOverπ P i).left =
      (toSource f P U h w ∣_ U i) ≫ h i := by
  rw [toTarget_π, toComponent_toTarget_restrict]

/-- The original individual graph projection is invertible on every smaller original open. -/
theorem component_restrict_isIso (i : Fin n) (V : X.Opens) (hV : V ≤ U i) :
    IsIso (GraphClosure.toSource f (P i).hom (U i) (h i) (w i) ∣_ V) := by
  let p := GraphClosure.toSource f (P i).hom (U i) (h i) (w i)
  have : IsIso (p ∣_ U i) := GraphClosure.isIso_toSource_restrict
    f (P i).hom (U i) (h i) (w i)
  have hs : IsPullback
      ((GraphClosure.closure f (P i).hom (U i) (h i) (w i)).homOfLE (p.preimage_mono hV))
      (p ∣_ V) (p ∣_ U i) (X.homOfLE hV) := by
    refine IsPullback.of_right ?_ (morphismRestrict_homOfLE p V (U i) hV).symm
      (isPullback_morphismRestrict p (U i)).flip
    simpa using (isPullback_morphismRestrict p V).flip
  exact hs.isIso_snd_of_isIso

/-- The original finite graph-product projection is invertible on every common open. -/
theorem isIso_toSource_restrict (V : X.Opens) (hV : ∀ i, V ≤ U i) :
    IsIso (toSource f P U h w ∣_ V) := by
  have hi (i : Fin n) :
      IsIso (((Over.pullback V.ι).obj (componentOver f P U h w i)).hom) := by
    let p := GraphClosure.toSource f (P i).hom (U i) (h i) (w i)
    change IsIso (pullback.snd p V.ι)
    have : IsIso (p ∣_ V) := component_restrict_isIso f P U h w i V (hV i)
    rw [← pullbackRestrictIsoRestrict_hom_morphismRestrict p V]
    infer_instance
  have : IsIso (finiteProductOver
      (fun i => (Over.pullback V.ι).obj (componentOver f P U h w i))).hom :=
    isIso_finiteProductOver _
  have hp : IsIso (pullback.snd (toSource f P U h w) V.ι) := by
    change IsIso (((Over.pullback V.ι).obj
      (finiteProductOver (componentOver f P U h w))).hom)
    rw [← (finiteProductOverPullbackIso V.ι (componentOver f P U h w)).hom.w]
    infer_instance
  change IsIso ((pullbackRestrictIsoRestrict (toSource f P U h w) V).inv ≫
    pullback.snd (toSource f P U h w) V.ι)
  infer_instance

/-- The isomorphism uses exactly the original restriction of the original projection. -/
def toSourceRestrictIso (V : X.Opens) (hV : ∀ i, V ≤ U i) :
    ((toSource f P U h w) ⁻¹ᵁ V).toScheme ≅ V.toScheme := by
  letI := isIso_toSource_restrict f P U h w V hV
  exact asIso (toSource f P U h w ∣_ V)

@[simp]
theorem toSourceRestrictIso_hom (V : X.Opens) (hV : ∀ i, V ≤ U i) :
    (toSourceRestrictIso f P U h w V hV).hom = toSource f P U h w ∣_ V := rfl

/-- In particular, the original projection is an isomorphism over the actual common intersection.
-/
theorem isIso_toSource_commonOpen : IsIso (toSource f P U h w ∣_ ⨅ i, U i) :=
  isIso_toSource_restrict f P U h w _ (fun i => iInf_le U i)

end AlgebraicGeometry.Scheme.Chow.GraphProduct
