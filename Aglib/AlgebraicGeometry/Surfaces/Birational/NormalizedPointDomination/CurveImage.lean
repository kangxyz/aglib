/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Surfaces.Birational.ExceptionalLocus

/-!
# Uniqueness of noncontracted proper images

A proper birational map to a normal surface is an isomorphism near every
nonclosed target point. Consequently two actual irreducible closed subsets
with the same nonsingleton proper image coincide. This is the uniqueness
part of the different-source curve map in normalized point domination.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme

universe u

/-- Proper images of actual irreducible closed subsets, retaining the original map. -/
def Hom.irreducibleClosedImage {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    (C : IrreducibleCloseds X) : IrreducibleCloseds Y :=
  ⟨f '' (C : Set X), C.isIrreducible.image f f.continuous.continuousOn,
    f.isClosedMap _ C.isClosed⟩

/-- The generic point of a proper image is the image of the original generic point. -/
theorem Hom.isGenericPoint_irreducibleClosedImage {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsProper f] (C : IrreducibleCloseds X) :
    IsGenericPoint (f C.isIrreducible.genericPoint)
      (f.irreducibleClosedImage C : Set Y) := by
  have h := (C.isIrreducible.isGenericPoint_genericPoint C.isClosed).image f.continuous
  change IsGenericPoint (f C.isIrreducible.genericPoint) (f '' (C : Set X))
  simpa only [(f.isClosedMap _ C.isClosed).closure_eq] using h

/-- Distinct irreducible closed subsets cannot have the same noncontracted image
under a proper birational morphism onto a normal integral surface. Source
regularity and source dimension bounds are unnecessary. -/
theorem Hom.irreducibleClosedImage_injective_of_not_subsingleton
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [IsProper f] [IsDominant f]
    (hff : IsIso (CommRingCat.ofHom (functionFieldMap f)))
    (hY : NormalStalks Y) (hdY : topologicalKrullDim Y ≤ 2)
    (C D : IrreducibleCloseds X)
    (hC : ¬ (f '' (C : Set X)).Subsingleton)
    (he : f.irreducibleClosedImage C = f.irreducibleClosedImage D) : C = D := by
  let c := C.isIrreducible.genericPoint
  let d := D.isIrreducible.genericPoint
  have hc := f.isGenericPoint_irreducibleClosedImage C
  have hd := f.isGenericPoint_irreducibleClosedImage D
  have hcd : f c = f d := hc.eq (he.symm ▸ hd)
  have hnc : ¬ IsClosed ({f c} : Set Y) := by
    intro hclosed
    apply hC
    have himage : f '' (C : Set X) = {f c} := hc.def.symm.trans hclosed.closure_eq
    rw [himage]
    exact Set.subsingleton_singleton
  obtain ⟨U, hcU, hU⟩ :=
    exists_isIso_restrict_of_isProper_birational_at_nonclosed_point f hff hY hdY (f c) hnc
  let : IsIso (f ∣_ U) := hU
  have hdU : f d ∈ U := hcd ▸ hcU
  have hres (z : (f ⁻¹ᵁ U).toScheme) : U.ι ((f ∣_ U) z) = f z.val :=
    congrArg (fun k : (f ⁻¹ᵁ U).toScheme ⟶ Y ↦ k z) (morphismRestrict_ι f U)
  have hrestrict : (f ∣_ U) ⟨c, hcU⟩ = (f ∣_ U) ⟨d, hdU⟩ := by
    apply U.ι.injective
    exact (hres ⟨c, hcU⟩).trans (hcd.trans (hres ⟨d, hdU⟩).symm)
  have hpoints : c = d := congrArg Subtype.val ((f ∣_ U).injective hrestrict)
  apply SetLike.coe_injective
  exact (C.isIrreducible.closure_genericPoint C.isClosed).symm.trans
    ((congrArg (fun z : X ↦ closure ({z} : Set X)) hpoints).trans
      (D.isIrreducible.closure_genericPoint D.isClosed))

/-- The original morphism is injective on points over its actual target
isomorphism locus. No choice of generic-field identification is involved. -/
theorem Hom.injOn_preimage_targetIsomorphismLocus
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Set.InjOn f (f ⁻¹' (f.targetIsomorphismLocus : Set Y)) := by
  let U := f.targetIsomorphismLocus
  let : IsIso (f ∣_ U) := f.isIso_restrict_targetIsomorphismLocus
  intro a ha b hb hab
  have hres (z : (f ⁻¹ᵁ U).toScheme) : U.ι ((f ∣_ U) z) = f z.val :=
    congrArg (fun k : (f ⁻¹ᵁ U).toScheme ⟶ Y ↦ k z) (morphismRestrict_ι f U)
  have he : (f ∣_ U) ⟨a, ha⟩ = (f ∣_ U) ⟨b, hb⟩ := by
    apply U.ι.injective
    exact (hres ⟨a, ha⟩).trans (hab.trans (hres ⟨b, hb⟩).symm)
  exact congrArg Subtype.val ((f ∣_ U).injective he)

/-- In a proper birational map to a normal target, the only point above the
actual target generic point is the actual source generic point. -/
theorem Hom.eq_genericPoint_of_map_eq_genericPoint
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [IsProper f] [IsDominant f]
    (hff : IsIso (CommRingCat.ofHom (functionFieldMap f)))
    (hY : NormalStalks Y) (x : X) (hx : f x = genericPoint Y) :
    x = genericPoint X := by
  have hη := genericPoint_mem_targetIsomorphismLocus f hff hY
  apply f.injOn_preimage_targetIsomorphismLocus
  · change f x ∈ f.targetIsomorphismLocus
    rw [hx]
    exact hη
  · change f (genericPoint X) ∈ f.targetIsomorphismLocus
    rw [map_genericPoint_of_isDominant X f]
    exact hη
  · exact hx.trans (map_genericPoint_of_isDominant X f).symm

/-- A noncontracted proper image of an irreducible closed subset avoiding the
source generic point is an actual curve on the normal target surface. -/
theorem Hom.dimension_irreducibleClosedImage_eq_one
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [IsProper f] [IsDominant f]
    (hff : IsIso (CommRingCat.ofHom (functionFieldMap f)))
    (hY : NormalStalks Y) (hdY : topologicalKrullDim Y ≤ 2)
    (C : IrreducibleCloseds X)
    (havoid : genericPoint X ∉ (C : Set X))
    (hC : ¬ (f '' (C : Set X)).Subsingleton) :
    topologicalKrullDim (f.irreducibleClosedImage C : Set Y) = 1 := by
  let c := C.isIrreducible.genericPoint
  have hc := f.isGenericPoint_irreducibleClosedImage C
  have hnc : ¬ IsClosed ({f c} : Set Y) := by
    intro hclosed
    apply hC
    have himage : f '' (C : Set X) = {f c} := hc.def.symm.trans hclosed.closure_eq
    rw [himage]
    exact Set.subsingleton_singleton
  have hne : f c ≠ genericPoint Y := by
    intro he
    have hce := f.eq_genericPoint_of_map_eq_genericPoint hff hY c he
    exact havoid (hce ▸ (C.isIrreducible.isGenericPoint_genericPoint C.isClosed).mem)
  rw [← hc.def]
  exact dimension_closure_point_eq_one hdY (f c) hnc hne

/-- Every actual contracted curve avoids the actual source generic point. -/
theorem genericPoint_not_mem_contractedCurve
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [IsProper f] [IsDominant f]
    (hff : IsIso (CommRingCat.ofHom (functionFieldMap f))) (hY : NormalStalks Y)
    (C : IrreducibleCloseds X) (hC : C ∈ contractedCurves f) :
    genericPoint X ∉ (C : Set X) := by
  intro hη
  have hnot := contractedCurve_avoids_targetLocus f C hC hη
  apply hnot
  rw [map_genericPoint_of_isDominant X f]
  exact genericPoint_mem_targetIsomorphismLocus f hff hY

/-- The actual proper image in a commuting square is a contracted curve when
it does not collapse to a point. This separates the finite-graph noncollapse
obligation from the already proved image dimension and uniqueness arguments. -/
theorem Hom.irreducibleClosedImage_mem_contractedCurves
    {X Y S T : Scheme.{u}} [IsIntegral X] [IsIntegral Y] [IsIntegral S]
    [IsLocallyNoetherian Y] [IsLocallyNoetherian S]
    (p : X ⟶ S) [IsProper p] [IsDominant p]
    (hp : IsIso (CommRingCat.ofHom (functionFieldMap p))) (hS : NormalStalks S)
    (g : X ⟶ Y) [IsProper g] [IsDominant g]
    (hg : IsIso (CommRingCat.ofHom (functionFieldMap g)))
    (hY : NormalStalks Y) (hdY : topologicalKrullDim Y ≤ 2)
    (q : Y ⟶ T) (r : S ⟶ T) (w : g ≫ q = p ≫ r)
    (C : IrreducibleCloseds X) (hC : C ∈ contractedCurves p)
    (hn : ¬ (g '' (C : Set X)).Subsingleton) :
    g.irreducibleClosedImage C ∈ contractedCurves q := by
  refine ⟨g.dimension_irreducibleClosedImage_eq_one hg hY hdY C
    (genericPoint_not_mem_contractedCurve p hp hS C hC) hn, ?_⟩
  rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩ _ ⟨_, ⟨b, hb, rfl⟩, rfl⟩
  have hw (x : X) : q (g x) = r (p x) :=
    congrArg (fun k : X ⟶ T ↦ k x) w
  exact (hw a).trans ((congrArg r (hC.2 ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩)).trans (hw b).symm)

/-- The genuine different-source embedding sends each noncollapsed contracted
curve to its proper image. Its domain explicitly excludes collapsed images;
showing that a finite normalized graph excludes all such collapses is a
separate geometric obligation, not an assumption hidden in this definition. -/
def contractedCurveImageEmbedding
    {X Y S T : Scheme.{u}} [IsIntegral X] [IsIntegral Y] [IsIntegral S]
    [IsLocallyNoetherian Y] [IsLocallyNoetherian S]
    (p : X ⟶ S) [IsProper p] [IsDominant p]
    (hp : IsIso (CommRingCat.ofHom (functionFieldMap p))) (hS : NormalStalks S)
    (g : X ⟶ Y) [IsProper g] [IsDominant g]
    (hg : IsIso (CommRingCat.ofHom (functionFieldMap g)))
    (hY : NormalStalks Y) (hdY : topologicalKrullDim Y ≤ 2)
    (q : Y ⟶ T) (r : S ⟶ T) (w : g ≫ q = p ≫ r) :
    {C : contractedCurves p // ¬ (g '' (C.val : Set X)).Subsingleton} ↪
      contractedCurves q where
  toFun C := ⟨g.irreducibleClosedImage C.val.val,
    Hom.irreducibleClosedImage_mem_contractedCurves p hp hS g hg hY hdY q r w
      C.val.val C.val.property C.property⟩
  inj' := by
    intro C D he
    apply Subtype.ext
    apply Subtype.ext
    exact g.irreducibleClosedImage_injective_of_not_subsingleton hg hY hdY
      C.val.val D.val.val C.property (congrArg Subtype.val he)

end AlgebraicGeometry.Scheme
