/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Nodal.Polygon.EtaleProjection
public import Aglib.AlgebraicGeometry.Gluing.OpenImmersion

/-!
# The literal one-component polygon

Source: frozen R5 revision `f8a3314ddecffcada2ec721d26d56a937bed9690`.
`Incidence/Polygons.lean`, lines 548–600.
SHA-256: `8abe8be85b399c16b249392252ef43817c226a7876005fa6d659e4da82882ff3`.
-/

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.Polygon
variable (k : Type u) [Field k]
/-- In the one-component cycle the literal diagonal node-ring map is an
isomorphism; its inverse is evaluation at the unique normalization coordinate. -/
theorem baseMap_one_bijective : Function.Bijective (baseMap k 1) := by
  refine ⟨baseMap_injective k 1, ?_⟩
  intro p
  have hp : (p.val 0).eval 0 = (p.val 0).eval 1 := by
    have h := (mem_nodeRing k 1 p.val).mp p.property 0
    have hrot : finRotate 1 0 = 0 := Subsingleton.elim _ _
    simpa only [hrot] using h.symm
  refine ⟨⟨p.val 0, hp⟩, ?_⟩
  apply Subtype.ext
  funext i
  change p.val 0 = p.val i
  rw [Subsingleton.elim i 0]

instance affineMap_one_isIso : IsIso (affineMap k 1) :=
  isIso_SpecMap_iff.mpr (baseMap_one_bijective k)

instance infinityMap_one_isIso : IsIso (infinityMap k 1) := by
  apply isIso_SpecMap_iff.mpr
  constructor
  · intro a b h
    exact congrArg (fun f : Fin 1 → V k => f 0) h
  · intro p
    refine ⟨p 0, ?_⟩
    funext i
    change p 0 = p i
    rw [Subsingleton.elim i 0]

/-- The actual one-cycle map is an isomorphism by its two actual affine chart
maps; no etale patching or supplied classification premise is needed. -/
instance cycleMap_one_isIso : IsIso (cycleMap k 1) := by
  apply IsZariskiLocalAtTarget.of_openCover (P := MorphismProperty.isomorphisms Scheme)
    (Scheme.OpenNormalizationGluing.twoChartCover
      (Scheme.PinchedLine.gluingToNode k) (Scheme.PinchedLine.gluingToInfinity k))
  intro b
  cases b
  · change IsIso (pullback.snd (cycleMap k 1) (pushout.inl _ _))
    rw [← (cycleMap_affine_isPullback k 1).flip.isoPullback_inv_snd]
    infer_instance
  · change IsIso (pullback.snd (cycleMap k 1) (pushout.inr _ _))
    rw [← (cycleMap_infinity_isPullback k 1).flip.isoPullback_inv_snd]
    infer_instance

/-- The isomorphism over `k` from the literal one-component polygon to the pinched line,
induced by `cycleMap k 1`. -/
def cycleOneOverIso :
    Over.mk (structureMap k 1) ≅ Over.mk (Scheme.PinchedLine.pinchedStructure k) :=
  Over.isoMk (asIso (cycleMap k 1)) rfl

end AlgebraicGeometry.Scheme.Polygon
end
