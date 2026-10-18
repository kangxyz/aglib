/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.IdealSheaf.BaseChange.Map
public import Aglib.AlgebraicGeometry.Modules.IsomorphismFunctors
public import Mathlib.CategoryTheory.Adjunction.FullyFaithful

/-!
# Canonical ideal maps under isomorphism squares

## Extraction basis

Existing proofs transferred from frozen dirty R5 revision
`79307ff88f07d34fd5c3edb859f799c55e38f290`. Source identities:

- `R5Lab/AlgebraicGeometry/Curves/RelativeDivisors/FlatIdealBaseChange.lean`, SHA-256
  `52ad81197b39689c02c7f936d7b8987c9dac2695568d56796cdb1c43743a6864`.

Actual objects, maps, universes and stated conditions are retained.
Native validation coverage is recorded separately in `doc/WORK_PLAN.md` and
the migration records; the source hashes above identify extraction inputs.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w t

open CategoryTheory Limits AlgebraicGeometry Opposite TopologicalSpace
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.Scheme.Modules
open LinearMap

section
namespace AlgebraicGeometry.Scheme.Hom

variable {D D' X Y : Scheme.{u}}
variable (i : D ⟶ X) (i' : D' ⟶ Y) (b : Y ⟶ X) (a : D' ⟶ D)
  (h : a ≫ i = i' ≫ b)

/-- The actual map on pushed-forward ideals is an isomorphism for an iso square. -/
theorem idealPushforwardMap_isIso_of_iso_square [IsIso a] [IsIso b] :
    IsIso (idealPushforwardMap i i' b a h) := by
  have : IsIso (squareStructureModuleMap i i' b a h) := by
    unfold squareStructureModuleMap
    infer_instance
  let e := kernel.mapIso (structureModuleMap i)
    ((Scheme.Modules.pushforward b).map (structureModuleMap i'))
    (asIso (structureModuleMap b)) (asIso (squareStructureModuleMap i i' b a h))
    (squareStructureModuleMap_comm i i' b a h)
  have he : idealPushforwardMap i i' b a h = e.hom ≫
      (PreservesKernel.iso (Scheme.Modules.pushforward b) (structureModuleMap i')).inv := by
    apply (cancel_mono ((Scheme.Modules.pushforward b).map (idealInclusion i'))).mp
    rw [idealPushforwardMap_inclusion]
    simp only [e, Category.assoc, PreservesKernel.iso_inv_ι, kernel.mapIso_hom,
      kernel.map, kernel.lift_ι, asIso_hom, idealInclusion]
  rw [he]
  infer_instance

/-- The original canonical ideal pullback map is invertible for a commutative square
whose horizontal arrows are isomorphisms. The vertical maps are arbitrary. -/
theorem idealPullbackMap_isIso_of_iso_square [IsIso a] [IsIso b] :
    IsIso (idealPullbackMap i i' b a h) := by
  have := idealPushforwardMap_isIso_of_iso_square i i' b a h
  have := pushforward_isEquivalence_of_isIso b
  unfold idealPullbackMap
  rw [Adjunction.homEquiv_counit]
  infer_instance

end AlgebraicGeometry.Scheme.Hom
end

section
namespace AlgebraicGeometry.Scheme.Hom

variable {D X D' Y DS XS DS' YS : Scheme.{u}}
  (i : D ⟶ X) (i' : D' ⟶ Y) (b : Y ⟶ X) (a : D' ⟶ D)
  (h : a ≫ i = i' ≫ b)
  (j : DS ⟶ XS) (j' : DS' ⟶ YS) (c : YS ⟶ XS) (d : DS' ⟶ DS)
  (hs : d ≫ j = j' ≫ c)
  (eX : X ≅ XS) (eD : D ≅ DS) (eY : Y ≅ YS) (eD' : D' ≅ DS')
  (hX : eD.hom ≫ j = i ≫ eX.hom) (hY : eD'.hom ≫ j' = i' ≫ eY.hom)
  (hb : eY.hom ≫ c = b ≫ eX.hom)
include hb

theorem idealPullbackMap_isIso_of_isoSquares
    [IsIso (idealPullbackMap j i eX.hom eD.hom hX)]
    [IsIso (idealPullbackMap j' i' eY.hom eD'.hom hY)]
    [IsIso (idealPullbackMap j j' c d hs)] :
    IsIso (idealPullbackMap i i' b a h) := by
  have hleft : (a ≫ eD.hom) ≫ j = i' ≫ (b ≫ eX.hom) := by
    rw [Category.assoc, hX, ← Category.assoc, h, Category.assoc]
  have hright : (eD'.hom ≫ d) ≫ j = i' ≫ (eY.hom ≫ c) := by
    rw [Category.assoc, hs, ← Category.assoc, hY, Category.assoc]
  have : IsIso (idealPullbackMap j i' (eY.hom ≫ c) (eD'.hom ≫ d) hright) := by
    rw [← idealPullbackMap_comp j j' i' c eY.hom d eD'.hom hs hY]
    infer_instance
  have : IsIso (idealPullbackMap j i' (b ≫ eX.hom) (a ≫ eD.hom) hleft) :=
    idealPullbackMap_isIso_of_eq_base j i' (b ≫ eX.hom) (eY.hom ≫ c)
      (a ≫ eD.hom) (eD'.hom ≫ d) hleft hright hb.symm
  have : IsIso ((Scheme.Modules.pullbackComp b eX.hom).inv.app (idealModule j) ≫
      (Scheme.Modules.pullback b).map (idealPullbackMap j i eX.hom eD.hom hX) ≫
        idealPullbackMap i i' b a h) := by
    rw [idealPullbackMap_comp]
    infer_instance
  have : IsIso ((Scheme.Modules.pullback b).map
      (idealPullbackMap j i eX.hom eD.hom hX) ≫ idealPullbackMap i i' b a h) :=
    (isIso_comp_left_iff ((Scheme.Modules.pullbackComp b eX.hom).inv.app (idealModule j)) _).mp
      inferInstance
  exact (isIso_comp_left_iff
    ((Scheme.Modules.pullback b).map (idealPullbackMap j i eX.hom eD.hom hX)) _).mp inferInstance

end AlgebraicGeometry.Scheme.Hom
end
