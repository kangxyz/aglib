/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Picard.Tangent.Cech.Units
public import Aglib.AlgebraicGeometry.Cohomology.Cech.PairCocycles
public import Aglib.AlgebraicGeometry.Modules.Invertible.Gluing.Tensor
public import Aglib.AlgebraicGeometry.Modules.Invertible.Gluing.PullbackCocycle
public import Aglib.AlgebraicGeometry.Modules.Invertible.PullbackTensor.Local

/-!
# Line bundles on a split square-zero thickening from pair cocycles

Let `i : X ⟶ Y`, `p : Y ⟶ X` with `i ≫ p = 𝟙 X`, let `G` be an `IdealGenerator` with generator
`ε` (for example the dual numbers `X[ε]`), and let `U : ι → X.Opens` cover `X`.

* `IdealGenerator.oneAddCocycle U b`: for a pair cocycle `b` of the structure sheaf of `X`
  on `U` (`Scheme.pairCocycles U`), the units `1 + ε p^♯ b j l` form a unit cocycle on the
  cover `p⁻¹ U` of `Y`.
* `IdealGenerator.cocycleClass U hU`: the additive map from pair cocycles to `Pic Y` sending `b`
  to the class of the glued line bundle; additivity is the tensor product of glued line
  bundles (`UnitCocycle.classOf_lineBundle_mul`).
* `IdealGenerator.pullbackHom_cocycleClass`: these classes lie in the kernel of `i^*`, since
  `i^♯ (1 + ε b) = 1`.
* `IdealGenerator.cocycleClass_eq_zero_iff`: when the members of `U` are affine, the class of `b`
  vanishes if and only if `b` is a pair coboundary.

This is the Čech construction of the kernel of `Pic(Y) → Pic(X)` on a fixed cover (Kleiman,
arXiv:math/0504020v1, proof of Thm 5.11, p. 43, where the kernel is read from the truncated
exponential sequence; for Čech `H^1` and torsors trivial on a cover, Stacks, Tag 0B8R).
-/

@[expose] public section

noncomputable section


open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry.Scheme.Modules.Invertible
open AlgebraicGeometry.Scheme.Modules.Invertible.PullbackTensor.Local

universe u

namespace AlgebraicGeometry.Scheme.SplitThickening.IdealGenerator

variable {X Y : Scheme.{u}} {i : X ⟶ Y} {p : Y ⟶ X} {h : i ≫ p = 𝟙 X}
  (G : IdealGenerator i p h) {ι : Type u} (U : ι → X.Opens)

/-- Restriction commutes with `p^♯` on units. -/
theorem units_map_restrict_projection {V W : X.Opens} (hVW : V ≤ W) (hp : p ⁻¹ᵁ V ≤ p ⁻¹ᵁ W)
    (x : (Γ(X, W))ˣ) :
    Units.map (sectionRestrict Y hp).toMonoidHom (Units.map (p.app W).hom.toMonoidHom x) =
      Units.map (p.app V).hom.toMonoidHom (Units.map (sectionRestrict X hVW).toMonoidHom x) := by
  apply Units.ext
  have e := congrArg (fun φ => φ.hom (x : Γ(X, W))) (p.naturality (homOfLE hVW).op)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e
  exact e.symm

/-- Restriction of `1 + ε b` along an open contained in a smaller preimage. -/
theorem units_map_oneAdd_of_le {T : Y.Opens} {V W : X.Opens} (hT : T ≤ p ⁻¹ᵁ V)
    (hVW : V ≤ W) (hTW : T ≤ p ⁻¹ᵁ W) (b : Γ(X, W)) :
    Units.map (sectionRestrict Y hTW).toMonoidHom (G.oneAdd W b) =
      Units.map (sectionRestrict Y hT).toMonoidHom (G.oneAdd V (sectionRestrict X hVW b)) := by
  rw [← G.units_map_oneAdd hVW ((Opens.map p.base).monotone hVW),
    UnitCocycle.units_map_sectionRestrict_comp]

/-- The unit cocycle `1 + ε p^♯ b j l` on the cover `p⁻¹ U` of `Y`, for a pair cocycle `b`. -/
def oneAddCocycle (b : pairCocycles U) : UnitCocycle (fun j => p ⁻¹ᵁ U j) where
  transition j l := G.oneAdd (U j ⊓ U l) ((b : ∀ j l : ι, Γ(X, U j ⊓ U l)) j l)
  cocycle j l m T hj hl hm := by
    have hT : T ≤ p ⁻¹ᵁ (U j ⊓ U l ⊓ U m) := le_inf (le_inf hj hl) hm
    have hWj : U j ⊓ U l ⊓ U m ≤ U j := inf_le_left.trans inf_le_left
    have hWl : U j ⊓ U l ⊓ U m ≤ U l := inf_le_left.trans inf_le_right
    have hWm : U j ⊓ U l ⊓ U m ≤ U m := inf_le_right
    change Units.map (sectionRestrict Y (show T ≤ p ⁻¹ᵁ (U j ⊓ U l) from le_inf hj hl)).toMonoidHom
        (G.oneAdd (U j ⊓ U l) ((b : ∀ j l : ι, Γ(X, U j ⊓ U l)) j l)) *
      Units.map (sectionRestrict Y (show T ≤ p ⁻¹ᵁ (U l ⊓ U m) from le_inf hl hm)).toMonoidHom
        (G.oneAdd (U l ⊓ U m) ((b : ∀ j l : ι, Γ(X, U j ⊓ U l)) l m)) =
      Units.map (sectionRestrict Y (show T ≤ p ⁻¹ᵁ (U j ⊓ U m) from le_inf hj hm)).toMonoidHom
        (G.oneAdd (U j ⊓ U m) ((b : ∀ j l : ι, Γ(X, U j ⊓ U l)) j m))
    rw [G.units_map_oneAdd_of_le hT (le_inf hWj hWl), G.units_map_oneAdd_of_le hT (le_inf hWl hWm),
      G.units_map_oneAdd_of_le hT (le_inf hWj hWm), ← map_mul, ← G.oneAdd_add,
      (mem_pairCocycles_iff _).mp b.2 j l m _ hWj hWl hWm]

theorem oneAddCocycle_transition (b : pairCocycles U) (j l : ι) :
    (G.oneAddCocycle U b).transition j l =
      G.oneAdd (U j ⊓ U l) ((b : ∀ j l : ι, Γ(X, U j ⊓ U l)) j l) :=
  rfl

theorem oneAddCocycle_zero : G.oneAddCocycle U 0 = 1 :=
  UnitCocycle.ext fun j l => G.oneAdd_zero (U j ⊓ U l)

theorem oneAddCocycle_add (b b' : pairCocycles U) :
    G.oneAddCocycle U (b + b') = G.oneAddCocycle U b * G.oneAddCocycle U b' :=
  UnitCocycle.ext fun j l => G.oneAdd_add (U j ⊓ U l) _ _

/-- `i^♯` on sections over a preimage is the reduction map. -/
theorem appLE_eq_reduction (W : X.Opens) (e : W ≤ i ⁻¹ᵁ (p ⁻¹ᵁ W)) :
    i.appLE (p ⁻¹ᵁ W) W e = (reduction i p h).hom.app (op W) := by
  rw [reduction_app]
  exact congrArg (fun k => i.app (p ⁻¹ᵁ W) ≫ X.presheaf.map k)
    (Quiver.Hom.unop_inj (Subsingleton.elim _ _))

-- Sections over `p⁻¹ (U ⊓ V)` and over `p⁻¹ U ⊓ p⁻¹ V` agree only after unfolding.
set_option backward.isDefEq.respectTransparency false in
/-- The transition units `1 + ε b` pull back along `i` to the trivial cocycle. -/
theorem transitionPullback_oneAddCocycle (b : pairCocycles U) :
    UnitCocycle.TransitionPullback i (G.oneAddCocycle U b) (1 : UnitCocycle U) := by
  intro j l e
  change Units.map (i.appLE (p ⁻¹ᵁ (U j ⊓ U l)) (U j ⊓ U l) e).hom.toMonoidHom
    (G.oneAdd (U j ⊓ U l) ((b : ∀ j l : ι, Γ(X, U j ⊓ U l)) j l)) = 1
  rw [appLE_eq_reduction]
  exact G.reduction_oneAdd _ _

variable (hU : iSup U = ⊤)

/-- The class in `Pic Y` of the line bundle glued from `1 + ε b`, additive in the pair
cocycle `b`. -/
def cocycleClass : pairCocycles U →+ PicardGroup Y where
  toFun b := classOf Y ((G.oneAddCocycle U b).lineBundle (p.iSup_preimage_eq_top hU))
  map_zero' := by
    rw [oneAddCocycle_zero]
    exact UnitCocycle.classOf_one_lineBundle _
  map_add' b b' := by
    rw [oneAddCocycle_add]
    exact UnitCocycle.classOf_lineBundle_mul _ _ _

theorem cocycleClass_apply (b : pairCocycles U) :
    G.cocycleClass U hU b =
      classOf Y ((G.oneAddCocycle U b).lineBundle (p.iSup_preimage_eq_top hU)) :=
  rfl

/-- The classes `1 + ε b` lie in the kernel of `i^*`. -/
theorem pullbackHom_cocycleClass (b : pairCocycles U) :
    pullbackHom i (G.cocycleClass U hU b) = 0 := by
  change classOf X (pullbackLineBundle i
    ((G.oneAddCocycle U b).lineBundle (p.iSup_preimage_eq_top hU))) = 0
  rw [← UnitCocycle.classOf_one_lineBundle hU]
  exact (class_eq_iff X _ _).mpr ⟨(G.oneAddCocycle U b).pullbackIso i 1
    (fun j => preimage_preimage_eq i p h (U j)) (G.transitionPullback_oneAddCocycle U b)
    (p.iSup_preimage_eq_top hU)⟩

/-- The class of `1 + ε b` vanishes if `b` is a coboundary. -/
theorem cocycleClass_eq_zero_of_mem (b : pairCocycles U) (hb : b ∈ pairCoboundaries U) :
    G.cocycleClass U hU b = 0 := by
  obtain ⟨a, ha⟩ := (mem_pairCoboundaries_iff U b).mp hb
  rw [cocycleClass_apply, UnitCocycle.classOf_lineBundle_eq_zero_iff]
  refine ⟨fun j => G.oneAdd (U j) (-a j), fun j l => ?_⟩
  change G.oneAdd (U j ⊓ U l) ((b : ∀ j l : ι, Γ(X, U j ⊓ U l)) j l) *
      Units.map (sectionRestrict Y ((Opens.map p.base).monotone
        (inf_le_right : U j ⊓ U l ≤ U l))).toMonoidHom (G.oneAdd (U l) (-a l)) =
    1 * Units.map (sectionRestrict Y ((Opens.map p.base).monotone
        (inf_le_left : U j ⊓ U l ≤ U j))).toMonoidHom (G.oneAdd (U j) (-a j))
  rw [G.units_map_oneAdd inf_le_right, G.units_map_oneAdd inf_le_left, one_mul, ← G.oneAdd_add,
    ha j l, map_neg, map_neg]
  congr 1
  abel

variable (hU₁ : ∀ j, IsAffineOpen (U j))

include hU₁ in
-- Sections over `p⁻¹ (U ⊓ V)` and over `p⁻¹ U ⊓ p⁻¹ V` agree only after unfolding.
set_option backward.isDefEq.respectTransparency false in
/-- On a cover by affine opens, the class of `1 + ε b` vanishes only if `b` is a
coboundary. -/
theorem mem_pairCoboundaries_of_cocycleClass_eq_zero (b : pairCocycles U)
    (hb : G.cocycleClass U hU b = 0) : b ∈ pairCoboundaries U := by
  rw [cocycleClass_apply, UnitCocycle.classOf_lineBundle_eq_zero_iff] at hb
  obtain ⟨u, hu⟩ := hb
  choose a ha using fun j => G.exists_eq_mul_oneAdd (U j) (hU₁ j) (u j)
  refine (mem_pairCoboundaries_iff U b).mpr ⟨fun j => -a j, fun j l => ?_⟩
  have e := hu j l
  change G.oneAdd (U j ⊓ U l) ((b : ∀ j l : ι, Γ(X, U j ⊓ U l)) j l) *
      Units.map (sectionRestrict Y ((Opens.map p.base).monotone
        (inf_le_right : U j ⊓ U l ≤ U l))).toMonoidHom (u l) =
    1 * Units.map (sectionRestrict Y ((Opens.map p.base).monotone
        (inf_le_left : U j ⊓ U l ≤ U j))).toMonoidHom (u j) at e
  rw [ha l, ha j, map_mul, map_mul, units_map_restrict_projection inf_le_right,
    units_map_restrict_projection inf_le_left, G.units_map_oneAdd inf_le_right,
    G.units_map_oneAdd inf_le_left, one_mul] at e
  -- The reductions of the two frames agree on the overlap.
  have hred := congrArg
    (Units.map ((reduction i p h).hom.app (op (U j ⊓ U l))).hom.toMonoidHom) e
  simp only [map_mul, G.reduction_oneAdd, reduction_units_map_projection, one_mul,
    mul_one] at hred
  rw [hred, ← mul_assoc, mul_comm (G.oneAdd _ _), mul_assoc] at e
  have e' := mul_left_cancel e
  rw [← G.oneAdd_add] at e'
  have e'' := G.oneAdd_injective _ e'
  change (b : ∀ j l : ι, Γ(X, U j ⊓ U l)) j l =
    sectionRestrict X inf_le_right (-a l) - sectionRestrict X inf_le_left (-a j)
  rw [map_neg, map_neg, ← e'']
  abel

include hU₁ in
/-- On a cover by affine opens, the class of `1 + ε b` vanishes exactly when `b` is a pair
coboundary. -/
theorem cocycleClass_eq_zero_iff (b : pairCocycles U) :
    G.cocycleClass U hU b = 0 ↔ b ∈ pairCoboundaries U :=
  ⟨G.mem_pairCoboundaries_of_cocycleClass_eq_zero U hU hU₁ b,
    G.cocycleClass_eq_zero_of_mem U hU b⟩

end AlgebraicGeometry.Scheme.SplitThickening.IdealGenerator
