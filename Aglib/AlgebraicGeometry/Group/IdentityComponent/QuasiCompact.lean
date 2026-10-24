/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Group.IdentityComponent.Irreducible
public import Aglib.CategoryTheory.Monoidal.GrpObjShear

/-!
# Quasi-compactness of the identity component over an algebraically closed field

Let `k` be a field and `G` a group scheme over `k`, that is `G : Over (Spec k)` with a group
object structure. This module proves:

* the division map `(a, b) ↦ a b⁻¹` of `G ×_k G` to `G` is open
  (`AlgebraicGeometry.Scheme.Group.isOpenMap_fst_div_snd_left`; Stacks Project, Tag 047K, for the
  multiplication): it is the shear automorphism `(a, b) ↦ (a b⁻¹, b)`
  (`CategoryTheory.GrpObj.shearIso`) followed by the first projection, which is
  universally open over a field (Mathlib's `UniversallyOpen` instance for morphisms to the
  spectrum of a field, Stacks 0383);
* **if `k` is algebraically closed, `G` is locally of finite type over `k` and irreducible, then
  `G` is quasi-compact**
  (`AlgebraicGeometry.Scheme.Group.compactSpace_of_irreducibleSpace_of_isAlgClosed`; Stacks 0B7P,
  after its reduction to an algebraically closed field);
* hence **the identity component `G⁰` is quasi-compact over an algebraically closed field**
  (`AlgebraicGeometry.Scheme.Group.compactSpace_identityComponent_of_isAlgClosed`), since it is
  irreducible (`Aglib.AlgebraicGeometry.Group.IdentityComponent.Irreducible`).

The proof follows Stacks 0B7P. Let `U` be a nonempty affine open of `G` and `m : U ×_k U ⟶ G` the
map `(u₁, u₂) ↦ u₁u₂⁻¹`. Its image is open, by the openness of the division map. It contains every
closed point `h`: the open sets `U` and `h⁻¹U` meet because `G` is irreducible, so they share a
closed point `u₂` (Mathlib's `nonempty_inter_closedPoints`; `G` is Jacobson by Mathlib's
`LocallyOfFiniteType.jacobsonSpace`); the closed points are `k`-points (Mathlib's
`AlgebraicGeometry.pointOfClosedPoint`), so `u₁ := h u₂` lies in `U` and `h = u₁ u₂⁻¹`. An open
subset of a Jacobson space containing every closed point is everything. So `G` is the image of the
affine, hence quasi-compact, scheme `U ×_k U`. Kleiman, *The Picard scheme*,
arXiv:math/0504020v1, Lemma 5.1(3), p. 37, concludes "α(U × U) = G⁰" without the openness of the
image and the Jacobson step, which Stacks 0B7P supplies.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory Topology
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.Scheme.Group

universe u

variable {k : Type u} [Field k] (G : Over (Spec (.of k))) [GrpObj G]

/-- **The division map `(a, b) ↦ a b⁻¹` of a group scheme over a field is open** (Stacks 047K,
for the multiplication): it is the shear automorphism followed by the first projection, which is
universally open. -/
theorem isOpenMap_fst_div_snd_left : IsOpenMap (fst G G / snd G G).left := by
  rw [← GrpObj.shearIso_hom_fst, Over.comp_left]
  have : UniversallyOpen (fst G G).left :=
    inferInstanceAs (UniversallyOpen (pullback.fst G.hom G.hom))
  exact (fst G G).left.isOpenMap.comp
    (Scheme.homeoOfIso ((Over.forget _).mapIso (GrpObj.shearIso G))).isOpenMap

/-- **An irreducible group scheme locally of finite type over an algebraically closed field is
quasi-compact** (Stacks 0B7P, after its reduction to an algebraically closed field). -/
theorem compactSpace_of_irreducibleSpace_of_isAlgClosed [IsAlgClosed k]
    [LocallyOfFiniteType G.hom] [IrreducibleSpace G.left] : CompactSpace G.left := by
  have : JacobsonSpace G.left := LocallyOfFiniteType.jacobsonSpace G.hom
  obtain ⟨x₀⟩ := (inferInstance : Nonempty G.left)
  obtain ⟨U, hU, hx₀U, -⟩ := exists_isAffineOpen_mem_and_subset (x := x₀) (U := ⊤) (by simp)
  have : IsAffine U.toScheme := hU
  -- `U` as a scheme over `k`, and `m : U ×_k U ⟶ G`, `(u₁, u₂) ↦ u₁ u₂⁻¹`.
  let Uo : Over (Spec (.of k)) := Over.mk (U.ι ≫ G.hom)
  let ιU : Uo ⟶ G := Over.homMk U.ι rfl
  let m : Uo ⊗ Uo ⟶ G := (ιU ⊗ₘ ιU) ≫ (fst G G / snd G G)
  have : CompactSpace (Uo ⊗ Uo).left :=
    inferInstanceAs (CompactSpace (pullback (U.ι ≫ G.hom) (U.ι ≫ G.hom) : Scheme.{u}))
  -- The image of `m` is open.
  have hopen : IsOpen (Set.range m.left) := by
    have : IsOpenImmersion (ιU ⊗ₘ ιU).left := by
      rw [Over.tensorHom_left]
      exact Scheme.pullback_map_isOpenImmersion _ _ _ _ U.ι U.ι _ _ _
    have hrange : Set.range m.left =
        (fst G G / snd G G).left '' Set.range (ιU ⊗ₘ ιU).left := by
      rw [← Set.range_comp]
      rfl
    rw [hrange]
    exact isOpenMap_fst_div_snd_left G _ (ιU ⊗ₘ ιU).left.isOpenEmbedding.isOpen_range
  -- Points of `G` lying in `U` lift to points of `U`.
  have hlift : ∀ q : 𝟙_ (Over (Spec (.of k))) ⟶ G, q.left (IsLocalRing.closedPoint k) ∈ U →
      ∃ a : 𝟙_ (Over (Spec (.of k))) ⟶ Uo, a ≫ ιU = q := by
    intro q hq
    have hr : Set.range q.left ⊆ Set.range U.ι := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨s, rfl⟩
      obtain rfl : s = IsLocalRing.closedPoint k := Subsingleton.elim (α := Spec (.of k)) _ _
      exact hq
    exact ⟨Over.homMk (IsOpenImmersion.lift U.ι q.left hr)
      ((IsOpenImmersion.lift_fac_assoc U.ι q.left hr G.hom).trans (Over.w q)),
      Over.OverMorphism.ext (IsOpenImmersion.lift_fac U.ι q.left hr)⟩
  -- The image of `m` contains every closed point.
  have hcl : ∀ z ∈ closedPoints G.left, z ∈ Set.range m.left := by
    intro z hz
    obtain ⟨ph, rfl⟩ := exists_point_left_apply_eq_of_isClosed_of_isAlgClosed G hz
    -- left translation by `ph`
    let L : G ⟶ G := (toUnit G ≫ ph) * 𝟙 G
    have hL : ∀ q : 𝟙_ (Over (Spec (.of k))) ⟶ G, q ≫ L = ph * q := fun q => by
      simp [L, MonObj.comp_mul]
    have hLpt : ∀ q : 𝟙_ (Over (Spec (.of k))) ⟶ G,
        L.left (q.left (IsLocalRing.closedPoint k)) =
          (ph * q).left (IsLocalRing.closedPoint k) := fun q =>
      (congrArg (fun φ : 𝟙_ (Over (Spec (.of k))) ⟶ G => φ.left (IsLocalRing.closedPoint k))
        (hL q) :)
    -- `U` contains a closed point `u₀`, so `L⁻¹ U` is a nonempty open set.
    obtain ⟨u₀, hu₀U, hu₀⟩ := nonempty_inter_closedPoints ⟨x₀, hx₀U⟩ U.isOpen.isLocallyClosed
    obtain ⟨q₀, rfl⟩ := exists_point_left_apply_eq_of_isClosed_of_isAlgClosed G hu₀
    have hVo : IsOpen (L.left ⁻¹' (U : Set G.left)) := U.isOpen.preimage L.left.continuous
    have hVne : (L.left ⁻¹' (U : Set G.left)).Nonempty := by
      refine ⟨(ph⁻¹ * q₀).left (IsLocalRing.closedPoint k), ?_⟩
      have h := hLpt (ph⁻¹ * q₀)
      rw [mul_inv_cancel_left] at h
      rw [Set.mem_preimage, h]
      exact hu₀U
    -- `U ∩ L⁻¹ U` contains a closed point `u₂`.
    obtain ⟨u₂, ⟨hu₂U, hu₂V⟩, hu₂⟩ := nonempty_inter_closedPoints
      (nonempty_preirreducible_inter U.isOpen hVo ⟨_, hu₀U⟩ hVne)
      (U.isOpen.inter hVo).isLocallyClosed
    obtain ⟨q₂, rfl⟩ := exists_point_left_apply_eq_of_isClosed_of_isAlgClosed G hu₂
    have hq₁ : (ph * q₂).left (IsLocalRing.closedPoint k) ∈ U := by
      rw [← hLpt]
      exact hu₂V
    obtain ⟨a₁, ha₁⟩ := hlift _ hq₁
    obtain ⟨a₂, ha₂⟩ := hlift _ hu₂U
    have hm : lift a₁ a₂ ≫ m = ph := by
      simp only [m, lift_map_assoc, ha₁, ha₂, GrpObj.comp_div, lift_fst, lift_snd,
        mul_div_cancel_right]
    exact ⟨(lift a₁ a₂).left (IsLocalRing.closedPoint k),
      congrArg (fun φ : 𝟙_ (Over (Spec (.of k))) ⟶ G => φ.left (IsLocalRing.closedPoint k)) hm⟩
  -- An open set containing every closed point of a Jacobson space is everything.
  have huniv : Set.range m.left = Set.univ := by
    by_contra hne
    obtain ⟨z, hz, hzc⟩ := nonempty_inter_closedPoints (Set.nonempty_compl.mpr hne)
      hopen.isClosed_compl.isLocallyClosed
    exact hz (hcl z hzc)
  exact ⟨huniv ▸ isCompact_range m.left.continuous⟩

variable [LocallyOfFiniteType G.hom]

/-- **The identity component is quasi-compact over an algebraically closed field** (Stacks
0B7P applied to `G⁰`; Kleiman, Lemma 5.1(3), p. 37), because it is irreducible. Over an arbitrary
field, see `Aglib.AlgebraicGeometry.Group.IdentityComponent.FiniteType`. -/
theorem compactSpace_identityComponent_of_isAlgClosed [IsAlgClosed k] :
    CompactSpace (identityComponent G).toScheme :=
  have : IrreducibleSpace (identityComponentOver G).left :=
    irreducibleSpace_identityComponent_of_isAlgClosed G
  compactSpace_of_irreducibleSpace_of_isAlgClosed (identityComponentOver G)

end AlgebraicGeometry.Scheme.Group
