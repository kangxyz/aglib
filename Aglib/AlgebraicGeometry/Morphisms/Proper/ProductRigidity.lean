/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
/-
The graph argument generalizes the proof in Group/LineBundleCube/Rigidity,
adapted from Mathlib/AlgebraicGeometry/Group/Abelian.lean.
Copyright (c) 2026 Andrew Yang. All rights reserved.
Authors of the upstream argument: Andrew Yang, Christian Merten.
-/
module

public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over

/-!
# Proper product rigidity with an integral product

Over an algebraically closed field, a morphism from `V × W` to a separated
locally finite-type scheme, with W proper, factors through V if one W-fibre
is constant and the product is integral. The factor is the original axis
restriction at a specified W-point. The proof is the proper graph argument
and native Stacks 0AH8, followed by equality on a dense open.

There is no group target or source requirement. Integrality of the product
is explicit; this is not the stronger connected nonreduced-parameter result.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

namespace AlgebraicGeometry.Scheme.OverField

universe u

attribute [local instance] Over.cartesianMonoidalCategory

/-- Whole original-map product rigidity. The proper factor is W; V need
only be locally of finite type, with integral product. -/
theorem eq_fst_comp_of_isProper_of_integral_tensor
    {k : Type u} [Field k] [IsAlgClosed k]
    (V W Y : Over (Spec (.of k)))
    [LocallyOfFiniteType V.hom] [IsProper W.hom]
    [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom] [IsIntegral (V ⊗ W).left]
    (v : 𝟙_ (Over (Spec (.of k))) ⟶ V)
    (w : 𝟙_ (Over (Spec (.of k))) ⟶ W)
    (y₀ : 𝟙_ (Over (Spec (.of k))) ⟶ Y)
    (σ : V ⊗ W ⟶ Y) (hleft : (v ▷ W) ≫ σ = toUnit _ ≫ y₀) :
    σ = fst V W ≫ (ρ_ V).inv ≫ V ◁ w ≫ σ := by
  let S := Spec (.of k)
  let point : S := IsLocalRing.closedPoint k
  have hpoint : IsClosed {point} := isClosed_discrete _
  have : Nonempty V.left := ⟨v.left point⟩
  have : Nonempty W.left := ⟨w.left point⟩
  have : LocallyOfFiniteType (V ⊗ W).hom := by dsimp; infer_instance
  have : LocallyOfFiniteType (σ.left ≫ Y.hom) := by rw [Over.w]; infer_instance
  have : JacobsonSpace (V ⊗ W).left := LocallyOfFiniteType.jacobsonSpace (V ⊗ W).hom
  have : Surjective V.hom := ⟨Function.surjective_to_subsingleton _⟩
  have : Surjective W.hom := ⟨Function.surjective_to_subsingleton _⟩
  have : IsProper (fst V W).left := by dsimp; infer_instance
  have : IsSeparated (fst V Y).left := by dsimp; infer_instance
  have : LocallyOfFiniteType (fst V Y).left := by dsimp; infer_instance
  have : Surjective (fst V W).left := by dsimp; infer_instance
  have : IsClosedImmersion v.left := isClosedImmersion_of_comp_eq_id V.hom v.left (Over.w v)
  have : IsClosedImmersion ((lift v y₀).left ≫ (fst V Y).left) := by
    simpa using inferInstanceAs (IsClosedImmersion v.left)
  have : IsClosedImmersion (lift v y₀).left := .of_comp _ (g := (fst V Y).left)
  let γ : V ⊗ W ⟶ V ⊗ Y := lift (fst _ _) σ
  have : IsProper (γ.left ≫ (fst V Y).left) := by simpa [γ]
  have : IsProper γ.left := .of_comp _ (fst V Y).left
  ext1
  have hγzero :
      γ.left '' ((fst V W).left ⁻¹' {v.left point}) ⊆ {(lift v y₀).left point} := by
    rw [Set.image_subset_iff, ← Set.sdiff_eq_empty, ← Set.not_nonempty_iff_eq_empty]
    intro hnonempty
    obtain ⟨c₀, ⟨hc₁, hc₂⟩, hc₃⟩ := nonempty_inter_closedPoints hnonempty <| by
      rw [Set.sdiff_eq_compl_inter, ← Set.image_singleton, ← Set.image_singleton]
      refine (IsOpen.isLocallyClosed ?_).inter (IsClosed.isLocallyClosed ?_)
      · exact (((lift v y₀).left.isClosedMap _ hpoint).preimage γ.left.continuous).isOpen_compl
      · exact (v.left.isClosedMap _ hpoint).preimage (fst V W).left.continuous
    obtain ⟨⟨c, hc⟩, e⟩ := (pointEquivClosedPoint (V ⊗ W).hom).surjective ⟨c₀, hc₃⟩
    obtain rfl : c point = c₀ := congr(($e).1)
    let fc : 𝟙_ (Over S) ⟶ 𝟙_ (Over S) ⊗ W :=
      lift (𝟙 _) (Over.homMk c hc ≫ snd V W)
    have : c ≫ pullback.fst V.hom W.hom = v.left :=
      ext_of_apply_closedPoint_eq V.hom (by simpa) (by simp) (by simpa)
    have H₁ : c = fc.left ≫ (v ▷ W).left := by dsimp; ext <;> simp [fc, S, this]
    have H₂ : fc ≫ v ▷ W ≫ γ = lift v y₀ := by ext1 <;> simp [fc, γ, S, hleft]
    exact hc₂ <| by simp [H₁, H₂, ← Scheme.Hom.comp_apply, Category.assoc, ← Over.comp_left]
  obtain ⟨U, hvU, hfinite⟩ := exists_finite_imageι_comp_morphismRestrict_of_finite_image_preimage
    γ.left (fst V Y).left (v.left point) (by
      dsimp [-Scheme.Hom.comp_base, γ]
      simp only [pullback.lift_fst]
      exact (Set.finite_singleton _).subset hγzero)
  have hfiniteFiber (x : U) :
      ((pullback.fst V.hom Y.hom) ⁻¹' {x.1} ∩ Set.range ⇑γ.left).Finite := by
    refine ((((γ.left.imageι ≫ (fst V Y).left) ∣_ U).finite_preimage_singleton x).image
      (Scheme.Opens.ι _ ≫ γ.left.imageι)).subset ?_
    have : U.ι ⁻¹' {x.1} = {x} := by ext; simp
    rw [← this, ← Set.preimage_comp, ← TopCat.coe_comp, ← Scheme.Hom.comp_base,
      morphismRestrict_ι, ← Category.assoc, Scheme.Hom.comp_base (_ ≫ _) (fst V Y).left,
      TopCat.coe_comp, Set.preimage_comp, Set.image_preimage_eq_inter_range]
    simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι]
    dsimp
    rw [Set.image_preimage_eq_inter_range, Scheme.IdealSheafData.range_subschemeι,
      Scheme.Hom.support_ker, ← Set.inter_assoc, ← Set.preimage_inter,
      Set.singleton_inter_of_mem x.2, IsClosed.closure_eq
      (by exact γ.left.isClosedMap.isClosed_range)]
  refine ext_of_apply_eq Y.hom _
    ((fst V W).left ⁻¹ᵁ U).isOpen.isLocallyClosed
    (((fst V W).left ⁻¹ᵁ U).isOpen.dense ?_) ?_ ?_
  · exact .preimage ⟨_, hvU⟩ (fst V W).left.surjective
  · intro y hyU hy
    have hx : IsClosed {(fst V W).left y} := by simpa using (fst V W).left.isClosedMap _ hy
    let x : 𝟙_ _ ⟶ V := Over.homMk (pointOfClosedPoint V.hom _ hx) (by simp)
    let yw : (V ⊗ W).left := (fst V W ≫ (ρ_ V).inv ≫ V ◁ w).left y
    have hγ : γ.left y = γ.left yw := by
      refine subsingleton_image_closure_of_finite_of_isPreirreducible
        (hx.preimage (fst V W).left.continuous).isLocallyClosed ?_ γ.left.continuous
        γ.left.isClosedMap ((hfiniteFiber ⟨_, hyU⟩).subset (Set.image_subset_iff.mpr fun _ ↦ by
          simp [← Scheme.Hom.comp_apply, -Scheme.Hom.comp_base, γ])) ?_ ?_
      · let α : V ⊗ W ⟶ V ⊗ W := (toUnit V ≫ x) ⊗ₘ 𝟙 W
        convert! ((IrreducibleSpace.isIrreducible_univ _).image α.left
          α.left.continuous.continuousOn).isPreirreducible
        rw [Over.tensorHom_left]
        simp [Set.range_comp, Scheme.Pullback.range_map, x]
      · exact ⟨y, subset_closure (by simp), rfl⟩
      · refine ⟨yw, subset_closure ?_, ?_⟩
        · simp [yw, ← Scheme.Hom.comp_apply, -Scheme.Hom.comp_base]
        · rfl
    have hcomp : γ ≫ snd V Y = σ := by simp [γ]
    have hmap := congrArg (fun z => (snd V Y).left z) hγ
    change (γ ≫ snd V Y).left y = (γ ≫ snd V Y).left yw at hmap
    rw [hcomp] at hmap
    exact hmap.trans (by simp only [yw, Over.comp_left, Scheme.Hom.comp_apply])
  · simp

end AlgebraicGeometry.Scheme.OverField
