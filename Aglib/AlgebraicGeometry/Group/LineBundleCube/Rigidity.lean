/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
/-
The graph argument extends Aglib's Group/PointedMorphism.lean, itself adapted
from Mathlib/AlgebraicGeometry/Group/Abelian.lean.
Copyright (c) 2026 Andrew Yang. All rights reserved.
Authors of the upstream graph argument: Andrew Yang, Christian Merten.
-/
module

public import Mathlib.AlgebraicGeometry.Group.Abelian
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over

/-!
# Rigidity with a separated Picard-scheme target

The graph proof of product rigidity only needs the target to be separated and
locally of finite type. Properness belongs to the source: the composite of the
graph with the first projection is proper, which is the exact input to Stacks
0AH8 (`exists_finite_imageι_comp_morphismRestrict_of_finite_image_preimage`).
This removes the unnecessary proper-target hypothesis for the Picard-scheme
consumer. Equality is proved as an equality of scheme morphisms, not merely on
points. The source square is integral in the algebraically closed argument;
the field-level homomorphism theorem retains geometric integrality.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj
open AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Group.PointedMorphism

universe u
variable {K : Type u} [Field K]
attribute [local instance] Over.cartesianMonoidalCategory

/-- Product rigidity for a proper source and a separated locally finite-type target.
The conclusion is equality of the original scheme morphisms, hence remains
true after pullback by every test-scheme morphism. -/
theorem rigidity_of_integral_tensor_of_isAlgClosed_of_isSeparated [IsAlgClosed K]
    (G H : Over (Spec (.of K))) [GrpObj G] [GrpObj H]
    [IsProper G.hom] [IsSeparated H.hom] [LocallyOfFiniteType H.hom] [IsIntegral (G ⊗ G).left]
    (σ : G ⊗ G ⟶ H)
    (hleft : (η[G] ▷ G) ≫ σ = toUnit _ ≫ η[H])
    (hright : (G ◁ η[G]) ≫ σ = toUnit _ ≫ η[H]) :
    σ = toUnit _ ≫ η[H] := by
  let S := Spec (.of K)
  let point : S := IsLocalRing.closedPoint K
  have hpoint : IsClosed {point} := isClosed_discrete _
  have : Nonempty G.left := ⟨η[G].left point⟩
  have : IsProper (G ⊗ G).hom := by dsimp; infer_instance
  have : IsProper (σ.left ≫ H.hom) := by rw [Over.w]; infer_instance
  have : JacobsonSpace (G ⊗ G).left := LocallyOfFiniteType.jacobsonSpace (Y := Spec _) (G ⊗ G).hom
  have : Surjective G.hom := ⟨Function.surjective_to_subsingleton (α := G.left) (β := Spec _) _⟩
  have : IsProper (fst G G).left := by dsimp; infer_instance
  have : IsSeparated (fst G H).left := by dsimp; infer_instance
  have : LocallyOfFiniteType (fst G H).left := by dsimp; infer_instance
  have : Surjective (fst G G).left := by dsimp; infer_instance
  have : IsClosedImmersion ((lift η[G] η[H]).left ≫ (fst G H).left) := by
    simpa using inferInstanceAs (IsClosedImmersion η[G].left)
  have : IsClosedImmersion (lift η[G] η[H]).left := .of_comp _ (g := (fst G H).left)
  let γ : G ⊗ G ⟶ G ⊗ H := lift (fst _ _) σ
  have : IsProper (γ.left ≫ (fst G H).left) := by simpa [γ]
  have : IsProper γ.left := .of_comp _ (fst G H).left
  ext1
  have hγzero :
      γ.left '' ((fst G G).left ⁻¹' {η[G].left point}) ⊆ {(lift η[G] η[H]).left point} := by
    rw [Set.image_subset_iff, ← Set.sdiff_eq_empty, ← Set.not_nonempty_iff_eq_empty]
    intro hnonempty
    obtain ⟨c₀, ⟨hc₁, hc₂⟩, hc₃⟩ := nonempty_inter_closedPoints hnonempty <| by
      rw [Set.sdiff_eq_compl_inter, ← Set.image_singleton, ← Set.image_singleton];
      refine (IsOpen.isLocallyClosed ?_).inter (IsClosed.isLocallyClosed ?_)
      · exact (((lift η[G] η[H]).left.isClosedMap _ hpoint).preimage γ.left.continuous).isOpen_compl
      · exact (η[G].left.isClosedMap _ hpoint).preimage (fst G G).left.continuous
    obtain ⟨⟨c, hc⟩, e⟩ := (pointEquivClosedPoint (G ⊗ G).hom).surjective ⟨c₀, hc₃⟩
    obtain rfl : c point = c₀ := congr(($e).1)
    let fc : 𝟙_ (Over S) ⟶ 𝟙_ (Over S) ⊗ G := lift (𝟙 _) (Over.homMk c hc ≫ snd G G)
    have : c ≫ pullback.fst G.hom G.hom = η[G].left :=
      ext_of_apply_closedPoint_eq G.hom (by simpa) (by simp) (by simpa)
    have H₁ : c = fc.left ≫ (η[G] ▷ G).left := by dsimp; ext <;> simp [fc, S, this]
    have H₂ : fc ≫ η ▷ G ≫ γ = lift η[G] η[H] := by ext1 <;> simp [fc, γ, S, hleft]
    exact hc₂ <| by simp [H₁, H₂, ← Scheme.Hom.comp_apply, Category.assoc, ← Over.comp_left]
  -- Since the image of `y ↦ γ(e, y)` is finite, by Zariski Main, there exists an open
  -- `1 ∈ U ⊆ G` such that `γ ∣_ U` factors through a finite scheme over `U`.
  obtain ⟨U, hηU, hfinite⟩ := exists_finite_imageι_comp_morphismRestrict_of_finite_image_preimage
    γ.left (fst G H).left (η[G].left point) (by
      dsimp [-Scheme.Hom.comp_base, γ]
      simp only [pullback.lift_fst]
      exact (Set.finite_singleton _).subset hγzero)
  have hfiniteFiber (x : U) :
      ((pullback.fst G.hom H.hom) ⁻¹' {x.1} ∩ Set.range ⇑γ.left).Finite := by
    refine ((((γ.left.imageι ≫ (fst G H).left) ∣_ U).finite_preimage_singleton x).image
      (Scheme.Opens.ι _ ≫ γ.left.imageι)).subset ?_
    have : U.ι ⁻¹' {x.1} = {x} := by ext; simp
    rw [← this, ← Set.preimage_comp, ← TopCat.coe_comp, ← Scheme.Hom.comp_base,
      morphismRestrict_ι, ← Category.assoc, Scheme.Hom.comp_base (_ ≫ _) (fst G H).left,
      TopCat.coe_comp, Set.preimage_comp, Set.image_preimage_eq_inter_range]
    simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι]
    dsimp
    rw [Set.image_preimage_eq_inter_range, Scheme.IdealSheafData.range_subschemeι,
      Scheme.Hom.support_ker, ← Set.inter_assoc, ← Set.preimage_inter,
      Set.singleton_inter_of_mem x.2, IsClosed.closure_eq
      (by exact γ.left.isClosedMap.isClosed_range)]
  -- It suffices to check set-theoretic equality on closed points of `U ×[k] G`.
  refine ext_of_apply_eq H.hom _
    ((fst G G).left ⁻¹ᵁ U).isOpen.isLocallyClosed
    (((fst G G).left ⁻¹ᵁ U).isOpen.dense ?_) ?_ ?_
  · exact .preimage ⟨_, hηU⟩ (fst G G).left.surjective
  · intro y hyU hy
    have hx : IsClosed {(fst G G).left y} := by simpa using (fst G G).left.isClosedMap _ hy
    let x : 𝟙_ _ ⟶ G := Over.homMk (pointOfClosedPoint G.hom _ hx) (by simp)
    let xe : (G ⊗ G).left := (fst G G ≫ (ρ_ _).inv ≫ G ◁ η[G]).left y
    have : γ.left y = γ.left xe := by
      -- By the choice of `U`, the set `γ({y} ×[k] G)` is finite and hence, by irreducibility,
      -- a singleton.
      refine subsingleton_image_closure_of_finite_of_isPreirreducible
        (hx.preimage (fst G G).left.continuous).isLocallyClosed ?_ γ.left.continuous
        γ.left.isClosedMap ((hfiniteFiber ⟨_, hyU⟩).subset (Set.image_subset_iff.mpr fun _ ↦ by
          simp [← Scheme.Hom.comp_apply, -Scheme.Hom.comp_base, γ])) ?_ ?_
      · let α : G ⊗ G ⟶ G ⊗ G := toUnit _ ≫ x ⊗ₘ 𝟙 _
        convert!
          ((IrreducibleSpace.isIrreducible_univ _).image α.left
              α.left.continuous.continuousOn).isPreirreducible
        rw [Over.tensorHom_left]
        simp [Set.range_comp, Scheme.Pullback.range_map, x]
      · exact ⟨y, subset_closure (by simp), rfl⟩
      · refine ⟨xe, subset_closure ?_, ?_⟩
        · simp [xe, ← Scheme.Hom.comp_apply, -Scheme.Hom.comp_base]
        · rfl
    convert! congr((snd G H).left $this) using 1
    · simp [γ, ← Scheme.Hom.comp_apply]
    · have he : fst G G ≫ (ρ_ G).inv ≫ G ◁ η[G] ≫ γ ≫ snd G H =
          toUnit _ ≫ η[H] := by simp [γ, hright]
      exact congr(($he).left y).symm
  · simp

/-- Over an algebraically closed field, a pointed morphism from a proper group
with integral square to a separated locally finite-type group is a homomorphism. -/
theorem isMonHom_of_integral_tensor_of_isAlgClosed_of_isSeparated [IsAlgClosed K]
    (G H : Over (Spec (.of K))) [GrpObj G] [GrpObj H]
    [IsProper G.hom] [IsSeparated H.hom] [LocallyOfFiniteType H.hom] [IsIntegral (G ⊗ G).left]
    (f : G ⟶ H) (hf : η[G] ≫ f = η[H]) : IsMonHom f := by
  let σ : G ⊗ G ⟶ H :=
    (μ[G] ≫ f) / ((fst G G ≫ f) * (snd G G ≫ f))
  have hleft : (η[G] ▷ G) ≫ σ = toUnit _ ≫ η[H] := by
    simp [σ, GrpObj.comp_div, comp_mul, hf]
    simp [one_eq_one, leftUnitor_hom]
  have hright : (G ◁ η[G]) ≫ σ = toUnit _ ≫ η[H] := by
    simp [σ, GrpObj.comp_div, comp_mul, hf]
    simp [one_eq_one, rightUnitor_hom]
  have hσ := rigidity_of_integral_tensor_of_isAlgClosed_of_isSeparated G H σ hleft hright
  have hmul : μ[G] ≫ f = (fst G G ≫ f) * (snd G G ≫ f) := by
    apply div_eq_one.mp
    exact hσ
  exact ⟨hf, by simpa [Hom.mul_def, tensorHom_def] using hmul⟩

/-- A pointed morphism from a proper geometrically integral group scheme over
a field to a separated locally finite-type group scheme is a homomorphism.
Faithful scalar extension descends the actual group-law equation. -/
theorem isMonHom_of_geometricallyIntegral_of_isSeparated
    (G H : Over (Spec (.of K))) [GrpObj G] [GrpObj H]
    [IsProper G.hom] [IsSeparated H.hom] [LocallyOfFiniteType H.hom] [GeometricallyIntegral G.hom]
    (f : G ⟶ H) (hf : η[G] ≫ f = η[H]) : IsMonHom f := by
  let k := Spec.map (CommRingCat.ofHom <| algebraMap K (AlgebraicClosure K))
  let P := Over.pullback k
  let G' := P.obj G
  let H' := P.obj H
  have : IsProper G'.hom := by dsimp [G', P]; infer_instance
  have : IsSeparated H'.hom := by dsimp [H', P]; infer_instance
  have : LocallyOfFiniteType H'.hom := by dsimp [H', P]; infer_instance
  have : IsIntegral (G' ⊗ G').left := by dsimp [G', P]; infer_instance
  let : GrpObj G' := Functor.grpObjObj
  let : GrpObj H' := Functor.grpObjObj
  have hf' : η[G'] ≫ P.map f = η[H'] := by
    change (Functor.LaxMonoidal.ε P ≫ P.map η[G]) ≫ P.map f =
      Functor.LaxMonoidal.ε P ≫ P.map η[H]
    simp only [Category.assoc, ← Functor.map_comp, hf]
  have hmap := isMonHom_of_integral_tensor_of_isAlgClosed_of_isSeparated G' H' (P.map f) hf'
  refine ⟨hf, P.map_injective ?_⟩
  rw [← cancel_epi (Functor.Monoidal.μIso P G G).hom]
  simpa using hmap.mul_hom

/-- The square of a proper geometrically integral scheme over a field is
geometrically integral. The proof compares the same chosen tensor square
after field base change. No group structure is needed. -/
theorem geometricallyIntegral_tensor_self
    (G : Over (Spec (.of K))) [IsProper G.hom] [GeometricallyIntegral G.hom] :
    GeometricallyIntegral (G ⊗ G).hom := by
  constructor
  intro L _ y Z f g hs
  let P := Over.pullback y
  have : IsIntegral (P.obj G ⊗ P.obj G).left := by dsimp [P]; infer_instance
  have : IsIntegral (pullback (G ⊗ G).hom y) :=
    IsIntegral.of_isIso (Functor.Monoidal.μIso P G G).hom.left
  exact IsIntegral.of_isIso hs.isoPullback.inv

/-- A morphism from the square of a proper geometrically integral group to a
separated locally finite-type group, trivial on both axes, is the original
constant identity morphism. The conclusion can be precomposed by arbitrary
test schemes, whether reduced or not. -/
theorem rigidity_of_geometricallyIntegral_of_isSeparated
    (G H : Over (Spec (.of K))) [GrpObj G] [GrpObj H]
    [IsProper G.hom] [GeometricallyIntegral G.hom]
    [IsSeparated H.hom] [LocallyOfFiniteType H.hom]
    (σ : G ⊗ G ⟶ H)
    (hleft : lift (𝟙 G) (1 : G ⟶ G) ≫ σ = 1)
    (hright : lift (1 : G ⟶ G) (𝟙 G) ≫ σ = 1) : σ = 1 := by
  have hη : η[G] ≫ lift (𝟙 G) (1 : G ⟶ G) = η[G ⊗ G] := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, lift_fst, Category.comp_id]
      exact (IsMonHom.one_hom (fst G G)).symm
    · rw [Category.assoc, lift_snd]
      calc
        η[G] ≫ (1 : G ⟶ G) = η[G] := by
          simp only [Hom.one_def, ← Category.assoc, comp_toUnit, toUnit_unit,
            Category.id_comp]
        _ = η[G ⊗ G] ≫ snd G G := (IsMonHom.one_hom (snd G G)).symm
  have hunit : η[G ⊗ G] ≫ σ = η[H] := by
    rw [← hη, Category.assoc, hleft]
    simp only [Hom.one_def, ← Category.assoc, comp_toUnit, toUnit_unit,
      Category.id_comp]
  have : IsProper (G ⊗ G).hom := by dsimp; infer_instance
  have : GeometricallyIntegral (G ⊗ G).hom := geometricallyIntegral_tensor_self G
  have : IsMonHom σ :=
    isMonHom_of_geometricallyIntegral_of_isSeparated (G ⊗ G) H σ hunit
  have hprod : lift (fst G G) (1 : G ⊗ G ⟶ G) *
      lift (1 : G ⊗ G ⟶ G) (snd G G) = 𝟙 (G ⊗ G) := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [MonObj.mul_comp, lift_fst, lift_fst, _root_.mul_one, Category.id_comp]
    · rw [MonObj.mul_comp, lift_snd, lift_snd, _root_.one_mul, Category.id_comp]
  have hl : lift (fst G G) (1 : G ⊗ G ⟶ G) ≫ σ = 1 := by
    have he : lift (fst G G) (1 : G ⊗ G ⟶ G) =
        fst G G ≫ lift (𝟙 G) (1 : G ⟶ G) := by
      apply CartesianMonoidalCategory.hom_ext <;>
        simp only [Category.assoc, lift_fst, lift_snd, Category.comp_id, MonObj.comp_one]
    rw [he, Category.assoc, hleft, MonObj.comp_one]
  have hr : lift (1 : G ⊗ G ⟶ G) (snd G G) ≫ σ = 1 := by
    have he : lift (1 : G ⊗ G ⟶ G) (snd G G) =
        snd G G ≫ lift (1 : G ⟶ G) (𝟙 G) := by
      apply CartesianMonoidalCategory.hom_ext <;>
        simp only [Category.assoc, lift_fst, lift_snd, Category.comp_id, MonObj.comp_one]
    rw [he, Category.assoc, hright, MonObj.comp_one]
  calc
    σ = 𝟙 (G ⊗ G) ≫ σ := (Category.id_comp σ).symm
    _ = (lift (fst G G) (1 : G ⊗ G ⟶ G) *
        lift (1 : G ⊗ G ⟶ G) (snd G G)) ≫ σ := by rw [hprod]
    _ = 1 := by rw [MonObj.mul_comp, hl, hr, _root_.mul_one]


end AlgebraicGeometry.Scheme.Group.PointedMorphism
