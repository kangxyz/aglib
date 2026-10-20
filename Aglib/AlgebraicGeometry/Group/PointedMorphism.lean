/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
/-
The product-rigidity proof adapts the graph argument in
Mathlib/AlgebraicGeometry/Group/Abelian.lean.
Copyright (c) 2026 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in mathlib's LICENSE file.
Authors of the upstream graph argument: Andrew Yang, Christian Merten.
-/
module

public import Mathlib.AlgebraicGeometry.Group.Abelian
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over

/-!
# Pointed morphisms of proper group schemes

Source: `K2-018#prop:k2018-arithmetic-characters`,
`research/exposes/K2/018/expose.tex`, lines 341–445 at revision
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`, SHA256
`e716cfb3c6eaba82370c5b46b806df5705ad4583df0ed41b1a576e419f3bd299`.
This is the source identity of the `GeometryBackground.pointedMorphism`
consumer in `PointedIsogenies.lean`.

The main theorem proves that every origin-preserving scheme morphism between
proper group schemes over a field is a homomorphism when the source is
geometrically integral. The proof uses product rigidity over an algebraic
closure, then faithful base change to recover equality of scheme morphisms.
No group-homomorphism or rigidity conclusion is assumed.

Coverage is narrower than `GeometryBackground.pointedMorphism`: deriving
geometric integrality from that consumer's smooth geometrically connected
curve hypotheses is still required. Thus this module does not instantiate
that field. The target need not be smooth, connected, or a curve.

The rigidity argument is adapted from mathlib's
`isCommMonObj_of_isProper_of_isIntegral_tensorObj_of_isAlgClosed`,
`Mathlib/AlgebraicGeometry/Group/Abelian.lean`, at mathlib revision `d13f23b`.
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

/-- Auxiliary product-rigidity statement for the source claim and snapshot above.
For a proper group scheme with integral square over an algebraically closed
field, a morphism to a proper group scheme that is the identity section on
both coordinate axes is the identity section everywhere. -/
theorem rigidity_of_integral_tensor_of_isAlgClosed [IsAlgClosed K]
    (G H : Over (Spec (.of K))) [GrpObj G] [GrpObj H]
    [IsProper G.hom] [IsProper H.hom] [IsIntegral (G ⊗ G).left]
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
  have : IsProper (fst G H).left := by dsimp; infer_instance
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

/-- Algebraically closed case of `K2-018#prop:k2018-arithmetic-characters`
(source snapshot above), with the additional hypothesis that the square of
the source group scheme is integral. -/
theorem isMonHom_of_integral_tensor_of_isAlgClosed [IsAlgClosed K]
    (G H : Over (Spec (.of K))) [GrpObj G] [GrpObj H]
    [IsProper G.hom] [IsProper H.hom] [IsIntegral (G ⊗ G).left]
    (f : G ⟶ H) (hf : η[G] ≫ f = η[H]) : IsMonHom f := by
  let σ : G ⊗ G ⟶ H :=
    (μ[G] ≫ f) / ((fst G G ≫ f) * (snd G G ≫ f))
  have hleft : (η[G] ▷ G) ≫ σ = toUnit _ ≫ η[H] := by
    simp [σ, GrpObj.comp_div, comp_mul, hf]
    simp [one_eq_one, leftUnitor_hom]
  have hright : (G ◁ η[G]) ≫ σ = toUnit _ ≫ η[H] := by
    simp [σ, GrpObj.comp_div, comp_mul, hf]
    simp [one_eq_one, rightUnitor_hom]
  have hσ := rigidity_of_integral_tensor_of_isAlgClosed G H σ hleft hright
  have hmul : μ[G] ≫ f = (fst G G ≫ f) * (snd G G ≫ f) := by
    apply div_eq_one.mp
    exact hσ
  exact ⟨hf, by simpa [Hom.mul_def, tensorHom_def] using hmul⟩

/-- The pointed proper-group morphism implication used in
`K2-018#prop:k2018-arithmetic-characters` (source snapshot above), proved under
the additional hypothesis that the source is geometrically integral.
The input is a scheme morphism preserving the identity section; its group
homomorphism property is the conclusion. -/
theorem isMonHom_of_geometricallyIntegral
    (G H : Over (Spec (.of K))) [GrpObj G] [GrpObj H]
    [IsProper G.hom] [IsProper H.hom] [GeometricallyIntegral G.hom]
    (f : G ⟶ H) (hf : η[G] ≫ f = η[H]) : IsMonHom f := by
  let k := Spec.map (CommRingCat.ofHom <| algebraMap K (AlgebraicClosure K))
  let P := Over.pullback k
  let G' := P.obj G
  let H' := P.obj H
  have : IsProper G'.hom := by dsimp [G', P]; infer_instance
  have : IsProper H'.hom := by dsimp [H', P]; infer_instance
  have : IsIntegral (G' ⊗ G').left := by dsimp [G', P]; infer_instance
  let : GrpObj G' := Functor.grpObjObj
  let : GrpObj H' := Functor.grpObjObj
  have hf' : η[G'] ≫ P.map f = η[H'] := by
    change (Functor.LaxMonoidal.ε P ≫ P.map η[G]) ≫ P.map f =
      Functor.LaxMonoidal.ε P ≫ P.map η[H]
    simp only [Category.assoc, ← Functor.map_comp, hf]
  have hmap := isMonHom_of_integral_tensor_of_isAlgClosed G' H' (P.map f) hf'
  refine ⟨hf, P.map_injective ?_⟩
  rw [← cancel_epi (Functor.Monoidal.μIso P G G).hom]
  simpa using hmap.mul_hom

end AlgebraicGeometry.Scheme.Group.PointedMorphism

/- Migration source: R5Lab/Aglib/AlgebraicGeometry/Group/PointedMorphism.lean
Frozen packet R5 f8a3314ddecffcada2ec721d26d56a937bed9690.
SHA-256 035eac63445e6dd364c92549e37f1dc1d2bd52249a255fb6bd1445150a649c93.
Native names and imports replace source wrappers; stated conditions and maps are retained. -/
