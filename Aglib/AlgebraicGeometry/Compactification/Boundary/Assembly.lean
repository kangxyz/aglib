/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Compactification.Boundary.NormalizedModels
public import Aglib.AlgebraicGeometry.Compactification.Boundary.NormalizedAssembly
public import Aglib.AlgebraicGeometry.Compactification.Boundary.InitialEmpty

/-!
# Boundary control from a finite open cover

Normalize the original proper models, apply boundary separation to the actual
finite-product image, and concatenate the genuine admissible sequences. This
is the boundary-control input for the Noetherian Nagata construction.
-/

@[expose] public noncomputable section
set_option autoImplicit false
open CategoryTheory Limits TopologicalSpace
universe u

namespace AlgebraicGeometry.Scheme.Compactification

private theorem exists_normalized_preimage_open
    {Y X S : Scheme.{u}} [IsNoetherian Y]
    (pY : Y ⟶ S) [IsSeparated pY]
    (pX : X ⟶ S) [IsSeparated pX] [QuasiCompact pX] [LocallyOfFiniteType pX]
    (V : Y.Opens) (hV : Dense (V : Set Y))
    (q : V.toScheme ⟶ X) [IsProper q]
    (hq : V.ι ≫ pY = q ≫ pX) :
    ∃ (Y' : Scheme.{u}) (β : Y' ⟶ Y)
      (hw : (β ⁻¹ᵁ V).ι ≫ (β ≫ pY) = ((β ∣_ V) ≫ q) ≫ pX),
      Blowup.AdmissibleSequence V β ∧ IsProper β ∧ IsIso (β ∣_ V) ∧
      IsClosedImmersion (pullback.lift (β ⁻¹ᵁ V).ι ((β ∣_ V) ≫ q) hw) := by
  obtain ⟨Y', β, e, hew, hseq, hp, hiso, _hopen, _hdense, heβ, hc⟩ :=
    exists_closedGraph_of_proper_dense_open pY pX V hV q hq.symm
  let : IsIso (β ∣_ V) := hiso
  let : IsClosedImmersion (pullback.lift e q hew) := hc
  have hre : (β ∣_ V) ≫ e = (β ⁻¹ᵁ V).ι := by
    rw [β.eq_inv_restrict_comp V e heβ, IsIso.hom_inv_id_assoc]
  have hw : (β ⁻¹ᵁ V).ι ≫ (β ≫ pY) = ((β ∣_ V) ≫ q) ≫ pX := by
    rw [← Category.assoc, ← morphismRestrict_ι β V, Category.assoc, hq, Category.assoc]
  have he : pullback.lift (β ⁻¹ᵁ V).ι ((β ∣_ V) ≫ q) hw =
      (β ∣_ V) ≫ pullback.lift e q hew := by
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst]
      exact hre.symm
    · simp only [Category.assoc, pullback.lift_snd]
  refine ⟨Y', β, hw, hseq, hp, hiso, ?_⟩
  rw [he]
  infer_instance

/-- Boundary control for a genuine finite open cover of the original scheme.
The closed graphs and the initial empty intersection are constructed, not
assumed. The output consists of actual protected admissible sequences. -/
theorem exists_finite_boundary_modification
    {S X : Scheme.{u}} [IsNoetherian S] {U : Over S} [IsNoetherian U.left]
    {n : ℕ} (C : Fin (n + 1) → Over S) [∀ i, IsProper (C i).hom]
    (j : ∀ i, U ⟶ C i) [IsOpenImmersion (j 0).left]
    (pX : X ⟶ S) [IsSeparated pX] [QuasiCompact pX] [LocallyOfFiniteType pX]
    (V : ∀ i, (C i).left.Opens) (hV : ∀ i, Dense (V i : Set (C i).left))
    (q : ∀ i, (V i).toScheme ⟶ X) [∀ i, IsProper (q i)]
    (hq : ∀ i, (V i).ι ≫ (C i).hom = q i ≫ pX)
    (a : ∀ i, U.left ⟶ (V i).toScheme)
    (ha : ∀ i, a i ≫ (V i).ι = (j i).left)
    (g : U.left ⟶ X) (hag : ∀ i, a i ≫ q i = g)
    (W : Fin (n + 1) → X.Opens) (hcover : ∀ x : X, ∃ i, x ∈ W i) :
    ∃ (C' : Fin (n + 1) → Over S) (β : ∀ i, C' i ⟶ C i)
      (j' : ∀ i, U ⟶ C' i),
      (∀ i, Blowup.AdmissibleSequence (V i) (β i).left) ∧
      (∀ i, IsProper (C' i).hom) ∧ (∀ i, j' i ≫ β i = j i) ∧
      IsImmersion (j' 0).left ∧
      (⋂ i, ((finiteProductOverLift C' j').left.imageι ≫
        (finiteProductOverπ C' i).left) ⁻¹'
          closure ((β i).left ⁻¹'
            ((V i).ι '' (q i ⁻¹' (W i : Set X)ᶜ)))) = ∅ := by
  classical
  let : ∀ i, IsNoetherian (C i).left := fun i => by
    let : IsLocallyNoetherian (C i).left := LocallyOfFiniteType.isLocallyNoetherian (C i).hom
    let : CompactSpace (C i).left := QuasiCompact.compactSpace_of_compactSpace (C i).hom
    exact ⟨⟩
  choose Y b hb hseq hp hiso hc using fun i =>
    exists_normalized_preimage_open (C i).hom pX (V i) (hV i) (q i) (hq i)
  let : ∀ i, IsProper (b i) := hp
  let : ∀ i, IsIso (b i ∣_ V i) := hiso
  let N : Fin (n + 1) → Over S := fun i => Over.mk (b i ≫ (C i).hom)
  let δ : ∀ i, N i ⟶ C i := fun i => Over.homMk (b i) rfl
  let Vn : ∀ i, (N i).left.Opens := fun i => b i ⁻¹ᵁ V i
  let qn : ∀ i, (Vn i).toScheme ⟶ X := fun i => (b i ∣_ V i) ≫ q i
  let an : ∀ i, U.left ⟶ (Vn i).toScheme := fun i => a i ≫ inv (b i ∣_ V i)
  have hqb : ∀ i, (Vn i).ι ≫ (N i).hom = qn i ≫ pX := hb
  let : ∀ i, IsClosedImmersion (pullback.lift (Vn i).ι (qn i) (hqb i)) := hc
  have hanb : ∀ i, an i ≫ (Vn i).ι ≫ b i = (j i).left := by
    intro i
    dsimp only [an, Vn]
    rw [← morphismRestrict_ι (b i) (V i), Category.assoc, IsIso.inv_hom_id_assoc]
    exact ha i
  let jn : ∀ i, U ⟶ N i := fun i => Over.homMk (an i ≫ (Vn i).ι) (by
    change (an i ≫ (Vn i).ι) ≫ b i ≫ (C i).hom = U.hom
    rw [Category.assoc, ← Category.assoc (Vn i).ι, ← Category.assoc, hanb i]
    exact (j i).w)
  have hjn : ∀ i, jn i ≫ δ i = j i := by
    intro i
    apply Over.OverMorphism.ext
    exact (Category.assoc _ _ _).trans (hanb i)
  let : ∀ i, IsProper (N i).hom := fun i => inferInstanceAs (IsProper (b i ≫ (C i).hom))
  let : IsImmersion ((jn 0).left ≫ (δ 0).left) := by
    have he := congrArg (fun z => z.left) (hjn 0)
    change (jn 0).left ≫ (δ 0).left = (j 0).left at he
    rw [he]
    infer_instance
  let : IsImmersion (jn 0).left := IsImmersion.of_comp (jn 0).left (δ 0).left
  let : IsOpenImmersion (a 0 ≫ (V 0).ι) := by rw [ha 0]; infer_instance
  let : IsOpenImmersion (a 0) := IsOpenImmersion.of_comp (a 0) (V 0).ι
  let : IsOpenImmersion (jn 0).left :=
    inferInstanceAs (IsOpenImmersion ((a 0 ≫ inv (b 0 ∣_ V 0)) ≫ (Vn 0).ι))
  have hagn : ∀ i, an i ≫ qn i = g := by
    intro i
    dsimp only [an, qn]
    rw [Category.assoc, IsIso.inv_hom_id_assoc]
    exact hag i
  let f := (finiteProductOverLift N jn).left
  let M := f.image
  let s : U.left ⟶ M := f.toImage
  let π : ∀ i, M ⟶ (N i).left := fun i => f.imageι ≫ (finiteProductOverπ N i).left
  let pM : M ⟶ S := f.imageι ≫ (finiteProductOver N).hom
  let : IsNoetherian M := finiteProductOverLift_image_isNoetherian N jn
  let : IsSchemeTheoreticallyDominant s := isSchemeTheoreticallyDominant_toImage f
  have hsπ : ∀ i, s ≫ π i = an i ≫ (Vn i).ι := by
    intro i
    dsimp only [π]
    rw [← Category.assoc, Scheme.Hom.toImage_imageι]
    exact congrArg (fun z => z.left) (finiteProductOverLift_π N jn i)
  have hπ : ∀ i, π i ≫ (N i).hom = pM := by
    intro i
    simp only [π, pM, Category.assoc, finiteProductOverπ_hom]
  let F : ∀ i, Closeds (Vn i).toScheme := fun i =>
    ⟨qn i ⁻¹' (W i : Set X)ᶜ, (W i).isOpen.isClosed_compl.preimage (qn i).continuous⟩
  have hempty : (⋂ i, π i ⁻¹' ((Vn i).ι '' (F i : Set (Vn i).toScheme))) = ∅ :=
    iInter_preimage_boundary_eq_empty (fun i => (N i).hom) pM pX π hπ Vn qn hqb
      s g an (fun i => (hsπ i).symm) hagn W hcover
  obtain ⟨C', β, j', hβ, hp', hj', himm, hboundary⟩ :=
    exists_normalized_finite_boundary_modification N jn pX Vn qn hqb an
      (fun _ => rfl) g hagn F hempty
  refine ⟨C', (fun i => β i ≫ δ i), j', ?_, hp', ?_, himm, ?_⟩
  · intro i
    exact (hseq i).comp (hβ i)
  · intro i
    rw [← Category.assoc, hj' i, hjn i]
  · have hsets : ∀ i, (Vn i).ι '' (F i : Set (Vn i).toScheme) =
        b i ⁻¹' ((V i).ι '' (q i ⁻¹' (W i : Set X)ᶜ)) := by
      intro i
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        refine ⟨(b i ∣_ V i) z, hz, ?_⟩
        exact congrArg (fun t : (Vn i).toScheme ⟶ (C i).left => t z)
          (morphismRestrict_ι (b i) (V i))
      · rintro ⟨z, hz, he⟩
        let y' : (Vn i).toScheme := ⟨y, by change b i y ∈ V i; exact he ▸ z.property⟩
        have hy : (b i ∣_ V i) y' = z := by
          apply (V i).ι.isOpenEmbedding.injective
          exact (congrArg (fun t : (Vn i).toScheme ⟶ (C i).left => t y')
            (morphismRestrict_ι (b i) (V i))).trans he.symm
        exact ⟨y', by change q i ((b i ∣_ V i) y') ∉ W i; rw [hy]; exact hz, rfl⟩
    change (⋂ i, ((finiteProductOverLift C' j').left.imageι ≫
      (finiteProductOverπ C' i).left) ⁻¹' closure
        (((β i).left ≫ b i) ⁻¹' ((V i).ι '' (q i ⁻¹' (W i : Set X)ᶜ)))) = ∅
    simpa only [hsets, Scheme.Hom.comp_base, TopCat.coe_comp, Set.preimage_comp] using hboundary

end AlgebraicGeometry.Scheme.Compactification
