/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Descent of open subschemes along fppf coverings

Let `f i : X i ⟶ Y` be a jointly surjective family of morphisms of schemes that are open maps,
and let `U i` be open subsets of the `X i` whose pullbacks to the fibre products agree:
`pullback.fst (f i) (f j) ⁻¹ᵁ U i = pullback.snd (f i) (f j) ⁻¹ᵁ U j`. Then the union `V` of the
open images `f i '' U i` is the unique open subset of `Y` with `f i ⁻¹ᵁ V = U i` for every `i`
(`existsUnique_preimage_eq_of_isOpenMap`). The inclusion `f i ⁻¹ᵁ V ⊆ U i` uses that the points of
a fibre product of schemes surject onto the fibre product of the underlying sets (Mathlib's
`Scheme.Pullback.exists_preimage_pullback`).

Flat morphisms locally of finite presentation are open (Mathlib's `UniversallyOpen.of_flat`), so
this applies to fppf coverings:

* `opensPresheaf`: the presheaf `X ↦ X.Opens`, `f ↦ (f ⁻¹ᵁ ·)` on schemes;
* `isSheaf_opensPresheaf_fppfTopology`: it is a sheaf for the fppf topology;
* `existsUnique_preimage_eq_of_flat_of_surjective`: for one flat surjective morphism `f`, locally
  of finite presentation, an open `U` of the source with equal pullbacks along the two projections
  of `X ×_Y X` is `f ⁻¹ᵁ V` for a unique open `V` of the target, namely the image of `U`
  (`preimage_imageOpens_eq_of_flat`).

Stacks Project, Tag 03N0: for an fpqc covering `{f_i : T_i → T}` and opens `W_i ⊂ T_i` with
`pr_0⁻¹(W_i) = pr_1⁻¹(W_j)` on `T_i ×_T T_j`, there is a unique open `W ⊂ T` with
`W_i = f_i⁻¹(W)`. Its proof takes `W = ⋃ f_i(W_i)` and obtains openness from Tag 02JY (a
quasi-compact, surjective, flat morphism is submersive). For fppf coverings, which are fpqc
coverings, openness is immediate because flat morphisms locally of finite presentation are open;
this is the route here.
-/

@[expose] public section

universe u

open CategoryTheory Opposite Limits

namespace AlgebraicGeometry.Scheme

/-- The presheaf of open subsets on schemes: `X ↦ X.Opens`, with the preimage maps `f ⁻¹ᵁ ·`. -/
@[simps]
def opensPresheaf : Scheme.{u}ᵒᵖ ⥤ Type u where
  obj X := X.unop.Opens
  map f := TypeCat.ofHom fun U ↦ f.unop ⁻¹ᵁ U
  map_id _ := rfl
  map_comp _ _ := rfl

variable {X Y : Scheme.{u}}

/-- The image of an open subset under a morphism of schemes that is an open map: Mathlib's
`IsOpenMap.functor` at `U`. -/
def imageOpens (f : X ⟶ Y) (hf : IsOpenMap f) (U : X.Opens) : Y.Opens :=
  hf.functor.obj U

lemma mem_imageOpens {f : X ⟶ Y} {hf : IsOpenMap f} {U : X.Opens} {y : Y} :
    y ∈ imageOpens f hf U ↔ ∃ x ∈ U, f x = y :=
  Iff.rfl

/-- The union of the open images of compatible opens pulls back to each of them. -/
lemma preimage_iSup_imageOpens_eq {ι : Type*} {X : ι → Scheme.{u}} (f : ∀ i, X i ⟶ Y)
    (hf : ∀ i, IsOpenMap (f i)) (U : ∀ i, (X i).Opens)
    (hU : ∀ i j, pullback.fst (f i) (f j) ⁻¹ᵁ U i = pullback.snd (f i) (f j) ⁻¹ᵁ U j) (i : ι) :
    f i ⁻¹ᵁ (⨆ j, imageOpens (f j) (hf j) (U j)) = U i := by
  ext x
  rw [SetLike.mem_coe, SetLike.mem_coe, Hom.mem_preimage, TopologicalSpace.Opens.mem_iSup]
  constructor
  · rintro ⟨j, u, hu, hux⟩
    obtain ⟨z, hz₁, hz₂⟩ := Scheme.Pullback.exists_preimage_pullback x u hux.symm
    have hz : z ∈ pullback.snd (f i) (f j) ⁻¹ᵁ U j := by
      rw [Hom.mem_preimage, hz₂]
      exact hu
    rw [← hU i j, Hom.mem_preimage, hz₁] at hz
    exact hz
  · intro hx
    exact ⟨i, x, hx, rfl⟩

/-- **Descent of open subsets along jointly surjective families of open morphisms.** -/
theorem existsUnique_preimage_eq_of_isOpenMap {ι : Type*} {X : ι → Scheme.{u}} (f : ∀ i, X i ⟶ Y)
    (hf : ∀ i, IsOpenMap (f i)) (hsurj : ∀ y, ∃ i, y ∈ Set.range (f i)) (U : ∀ i, (X i).Opens)
    (hU : ∀ i j, pullback.fst (f i) (f j) ⁻¹ᵁ U i = pullback.snd (f i) (f j) ⁻¹ᵁ U j) :
    ∃! V : Y.Opens, ∀ i, f i ⁻¹ᵁ V = U i := by
  refine ⟨⨆ j, imageOpens (f j) (hf j) (U j), preimage_iSup_imageOpens_eq f hf U hU,
    fun W hW ↦ ?_⟩
  ext y
  rw [SetLike.mem_coe, SetLike.mem_coe, TopologicalSpace.Opens.mem_iSup]
  constructor
  · intro hy
    obtain ⟨i, x, rfl⟩ := hsurj y
    have hx : x ∈ f i ⁻¹ᵁ W := hy
    rw [hW i] at hx
    exact ⟨i, x, hx, rfl⟩
  · rintro ⟨j, u, hu, rfl⟩
    rw [← hW j] at hu
    exact hu

/-- **Open subschemes form an fppf sheaf**: the presheaf `opensPresheaf` is a sheaf for the
fppf topology. -/
theorem isSheaf_opensPresheaf_fppfTopology :
    Presieve.IsSheaf Scheme.fppfTopology opensPresheaf.{u} := by
  rw [Precoverage.isSheaf_toGrothendieck_iff_of_isStableUnderBaseChange]
  intro S R hR
  obtain ⟨ι, X, f, rfl⟩ := R.exists_eq_ofArrows
  rw [fppfPrecoverage, ofArrows_mem_precoverage_iff] at hR
  obtain ⟨hsurj, hP⟩ := hR
  have hf : ∀ i, IsOpenMap (f i) := fun i ↦ by
    have : Flat (f i) := (hP i).1
    have : LocallyOfFinitePresentation (f i) := (hP i).2
    exact (f i).isOpenMap
  rw [Presieve.isSheafFor_arrows_iff]
  intro x hx
  exact existsUnique_preimage_eq_of_isOpenMap f hf hsurj x fun i j ↦
    hx i j _ (pullback.fst (f i) (f j)) (pullback.snd (f i) (f j)) pullback.condition

/-- An open of the source of a flat morphism locally of finite presentation whose pullbacks along
the two projections of `X ×_Y X` agree is the preimage of its (open) image. -/
theorem preimage_imageOpens_eq_of_flat (f : X ⟶ Y) [Flat f] [LocallyOfFinitePresentation f]
    (U : X.Opens) (hU : pullback.fst f f ⁻¹ᵁ U = pullback.snd f f ⁻¹ᵁ U) :
    f ⁻¹ᵁ imageOpens f f.isOpenMap U = U := by
  have := preimage_iSup_imageOpens_eq (fun _ : PUnit.{1} ↦ f) (fun _ ↦ f.isOpenMap)
    (fun _ ↦ U) (fun _ _ ↦ hU) PUnit.unit
  rwa [iSup_const] at this

/-- **Descent of open subschemes along one fppf morphism.** For a flat surjective morphism `f`,
locally of finite presentation, an open `U` of the source whose pullbacks along the two
projections of `X ×_Y X` agree is `f ⁻¹ᵁ V` for a unique open `V` of the target. -/
theorem existsUnique_preimage_eq_of_flat_of_surjective (f : X ⟶ Y) [Flat f]
    [LocallyOfFinitePresentation f] [Surjective f] (U : X.Opens)
    (hU : pullback.fst f f ⁻¹ᵁ U = pullback.snd f f ⁻¹ᵁ U) :
    ∃! V : Y.Opens, f ⁻¹ᵁ V = U := by
  obtain ⟨V, hV, hV'⟩ := existsUnique_preimage_eq_of_isOpenMap (fun _ : PUnit.{1} ↦ f)
    (fun _ ↦ f.isOpenMap) (fun y ↦ ⟨PUnit.unit, f.surjective y⟩) (fun _ ↦ U) (fun _ _ ↦ hU)
  exact ⟨V, hV PUnit.unit, fun W hW ↦ hV' W fun _ ↦ hW⟩

end AlgebraicGeometry.Scheme
