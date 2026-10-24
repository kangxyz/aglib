/-
Copyright (c) 2026 Algebraic geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Grassmannian.LocallyFree.Basic
public import Aglib.AlgebraicGeometry.Descent.Modules.ZariskiStack
public import Aglib.AlgebraicGeometry.Descent.Modules.ZariskiEpi
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Locality
public import Aglib.CategoryTheory.Sites.Descent.OfEpi
public import Mathlib.AlgebraicGeometry.Sites.Small

/-!
# `Quot_k(E)` is a Zariski sheaf on schemes over `S`

For a module sheaf `E` on a scheme `S`, the functor `quotBundleFunctor E k` of rank-`k` locally
free quotients of `E_T` is a sheaf for the Zariski topology `Scheme.zariskiTopology.over S` on
`Over S` (`isSheaf_quotBundleFunctor`, also in `Presheaf.IsSheaf` form). Covering families are
families of morphisms over `S` whose underlying morphisms are open immersions covering the target
(Mathlib's `over_toGrothendieck_eq_toGrothendieck_comap_forget` and
`Precoverage.isSheaf_toGrothendieck_iff_of_isStableUnderBaseChange_of_small`).

- Separatedness (`quotBundleFunctor_ext`): two quotients whose pullbacks along such a family are
  isomorphic are isomorphic; the local isomorphisms are unique, so they glue
  (`Scheme.Modules.exists_iso_of_openImmersion`, as in F8's `equiv_of_openImmersion`).
- Gluing (`quotBundleFunctor_exists_glue`): a compatible family of quotients glues. The local
  quotient maps `(g i)^* E_T ≅ E_{Y i} ⟶ Q i` and the unique compatible isomorphisms on overlaps
  form a descent datum relative to the descent datum of `E_T`
  (`Pseudofunctor.DescentData.ofEpi`), which is effective (`Scheme.Modules.exists_glued_quotient`,
  F8's `exists_glued_quot` with an arbitrary source sheaf). The overlap compatibility is the
  coherence `Scheme.Modules.pullback_map_pullbackTriangleIso_hom_app` of
  `Scheme.Modules.pullbackTriangleIso`, with the descent datum in that form
  (`Scheme.Modules.pullbackPseudofunctor_toDescentData_obj_hom_eq_triangle`).

Source: for `E = O^n` (Stacks' `G(n − k, n)`) this is the sheaf step in the proof of Stacks,
Tag 089T (Lemma 27.22.1), TeX snapshot `a04446e5`: "we will use the criterion of Schemes,
Lemma 26.15.4. The reason `F` satisfies the sheaf property for the Zariski topology is that we
can glue sheaves, see Sheaves, Section 6.33"; for a locally free `E` it is the first step of the
representability of `Grass(E, d)` in Nitsure, arXiv:math/0504590v1, §1, Exercises (2),
pp. 5–6. No hypothesis on `E` or `S`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Opposite Limits

namespace AlgebraicGeometry.Scheme.Modules

/-- The descent datum of a module sheaf along a family of morphisms, in terms of
`pullbackTriangleIso`. -/
theorem pullbackPseudofunctor_toDescentData_obj_hom_eq_triangle {T : Scheme.{u}} {ι : Type*}
    {X : ι → Scheme.{u}} (f : ∀ i, X i ⟶ T) (M : T.Modules) {Y : Scheme.{u}} (q : Y ⟶ T)
    {i₁ i₂ : ι} (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂) (hf₁ : f₁ ≫ f i₁ = q) (hf₂ : f₂ ≫ f i₂ = q) :
    ((pullbackPseudofunctor.toDescentData f).obj M).hom q f₁ f₂ hf₁ hf₂ =
      (pullbackTriangleIso f₁ (f i₁) q hf₁).hom.app M ≫
        (pullbackTriangleIso f₂ (f i₂) q hf₂).inv.app M := by
  rw [pullbackPseudofunctor_toDescentData_obj_hom, pullbackTriangleIso_hom_app,
    pullbackTriangleIso_inv_app]
  simp only [Category.assoc]
  rfl

/-! ### Gluing quotients along open immersions -/

/-- **Gluing of quotients.** Let `f i : X i ⟶ T` (`ι : Type u`) be a jointly surjective family of
open immersions, `M` a module sheaf on `T`, and `p i : (f i)^* M ⟶ Q i` epimorphisms onto
finite locally free sheaves of rank `k` such that on every scheme over two members there is a
morphism of the pulled back targets compatible with the `p i` and with the descent datum of `M`.
Then there is an epimorphism `π : M ⟶ Q₀` onto a finite locally free sheaf of rank `k` with
isomorphisms `(f i)^* Q₀ ≅ Q i` carrying `(f i)^* π` to `p i`. This is F8's
`Grassmannian.exists_glued_quot` for an arbitrary source `M`. -/
theorem exists_glued_quotient {T : Scheme.{u}} {ι : Type u} {X : ι → Scheme.{u}}
    (f : ∀ i, X i ⟶ T) [∀ i, IsOpenImmersion (f i)]
    (hf : ∀ x : T, ∃ (i : ι) (y : X i), f i y = x) (M : T.Modules) {k : ℕ}
    (Q : ∀ i, (X i).Modules) (hQ : ∀ i, SheafHasRank (Q i) k)
    (p : ∀ i, (Scheme.Modules.pullback (f i)).obj M ⟶ Q i) [∀ i, Epi (p i)]
    (hhom : ∀ ⦃Y : Scheme.{u}⦄ (q : Y ⟶ T) ⦃i₁ i₂ : ι⦄ (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂)
      (hf₁ : f₁ ≫ f i₁ = q) (hf₂ : f₂ ≫ f i₂ = q),
      ∃ h : (Scheme.Modules.pullback f₁).obj (Q i₁) ⟶ (Scheme.Modules.pullback f₂).obj (Q i₂),
        (Scheme.Modules.pullback f₁).map (p i₁) ≫ h =
          ((pullbackPseudofunctor.toDescentData f).obj M).hom q f₁ f₂ hf₁ hf₂ ≫
            (Scheme.Modules.pullback f₂).map (p i₂)) :
    ∃ (Q₀ : T.Modules) (π : M ⟶ Q₀), Epi π ∧ SheafHasRank Q₀ k ∧ ∀ i,
      ∃ e : (Scheme.Modules.pullback (f i)).obj Q₀ ≅ Q i,
        (Scheme.Modules.pullback (f i)).map π ≫ e.hom = p i := by
  have := OpenCoverGluing.essSurj_toDescentData f
    (fun D l V hV ↦ projectionSurjective _ _ _ f D l V hV)
  let D : pullbackPseudofunctor.DescentData f :=
    Pseudofunctor.DescentData.ofEpi ((pullbackPseudofunctor.toDescentData f).obj M) Q p
      (fun _ i g ↦ (inferInstance : Epi ((Scheme.Modules.pullback g).map (p i))))
      (fun _ q _ _ f₁ f₂ hf₁ hf₂ ↦ (hhom q f₁ f₂ hf₁ hf₂).choose)
      (fun _ q _ _ f₁ f₂ hf₁ hf₂ ↦ (hhom q f₁ f₂ hf₁ hf₂).choose_spec)
  let toD : (pullbackPseudofunctor.toDescentData f).obj M ⟶ D :=
    Pseudofunctor.DescentData.toOfEpi _ _ _ _ _ _
  have htoD : ∀ i, toD.hom i = p i := fun _ ↦ rfl
  let Q₀ := (pullbackPseudofunctor.toDescentData f).objPreimage D
  let e := (pullbackPseudofunctor.toDescentData f).objObjPreimageIso D
  let hff := fullyFaithfulToDescentDataOfOpenImmersion f hf
  let φ : (pullbackPseudofunctor.toDescentData f).obj M ⟶
      (pullbackPseudofunctor.toDescentData f).obj Q₀ :=
    toD ≫ e.inv
  let π : M ⟶ Q₀ := hff.preimage φ
  have hπ : ∀ i, (Scheme.Modules.pullback (f i)).map π = p i ≫ e.inv.hom i :=
    fun i ↦ (congrArg (fun ψ ↦ ψ.hom i) (hff.map_preimage φ)).trans (by
      rw [Pseudofunctor.DescentData.comp_hom, htoD])
  let eI : ∀ i, (Scheme.Modules.pullback (f i)).obj Q₀ ≅ Q i := fun i ↦
    { hom := e.hom.hom i
      inv := e.inv.hom i
      hom_inv_id := by
        rw [← Pseudofunctor.DescentData.comp_hom, e.hom_inv_id]
        rfl
      inv_hom_id := by
        rw [← Pseudofunctor.DescentData.comp_hom, e.inv_hom_id]
        rfl }
  have hepi : Epi π := by
    constructor
    intro Z g g' hgg
    apply hff.map_injective
    ext i
    have : Epi ((Scheme.Modules.pullback (f i)).map π) := by
      rw [hπ i]
      have : Epi (eI i).inv := @IsIso.epi_of_iso _ _ _ _ (eI i).inv (Iso.isIso_inv (eI i))
      exact epi_comp (p i) (eI i).inv
    rw [← cancel_epi ((Scheme.Modules.pullback (f i)).map π)]
    change (Scheme.Modules.pullback (f i)).map π ≫ (Scheme.Modules.pullback (f i)).map g =
      (Scheme.Modules.pullback (f i)).map π ≫ (Scheme.Modules.pullback (f i)).map g'
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp, hgg]
  have hloc : ∀ i, SheafHasRank ((Scheme.Modules.pullback (f i)).obj Q₀) k :=
    fun i ↦ sheafHasRank_of_iso (eI i).symm (hQ i)
  have hrank : SheafHasRank Q₀ k := by
    have : IsFiniteLocallyFree T Q₀ := by
      refine finiteLocallyFree_of_openCover Q₀ (fun i ↦ (f i).opensRange) ?_ fun i ↦ ?_
      · refine eq_top_iff.mpr fun x _ ↦ ?_
        obtain ⟨i, y, hy⟩ := hf x
        exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, y, hy⟩
      · have := (hloc i).isFiniteLocallyFree
        have : IsFiniteLocallyFree _ (Q₀.restrict (f i)) :=
          finiteLocallyFree_of_iso ((restrictFunctorIsoPullback (f i)).app Q₀).symm
        exact finiteLocallyFree_restrict_opensRange Q₀ (f i)
    rw [sheafHasRank_iff_rank_eq]
    intro x
    obtain ⟨i, y, rfl⟩ := hf x
    rw [← sheafRank_pullback Q₀ (f i) y]
    have := (hloc i).isFiniteLocallyFree
    exact (sheafHasRank_iff_rank_eq _ k).mp (hloc i) y
  refine ⟨Q₀, π, hepi, hrank, fun i ↦ ⟨eI i, ?_⟩⟩
  change (Scheme.Modules.pullback (f i)).map π ≫ e.hom.hom i = p i
  rw [hπ i, Category.assoc, ← Pseudofunctor.DescentData.comp_hom, e.inv_hom_id,
    Pseudofunctor.DescentData.id_hom]
  erw [Category.comp_id]

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Grassmannian

open Scheme.Modules LocallyFreeQuotientOf

/-! ### Separatedness and gluing for `Quot_k(E)` -/

variable {S : Scheme.{u}} (E : S.Modules) (k : ℕ)

/-- **Separatedness**: classes of quotients that agree on a family of morphisms over `S` whose
underlying morphisms are jointly surjective open immersions are equal. -/
theorem quotBundleFunctor_ext {T : Over S} {ι : Type*} {Y : ι → Over S} (g : ∀ i, Y i ⟶ T)
    (hg : ∀ i, IsOpenImmersion (g i).left)
    (hcov : ∀ x : T.left, ∃ (i : ι) (y : (Y i).left), (g i).left y = x)
    {a b : (quotBundleFunctor E k).obj (op T)}
    (h : ∀ i, (quotBundleFunctor E k).map (g i).op a = (quotBundleFunctor E k).map (g i).op b) :
    a = b := by
  induction a using Quotient.inductionOn with | h P =>
  induction b using Quotient.inductionOn with | h P' =>
  have e : ∀ i, IsoUnder (P.pullbackOver (g i)) (P'.pullbackOver (g i)) := fun i ↦ by
    have hi := h i
    change Quotient.mk _ (P.pullbackOver (g i)) = Quotient.mk _ (P'.pullbackOver (g i)) at hi
    exact (Quotient.exact hi).some
  obtain ⟨φ, hφ⟩ := exists_iso_of_openImmersion (fun i ↦ (g i).left) hcov P.π P'.π
    (fun i ↦ (e i).iso) fun i ↦ by
      have := (e i).comm
      rw [pullbackOver_π, pullbackOver_π, Category.assoc, cancel_epi] at this
      exact this
  exact Quotient.sound ⟨⟨φ, hφ⟩⟩

/-- **The overlap compatibility of local quotients.** For a compatible family of quotients on
`g i : Y i ⟶ T`, on every scheme `Y` over two members the local quotient maps
`(g i)^* E_T ≅ E_{Y i} ⟶ Q i` are compatible with the descent datum of `E_T`. -/
theorem exists_quotBundle_descentHom {T : Over S} {ι : Type*} {Y : ι → Over S}
    (g : ∀ i, Y i ⟶ T)
    (P : ∀ i, LocallyFreeQuotientOf (overPullback E (Y i)) k)
    (hP : ∀ (Z : Over S) (i₁ i₂ : ι) (h₁ : Z ⟶ Y i₁) (h₂ : Z ⟶ Y i₂), h₁ ≫ g i₁ = h₂ ≫ g i₂ →
      (P i₁).pullbackOver h₁ ≈ (P i₂).pullbackOver h₂)
    {Y₀ : Scheme.{u}} (q : Y₀ ⟶ T.left) {i₁ i₂ : ι} (f₁ : Y₀ ⟶ (Y i₁).left)
    (f₂ : Y₀ ⟶ (Y i₂).left) (hf₁ : f₁ ≫ (g i₁).left = q) (hf₂ : f₂ ≫ (g i₂).left = q) :
    ∃ h : (Scheme.Modules.pullback f₁).obj (P i₁).obj ⟶
        (Scheme.Modules.pullback f₂).obj (P i₂).obj,
      (Scheme.Modules.pullback f₁).map ((overPullbackIso E (g i₁)).inv ≫ (P i₁).π) ≫ h =
        ((pullbackPseudofunctor.toDescentData (fun i ↦ (g i).left)).obj
          (overPullback E T)).hom q f₁ f₂ hf₁ hf₂ ≫
            (Scheme.Modules.pullback f₂).map ((overPullbackIso E (g i₂)).inv ≫ (P i₂).π) := by
  let Z : Over S := Over.mk (q ≫ T.hom)
  have hw₁ : f₁ ≫ (Y i₁).hom = q ≫ T.hom := by
    rw [← Over.w (g i₁), ← Category.assoc, hf₁]
  have hw₂ : f₂ ≫ (Y i₂).hom = q ≫ T.hom := by
    rw [← Over.w (g i₂), ← Category.assoc, hf₂]
  let h₁ : Z ⟶ Y i₁ := Over.homMk f₁ hw₁
  let h₂ : Z ⟶ Y i₂ := Over.homMk f₂ hw₂
  have hh : h₁ ≫ g i₁ = h₂ ≫ g i₂ := by
    apply Over.OverMorphism.ext
    change f₁ ≫ (g i₁).left = f₂ ≫ (g i₂).left
    rw [hf₁, hf₂]
  obtain ⟨e⟩ := hP Z i₁ i₂ h₁ h₂ hh
  refine ⟨e.iso.hom, ?_⟩
  have K₁ : (Scheme.Modules.pullback f₁).map (overPullbackIso E (g i₁)).inv =
      (pullbackTriangleIso f₁ (g i₁).left q hf₁).hom.app (overPullback E T) ≫
        (pullbackTriangleIso q T.hom (q ≫ T.hom) rfl).hom.app E ≫ (overPullbackIso E h₁).hom :=
    pullback_map_pullbackTriangleIso_hom_app f₁ (g i₁).left T.hom hf₁ (Over.w (g i₁)) hw₁ E
  have K₂ : (Scheme.Modules.pullback f₂).map (overPullbackIso E (g i₂)).inv =
      (pullbackTriangleIso f₂ (g i₂).left q hf₂).hom.app (overPullback E T) ≫
        (pullbackTriangleIso q T.hom (q ≫ T.hom) rfl).hom.app E ≫ (overPullbackIso E h₂).hom :=
    pullback_map_pullbackTriangleIso_hom_app f₂ (g i₂).left T.hom hf₂ (Over.w (g i₂)) hw₂ E
  have he : (overPullbackIso E h₁).hom ≫ (Scheme.Modules.pullback f₁).map (P i₁).π ≫
      e.iso.hom = (overPullbackIso E h₂).hom ≫ (Scheme.Modules.pullback f₂).map (P i₂).π := by
    have := e.comm
    rw [pullbackOver_π, pullbackOver_π, Category.assoc] at this
    exact this
  rw [pullbackPseudofunctor_toDescentData_obj_hom_eq_triangle, CategoryTheory.Functor.map_comp,
    CategoryTheory.Functor.map_comp, K₁, K₂]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  rw [he]

/-- **Gluing**: a compatible family of classes of quotients on a family `g i : Y i ⟶ T` over `S`
(`ι : Type u`) whose underlying morphisms are jointly surjective open immersions glues to a class
on `T`. -/
theorem quotBundleFunctor_exists_glue {T : Over S} {ι : Type u} {Y : ι → Over S}
    (g : ∀ i, Y i ⟶ T) (hg : ∀ i, IsOpenImmersion (g i).left)
    (hcov : ∀ x : T.left, ∃ (i : ι) (y : (Y i).left), (g i).left y = x)
    (x : ∀ i, (quotBundleFunctor E k).obj (op (Y i)))
    (hx : Presieve.Arrows.Compatible (quotBundleFunctor E k) g x) :
    ∃ a : (quotBundleFunctor E k).obj (op T),
      ∀ i, (quotBundleFunctor E k).map (g i).op a = x i := by
  let P : ∀ i, LocallyFreeQuotientOf (overPullback E (Y i)) k := fun i ↦
    Quotient.out (s := LocallyFreeQuotientOf.setoid (overPullback E (Y i)) k) (x i)
  have hPx : ∀ i, (Quotient.mk _ (P i) : (quotBundleFunctor E k).obj (op (Y i))) = x i :=
    fun i ↦ Quotient.out_eq (s := LocallyFreeQuotientOf.setoid (overPullback E (Y i)) k) (x i)
  have hP : ∀ (Z : Over S) (i₁ i₂ : ι) (h₁ : Z ⟶ Y i₁) (h₂ : Z ⟶ Y i₂), h₁ ≫ g i₁ = h₂ ≫ g i₂ →
      (P i₁).pullbackOver h₁ ≈ (P i₂).pullbackOver h₂ := by
    intro Z i₁ i₂ h₁ h₂ hh
    have := hx i₁ i₂ Z h₁ h₂ hh
    rw [← hPx i₁, ← hPx i₂] at this
    exact Quotient.exact this
  let p : ∀ i, (Scheme.Modules.pullback (g i).left).obj (overPullback E T) ⟶ (P i).obj :=
    fun i ↦ (overPullbackIso E (g i)).inv ≫ (P i).π
  have : ∀ i, Epi (p i) := fun i ↦ epi_comp _ _
  obtain ⟨Q₀, π, hπ, hrank, hQ⟩ := exists_glued_quotient (fun i ↦ (g i).left) hcov
    (overPullback E T) (fun i ↦ (P i).obj) (fun i ↦ (P i).hasRank) p
    (fun _ q _ _ f₁ f₂ hf₁ hf₂ ↦ exists_quotBundle_descentHom E k g P hP q f₁ f₂ hf₁ hf₂)
  let Q : LocallyFreeQuotientOf (overPullback E T) k := ⟨Q₀, π, hπ, hrank⟩
  refine ⟨Quotient.mk _ Q, fun i ↦ ?_⟩
  rw [← hPx i]
  obtain ⟨e, he⟩ := hQ i
  refine Quotient.sound ⟨⟨e, ?_⟩⟩
  change ((overPullbackIso E (g i)).hom ≫ (Scheme.Modules.pullback (g i).left).map π) ≫ e.hom =
    (P i).π
  rw [Category.assoc, he]
  exact Iso.hom_inv_id_assoc _ _

/-- **`Quot_k(E)` is a Zariski sheaf** on schemes over `S`.

Sources: Stacks, Tag 089T (Lemma 27.22.1), proof, for `E = O^n`, Stacks' `G(n − k, n)` (gluing
of sheaves, Sheaves, Section 6.33); Nitsure, arXiv:math/0504590v1, §1, Exercises (2), pp. 5–6.
Encoded subset: an arbitrary module sheaf `E` on an arbitrary scheme `S`, all `k`, the topology
`Scheme.zariskiTopology.over S`. No premise. -/
theorem isSheaf_quotBundleFunctor :
    Presieve.IsSheaf (Scheme.zariskiTopology.over S) (quotBundleFunctor E k) := by
  have h : Scheme.zariskiTopology.{u}.over S =
      ((Scheme.precoverage @IsOpenImmersion).comap (Over.forget S)).toGrothendieck :=
    over_toGrothendieck_eq_toGrothendieck_comap_forget _ S
  rw [h, Precoverage.isSheaf_toGrothendieck_iff_of_isStableUnderBaseChange_of_small.{u}]
  intro T 𝒰
  have hmem := Precoverage.mem_comap_iff.mp 𝒰.mem₀
  change (Presieve.ofArrows 𝒰.X 𝒰.f).map (Over.forget S) ∈ _ at hmem
  rw [Presieve.map_ofArrows, Scheme.ofArrows_mem_precoverage_iff] at hmem
  obtain ⟨hcov, hopen⟩ := hmem
  change Presieve.IsSheafFor _ (Presieve.ofArrows 𝒰.X 𝒰.f)
  rw [Presieve.isSheafFor_arrows_iff]
  have hcov' : ∀ x : T.left, ∃ (i : 𝒰.I₀) (y : (𝒰.X i).left), (𝒰.f i).left y = x := by
    intro x
    obtain ⟨i, y, hy⟩ := hcov x
    exact ⟨i, y, hy⟩
  intro x hx
  obtain ⟨a, ha⟩ := quotBundleFunctor_exists_glue E k 𝒰.f hopen hcov' x hx
  exact ⟨a, ha, fun b hb ↦ quotBundleFunctor_ext E k 𝒰.f hopen hcov'
    (fun i ↦ (hb i).trans (ha i).symm)⟩

/-- **`Quot_k(E)` is a Zariski sheaf**, in `Presheaf.IsSheaf` form. -/
theorem presheaf_isSheaf_quotBundleFunctor :
    Presheaf.IsSheaf (Scheme.zariskiTopology.over S) (quotBundleFunctor E k) :=
  (isSheaf_iff_isSheaf_of_type _ _).mpr (isSheaf_quotBundleFunctor E k)

end AlgebraicGeometry.Grassmannian
