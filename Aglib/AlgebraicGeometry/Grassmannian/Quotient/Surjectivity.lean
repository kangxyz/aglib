/-
Copyright (c) 2026 Algebraic geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Grassmannian.Quotient.Injectivity
public import Aglib.AlgebraicGeometry.Descent.Modules.ZariskiStack
public import Aglib.CategoryTheory.Sites.Descent.OfEpi

/-!
# Every Grassmannian point comes from a locally free quotient

For a scheme `T` over `Spec R` and a natural transformation `α : algSpecPoints T ⟶
Module.Grassmannian.functor k`, the points of `α` on the affine open cover of `T` give local
quotients `localQuot α i`. Their pullbacks to any scheme over two charts are isomorphic
(`localQuot_pullback_equiv`, by injectivity on that scheme), so the unique compatible
isomorphisms form a descent datum `quotDescentData α` (`Pseudofunctor.DescentData.ofEpi`, relative
to the descent datum of `O_T^n`), which glues along the Zariski cover (`exists_glued_quot`). The
glued quotient has the points `α` (`toPointsNatTrans_of_local`), so `toPointsNatTrans T` is
surjective (`toPointsNatTrans_surjective`).
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Opposite Limits

namespace AlgebraicGeometry

namespace Grassmannian

open Scheme.Modules LocallyFreeQuotient AlgSpecPoints

variable {R : CommRingCat.{u}} {k n : ℕ}
variable [Module.Grassmannian.BaseChangeMkQFormula.{u, u, u} R (Fin n → R)]

set_option hygiene false in
/-- Mathlib's Grassmannian functor `A ↦ G(k, A ⊗[R] (Fin n → R); A)` on `R`-algebras. -/
local notation "𝐆" => Module.Grassmannian.functor.{u, u, u} (R := R) (M := Fin n → R) k

omit [Module.Grassmannian.BaseChangeMkQFormula.{u, u, u} R (Fin n → R)] in
theorem pullback_pullback_equiv {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (P : LocallyFreeQuotient Z k n) : (P.pullback g).pullback f ≈ P.pullback (f ≫ g) :=
  ⟨pullbackCompIso f g P⟩

variable {T : Over (Spec R)} (α : algSpecPoints T ⟶ 𝐆)

/-- The quotient on the `i`-th affine chart of `T` given by the point of `α` there. -/
abbrev localQuot (i : T.left.affineOpenCover.I₀) :
    LocallyFreeQuotient (Spec (CommRingCat.of (coverAlg i))) k n :=
  pointQuot (coverAlg i) (α.app (coverAlg i) (coverPt i))

/-- The points of the pullbacks of a local quotient are the values of `α`. -/
theorem affinePoint_localQuot_pullback (i : T.left.affineOpenCover.I₀) {C : CommAlgCat.{u} R}
    (w : (algSpec R).obj (op C) ⟶ (algSpec R).obj (op (coverAlg i))) :
    affinePoint C (Quotient.mk _ ((localQuot α i).pullback w.left)) = α.app C (w ≫ coverPt i) := by
  obtain ⟨ψ, rfl⟩ : ∃ ψ : coverAlg i ⟶ C, (algSpec R).map ψ.op = w :=
    ⟨((algSpec R).preimage w).unop, by rw [Quiver.Hom.op_unop, Functor.map_preimage]⟩
  rw [show ((algSpec R).map ψ.op).left =
    Spec.map (CommRingCat.ofHom (ψ.hom : coverAlg i →+* C)) from rfl, affinePoint_pullback,
    affinePoint_pointQuot]
  exact (NatTrans.naturality_apply α ψ (coverPt i)).symm

/-- **Local quotients agree on overlaps**: their pullbacks to any scheme over two charts are
isomorphic. -/
theorem localQuot_pullback_equiv {Y : Scheme.{u}} (q : Y ⟶ T.left)
    {i₁ i₂ : T.left.affineOpenCover.I₀}
    (f₁ : Y ⟶ ((algSpec R).obj (op (coverAlg i₁))).left)
    (f₂ : Y ⟶ ((algSpec R).obj (op (coverAlg i₂))).left)
    (hf₁ : f₁ ≫ (coverPt i₁).left = q) (hf₂ : f₂ ≫ (coverPt i₂).left = q) :
    (localQuot α i₁).pullback f₁ ≈ (localQuot α i₂).pullback f₂ := by
  let Y' : Over (Spec R) := Over.mk (q ≫ T.hom)
  refine Quotient.exact (toPointsNatTrans_injective (k := k) (n := n) Y' ?_)
  refine NatTrans.ext (funext fun C ↦ ?_)
  ext v
  change affinePoint C (Quotient.mk _ (((localQuot α i₁).pullback f₁).pullback v.left)) =
    affinePoint C (Quotient.mk _ (((localQuot α i₂).pullback f₂).pullback v.left))
  have hv : v.left ≫ q ≫ T.hom = ((algSpec R).obj (op C)).hom := Over.w v
  let w₁ : (algSpec R).obj (op C) ⟶ (algSpec R).obj (op (coverAlg i₁)) :=
    Over.homMk (v.left ≫ f₁) (by
      rw [← Over.w (coverPt i₁), Category.assoc, ← Category.assoc f₁, hf₁]
      exact hv)
  let w₂ : (algSpec R).obj (op C) ⟶ (algSpec R).obj (op (coverAlg i₂)) :=
    Over.homMk (v.left ≫ f₂) (by
      rw [← Over.w (coverPt i₂), Category.assoc, ← Category.assoc f₂, hf₂]
      exact hv)
  have hw : w₁ ≫ coverPt i₁ = w₂ ≫ coverPt i₂ := by
    apply Over.OverMorphism.ext
    change (v.left ≫ f₁) ≫ (coverPt i₁).left = (v.left ≫ f₂) ≫ (coverPt i₂).left
    rw [Category.assoc, Category.assoc, hf₁, hf₂]
  calc affinePoint C (Quotient.mk _ (((localQuot α i₁).pullback f₁).pullback v.left))
      = affinePoint C (Quotient.mk _ ((localQuot α i₁).pullback w₁.left)) :=
        congrArg (affinePoint C) (Quotient.sound (pullback_pullback_equiv v.left f₁ _))
    _ = α.app C (w₁ ≫ coverPt i₁) := affinePoint_localQuot_pullback α i₁ w₁
    _ = α.app C (w₂ ≫ coverPt i₂) := by rw [hw]
    _ = affinePoint C (Quotient.mk _ ((localQuot α i₂).pullback w₂.left)) :=
        (affinePoint_localQuot_pullback α i₂ w₂).symm
    _ = affinePoint C (Quotient.mk _ (((localQuot α i₂).pullback f₂).pullback v.left)) :=
        congrArg (affinePoint C) (Quotient.sound (pullback_pullback_equiv v.left f₂ _)).symm

/-- The quotient map on the `i`-th chart, out of the pullback of `O_T^n`. -/
def chartQuotMap (i : T.left.affineOpenCover.I₀) :
    (Scheme.Modules.pullback (coverPt i).left).obj (freeSheaf T.left n) ⟶ (localQuot α i).obj :=
  (pullbackFreeIso (coverPt i).left (ULift.{u} (Fin n))).hom ≫ (localQuot α i).π

instance (i : T.left.affineOpenCover.I₀) : Epi (chartQuotMap α i) := by
  unfold chartQuotMap
  infer_instance

/-- The compatible isomorphisms of the local quotients on overlaps. -/
theorem exists_localQuot_descentHom {Y : Scheme.{u}} (q : Y ⟶ T.left)
    {i₁ i₂ : T.left.affineOpenCover.I₀}
    (f₁ : Y ⟶ ((algSpec R).obj (op (coverAlg i₁))).left)
    (f₂ : Y ⟶ ((algSpec R).obj (op (coverAlg i₂))).left)
    (hf₁ : f₁ ≫ (coverPt i₁).left = q) (hf₂ : f₂ ≫ (coverPt i₂).left = q) :
    ∃ h : (Scheme.Modules.pullback f₁).obj (localQuot α i₁).obj ⟶
        (Scheme.Modules.pullback f₂).obj (localQuot α i₂).obj,
      (Scheme.Modules.pullback f₁).map (chartQuotMap α i₁) ≫ h =
        ((pullbackPseudofunctor.toDescentData (fun i ↦ (coverPt (T := T) i).left)).obj
          (freeSheaf T.left n)).hom q f₁ f₂ hf₁ hf₂ ≫
            (Scheme.Modules.pullback f₂).map (chartQuotMap α i₂) := by
  obtain ⟨e⟩ := localQuot_pullback_equiv α q f₁ f₂ hf₁ hf₂
  refine ⟨e.iso.hom, ?_⟩
  have hc := toDescentData_obj_free_hom (fun i ↦ (coverPt (T := T) i).left)
    (ULift.{u} (Fin n)) q f₁ f₂ hf₁ hf₂
  have he := e.comm
  rw [pullback_π, pullback_π, Category.assoc] at he
  have he' : (Scheme.Modules.pullback f₁).map (localQuot α i₁).π ≫ e.iso.hom =
      (pullbackFreeIso f₁ (ULift.{u} (Fin n))).hom ≫
        (pullbackFreeIso f₂ (ULift.{u} (Fin n))).inv ≫
          (Scheme.Modules.pullback f₂).map (localQuot α i₂).π := by
    rw [← he, Iso.hom_inv_id_assoc]
  simp only [chartQuotMap, CategoryTheory.Functor.map_comp, Category.assoc]
  rw [he', ← reassoc_of% hc, Iso.hom_inv_id_assoc]

/-- The descent datum of the local quotients of `α` along the affine open cover of `T`. -/
def quotDescentData : pullbackPseudofunctor.DescentData (fun i ↦ (coverPt (T := T) i).left) :=
  Pseudofunctor.DescentData.ofEpi
    ((pullbackPseudofunctor.toDescentData (fun i ↦ (coverPt (T := T) i).left)).obj
      (freeSheaf T.left n))
    (fun i ↦ (localQuot α i).obj) (chartQuotMap α)
    (fun _ i g ↦ (inferInstance : Epi ((Scheme.Modules.pullback g).map (chartQuotMap α i))))
    (fun _ q _ _ f₁ f₂ hf₁ hf₂ ↦ (exists_localQuot_descentHom α q f₁ f₂ hf₁ hf₂).choose)
    (fun _ q _ _ f₁ f₂ hf₁ hf₂ ↦ (exists_localQuot_descentHom α q f₁ f₂ hf₁ hf₂).choose_spec)

/-- The local quotient maps, as a morphism of descent data. -/
def toQuotDescentData :
    (pullbackPseudofunctor.toDescentData (fun i ↦ (coverPt (T := T) i).left)).obj
      (freeSheaf T.left n) ⟶ quotDescentData (k := k) α := by
  unfold quotDescentData
  exact Pseudofunctor.DescentData.toOfEpi _ _ _ _ _ _

theorem toQuotDescentData_hom (i : T.left.affineOpenCover.I₀) :
    (toQuotDescentData (k := k) α).hom i = chartQuotMap α i := by
  unfold toQuotDescentData
  rfl

/-- **Gluing**: the local quotients of `α` glue to a rank-`k` locally free quotient of `O_T^n`. -/
theorem exists_glued_quot : ∃ P : LocallyFreeQuotient T.left k n,
    ∀ i, P.pullback (coverPt i).left ≈ localQuot α i := by
  let f := fun i ↦ (coverPt (T := T) i).left
  have : ∀ i, IsOpenImmersion (f i) := isOpenImmersion_coverPt
  have hf : ∀ x : T.left, ∃ (i : T.left.affineOpenCover.I₀) (y : _), f i y = x :=
    exists_coverPt_apply_eq
  have := OpenCoverGluing.essSurj_toDescentData f
    (fun D l V hV ↦ projectionSurjective _ _ _ f D l V hV)
  let D := quotDescentData (k := k) α
  let Q := (pullbackPseudofunctor.toDescentData f).objPreimage D
  let e := (pullbackPseudofunctor.toDescentData f).objObjPreimageIso D
  let hff := fullyFaithfulToDescentDataOfOpenImmersion f hf
  let φ : (pullbackPseudofunctor.toDescentData f).obj (freeSheaf T.left n) ⟶
      (pullbackPseudofunctor.toDescentData f).obj Q :=
    toQuotDescentData α ≫ e.inv
  let π : freeSheaf T.left n ⟶ Q := hff.preimage φ
  have hπ : ∀ i, (Scheme.Modules.pullback (f i)).map π = chartQuotMap α i ≫ e.inv.hom i :=
    fun i ↦ (congrArg (fun ψ ↦ ψ.hom i) (hff.map_preimage φ)).trans (by
      rw [Pseudofunctor.DescentData.comp_hom, toQuotDescentData_hom])
  let eI : ∀ i, (Scheme.Modules.pullback (f i)).obj Q ≅ (localQuot α i).obj := fun i ↦
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
      exact epi_comp (chartQuotMap α i) (eI i).inv
    rw [← cancel_epi ((Scheme.Modules.pullback (f i)).map π)]
    change (Scheme.Modules.pullback (f i)).map π ≫ (Scheme.Modules.pullback (f i)).map g =
      (Scheme.Modules.pullback (f i)).map π ≫ (Scheme.Modules.pullback (f i)).map g'
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp, hgg]
  have hloc : ∀ i, SheafHasRank ((Scheme.Modules.pullback (f i)).obj Q) k :=
    fun i ↦ sheafHasRank_of_iso (eI i).symm (localQuot α i).hasRank
  have hrank : SheafHasRank Q k := by
    have : IsFiniteLocallyFree T.left Q := by
      refine finiteLocallyFree_of_openCover Q (fun i ↦ (f i).opensRange) ?_ fun i ↦ ?_
      · refine eq_top_iff.mpr fun x _ ↦ ?_
        obtain ⟨i, y, hy⟩ := hf x
        exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, y, hy⟩
      · have := (hloc i).isFiniteLocallyFree
        have : IsFiniteLocallyFree _ (Q.restrict (f i)) :=
          finiteLocallyFree_of_iso ((restrictFunctorIsoPullback (f i)).app Q).symm
        exact finiteLocallyFree_restrict_opensRange Q (f i)
    rw [sheafHasRank_iff_rank_eq]
    intro x
    obtain ⟨i, y, rfl⟩ := hf x
    rw [← sheafRank_pullback Q (f i) y]
    have := (hloc i).isFiniteLocallyFree
    exact (sheafHasRank_iff_rank_eq _ k).mp (hloc i) y
  refine ⟨⟨Q, π, hepi, hrank⟩, fun i ↦ ⟨⟨eI i, ?_⟩⟩⟩
  change (pullbackFreeIso (f i) _).inv ≫ (Scheme.Modules.pullback (f i)).map π ≫ e.hom.hom i = _
  rw [hπ i, Category.assoc, ← Pseudofunctor.DescentData.comp_hom, e.inv_hom_id,
    Pseudofunctor.DescentData.id_hom]
  erw [Category.comp_id]
  rw [chartQuotMap, Iso.inv_hom_id_assoc]

/-- A quotient that is locally the local quotients of `α` has the points `α`. -/
theorem toPointsNatTrans_of_local {P : LocallyFreeQuotient T.left k n}
    (hP : ∀ i, P.pullback (coverPt i).left ≈ localQuot α i) :
    toPointsNatTrans T (Quotient.mk _ P) = α := by
  refine NatTrans.ext (funext fun C ↦ ?_)
  ext v
  change affinePoint C (Quotient.mk _ (P.pullback v.left)) = α.app C v
  have H : ∀ p : PrimeSpectrum C, ∃ (r : C) (_ : r ∉ p.asIdeal),
      Module.Grassmannian.map (locAway r).hom (affinePoint C (Quotient.mk _ (P.pullback v.left))) =
        Module.Grassmannian.map (locAway r).hom (α.app C v) := by
    intro p
    obtain ⟨r, hr, a, ha⟩ := exists_locAway_comp_eq
      (coverι (T.left.affineOpenCover.idx (v.left p))) v p
      (T.left.affineOpenCover.covers (v.left p))
    refine ⟨r, hr, ?_⟩
    let i := T.left.affineOpenCover.idx (v.left p)
    let a' : (algSpec R).obj (op (CommAlgCat.of R (Localization.Away r))) ⟶
        (algSpec R).obj (op (coverAlg i)) := a ≫ (coverIso i).inv
    have ha' : a' ≫ coverPt i = (algSpec R).map (locAway r).op ≫ v := by
      simp only [a', coverPt, Category.assoc, Iso.inv_hom_id_assoc, ha]
      rfl
    obtain ⟨e⟩ := hP i
    calc Module.Grassmannian.map (locAway r).hom (affinePoint C (Quotient.mk _ (P.pullback v.left)))
        = affinePoint _ (Quotient.mk _
            ((P.pullback v.left).pullback ((algSpec R).map (locAway r).op).left)) :=
          (affinePoint_pullback (locAway r) _).symm
      _ = affinePoint _ (Quotient.mk _ (P.pullback (((algSpec R).map (locAway r).op ≫ v).left))) :=
          congrArg _ (Quotient.sound (pullback_pullback_equiv _ _ _))
      _ = affinePoint _ (Quotient.mk _ (P.pullback ((a' ≫ coverPt i).left))) := by rw [ha']
      _ = affinePoint _ (Quotient.mk _ ((P.pullback (coverPt i).left).pullback a'.left)) :=
          congrArg _ (Quotient.sound (pullback_pullback_equiv _ _ _)).symm
      _ = affinePoint _ (Quotient.mk _ ((localQuot α i).pullback a'.left)) :=
          congrArg _ (Quotient.sound ⟨e.pullback a'.left⟩)
      _ = α.app _ (a' ≫ coverPt i) := affinePoint_localQuot_pullback α i a'
      _ = α.app _ ((algSpec R).map (locAway r).op ≫ v) := by rw [ha']
      _ = Module.Grassmannian.map (locAway r).hom (α.app C v) :=
          NatTrans.naturality_apply α (locAway r) v
  choose r hr H using H
  exact Module.Grassmannian.eq_of_map_localization_eq r
    (span_range_eq_top_of_forall_notMem r hr) H

variable (T) in
/-- **Every Grassmannian point comes from a quotient.** -/
theorem toPointsNatTrans_surjective :
    Function.Surjective (toPointsNatTrans (k := k) (n := n) T) := by
  intro α
  obtain ⟨P, hP⟩ := exists_glued_quot α
  exact ⟨Quotient.mk _ P, toPointsNatTrans_of_local α hP⟩

end Grassmannian

end AlgebraicGeometry
