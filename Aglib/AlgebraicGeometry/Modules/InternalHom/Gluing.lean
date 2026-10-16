/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.AlgebraicGeometry.Modules.InternalHom.Restriction
public import Aglib.AlgebraicGeometry.Modules.Restriction.Overlap
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-!
# Gluing original module morphisms on native open families

Native compatibility on actual pullback overlaps gives a matching family in the original
structure-linear Hom sheaf. A jointly covering family of actual open immersions therefore
glues to a unique actual global morphism, with exact native restriction equations. The index
universe is independent of the scheme universe, and empty covers on empty schemes are allowed.
Both module sheaves are arbitrary. No finiteness, quasicoherence, or field hypothesis is used.
-/

@[expose] public section
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
universe u v
namespace AlgebraicGeometry.Scheme.Modules.InternalHom

/-- A genuine morphism over an open equal to the whole space is the original global morphism. -/
def fullOpenHomToGlobal {X : Scheme.{u}} {M N : X.Modules}
    (W : X.Opens) (hW : (⊤ : X.Opens) ≤ W)
    (a : SheafOfModules.Hom (M.over W) (N.over W)) : SheafOfModules.Hom M N := by
  let A : (Over.forget W).op ⋙ M.val.presheaf ⟶ (Over.forget W).op ⋙ N.val.presheaf :=
    (_root_.PresheafOfModules.toPresheaf (X.ringCatSheaf.over W).obj).map a.val
  let e (V : X.Opens) : V ⟶ W := homOfLE ((show V ≤ ⊤ from le_top).trans hW)
  let φ : M.val.presheaf ⟶ N.val.presheaf := {
    app V := A.app (op (Over.mk (e V.unop)))
    naturality {V V'} k := by
      let q : Over.mk (e V'.unop) ⟶ Over.mk (e V.unop) := Over.homMk k.unop
      exact A.naturality q.op }
  refine ⟨_root_.PresheafOfModules.homMk (M₁ := M.val) (M₂ := N.val) φ ?_⟩
  intro V r m
  exact (a.val.app (op (Over.mk (e V.unop)))).hom.map_smul r m

/-- Original global module morphisms identify with original global Hom-sheaf sections. -/
def globalHomEquiv (X : Scheme.{u}) (M N : X.Modules) :
    (M ⟶ N) ≃ Γ(sheaf X M N, (⊤ : X.Opens)) := by
  let e := sectionHomEquiv X M N (⊤ : X.Opens)
  refine {
    toFun f := e.symm ((SheafOfModules.overFunctor X.ringCatSheaf (⊤ : X.Opens)).map f)
    invFun s := fullOpenHomToGlobal (⊤ : X.Opens) le_rfl (e s)
    left_inv f := by
      simp only [Equiv.apply_symm_apply]
      ext V m
      rfl
    right_inv s := by
      apply e.injective
      simp only [Equiv.apply_symm_apply]
      ext V m
      rfl }

/-- The original global Hom-section restriction gives the original actual restricted arrow. -/
theorem globalHomEquiv_restrict {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (M N : X.Modules) (f : M ⟶ N) :
    (sheaf X M N).val.map (homOfLE (show j.opensRange ≤ (⊤ : X.Opens) from le_top)).op
        (globalHomEquiv X M N f) =
      restrictionHomEquiv j M N ((Scheme.Modules.restrictFunctor j).map f) := by
  apply (restrictionHomEquiv j M N).symm.injective
  simp only [Equiv.symm_apply_apply]
  ext V m
  rfl

/-- Equal actual open immersions give the same original Hom-section after native transport. -/
theorem restrictionHomEquiv_congr {U X : Scheme.{u}} {j k : U ⟶ X}
    [IsOpenImmersion j] [IsOpenImmersion k] (h : j = k) (M N : X.Modules)
    (f : M.restrict j ⟶ N.restrict j) (g : M.restrict k ⟶ N.restrict k)
    (hf : f ≫ (Scheme.Modules.restrictFunctorCongr h).hom.app N =
      (Scheme.Modules.restrictFunctorCongr h).hom.app M ≫ g) :
    let e : j.opensRange = k.opensRange := by cases h; rfl
    (sheaf X M N).val.map (eqToHom e.symm).op (restrictionHomEquiv j M N f) =
      restrictionHomEquiv k M N g := by
  subst k
  have hc (P : X.Modules) :
      (Scheme.Modules.restrictFunctorCongr (rfl : j = j)).hom.app P = 𝟙 _ := by
    apply Scheme.Modules.hom_ext
    intro V
    rw [Scheme.Modules.restrictFunctorCongr_hom_app_app]
    change P.presheaf.map (𝟙 (op (j ''ᵁ V))) = 𝟙 _
    exact P.presheaf.map_id _
  have hfg : f = g := by
    simpa only [hc, Category.comp_id, Category.id_comp] using hf
  subst g
  change (sheaf X M N).val.presheaf.map (𝟙 (op j.opensRange)) _ = _
  exact ConcreteCategory.congr_hom ((sheaf X M N).val.presheaf.map_id _) _

/-- The literal native overlap equation gives the corresponding base-restriction equation. -/
theorem overlapRestriction_conjugate {X U V : Scheme.{u}} (j : U ⟶ X) (a : V ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion a] (M N : X.Modules)
    (f : M.restrict j ⟶ N.restrict j) (g : M.restrict a ⟶ N.restrict a)
    (h : (Scheme.Modules.restrictFunctor (pullback.fst j a)).map f ≫
        (Scheme.Modules.overlapRestrictIso j a).hom.app N =
      (Scheme.Modules.overlapRestrictIso j a).hom.app M ≫
        (Scheme.Modules.restrictFunctor (pullback.snd j a)).map g) :
    restrictionHomMap j (pullback.fst j a) f ≫
        (Scheme.Modules.restrictFunctorCongr (pullback.condition (f := j) (g := a))).hom.app N =
      (Scheme.Modules.restrictFunctorCongr (pullback.condition (f := j) (g := a))).hom.app M ≫
        restrictionHomMap a (pullback.snd j a) g := by
  apply (cancel_mono ((Scheme.Modules.restrictFunctorComp (pullback.snd j a) a).hom.app N)).1
  apply (cancel_epi ((Scheme.Modules.restrictFunctorComp (pullback.fst j a) j).inv.app M)).1
  simpa [restrictionHomMap, Scheme.Modules.overlapRestrictIso, Category.assoc] using h

/-- Native compatibility on the actual pullback overlap gives a matching family of original
Hom-sheaf sections on the original range intersection. -/
theorem restrictionHomSections_overlap {X U V : Scheme.{u}} (j : U ⟶ X) (a : V ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion a] (M N : X.Modules)
    (f : M.restrict j ⟶ N.restrict j) (g : M.restrict a ⟶ N.restrict a)
    (h : (Scheme.Modules.restrictFunctor (pullback.fst j a)).map f ≫
        (Scheme.Modules.overlapRestrictIso j a).hom.app N =
      (Scheme.Modules.overlapRestrictIso j a).hom.app M ≫
        (Scheme.Modules.restrictFunctor (pullback.snd j a)).map g) :
    (sheaf X M N).val.presheaf.map
        (homOfLE (inf_le_left : j.opensRange ⊓ a.opensRange ≤ j.opensRange)).op
          (restrictionHomEquiv j M N f) =
      (sheaf X M N).val.presheaf.map
        (homOfLE (inf_le_right : j.opensRange ⊓ a.opensRange ≤ a.opensRange)).op
          (restrictionHomEquiv a M N g) := by
  let H : X.Modules := sheaf X M N
  let b := pullback.fst j a ≫ j
  let c := pullback.snd j a ≫ a
  let fb := restrictionHomMap j (pullback.fst j a) f
  let fc := restrictionHomMap a (pullback.snd j a) g
  have e : b.opensRange = c.opensRange := by
    apply TopologicalSpace.Opens.ext
    exact congrArg (fun t : CategoryTheory.Limits.pullback j a ⟶ X => Set.range t)
      (pullback.condition (f := j) (g := a))
  have eb : b.opensRange = j.opensRange ⊓ a.opensRange :=
    TopologicalSpace.Opens.ext (IsOpenImmersion.range_pullback_to_base_of_left j a)
  have ec : c.opensRange = j.opensRange ⊓ a.opensRange := e.symm.trans eb
  have hs := restrictionHomEquiv_congr (pullback.condition (f := j) (g := a)) M N fb fc
    (overlapRestriction_conjugate j a M N f g h)
  change H.val.presheaf.map (eqToHom e.symm).op (restrictionHomEquiv b M N fb) =
    restrictionHomEquiv c M N fc at hs
  have hi := restrictionHomEquiv_restrict j (pullback.fst j a) M N f
  change H.val.presheaf.map
      (homOfLE (restrictionRange_le j (pullback.fst j a))).op
        (restrictionHomEquiv j M N f) = restrictionHomEquiv b M N fb at hi
  have hk := restrictionHomEquiv_restrict a (pullback.snd j a) M N g
  change H.val.presheaf.map
      (homOfLE (restrictionRange_le a (pullback.snd j a))).op
        (restrictionHomEquiv a M N g) = restrictionHomEquiv c M N fc at hk
  have hh := (congrArg (H.val.presheaf.map (eqToHom e.symm).op) hi).trans
    (hs.trans hk.symm)
  let E := H.val.presheaf.mapIso (eqToIso ec).op
  apply (show Function.Injective E.hom from fun x y hxy =>
    (Iso.hom_inv_id_apply E x).symm.trans
      ((congrArg E.inv hxy).trans (Iso.hom_inv_id_apply E y)))
  change H.val.presheaf.map (eqToHom ec).op
      (H.val.presheaf.map (homOfLE inf_le_left).op (restrictionHomEquiv j M N f)) =
    H.val.presheaf.map (eqToHom ec).op
      (H.val.presheaf.map (homOfLE inf_le_right).op (restrictionHomEquiv a M N g))
  have hiPath :
      H.val.presheaf.map (homOfLE inf_le_left).op ≫
          H.val.presheaf.map (eqToHom ec).op =
        H.val.presheaf.map
          (homOfLE (restrictionRange_le j (pullback.fst j a))).op ≫
            H.val.presheaf.map (eqToHom e.symm).op := by
    rw [← Functor.map_comp, ← Functor.map_comp]
    congr 1
  have hkPath : H.val.presheaf.map
      (homOfLE (restrictionRange_le a (pullback.snd j a))).op =
        H.val.presheaf.map (homOfLE inf_le_right).op ≫
          H.val.presheaf.map (eqToHom ec).op := by
    rw [← Functor.map_comp]
    congr 1
  exact (ConcreteCategory.congr_hom hiPath (restrictionHomEquiv j M N f)).trans
    (hh.trans (ConcreteCategory.congr_hom hkPath (restrictionHomEquiv a M N g)))

/-- Original local morphisms agree through the native actual pullback-overlap comparison. -/
def RestrictionHomCompatible {X : Scheme.{u}} {ι : Type v} {Y : ι → Scheme.{u}}
    (a : ∀ i, Y i ⟶ X) [∀ i, IsOpenImmersion (a i)] (M N : X.Modules)
    (f : ∀ i, M.restrict (a i) ⟶ N.restrict (a i)) : Prop :=
  ∀ i k, (Scheme.Modules.restrictFunctor (pullback.fst (a i) (a k))).map (f i) ≫
      (Scheme.Modules.overlapRestrictIso (a i) (a k)).hom.app N =
    (Scheme.Modules.overlapRestrictIso (a i) (a k)).hom.app M ≫
      (Scheme.Modules.restrictFunctor (pullback.snd (a i) (a k))).map (f k)

/-- A jointly covering native open family has its original ranges as an open cover. -/
theorem restrictionRanges_cover {X : Scheme.{u}} {ι : Type v}
    (Y : ι → Scheme.{u}) (a : ∀ i, Y i ⟶ X) [∀ i, IsOpenImmersion (a i)]
    (hcover : ∀ x : X, ∃ (i : ι) (y : Y i), a i y = x) :
    iSup (fun i => (a i).opensRange) = ⊤ := by
  apply top_unique
  intro x _hx
  obtain ⟨i, y, hy⟩ := hcover x
  refine TopologicalSpace.Opens.mem_iSup.mpr ⟨i, ?_⟩
  exact ⟨y, hy⟩

section Cover
variable {X : Scheme.{u}} {ι : Type v}
  (Y : ι → Scheme.{u}) (a : ∀ i, Y i ⟶ X) [∀ i, IsOpenImmersion (a i)]
  (hcover : ∀ x : X, ∃ (i : ι) (y : Y i), a i y = x)
  (M N : X.Modules) (f : ∀ i, M.restrict (a i) ⟶ N.restrict (a i))
  (hcomp : RestrictionHomCompatible a M N f)

include hcover hcomp

/-- Compatible native local module morphisms have a unique actual global morphism. -/
theorem existsUnique_restrictionHom :
    ∃! F : M ⟶ N, ∀ i, (Scheme.Modules.restrictFunctor (a i)).map F = f i := by
  let H : X.Modules := sheaf X M N
  let A : TopCat.Sheaf Ab X := ⟨H.val.presheaf, H.isSheaf⟩
  let s i : Γ(H, (a i).opensRange) := restrictionHomEquiv (a i) M N (f i)
  have hs : TopCat.Presheaf.IsCompatible H.val.presheaf (fun i => (a i).opensRange) s := by
    intro i k
    exact restrictionHomSections_overlap (a i) (a k) M N (f i) (f k) (hcomp i k)
  obtain ⟨t, ht, huniq⟩ := A.existsUnique_gluing' (fun i => (a i).opensRange)
    (⊤ : X.Opens) (fun _ => homOfLE le_top) (restrictionRanges_cover Y a hcover).ge s hs
  refine ⟨(globalHomEquiv X M N).symm t, ?_, ?_⟩
  · intro i
    apply (restrictionHomEquiv (a i) M N).injective
    have hh := globalHomEquiv_restrict (a i) M N ((globalHomEquiv X M N).symm t)
    simp only [Equiv.apply_symm_apply] at hh
    exact hh.symm.trans (ht i)
  · intro F hF
    apply (globalHomEquiv X M N).injective
    have hsec : globalHomEquiv X M N F = t := huniq _ (by
      intro i
      exact (globalHomEquiv_restrict (a i) M N F).trans
        (congrArg (restrictionHomEquiv (a i) M N) (hF i)))
    exact hsec.trans ((globalHomEquiv X M N).apply_symm_apply t).symm

/-- The unique actual global morphism glued from the original compatible restricted arrows. -/
def glueRestrictionHom : M ⟶ N :=
  (existsUnique_restrictionHom Y a hcover M N f hcomp).choose

/-- The glued global morphism restricts to each original actual local arrow. -/
theorem glueRestrictionHom_restrict (i : ι) :
    (Scheme.Modules.restrictFunctor (a i)).map (glueRestrictionHom Y a hcover M N f hcomp) =
      f i :=
  (existsUnique_restrictionHom Y a hcover M N f hcomp).choose_spec.1 i

/-- Any actual global morphism with the original local arrows is the glued morphism. -/
theorem glueRestrictionHom_unique (F : M ⟶ N)
    (hF : ∀ i, (Scheme.Modules.restrictFunctor (a i)).map F = f i) :
    F = glueRestrictionHom Y a hcover M N f hcomp :=
  (existsUnique_restrictionHom Y a hcover M N f hcomp).choose_spec.2 F hF

end Cover

end AlgebraicGeometry.Scheme.Modules.InternalHom
