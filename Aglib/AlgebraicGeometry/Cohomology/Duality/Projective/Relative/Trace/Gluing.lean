/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.AlgebraicGeometry.Modules.InternalHom.Gluing
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
/-!
# Gluing module morphisms from compatible affine restrictions

The affine restriction morphisms remain opaque. Their refinement and equality
transport laws give the ordinary sheaf matching condition over a separated base.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option Elab.async false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
universe u
namespace AlgebraicGeometry.Scheme.Cohomology.RelativeProjectiveTrace
/-- An affine open chart of `Y`, retaining its coordinate ring and open immersion. -/
abbrev AffineTraceChart (Y : Scheme.{u}) :=
  Σ A : CommRingCat.{u}, {j : Spec A ⟶ Y // IsOpenImmersion j}
/-- The open immersion underlying an affine trace chart. -/
abbrev affineTraceChartMap {Y : Scheme.{u}} (c : AffineTraceChart Y) := c.2.val
instance {Y : Scheme.{u}} (c : AffineTraceChart Y) :
    IsOpenImmersion (affineTraceChartMap c) := c.2.property
theorem affineTraceCharts_cover (Y : Scheme.{u}) (y : Y) :
    ∃ (c : AffineTraceChart Y) (x : Spec c.1), affineTraceChartMap c x = y := by
  let C := Y.affineOpenCover
  obtain ⟨x, hx⟩ := C.openCover.covers y
  exact ⟨⟨C.X (C.openCover.idx y), C.f (C.openCover.idx y), C.map_prop (C.openCover.idx y)⟩, x, hx⟩

section AffineGluing
variable {Y : Scheme.{u}} [Y.IsSeparated] (M N : Y.Modules)
  (t : ∀ {A : CommRingCat.{u}} (j : Spec A ⟶ Y) [IsOpenImmersion j],
    M.restrict j ⟶ N.restrict j)
  (hrefine : ∀ {A B : CommRingCat.{u}} (j : Spec A ⟶ Y) (k : Spec B ⟶ Spec A)
    [IsOpenImmersion j] [IsOpenImmersion k],
    Scheme.Modules.InternalHom.restrictionHomMap j k (t j) = t (k ≫ j))
  (hcongr : ∀ {A : CommRingCat.{u}} {j k : Spec A ⟶ Y}
    [IsOpenImmersion j] [IsOpenImmersion k] (w : j = k),
    t j ≫ (restrictFunctorCongr w).hom.app N =
      (restrictFunctorCongr w).hom.app M ≫ t k)

include hrefine hcongr in
theorem affineTraceLocal_matching (c d : AffineTraceChart Y) :
    let H : Y.Modules := Scheme.Modules.InternalHom.sheaf Y M N
    H.val.presheaf.map (homOfLE (inf_le_left :
      (affineTraceChartMap c).opensRange ⊓ (affineTraceChartMap d).opensRange ≤
        (affineTraceChartMap c).opensRange)).op
        (Scheme.Modules.InternalHom.restrictionHomEquiv (affineTraceChartMap c) M N
          (t (affineTraceChartMap c))) =
      H.val.presheaf.map (homOfLE (inf_le_right :
        (affineTraceChartMap c).opensRange ⊓ (affineTraceChartMap d).opensRange ≤
          (affineTraceChartMap d).opensRange)).op
        (Scheme.Modules.InternalHom.restrictionHomEquiv (affineTraceChartMap d) M N
          (t (affineTraceChartMap d))) := by
  let j := affineTraceChartMap c
  let k := affineTraceChartMap d
  let : IsAffineHom j := by
    have : IsAffineHom (j ≫ terminal.from Y) := by rw [terminal.comp_from]; infer_instance
    exact IsAffineHom.of_comp j (terminal.from Y)
  let W := pullback j k
  let s := W.isoSpec.inv
  let b := (s ≫ pullback.fst j k) ≫ j
  let d' := (s ≫ pullback.snd j k) ≫ k
  have w : b = d' := by simp only [b, d', Category.assoc, pullback.condition]
  have ew : b.opensRange = d'.opensRange := by
    apply TopologicalSpace.Opens.ext
    exact congrArg (fun t : Spec Γ(W, ⊤) ⟶ Y => Set.range t) w
  let H : Y.Modules := Scheme.Modules.InternalHom.sheaf Y M N
  let fb := t b
  let fd := t d'
  have hs := Scheme.Modules.InternalHom.restrictionHomEquiv_congr w M N fb fd
    (hcongr w)
  have hi := Scheme.Modules.InternalHom.restrictionHomEquiv_restrict j
    (s ≫ pullback.fst j k) M N (t j)
  have hk := Scheme.Modules.InternalHom.restrictionHomEquiv_restrict k
    (s ≫ pullback.snd j k) M N (t k)
  rw [hrefine] at hi hk
  change H.val.presheaf.map (eqToHom ew.symm).op
      (Scheme.Modules.InternalHom.restrictionHomEquiv b M N fb) =
    Scheme.Modules.InternalHom.restrictionHomEquiv d' M N fd at hs
  change H.val.presheaf.map
      (homOfLE (Scheme.Modules.InternalHom.restrictionRange_le j (s ≫ pullback.fst j k))).op
        (Scheme.Modules.InternalHom.restrictionHomEquiv j M N (t j)) =
    Scheme.Modules.InternalHom.restrictionHomEquiv b M N fb at hi
  change H.val.presheaf.map
      (homOfLE (Scheme.Modules.InternalHom.restrictionRange_le k (s ≫ pullback.snd j k))).op
        (Scheme.Modules.InternalHom.restrictionHomEquiv k M N (t k)) =
    Scheme.Modules.InternalHom.restrictionHomEquiv d' M N fd at hk
  have hsurj : Function.Surjective s := by
    intro x
    refine ⟨W.isoSpec.hom x, ?_⟩
    change (W.isoSpec.hom ≫ W.isoSpec.inv) x = x
    rw [W.isoSpec.hom_inv_id]; rfl
  have eb : b.opensRange = j.opensRange ⊓ k.opensRange := by
    calc
      b.opensRange = (pullback.fst j k ≫ j).opensRange := by
        apply TopologicalSpace.Opens.ext
        ext x
        constructor
        · rintro ⟨z, rfl⟩; exact ⟨s z, rfl⟩
        · rintro ⟨z, rfl⟩; obtain ⟨t, rfl⟩ := hsurj z; exact ⟨t, rfl⟩
      _ = _ := by
        apply TopologicalSpace.Opens.ext
        change Set.range (pullback.fst j k ≫ j) = Set.range j ∩ Set.range k
        exact IsOpenImmersion.range_pullback_to_base_of_left j k
  have ec : d'.opensRange = j.opensRange ⊓ k.opensRange := ew.symm.trans eb
  have hh := (congrArg (H.val.presheaf.map (eqToHom ew.symm).op) hi).trans (hs.trans hk.symm)
  let E := H.val.presheaf.mapIso (eqToIso ec).op
  apply (show Function.Injective E.hom from fun x y hxy =>
    (Iso.hom_inv_id_apply E x).symm.trans
      ((congrArg E.inv hxy).trans (Iso.hom_inv_id_apply E y)))
  change H.val.presheaf.map (eqToHom ec).op
      (H.val.presheaf.map (homOfLE inf_le_left).op
        (Scheme.Modules.InternalHom.restrictionHomEquiv j M N (t j))) =
    H.val.presheaf.map (eqToHom ec).op
      (H.val.presheaf.map (homOfLE inf_le_right).op
        (Scheme.Modules.InternalHom.restrictionHomEquiv k M N (t k)))
  have hiPath : H.val.presheaf.map (homOfLE inf_le_left).op ≫
      H.val.presheaf.map (eqToHom ec).op =
    H.val.presheaf.map
      (homOfLE (Scheme.Modules.InternalHom.restrictionRange_le j (s ≫ pullback.fst j k))).op ≫
        H.val.presheaf.map (eqToHom ew.symm).op := by
    rw [← Functor.map_comp, ← Functor.map_comp]
    congr 1
  have hkPath : H.val.presheaf.map
      (homOfLE (Scheme.Modules.InternalHom.restrictionRange_le k (s ≫ pullback.snd j k))).op =
    H.val.presheaf.map (homOfLE inf_le_right).op ≫
      H.val.presheaf.map (eqToHom ec).op := by
    rw [← Functor.map_comp]
    congr 1
  exact (ConcreteCategory.congr_hom hiPath
    (Scheme.Modules.InternalHom.restrictionHomEquiv j M N (t j))).trans
      (hh.trans (ConcreteCategory.congr_hom hkPath
        (Scheme.Modules.InternalHom.restrictionHomEquiv k M N (t k))))

include hrefine hcongr in
theorem affineTrace_existsUnique :
    ∃! z : M ⟶ N, ∀ c : AffineTraceChart Y,
      (Modules.restrictFunctor (affineTraceChartMap c)).map z = t (affineTraceChartMap c) := by
  let H : Y.Modules := Scheme.Modules.InternalHom.sheaf Y M N
  let A : TopCat.Sheaf AddCommGrpCat Y := ⟨H.val.presheaf, H.isSheaf⟩
  let s (c : AffineTraceChart Y) := Scheme.Modules.InternalHom.restrictionHomEquiv
    (affineTraceChartMap c) M N
      (t (affineTraceChartMap c))
  have hs : TopCat.Presheaf.IsCompatible H.val.presheaf
      (fun c => (affineTraceChartMap c).opensRange) s :=
    affineTraceLocal_matching M N t hrefine hcongr
  have hcover := Scheme.Modules.InternalHom.restrictionRanges_cover
    (fun c : AffineTraceChart Y => Spec c.1) affineTraceChartMap (affineTraceCharts_cover Y)
  obtain ⟨t, ht, huniq⟩ := A.existsUnique_gluing'
    (fun c : AffineTraceChart Y => (affineTraceChartMap c).opensRange) ⊤
    (fun _ => homOfLE le_top) hcover.ge s hs
  refine ⟨(Scheme.Modules.InternalHom.globalHomEquiv Y M N).symm t, ?_, ?_⟩
  · intro c
    apply (Scheme.Modules.InternalHom.restrictionHomEquiv (affineTraceChartMap c) M N).injective
    have hh := Scheme.Modules.InternalHom.globalHomEquiv_restrict
      (affineTraceChartMap c) M N ((Scheme.Modules.InternalHom.globalHomEquiv Y M N).symm t)
    exact hh.symm.trans (ht c)
  · intro F hF
    apply (Scheme.Modules.InternalHom.globalHomEquiv Y M N).injective
    have hsec := huniq (Scheme.Modules.InternalHom.globalHomEquiv Y M N F) (by
      intro c
      exact (Scheme.Modules.InternalHom.globalHomEquiv_restrict (affineTraceChartMap c) M N F).trans
        (congrArg (Scheme.Modules.InternalHom.restrictionHomEquiv
          (affineTraceChartMap c) M N) (hF c)))
    exact hsec.trans ((Scheme.Modules.InternalHom.globalHomEquiv Y M N).apply_symm_apply t).symm

end AffineGluing
theorem affineTraceCharts_hom_ext {Y : Scheme.{u}} {M N : Y.Modules} {b c : M ⟶ N}
    (he : ∀ d : AffineTraceChart Y, (Modules.restrictFunctor (affineTraceChartMap d)).map b =
        (Modules.restrictFunctor (affineTraceChartMap d)).map c) : b = c := by
  let d (i : AffineTraceChart Y) := (Modules.restrictFunctor (affineTraceChartMap i)).map c
  have hd : Scheme.Modules.InternalHom.RestrictionHomCompatible affineTraceChartMap M N d := by
    intro i j
    exact (Scheme.Modules.overlapRestrictIso (affineTraceChartMap i)
      (affineTraceChartMap j)).hom.naturality c
  have hb := Scheme.Modules.InternalHom.glueRestrictionHom_unique
    (fun i : AffineTraceChart Y => Spec i.1) affineTraceChartMap (affineTraceCharts_cover Y)
      M N d hd b he
  have hc := Scheme.Modules.InternalHom.glueRestrictionHom_unique
    (fun i : AffineTraceChart Y => Spec i.1) affineTraceChartMap (affineTraceCharts_cover Y)
      M N d hd c (fun _ => rfl)
  exact hb.trans hc.symm

end AlgebraicGeometry.Scheme.Cohomology.RelativeProjectiveTrace
