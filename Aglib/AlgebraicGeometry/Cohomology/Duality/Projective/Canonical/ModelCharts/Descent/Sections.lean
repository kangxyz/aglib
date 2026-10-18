/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.InternalHom.Gluing

/-!
# Original Hom sections on actual refinements and overlaps

The native composition and congruence square gives literal restriction
of the original Hom-sheaf section. Conversely, matching on each original
range intersection gives compatibility through the actual overlap map.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u v
namespace AlgebraicGeometry.Scheme.Modules
open InternalHom

private theorem canonicalRestrictionCongr_refl {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] (P : X.Modules) :
    (restrictFunctorCongr (rfl : j = j)).hom.app P = 𝟙 _ := by
  apply Scheme.Modules.hom_ext
  intro V
  rw [restrictFunctorCongr_hom_app_app]
  change P.presheaf.map (𝟙 (op (j ''ᵁ V))) = 𝟙 _
  exact P.presheaf.map_id _

/-- The original whole-arrow refinement square restricts the original Hom section. -/
theorem canonicalRestrictionHomEquiv_refinement {U V X : Scheme.{u}}
    (a : U ⟶ X) (b : V ⟶ X) (g : V ⟶ U)
    [IsOpenImmersion a] [IsOpenImmersion b] [IsOpenImmersion g]
    (h : b = g ≫ a) (M N : X.Modules)
    (f : M.restrict a ⟶ N.restrict a) (f' : M.restrict b ⟶ N.restrict b)
    (hSquare : ((restrictFunctorCongr h).app M ≪≫ (restrictFunctorComp g a).app M).hom ≫
        (restrictFunctor g).map f =
      f' ≫ ((restrictFunctorCongr h).app N ≪≫ (restrictFunctorComp g a).app N).hom) :
    let hba : b.opensRange ≤ a.opensRange := by
      subst b
      exact restrictionRange_le a g
    (InternalHom.sheaf X M N).val.presheaf.map (homOfLE hba).op
        (restrictionHomEquiv a M N f) = restrictionHomEquiv b M N f' := by
  subst b
  change ((restrictFunctorCongr (rfl : g ≫ a = g ≫ a)).hom.app M ≫
      (restrictFunctorComp g a).hom.app M) ≫ (restrictFunctor g).map f =
    f' ≫ ((restrictFunctorCongr (rfl : g ≫ a = g ≫ a)).hom.app N ≫
      (restrictFunctorComp g a).hom.app N) at hSquare
  simp only [canonicalRestrictionCongr_refl, Category.id_comp] at hSquare
  have hf : restrictionHomMap a g f = f' := by
    simpa [restrictionHomMap, Category.assoc] using congrArg
      (fun t => t ≫ (restrictFunctorComp g a).inv.app N) hSquare
  dsimp only
  have hr := restrictionHomEquiv_restrict a g M N f
  change (InternalHom.sheaf X M N).val.presheaf.map
      (homOfLE (restrictionRange_le a g)).op (restrictionHomEquiv a M N f) =
    restrictionHomEquiv (g ≫ a) M N (restrictionHomMap a g f) at hr
  simpa only [hf] using hr

private theorem canonicalRestrictionHomEquiv_congr_inverse {U X : Scheme.{u}}
    {j k : U ⟶ X} [IsOpenImmersion j] [IsOpenImmersion k]
    (h : j = k) (M N : X.Modules)
    (f : M.restrict j ⟶ N.restrict j) (g : M.restrict k ⟶ N.restrict k)
    (hs : let e : j.opensRange = k.opensRange := by cases h; rfl
      (InternalHom.sheaf X M N).val.presheaf.map (eqToHom e.symm).op
          (restrictionHomEquiv j M N f) = restrictionHomEquiv k M N g) :
    f ≫ (restrictFunctorCongr h).hom.app N =
      (restrictFunctorCongr h).hom.app M ≫ g := by
  subst k
  change (InternalHom.sheaf X M N).val.presheaf.map (𝟙 (op j.opensRange))
      (restrictionHomEquiv j M N f) = restrictionHomEquiv j M N g at hs
  have hi := ConcreteCategory.congr_hom
    ((InternalHom.sheaf X M N).val.presheaf.map_id (op j.opensRange))
    (restrictionHomEquiv j M N f)
  have hfg : f = g := (restrictionHomEquiv j M N).injective (hi.symm.trans hs)
  subst g
  simp only [canonicalRestrictionCongr_refl, Category.comp_id, Category.id_comp]

private theorem canonicalRestrictionHom_overlap_of_sections {X U V : Scheme.{u}}
    (j : U ⟶ X) (a : V ⟶ X) [IsOpenImmersion j] [IsOpenImmersion a]
    (M N : X.Modules) (f : M.restrict j ⟶ N.restrict j)
    (g : M.restrict a ⟶ N.restrict a)
    (hMatching : (InternalHom.sheaf X M N).val.presheaf.map
        (homOfLE (inf_le_left : j.opensRange ⊓ a.opensRange ≤ j.opensRange)).op
          (restrictionHomEquiv j M N f) =
      (InternalHom.sheaf X M N).val.presheaf.map
        (homOfLE (inf_le_right : j.opensRange ⊓ a.opensRange ≤ a.opensRange)).op
          (restrictionHomEquiv a M N g)) :
    (restrictFunctor (pullback.fst j a)).map f ≫ (overlapRestrictIso j a).hom.app N =
      (overlapRestrictIso j a).hom.app M ≫
        (restrictFunctor (pullback.snd j a)).map g := by
  let H : X.Modules := InternalHom.sheaf X M N
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
  have hi := restrictionHomEquiv_restrict j (pullback.fst j a) M N f
  change H.val.presheaf.map (homOfLE (restrictionRange_le j (pullback.fst j a))).op
      (restrictionHomEquiv j M N f) = restrictionHomEquiv b M N fb at hi
  have hk := restrictionHomEquiv_restrict a (pullback.snd j a) M N g
  change H.val.presheaf.map (homOfLE (restrictionRange_le a (pullback.snd j a))).op
      (restrictionHomEquiv a M N g) = restrictionHomEquiv c M N fc at hk
  have hiPath :
      H.val.presheaf.map (homOfLE inf_le_left).op ≫
          H.val.presheaf.map (eqToHom ec).op =
        H.val.presheaf.map (homOfLE (restrictionRange_le j (pullback.fst j a))).op ≫
          H.val.presheaf.map (eqToHom e.symm).op := by
    rw [← Functor.map_comp, ← Functor.map_comp]
    congr 1
  have hkPath : H.val.presheaf.map
      (homOfLE (restrictionRange_le a (pullback.snd j a))).op =
        H.val.presheaf.map (homOfLE inf_le_right).op ≫
          H.val.presheaf.map (eqToHom ec).op := by
    rw [← Functor.map_comp]
    congr 1
  have hs : H.val.presheaf.map (eqToHom e.symm).op (restrictionHomEquiv b M N fb) =
      restrictionHomEquiv c M N fc := by
    calc
      _ = H.val.presheaf.map (eqToHom e.symm).op
          (H.val.presheaf.map (homOfLE (restrictionRange_le j (pullback.fst j a))).op
            (restrictionHomEquiv j M N f)) := congrArg _ hi.symm
      _ = H.val.presheaf.map (eqToHom ec).op
          (H.val.presheaf.map (homOfLE inf_le_left).op
            (restrictionHomEquiv j M N f)) :=
        (ConcreteCategory.congr_hom hiPath (restrictionHomEquiv j M N f)).symm
      _ = H.val.presheaf.map (eqToHom ec).op
          (H.val.presheaf.map (homOfLE inf_le_right).op
            (restrictionHomEquiv a M N g)) := congrArg _ hMatching
      _ = H.val.presheaf.map (homOfLE (restrictionRange_le a (pullback.snd j a))).op
          (restrictionHomEquiv a M N g) :=
        (ConcreteCategory.congr_hom hkPath (restrictionHomEquiv a M N g)).symm
      _ = restrictionHomEquiv c M N fc := hk
  have hConj := canonicalRestrictionHomEquiv_congr_inverse
    (pullback.condition (f := j) (g := a)) M N fb fc hs
  apply (cancel_mono ((restrictFunctorComp (pullback.snd j a) a).inv.app N)).1
  apply (cancel_epi ((restrictFunctorComp (pullback.fst j a) j).hom.app M)).1
  simpa [fb, fc, restrictionHomMap, overlapRestrictIso, Category.assoc] using hConj

/-- Pairwise matching of literal Hom sections gives the original overlap compatibility. -/
theorem canonicalRestrictionHomCompatible_of_sections {X : Scheme.{u}} {ι : Type v}
    (Y : ι → Scheme.{u}) (a : ∀ i, Y i ⟶ X) [∀ i, IsOpenImmersion (a i)]
    (M N : X.Modules) (f : ∀ i, M.restrict (a i) ⟶ N.restrict (a i))
    (hMatching : ∀ i k, (InternalHom.sheaf X M N).val.presheaf.map
        (homOfLE (inf_le_left : (a i).opensRange ⊓ (a k).opensRange ≤ (a i).opensRange)).op
          (restrictionHomEquiv (a i) M N (f i)) =
      (InternalHom.sheaf X M N).val.presheaf.map
        (homOfLE (inf_le_right : (a i).opensRange ⊓ (a k).opensRange ≤ (a k).opensRange)).op
          (restrictionHomEquiv (a k) M N (f k))) :
    InternalHom.RestrictionHomCompatible a M N f := by
  intro i k
  exact canonicalRestrictionHom_overlap_of_sections (a i) (a k) M N (f i) (f k)
    (hMatching i k)

end AlgebraicGeometry.Scheme.Modules
