/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Localization.AffineSections
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Localization.AffineSectionsPushforward
/-!
# Quasicoherent pushforward from a quasi-compact open of an affine scheme

The proof uses actual restrictions and the finite-cover section-localization
theorem. Quasicoherence of the pushforward is a conclusion, not an input.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open PrimeSpectrum

namespace AlgebraicGeometry.Scheme.Modules.QuasiCoherent.AffineSections

/-- Restricting an open pushforward to its image is quasicoherent whenever
the original sheaf is quasicoherent. This uses only restriction and the
open-immersion counit, not quasicoherence of the pushforward on the target. -/
lemma isQuasicoherent_restrict_pushforward_opensRange
    {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
    (F : X.Modules) [F.IsQuasicoherent] :
    (((Scheme.Modules.pushforward j).obj F).restrict j.opensRange.ι).IsQuasicoherent := by
  let N := (Scheme.Modules.pushforward j).obj F
  have : (N.restrict j).IsQuasicoherent := isQuasicoherent_restrict_pushforward j F
  let e : Scheme.Modules.restrictFunctor j ⋙
      Scheme.Modules.restrictFunctor j.isoOpensRange.inv ≅
      Scheme.Modules.restrictFunctor j.opensRange.ι :=
    (Scheme.Modules.restrictFunctorComp j.isoOpensRange.inv j).symm ≪≫
      Scheme.Modules.restrictFunctorCongr j.isoOpensRange_inv_comp
  have h : ((N.restrict j).restrict j.isoOpensRange.inv).IsQuasicoherent := inferInstance
  exact (SheafOfModules.isQuasicoherent j.opensRange.toScheme.ringCatSheaf).prop_of_iso
    (e.app N) h

/-- The actual pushforward from a quasi-compact open into an affine scheme
satisfies section localization at every coordinate-ring element. -/
theorem isLocalizing_pushforward_of_isCompact
    {R : CommRingCat.{u}} {X : Scheme.{u}} (j : X ⟶ Spec R) [IsOpenImmersion j]
    (hcompact : IsCompact (j.opensRange : Set (Spec R)))
    (F : X.Modules) [F.IsQuasicoherent] :
    IsLocalizing (modulesSpecToSheaf.obj ((Scheme.Modules.pushforward j).obj F)) := by
  let N := (Scheme.Modules.pushforward j).obj F
  let P := (modulesSpecToSheaf.obj N).obj
  have : (N.restrict j.opensRange.ι).IsQuasicoherent :=
    isQuasicoherent_restrict_pushforward_opensRange j F
  intro f
  let a := P.map j.opensRange.leTop.op
  let b := P.map (homOfLE
    (inf_le_right : j.opensRange ⊓ PrimeSpectrum.basicOpen f ≤ PrimeSpectrum.basicOpen f)).op
  let c := P.map (PrimeSpectrum.basicOpen f).leTop.op
  let d := P.map (homOfLE
    (inf_le_left : j.opensRange ⊓ PrimeSpectrum.basicOpen f ≤ j.opensRange)).op
  have ha : IsIso a :=
    isIso_pushforward_modulesSpecToSheaf_map_of_preimage_eq j F _ (by simp)
  have hb : IsIso b :=
    isIso_pushforward_modulesSpecToSheaf_map_of_preimage_eq j F _ (by simp
      [Scheme.Hom.preimage_inf])
  have heq : a ≫ d = c ≫ b := by
    simp only [a, b, c, d, ← P.map_comp, ← op_comp]
    rfl
  have hd : IsLocalizedModule.Away f d.hom :=
    isLocalized_of_isCompact N j.opensRange hcompact f
  have had : IsLocalizedModule.Away f (d.hom.comp a.hom) :=
    (IsLocalizedModule.comp_iff_of_bijective_right _ _
      (ConcreteCategory.bijective_of_isIso a)).mpr hd
  have hcb : IsLocalizedModule.Away f (b.hom.comp c.hom) := by
    simpa only [← ModuleCat.hom_comp, heq] using had
  exact (IsLocalizedModule.comp_iff_of_bijective_left _ _
    (ConcreteCategory.bijective_of_isIso b)).mp hcb

/-- Quasicoherent modules push forward to quasicoherent modules along a
quasi-compact open immersion into an affine scheme. -/
theorem isQuasicoherent_pushforward_of_isCompact
    {R : CommRingCat.{u}} {X : Scheme.{u}} (j : X ⟶ Spec R) [IsOpenImmersion j]
    (hcompact : IsCompact (j.opensRange : Set (Spec R)))
    (F : X.Modules) [F.IsQuasicoherent] :
    ((Scheme.Modules.pushforward j).obj F).IsQuasicoherent := by
  rw [isQuasicoherent_iff_isIso_fromTildeΓ, isIso_fromTildeΓ_iff_isLocalizing]
  exact isLocalizing_pushforward_of_isCompact j hcompact F

/-- Every section on the inverse image of `D(f)` extends to the entire open
subscheme after multiplication by some power of `f`. The displayed sections
of the actual pushforward are definitionally the sections on those preimages. -/
theorem exists_pow_smul_extension
    {R : CommRingCat.{u}} {X : Scheme.{u}} (j : X ⟶ Spec R) [IsOpenImmersion j]
    (hcompact : IsCompact (j.opensRange : Set (Spec R)))
    (F : X.Modules) [F.IsQuasicoherent] (f : R)
    (s : Γ((Scheme.Modules.pushforward j).obj F, PrimeSpectrum.basicOpen f)) :
    ∃ (n : ℕ) (t : Γ((Scheme.Modules.pushforward j).obj F, ⊤)),
      ((Scheme.Modules.pushforward j).obj F).presheaf.map (PrimeSpectrum.basicOpen f).leTop.op t =
        f ^ n • s := by
  have h : IsLocalizedModule.Away f
      ((modulesSpecToSheaf.obj ((Scheme.Modules.pushforward j).obj F)).obj.map
        (PrimeSpectrum.basicOpen f).leTop.op).hom :=
    isLocalizing_pushforward_of_isCompact j hcompact F f
  obtain ⟨n, t, ht⟩ := h.surj _ _ s
  exact ⟨n, t, ht.symm⟩

/-- A global section vanishing over the inverse image of `D(f)` is killed
by some power of `f`. -/
theorem exists_pow_smul_eq_zero
    {R : CommRingCat.{u}} {X : Scheme.{u}} (j : X ⟶ Spec R) [IsOpenImmersion j]
    (hcompact : IsCompact (j.opensRange : Set (Spec R)))
    (F : X.Modules) [F.IsQuasicoherent] (f : R)
    (t : Γ((Scheme.Modules.pushforward j).obj F, ⊤))
    (ht : ((Scheme.Modules.pushforward j).obj F).presheaf.map
      (PrimeSpectrum.basicOpen f).leTop.op t = 0) :
    ∃ n : ℕ, f ^ n • t = 0 := by
  have h : IsLocalizedModule.Away f
      ((modulesSpecToSheaf.obj ((Scheme.Modules.pushforward j).obj F)).obj.map
        (PrimeSpectrum.basicOpen f).leTop.op).hom :=
    isLocalizing_pushforward_of_isCompact j hcompact F f
  have ht' : ((modulesSpecToSheaf.obj ((Scheme.Modules.pushforward j).obj F)).obj.map
      (PrimeSpectrum.basicOpen f).leTop.op).hom t = 0 := ht
  obtain ⟨n, hn⟩ := h.exists_of_eq f (x := t) (y := 0)
    (by rw [map_zero]; exact ht')
  exact ⟨n, by simpa only [smul_zero] using hn⟩

end AlgebraicGeometry.Scheme.Modules.QuasiCoherent.AffineSections
