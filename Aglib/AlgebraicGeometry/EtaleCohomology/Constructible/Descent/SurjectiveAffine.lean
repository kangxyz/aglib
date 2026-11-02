/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Basic.PullbackAffine
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.FinitePresentation.FiniteGeneration
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteStratification.AffineRepresentable
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.PositivePresentation.FiniteEtalePartitions
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Closure
public import Aglib.AlgebraicGeometry.EtaleCohomology.Proper.Reduction.SurjectivePullback

/-! # Surjective qcqs descent of constructible abelian sheaves to affine schemes

A positive scalar bound on the constructible original inverse image descends
by faithfulness. The original positive bounded presentation then has genuine
constructible stages on the affine target. After inverse image, finite
generation selects an epimorphic stage, which faithfulness reflects.
The same construction for its kernel gives the original coefficient as the
cokernel of an arrow between constructible coefficients.

This is the affine-target case of Stacks 095Q. The source is qcqs and the
original morphism is surjective; no flatness, finiteness or Noetherianity is
assumed. No constructibility or finite presentability of the original target
coefficient is used as an input.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible

universe u

attribute [local instance] hasSheafifyLarge

/-- A constructible original inverse image gives an actual constructible
coefficient surjecting onto the original coefficient on the affine target. -/
theorem exists_epi_from_constructible_of_surjective_pullback_of_isAffine
    {X S : Scheme.{u}} [IsAffine X] [CompactSpace S] [QuasiSeparatedSpace S]
    (f : S ⟶ X) [Surjective f] (F : AbelianSheaf.{u, u + 1} X)
    (hF : IsConstructible ((inverseImage f).obj F)) :
    ∃ (P : AbelianSheaf.{u, u + 1} X) (q : P ⟶ F), IsConstructible P ∧ Epi q := by
  have : (inverseImage f).Faithful := Proper.Reduction.inverseImage_faithful_of_surjective f
  obtain ⟨n, hn, hk⟩ := exists_positive_annihilator_of_isConstructible _ hF
  have hkill : n • 𝟙 F = 0 := by
    apply (inverseImage f).map_injective
    have hid : (inverseImage f).map (𝟙 F) =
        𝟙 ((inverseImage f).obj F) := (inverseImage f).map_id F
    have hnormal : n • (inverseImage f).map (𝟙 F) = 0 :=
      (congrArg (fun a => n • a) hid).trans hk
    simpa only [Functor.map_nsmul, Functor.map_zero] using hnormal
  have hparts : ∀ U : Scheme.AffineEtale X, ∀ V : X.affineOpens,
      ∃ p : FiniteLocallyClosedPartition V.1.toScheme,
        ∀ i, IsFinite ((siteBaseChange (p.inclusion i ≫ V.1.ι)).obj
          ((Scheme.AffineEtale.Spec X).obj U)).hom := by
    intro U
    have : IsAffine ((Scheme.AffineEtale.Spec X).obj U).left :=
      inferInstanceAs (IsAffine (Spec U.left.unop))
    exact PositivePresentation.finiteEtalePartitions_of_isAffine_of_isSeparated _
  obtain ⟨I, hI, hfilt, D, ι, hc, hstage⟩ :=
    PositivePresentation.exists_filtered_presentation_constructible_of_finiteEtalePartitions
      X n (Nat.ne_of_gt hn) hparts F hkill
  let := hI
  have : IsFiltered I := hfilt
  obtain ⟨i, hi⟩ := exists_epi_of_isColimit_of_isConstructible
    (isColimitOfPreserves (inverseImage f) hc.some) hF
  have hepi : Epi (ι.app i) := (inverseImage f).epi_of_epi_map hi
  exact ⟨(D.obj i).obj, ι.app i, (hstage i).2.2, hepi⟩

/-- Constructibility descends from a qcqs source along an arbitrary surjective
morphism to an affine scheme, for the original abelian coefficient sheaf. -/
theorem isConstructible_of_surjective_pullback_of_isAffine
    {X S : Scheme.{u}} [IsAffine X] [CompactSpace S] [QuasiSeparatedSpace S]
    (f : S ⟶ X) [Surjective f] (F : AbelianSheaf.{u, u + 1} X)
    (hF : IsConstructible ((inverseImage f).obj F)) : IsConstructible F := by
  obtain ⟨P, q, hP, hq⟩ :=
    exists_epi_from_constructible_of_surjective_pullback_of_isAffine f F hF
  have : Epi q := hq
  have hK : IsConstructible ((inverseImage f).obj (kernel q)) :=
    (isConstructible_iff_of_iso (PreservesKernel.iso (inverseImage f) q)).mpr
      (isConstructible_kernel ((inverseImage f).map q)
        (isConstructible_pullback_of_isAffine f hP) hF)
  obtain ⟨R, r, hR, hr⟩ :=
    exists_epi_from_constructible_of_surjective_pullback_of_isAffine f (kernel q) hK
  have : Epi r := hr
  let d : R ⟶ P := r ≫ kernel.ι q
  have hd : d ≫ q = 0 := by simp [d, Category.assoc]
  have hc : IsColimit (CokernelCofork.ofπ q hd) :=
    isCokernelEpiComp (Abelian.epiIsCokernelOfKernel _ (kernelIsKernel q)) r rfl
  exact (isConstructible_iff_of_iso
    (hc.coconePointUniqueUpToIso (cokernelIsCokernel d))).mpr
      (isConstructible_cokernel d hR hP)

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible
