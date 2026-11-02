/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.ArtinSchreier.HigherDirectImageKernel
public import Aglib.AlgebraicGeometry.EtaleCohomology.QuasiCoherent.HigherDirectImage.FrobeniusComparison
public import Aglib.AlgebraicGeometry.EtaleCohomology.QuasiCoherent.Semilinear.KernelRepresentation.GenericFinitePair
public import Aglib.AlgebraicGeometry.Cohomology.Proper.Finiteness
public import Aglib.AlgebraicGeometry.Cohomology.Proper.StructureSheaf.Coefficient

/-! # Generic finite local constancy of the original prime-field higher image

Proper coherence supplies both original higher-image modules. One common
nonzero principal shrink gives the finite kernel and the preceding epimorphism;
the original Artin--Schreier sequence identifies the actual prime-field image
with that same restricted kernel. No flatness or smoothness is assumed.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent

universe u w s e

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open QuasiCoherent

attribute [local instance] hasSheafifyLarge HasExt.standard HasDerivedCategory.standard
  Scheme.Modules.isQuasicoherent_unit
  instIsQuasicoherentOpensCarrierCarrierCommRingCatObjModulesRightDerivedPushforward_aglib

private theorem epi_map_of_intertwining
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {M N : C} (a : M ⟶ M) (b : N ⟶ N) (c : M ≅ N)
    (h : a ≫ c.hom = c.hom ≫ b) [Epi (F.map a)] : Epi (F.map b) := by
  have hw := congrArg (fun k => F.map k) h
  simp only [Functor.map_comp] at hw
  exact epi_of_epi_fac hw.symm

private def restrictedKernelComparison
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    (F : C ⥤ D) [PreservesFiniteLimits F]
    {M N : C} (a : M ⟶ M) (b : N ⟶ N) (c : M ≅ N)
    (h : a ≫ c.hom = c.hom ≫ b) :
    F.obj (kernel a) ≅ kernel (F.map b) := by
  have hw := congrArg (fun k => F.map k) h
  simp only [Functor.map_comp] at hw
  exact PreservesKernel.iso F a ≪≫
    kernel.mapIso (F.map a) (F.map b) (F.mapIso c) (F.mapIso c) hw

/-- Over a Noetherian integral affine base of characteristic `p`, each original
prime-field higher direct image of a proper morphism is finite locally constant
on a genuine nonzero principal localization of that same base. -/
theorem exists_restricted_primeFieldHigherDirectImage_finiteLocallyConstant
    (A : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f]
    (q p : ℕ) (hp : p.Prime) (hA : (p : A) = 0)
    [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
    [∀ U : (Spec (CommRingCat.of A)).Etale, HasExt.{s}
      (Sheaf ((smallEtaleTopology X).over ((siteBaseChange f).obj U)) AddCommGrpCat.{u + 1})]
    [∀ U : (Spec (CommRingCat.of A)).Etale,
      HasExt.{e} (AbelianSheaf.{u, u + 1} (Limits.pullback U.hom f))] :
    ∃ (r : A), r ≠ 0 ∧
      ∃ (R : Type u) (_ : CommRing R) (_ : Algebra A R) (_ : IsLocalization.Away r R)
        (_ : Etale (Spec.map (CommRingCat.ofHom (algebraMap A R)))),
        IsFiniteLocallyConstant
          ((etaleRestriction (Spec.map (CommRingCat.ofHom (algebraMap A R)))).obj
            ((higherDirectImage f q).obj (primeFieldSheaf X p))) := by
  let O : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let Q (n : ℕ) := ((Scheme.Modules.pushforward f).rightDerived n).obj O
  have hQ (n : ℕ) : affineFiniteSheaf (CommRingCat.of A) (Q n) :=
    (affineLocallyFiniteType_spec_iff (CommRingCat.of A) (Q n)).mp
      (Scheme.Cohomology.proper_higherDirectImage_coherent A f O
        (Scheme.Modules.affineLocallyFiniteType_unit X) n)
  let (n : ℕ) : (Q n).IsQuasicoherent := (hQ n).1
  let (n : ℕ) : Module.Finite A (moduleSpecΓFunctor.obj (Q n)) := (hQ n).2
  let Φ (n : ℕ) := higherDirectImageFrobenius.{u, w} f n p hp hA
  let δ (n : ℕ) := affineFrobenius (CommRingCat.of A) (Q n) p hp hA (Φ n) - 𝟙 _
  let hX := higherDirectImage_primeCast_source f p hA
  let b (n : ℕ) := (higherDirectImage f n).map (artinSchreierMap X p hp hX)
  let c (n : ℕ) := higherDirectImageComparison.{u, w, s, e} f O n ≪≫
    (higherDirectImage f n).mapIso (additiveUnitStructureIso X)
  have hc (n : ℕ) : δ n ≫ (c n).hom = (c n).hom ≫ b n :=
    higherDirectImageComparison_artinSchreierMap.{u, w, s, e} f n p hp hA
  have hpair := exists_common_restrictedKernel_finiteLocallyConstant_and_epi
    (CommRingCat.of A) (Q q) (Q (q - 1)) p hp hA (Φ q) (Φ (q - 1))
  obtain ⟨r, hr, R, hR, hAR, hloc, het, _, _, hfinite, _, hprev⟩ := hpair
  let j := Spec.map (CommRingCat.ofHom (algebraMap A R))
  let F := etaleRestriction j
  let eK : F.obj (kernel (δ q)) ≅ kernel (F.map (b q)) :=
    restrictedKernelComparison F (δ q) (b q) (c q) (hc q)
  have hkernel : Nonempty
      (F.obj ((higherDirectImage f q).obj (primeFieldSheaf X p)) ≅
        kernel (F.map (b q))) := by
    cases q with
    | zero => exact ⟨restrictedPrimeFieldHigherDirectImageKernelIsoZero f j p hp hX⟩
    | succ n =>
        let : Epi (F.map (δ n)) := hprev
        let : Epi (F.map (b n)) := epi_map_of_intertwining F (δ n) (b n) (c n) (hc n)
        exact ⟨restrictedPrimeFieldHigherDirectImageKernelIsoSucc f j p hp hX n⟩
  obtain ⟨eH⟩ := hkernel
  exact ⟨r, hr, R, hR, hAR, hloc, het,
    (isFiniteLocallyConstant_iff_of_iso (eH ≪≫ eK.symm)).mpr hfinite⟩

end AlgebraicGeometry.Scheme.EtaleCohomology
