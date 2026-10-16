/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Localization

/-!
# Affine sheafification from original localization seeds

For an arbitrary module presheaf on `Spec R`, a compatible seed from a module
that is localization on every principal open supplies the actual
sheafification/tilde isomorphism. Its map sends each original sheafified seed
to the original tilde section. No differential, field, smoothness, or
cohomology construction is used.

Sole-owner extraction of the first generic block of
`Modules/Differentials/SmoothRank.lean`, admitted from Aglib revision
`40af743`. Original source: R5Lab
`AlgebraicGeometry/Curves/Differentials/SmoothRank.lean`, frozen revision
`79307ff88f07d34fd5c3edb859f799c55e38f290`, source SHA-256
`bab90251fd10024bc7477d90539648aa6b08e4047f6d288f0e755b0b852443b5`.
The native module namespace owns the implementation; the former SmoothRank
qualified names remain compatibility exports of this implementation.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
namespace AlgebraicGeometry.Scheme.Modules
universe u
variable {R : CommRingCat.{u}}

/-- Evaluate a module presheaf on `Spec R` with scalars transported to `R`. -/
def affinePresheafModules (P : (Spec R).PresheafOfModules) :
    (Spec R).Opensᵒᵖ ⥤ ModuleCat R :=
  (PresheafOfModules.forgetToPresheafModuleCat (op ⊤)
    (Limits.initialOpOfTerminal Limits.isTerminalTop)).obj P ⋙
      ModuleCat.restrictScalars (Scheme.ΓSpecIso R).inv.hom

/-- The scalar action on presheaf sections obtained from the affine global-sections comparison. -/
instance presheafModule (P : (Spec R).PresheafOfModules) (U : (Spec R).Opensᵒᵖ) :
    Module R (P.obj U) :=
  inferInstanceAs (Module R ((affinePresheafModules P).obj U))

/-- Compatibility of the transported affine scalars with the structure-section scalar action. -/
instance presheafModuleTower (P : (Spec R).PresheafOfModules)
    (U : (Spec R).Opensᵒᵖ) : IsScalarTower R Γ(Spec R, U.unop) (P.obj U) :=
  IsScalarTower.of_compHom R Γ(Spec R, U.unop) (P.obj U)

variable (P : (Spec R).PresheafOfModules) (N : ModuleCat R)
  (γ : (Functor.const (Spec R).Opensᵒᵖ).obj N ⟶ affinePresheafModules P)
  (hγ : ∀ r : R, IsLocalizedModule.Away r (γ.app (op (PrimeSpectrum.basicOpen r))).hom)

/-- The localization-seed comparison on the principal affine-open basis. -/
def affineBasicComparison :
    (inducedFunctor (PrimeSpectrum.basicOpen (R := R))).op ⋙ affinePresheafModules P ⟶
      (inducedFunctor (PrimeSpectrum.basicOpen (R := R))).op ⋙
        (modulesSpecToSheaf.obj (tilde N)).obj where
  app (r : Rᵒᵖ) := by
    let := hγ r.unop
    exact (IsLocalizedModule.linearEquiv (.powers r.unop)
      (γ.app (op (PrimeSpectrum.basicOpen r.unop))).hom
      (tilde.toOpen N (PrimeSpectrum.basicOpen r.unop)).hom).toModuleIso.hom
  naturality {r s : Rᵒᵖ} i := by
    let := hγ r.unop
    ext1
    apply IsLocalizedModule.ext (.powers r.unop)
      (γ.app (op (PrimeSpectrum.basicOpen r.unop))).hom
    · rw [Subtype.forall]
      change Submonoid.powers _ ≤ (IsUnit.submonoid _).comap _
      simp only [Submonoid.powers_le, Submonoid.mem_comap, IsUnit.mem_submonoid_iff]
      obtain ⟨n, a, e⟩ : ∃ n, r.unop ∣ s.unop ^ n := by
        simpa only [Ideal.mem_radical_iff, Ideal.mem_span_singleton] using
          (PrimeSpectrum.basicOpen_le_basicOpen_iff _ _).mp i.1.hom.le
      refine ((Commute.isUnit_mul_iff (b := algebraMap R _ a) (.map (.all _ _) _)).mp ?_).1
      rw [← map_mul, ← e, map_pow]
      exact ((tilde N).isUnit_algebraMap_end_of_le_basicOpen s.unop le_rfl).pow n
    · ext m
      have h := congrArg (fun f ↦ f m) (γ.naturality i.1.hom.op)
      dsimp at h ⊢
      erw [← h]
      simp only [IsLocalizedModule.linearEquiv_apply]
      rfl

/-- The extension of the affine basis comparison to all opens with transported scalars. -/
def affineComparisonR : affinePresheafModules P ⟶
    (modulesSpecToSheaf.obj (tilde N)).obj :=
  TopCat.Sheaf.restrictHomEquivHom _ _ PrimeSpectrum.isBasis_basic_opens
    (affineBasicComparison P N γ hγ)

/-- The actual module-presheaf morphism determined by the localization-seed comparison. -/
def affineComparison : P ⟶ (tilde N).val := by
  let α := affineComparisonR P N γ hγ
  apply PresheafOfModules.homMk (Functor.whiskerRight α (forget₂ (ModuleCat R) Ab))
  intro U t m
  change Γ(Spec R, U.unop) at t
  apply TopCat.Presheaf.IsSheaf.section_ext (tilde N).isSheaf
  intro x hxU
  obtain ⟨a, ⟨_, ⟨r, rfl⟩, rfl⟩, hxr, hrU : PrimeSpectrum.basicOpen _ ≤ _⟩ :=
    PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hxU U.unop.2
  refine ⟨_, hrU, hxr, ?_⟩
  have h (y : P.obj U) :
      α.app (op (PrimeSpectrum.basicOpen r)) (P.map (homOfLE hrU).op y) =
        (tilde N).val.map (homOfLE hrU).op (α.app U y) :=
    congrArg (fun f ↦ f y) (α.naturality (homOfLE hrU).op)
  change (tilde N).val.map (homOfLE hrU).op (α.app U (t • m)) =
    (tilde N).val.map (homOfLE hrU).op (t • (show Γ(tilde N, U.unop) from α.app U m))
  erw [← h, (tilde N).val.map_smul, ← h, P.map_smul]
  generalize (Spec R).ringCatSheaf.obj.map (homOfLE hrU).op t = t'
  let : IsScalarTower R Γ(Spec R, PrimeSpectrum.basicOpen r)
      (P.obj (op (PrimeSpectrum.basicOpen r))) :=
    presheafModuleTower P (op (PrimeSpectrum.basicOpen r))
  exact (IsLocalization.linearMap_compatibleSMul (.powers r)
    Γ(Spec R, PrimeSpectrum.basicOpen r)
    (P.obj (op (PrimeSpectrum.basicOpen r)))
    Γ(tilde N, PrimeSpectrum.basicOpen r)).map_smul (α.app _).hom t' _

theorem affineComparison_basic_bijective (r : R) :
    Function.Bijective (((PresheafOfModules.toPresheaf _).map
      (affineComparison P N γ hγ)).app (op (PrimeSpectrum.basicOpen r))) := by
  change Function.Bijective ((affineComparisonR P N γ hγ).app
    (op (PrimeSpectrum.basicOpen r)))
  rw [affineComparisonR, TopCat.Sheaf.extend_hom_app]
  let := hγ r
  exact (IsLocalizedModule.linearEquiv (.powers r)
    (γ.app (op (PrimeSpectrum.basicOpen r))).hom
    (tilde.toOpen N (PrimeSpectrum.basicOpen r)).hom).bijective

theorem affineComparison_locallyInjective :
    Presheaf.IsLocallyInjective (Opens.grothendieckTopology (Spec R))
      ((PresheafOfModules.toPresheaf _).map (affineComparison P N γ hγ)) := by
  let f := (PresheafOfModules.toPresheaf _).map (affineComparison P N γ hγ)
  constructor
  intro U x y h z hz
  obtain ⟨a, ⟨_, ⟨r, rfl⟩, rfl⟩, hzr, hrU : PrimeSpectrum.basicOpen _ ≤ _⟩ :=
    PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hz U.unop.2
  refine ⟨_, homOfLE hrU, ?_, hzr⟩
  apply (affineComparison_basic_bijective P N γ hγ r).injective
  change f.app _ (P.presheaf.map (homOfLE hrU).op x) =
    f.app _ (P.presheaf.map (homOfLE hrU).op y)
  have hx := congrArg (fun g ↦ g x) (f.naturality (homOfLE hrU).op)
  have hy := congrArg (fun g ↦ g y) (f.naturality (homOfLE hrU).op)
  exact hx.trans ((congrArg (fun v ↦ (tilde N).presheaf.map (homOfLE hrU).op v) h).trans hy.symm)

theorem affineComparison_locallySurjective :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology (Spec R))
      ((PresheafOfModules.toPresheaf _).map (affineComparison P N γ hγ)) := by
  constructor
  intro U t x hx
  obtain ⟨a, ⟨_, ⟨r, rfl⟩, rfl⟩, hxr, hrU : PrimeSpectrum.basicOpen _ ≤ _⟩ :=
    PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hx U.2
  refine ⟨_, homOfLE hrU, ?_, hxr⟩
  exact (affineComparison_basic_bijective P N γ hγ r).surjective _

/-- Localizing seed maps identify the actual presheaf sheafification with the tilde module sheaf. -/
def affineSheafificationTildeIso :
    (PresheafOfModules.sheafification (𝟙 (Spec R).ringCatSheaf.obj)).obj P ≅ tilde N := by
  let f := affineComparison P N γ hγ
  have := affineComparison_locallyInjective P N γ hγ
  have := affineComparison_locallySurjective P N γ hγ
  have hw := (Opens.grothendieckTopology (Spec R)).W_of_isLocallyBijective
    ((PresheafOfModules.toPresheaf _).map f)
  have hmap : IsIso ((presheafToSheaf (Opens.grothendieckTopology (Spec R)) Ab).map
      ((PresheafOfModules.toPresheaf _).map f)) :=
    ((Opens.grothendieckTopology (Spec R)).W_iff _).mp hw
  have : IsIso ((PresheafOfModules.sheafification (𝟙 (Spec R).ringCatSheaf.obj)).map f) := by
    have : IsIso ((SheafOfModules.toSheaf (Spec R).ringCatSheaf).map
        ((PresheafOfModules.sheafification (𝟙 (Spec R).ringCatSheaf.obj)).map f)) := hmap
    exact isIso_of_reflects_iso _ (SheafOfModules.toSheaf (Spec R).ringCatSheaf)
  exact asIso ((PresheafOfModules.sheafification (𝟙 (Spec R).ringCatSheaf.obj)).map f ≫
    (PresheafOfModules.sheafificationAdjunction (𝟙 (Spec R).ringCatSheaf.obj)).counit.app
      (tilde N))

theorem affineSheafificationTildeIso_homEquiv :
    (PresheafOfModules.sheafificationHomEquiv (𝟙 (Spec R).ringCatSheaf.obj))
      (affineSheafificationTildeIso P N γ hγ).hom = affineComparison P N γ hγ := by
  change (PresheafOfModules.sheafificationAdjunction (𝟙 (Spec R).ringCatSheaf.obj)).homEquiv
      P (tilde N) (_ ≫ _) = _
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 (Spec R).ringCatSheaf.obj)
  have h := adj.homEquiv_counit P (tilde N) (affineComparison P N γ hγ)
  exact (congrArg (adj.homEquiv P (tilde N)) h.symm).trans
    ((adj.homEquiv P (tilde N)).apply_symm_apply _)

/-- The affine sheafification comparison sends every localized seed to its canonical
tilde section. -/
theorem affineSheafificationTildeIso_seed (r : R) (m : N) :
    (affineSheafificationTildeIso P N γ hγ).hom.val.app (op (PrimeSpectrum.basicOpen r))
      (((PresheafOfModules.sheafificationAdjunction (𝟙 (Spec R).ringCatSheaf.obj)).unit.app P).app
        (op (PrimeSpectrum.basicOpen r)) (γ.app (op (PrimeSpectrum.basicOpen r)) m)) =
      tilde.toOpen N (PrimeSpectrum.basicOpen r) m := by
  change ((PresheafOfModules.sheafificationHomEquiv (𝟙 (Spec R).ringCatSheaf.obj))
    (affineSheafificationTildeIso P N γ hγ).hom).app (op (PrimeSpectrum.basicOpen r))
      (γ.app (op (PrimeSpectrum.basicOpen r)) m) = _
  rw [affineSheafificationTildeIso_homEquiv]
  change (affineComparisonR P N γ hγ).app (op (PrimeSpectrum.basicOpen r))
      (γ.app (op (PrimeSpectrum.basicOpen r)) m) = _
  rw [affineComparisonR, TopCat.Sheaf.extend_hom_app]
  let := hγ r
  exact IsLocalizedModule.linearEquiv_apply _ _ _ _

end AlgebraicGeometry.Scheme.Modules
