/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Differentials.EtalePullback
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.FreeCover
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.Free
public import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# Smooth rank of the actual differential sheaf

Canonical affine localization maps identify the actual differential sheaf with
the tilde of the Kahler module. Standard-smooth presentations supply the basis,
and the existing canonical etale differential pullback glues these free charts.
The actual differential sheaf has the stated rank in every relative dimension
over every field in the original universe, including on the empty scheme.

Source: `R5Lab/AlgebraicGeometry/Curves/Differentials/SmoothRank.lean` at frozen R5 integration
`79307ff88f07d34fd5c3edb859f799c55e38f290`,
SHA-256 `bab90251fd10024bc7477d90539648aa6b08e4047f6d288f0e755b0b852443b5`.
The source free-cover and tilde-basis prerequisites have separate general owners.
-/

@[expose] public section
open AlgebraicGeometry.Scheme (constantSection constants)
open AlgebraicGeometry.Scheme.Modules.Differentials
  (constantsPresheafMap differentialPresheaf differentialPullbackMap differentialSheaf)
open AlgebraicGeometry.Scheme.OverField (FScheme)

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
namespace AlgebraicGeometry.Scheme.Modules.Differentials.SmoothRank
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
    letI := hγ r.unop
    exact (IsLocalizedModule.linearEquiv (.powers r.unop)
      (γ.app (op (PrimeSpectrum.basicOpen r.unop))).hom
      (tilde.toOpen N (PrimeSpectrum.basicOpen r.unop)).hom).toModuleIso.hom
  naturality {r s : Rᵒᵖ} i := by
    letI := hγ r.unop
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
  letI : IsScalarTower R Γ(Spec R, PrimeSpectrum.basicOpen r)
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
  letI := hγ r
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
  haveI := affineComparison_locallyInjective P N γ hγ
  haveI := affineComparison_locallySurjective P N γ hγ
  have hw := (Opens.grothendieckTopology (Spec R)).W_of_isLocallyBijective
    ((PresheafOfModules.toPresheaf _).map f)
  haveI hmap : IsIso ((presheafToSheaf (Opens.grothendieckTopology (Spec R)) Ab).map
      ((PresheafOfModules.toPresheaf _).map f)) :=
    ((Opens.grothendieckTopology (Spec R)).W_iff _).mp hw
  haveI : IsIso ((PresheafOfModules.sheafification (𝟙 (Spec R).ringCatSheaf.obj)).map f) := by
    haveI : IsIso ((SheafOfModules.toSheaf (Spec R).ringCatSheaf).map
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
  letI := hγ r
  exact IsLocalizedModule.linearEquiv_apply _ _ _ _

end AlgebraicGeometry.Scheme.Modules.Differentials.SmoothRank

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
namespace AlgebraicGeometry.Scheme.Modules.Differentials.SmoothRank
universe u
variable {F R : CommRingCat.{u}} (f : F ⟶ R)

/-- The structural ring map gives constants on all opens of its affine target. -/
def affineRelativeConstants :
    (Functor.const (Spec R).Opensᵒᵖ).obj F ⟶ (Spec R).presheaf where
  app U := f ≫ CommRingCat.ofHom (algebraMap R Γ(Spec R, U.unop))
  naturality {U V} i := by
    simp only [Functor.const_obj_map, Category.assoc]
    rfl

/-- The actual relative differential presheaf of the affine structural map. -/
abbrev affineRelativeDifferentials : (Spec R).PresheafOfModules :=
  PresheafOfModulesOfCommRing.DifferentialsConstruction.relativeDifferentials'
    (affineRelativeConstants f)

/-- The canonical localization map from ring differentials on the indicated affine open. -/
def affineRelativeSeedApp (U : (Spec R).Opensᵒᵖ) :
    CommRingCat.KaehlerDifferential f ⟶
      (affinePresheafModules (affineRelativeDifferentials f)).obj U := by
  let g : R ⟶ (Spec R).presheaf.obj U :=
    CommRingCat.ofHom (algebraMap R Γ(Spec R, U.unop))
  let q := CommRingCat.KaehlerDifferential.map
    (g := 𝟙 F) (g' := g) (f := f) (f' := (affineRelativeConstants f).app U)
    (by simp [affineRelativeConstants, g])
  exact ModuleCat.ofHom (Y := (affinePresheafModules (affineRelativeDifferentials f)).obj U)
    { toFun := q
      map_add' := q.hom.map_add
      map_smul' := q.hom.map_smul }

@[simp]
theorem affineRelativeSeedApp_d (U : (Spec R).Opensᵒᵖ) (a : R) :
    affineRelativeSeedApp f U (CommRingCat.KaehlerDifferential.d a) =
      CommRingCat.KaehlerDifferential.d (algebraMap R Γ(Spec R, U.unop) a) := by
  apply CommRingCat.KaehlerDifferential.map_d
  simp [affineRelativeConstants]

/-- The canonical localization maps from the ring differential module to the affine
differential presheaf. -/
def affineRelativeSeed :
    (Functor.const (Spec R).Opensᵒᵖ).obj (CommRingCat.KaehlerDifferential f) ⟶
      affinePresheafModules (affineRelativeDifferentials f) where
  app := affineRelativeSeedApp f
  naturality {U V} i := by
    apply CommRingCat.KaehlerDifferential.ext
    intro a
    change affineRelativeSeedApp f V (CommRingCat.KaehlerDifferential.d a) =
      (affineRelativeDifferentials f).map i
        (affineRelativeSeedApp f U (CommRingCat.KaehlerDifferential.d a))
    rw [affineRelativeSeedApp_d, affineRelativeSeedApp_d]
    erw [PresheafOfModulesOfCommRing.DifferentialsConstruction.relativeDifferentials'_map_d]
    rfl

/-- The canonical differential seed is module localization on each principal affine open. -/
theorem affineRelativeSeed_localizing (r : R) :
    IsLocalizedModule.Away r
      ((affineRelativeSeed f).app (op (PrimeSpectrum.basicOpen r))).hom := by
  letI : Algebra F R := f.hom.toAlgebra
  letI : Algebra F Γ(Spec R, PrimeSpectrum.basicOpen r) :=
    ((affineRelativeConstants f).app (op (PrimeSpectrum.basicOpen r))).hom.toAlgebra
  haveI : IsScalarTower F R Γ(Spec R, PrimeSpectrum.basicOpen r) :=
    IsScalarTower.of_algebraMap_eq' rfl
  let e : Ω[Γ(Spec R, PrimeSpectrum.basicOpen r)⁄F] ≃ₗ[R]
      (affinePresheafModules (affineRelativeDifferentials f)).obj
        (op (PrimeSpectrum.basicOpen r)) := {
    __ := AddEquiv.refl _
    map_smul' a m := by
      change (a • m : Ω[Γ(Spec R, PrimeSpectrum.basicOpen r)⁄F]) =
        (algebraMap R Γ(Spec R, PrimeSpectrum.basicOpen r) a) • m
      exact (IsScalarTower.algebraMap_smul Γ(Spec R, PrimeSpectrum.basicOpen r) a m).symm }
  letI := _root_.KaehlerDifferential.isLocalizedModule_map F R
    Γ(Spec R, PrimeSpectrum.basicOpen r) (.powers r)
  have he := IsLocalizedModule.of_linearEquiv (.powers r)
    (_root_.KaehlerDifferential.map F F R Γ(Spec R, PrimeSpectrum.basicOpen r)) e
  letI : Module F ((affinePresheafModules (affineRelativeDifferentials f)).obj
      (op (PrimeSpectrum.basicOpen r))) := Module.compHom _ f.hom
  letI : IsScalarTower F R ((affinePresheafModules (affineRelativeDifferentials f)).obj
      (op (PrimeSpectrum.basicOpen r))) := IsScalarTower.of_compHom _ _ _
  convert! he using 1
  apply Derivation.liftKaehlerDifferential_unique
  ext a
  change affineRelativeSeedApp f (op (PrimeSpectrum.basicOpen r))
      (CommRingCat.KaehlerDifferential.d a) =
    _root_.KaehlerDifferential.map F F R Γ(Spec R, PrimeSpectrum.basicOpen r)
      (_root_.KaehlerDifferential.D F R a)
  rw [affineRelativeSeedApp_d, _root_.KaehlerDifferential.map_D]
  rfl

/-- The sheafification of the actual affine differential presheaf is the tilde of the
ring-theoretic Kahler module, via its canonical localization maps. -/
def affineRelativeDifferentialIso :
    (PresheafOfModules.sheafification (𝟙 (Spec R).ringCatSheaf.obj)).obj
      (affineRelativeDifferentials f) ≅ tilde (CommRingCat.KaehlerDifferential f) :=
  affineSheafificationTildeIso _ _ (affineRelativeSeed f) (affineRelativeSeed_localizing f)

end AlgebraicGeometry.Scheme.Modules.Differentials.SmoothRank

noncomputable section
namespace AlgebraicGeometry.Scheme.Modules.Differentials.SmoothRank
universe u v

/-- A standard smooth presentation of relative dimension `n` supplies a basis of its
differential module. -/
def standardSmoothDifferentialBasis
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    (n : ℕ) [Algebra.IsStandardSmoothOfRelativeDimension n R S] :
    Module.Basis (Fin n) S Ω[S⁄R] := by
  classical
  exact Classical.choice (show Nonempty (Module.Basis (Fin n) S Ω[S⁄R]) from by
    obtain ⟨ι, σ, hσ, hι, P, hP⟩ :=
      (inferInstance : Algebra.IsStandardSmoothOfRelativeDimension n R S).out
    letI : Finite ι := hι
    letI : Finite σ := hσ
    letI : Fintype ι := Fintype.ofFinite ι
    letI : Fintype σ := Fintype.ofFinite σ
    have hc : Fintype.card ((Set.range P.map)ᶜ : Set ι) = n := by
      rw [Fintype.card_compl_set, Set.card_range_of_injective P.map_inj]
      simpa only [Algebra.Presentation.dimension, Nat.card_eq_fintype_card] using hP
    exact ⟨P.basisKaehler.reindex (Fintype.equivFinOfCardEq hc)⟩)

end AlgebraicGeometry.Scheme.Modules.Differentials.SmoothRank

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open AlgebraicGeometry.Scheme.OverField
namespace AlgebraicGeometry.Scheme.Modules.Differentials.SmoothRank
universe u
variable (F S : Type u) [Field F] [CommRing S] [Algebra F S]

/-- The spectrum of an algebra with its structural morphism to the field spectrum. -/
def affineFScheme : FScheme F :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap F S)))

/-- Constants on the affine field scheme are restrictions of the original algebra map. -/
theorem affineConstantSection (U : (Spec (CommRingCat.of S)).Opens) :
    constantSection (affineFScheme F S) U =
      ((Scheme.ΓSpecIso (.of S)).inv ≫ (Spec (.of S)).presheaf.map U.leTop.op).hom.comp
        (algebraMap F S) := by
  ext a
  dsimp [constantSection, constants, affineFScheme]
  change ((Scheme.ΓSpecIso (.of F)).inv ≫
    (Spec.map (CommRingCat.ofHom (algebraMap F S))).appTop ≫
      (Spec (.of S)).presheaf.map U.leTop.op) a = _
  rw [← Scheme.ΓSpecIso_inv_naturality_assoc]
  rfl

/-- The affine field scheme has precisely the constants presheaf of its algebra map. -/
theorem constantsPresheafMap_affineFScheme :
    constantsPresheafMap (affineFScheme F S) =
      affineRelativeConstants (CommRingCat.ofHom (algebraMap F S)) := by
  ext U a
  change constantSection (affineFScheme F S) U.unop a = _
  rw [affineConstantSection]
  rfl

/-- Actual differential/tilde identification on an affine scheme over the field. -/
def differentialSheafAffineIso :
    differentialSheaf (affineFScheme F S) ≅
      tilde (CommRingCat.KaehlerDifferential (CommRingCat.ofHom (algebraMap F S))) := by
  dsimp only [differentialSheaf, differentialPresheaf]
  rw [constantsPresheafMap_affineFScheme]
  exact affineRelativeDifferentialIso _

/-- The actual affine differential sheaf is free with the standard-smooth basis. -/
def standardSmoothAffineFreeIso (n : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension n F S] :
    SheafOfModules.free (R := (Spec (.of S)).ringCatSheaf) (ULift.{u} (Fin n)) ≅
      differentialSheaf (affineFScheme F S) := by
  let b : Module.Basis (ULift.{u} (Fin n)) (CommRingCat.of S)
      (CommRingCat.KaehlerDifferential (CommRingCat.ofHom (algebraMap F S))) := by
    let f : CommRingCat.of F ⟶ CommRingCat.of S := CommRingCat.ofHom (algebraMap F S)
    have hf : RingHom.IsStandardSmoothOfRelativeDimension n f.hom := by
      change RingHom.IsStandardSmoothOfRelativeDimension n (algebraMap F S)
      exact (RingHom.isStandardSmoothOfRelativeDimension_algebraMap (n := n)).mpr inferInstance
    letI : Algebra (CommRingCat.of F) (CommRingCat.of S) := f.hom.toAlgebra
    letI : Algebra.IsStandardSmoothOfRelativeDimension n (CommRingCat.of F) (CommRingCat.of S) :=
      hf.toAlgebra
    change Module.Basis (ULift.{u} (Fin n)) (CommRingCat.of S)
      Ω[(CommRingCat.of S)⁄(CommRingCat.of F)]
    exact (standardSmoothDifferentialBasis (CommRingCat.of F) (CommRingCat.of S) n).reindex
      Equiv.ulift.symm
  exact (Scheme.Modules.tildeBasisIso _ b).symm ≪≫
    (differentialSheafAffineIso F S).symm

end AlgebraicGeometry.Scheme.Modules.Differentials.SmoothRank

noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open AlgebraicGeometry.Scheme.OverField
namespace AlgebraicGeometry.Scheme.Modules.Differentials.SmoothRank
universe u
variable {F : Type u} [Field F] (X : FScheme F)

/-- A constant section is the structural map on sections after the canonical
field-spectrum comparison. -/
lemma constantSection_eq_appLE (V : X.left.Opens) :
    CommRingCat.ofHom (constantSection X V) =
      (Scheme.ΓSpecIso (.of F)).inv ≫ X.hom.appLE ⊤ V (by simp) := by
  rfl

/-- The canonical spectrum chart commutes with the structural morphism to the field. -/
lemma fromSpec_overField (V : X.left.Opens) (hV : IsAffineOpen V) :
    hV.fromSpec ≫ X.hom = Spec.map (CommRingCat.ofHom (constantSection X V)) := by
  have h := IsAffineOpen.SpecMap_appLE_fromSpec X.hom
    (isAffineOpen_top _) hV (show V ≤ X.hom ⁻¹ᵁ ⊤ by simp)
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp] at h
  rw [← h, ← constantSection_eq_appLE]

/-- A smooth field scheme of relative dimension `n` has standard smooth affine charts
of dimension `n`. -/
lemma exists_standardSmoothChart (n : ℕ) [SmoothOfRelativeDimension n X.hom] (x : X.left) :
    ∃ (V : X.left.Opens), IsAffineOpen V ∧ x ∈ V ∧
      RingHom.IsStandardSmoothOfRelativeDimension n (constantSection X V) := by
  obtain ⟨U, hU, V, hV, hx, e, hf⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension (n := n) (f := X.hom) x
  have hxU : X.hom x ∈ U := e hx
  have htop : U = ⊤ := by
    ext y
    constructor
    · intro; trivial
    · intro
      have hy : y = X.hom x := Subsingleton.elim _ _
      subst y
      exact hxU
  subst U
  refine ⟨V, hV, hx, ?_⟩
  have h := (RingHom.isStandardSmoothOfRelativeDimension_respectsIso (n := n)).2
    (X.hom.appLE ⊤ V e).hom
    (Scheme.ΓSpecIso (.of F)).symm.commRingCatIsoToRingEquiv hf
  change RingHom.IsStandardSmoothOfRelativeDimension n
    ((Scheme.ΓSpecIso (.of F)).inv ≫ X.hom.appLE ⊤ V e).hom at h
  simpa only [← constantSection_eq_appLE, CommRingCat.hom_ofHom] using h

/-- Actual free differential presentation on a standard-smooth affine chart. -/
def standardSmoothChartFreeIso (n : ℕ) (V : X.left.Opens) (hV : IsAffineOpen V)
    (hstd : RingHom.IsStandardSmoothOfRelativeDimension n (constantSection X V)) :
    SheafOfModules.free (R := V.toScheme.ringCatSheaf) (ULift.{u} (Fin n)) ≅
      (differentialSheaf X).restrict V.ι := by
  letI : Algebra F Γ(X.left, V) := (constantSection X V).toAlgebra
  letI : Algebra.IsStandardSmoothOfRelativeDimension n F Γ(X.left, V) := hstd.toAlgebra
  let a : affineFScheme F Γ(X.left, V) ⟶ X :=
    Over.homMk hV.fromSpec (fromSpec_overField X V hV)
  letI : Etale a.left := inferInstanceAs (Etale hV.fromSpec)
  letI := EtalePullback.isIso_differentialPullbackMap a
  let c : SheafOfModules.free (R := (Spec Γ(X.left, V)).ringCatSheaf)
      (ULift.{u} (Fin n)) ≅ (differentialSheaf X).restrict hV.fromSpec :=
    standardSmoothAffineFreeIso F Γ(X.left, V) n ≪≫
      (asIso (differentialPullbackMap a)).symm ≪≫
      ((Scheme.Modules.restrictFunctorIsoPullback hV.fromSpec).app (differentialSheaf X)).symm
  exact Scheme.Modules.freeIsoOfRestrictIso hV.isoSpec.symm
    ((differentialSheaf X).restrict V.ι)
    (c ≪≫ (Scheme.Modules.restrictFunctorComp hV.isoSpec.inv V.ι).app (differentialSheaf X))

end AlgebraicGeometry.Scheme.Modules.Differentials.SmoothRank

namespace AlgebraicGeometry.Scheme.Modules.Differentials

universe u

/-- Smooth differentials have actual local bases of the specified relative rank. -/
theorem differentialSheaf_hasRank_of_smooth (K : Type u) [Field K] (X : FScheme K) (n : ℕ)
    (hX : SmoothOfRelativeDimension n X.hom) :
    Scheme.Modules.SheafHasRank (differentialSheaf X) n := by
  letI := hX
  classical
  choose V hV hx hstd using SmoothRank.exists_standardSmoothChart X n
  have hcov : IsOpenCover V := by
    change (⨆ x : X.left, V x) = ⊤
    apply top_unique
    intro x _
    exact Opens.mem_iSup.mpr ⟨x, hx x⟩
  exact Scheme.Modules.sheafHasRank_of_coverFreeIso V hcov
    (fun x ↦ SmoothRank.standardSmoothChartFreeIso X n (V x) (hV x) (hstd x))

variable {F : Type u} [Field F]

/-- Smooth relative differentials are finite locally free, with the basis supplied by their rank. -/
theorem smoothDifferential_finiteLocallyFree (X : FScheme F) (n : ℕ)
    (hX : SmoothOfRelativeDimension n X.hom) :
    Scheme.Modules.SheafFiniteLocallyFree (differentialSheaf X) := by
  exact (differentialSheaf_hasRank_of_smooth F X n hX).isFiniteLocallyFree

end AlgebraicGeometry.Scheme.Modules.Differentials
