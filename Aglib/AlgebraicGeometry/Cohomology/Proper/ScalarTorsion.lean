/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Proper.Finiteness
public import Aglib.AlgebraicGeometry.Cohomology.Proper.StructureSheaf.Coefficient
public import Aglib.AlgebraicGeometry.Surfaces.Resolution.ExtensionGraph.Construction
public import Aglib.AlgebraicGeometry.Cohomology.Restriction.Coefficients
public import Aglib.AlgebraicGeometry.Cohomology.MayerVietoris.GeometricTop
public import Aglib.AlgebraicGeometry.Modules.IdealPowers.Functor
public import Aglib.AlgebraicGeometry.Modules.IdealPowers.Thickening
public import Aglib.AlgebraicGeometry.Modules.Pullback.Unit
public import Aglib.AlgebraicGeometry.Modules.IdealPowers.IdealSheaf
public import Aglib.AlgebraicGeometry.Morphisms.Proper.BirationalSurface
public import Aglib.AlgebraicGeometry.Spec.Localization
public import Aglib.RingTheory.LocalRing.ReducedPrincipalCover
public import Aglib.AlgebraicGeometry.Cohomology.Exact.KernelLength
public import Aglib.AlgebraicGeometry.Cohomology.Proper.BirationalStructureSheaf
public import Aglib.RingTheory.IntegralClosure.Colength
public import Aglib.RingTheory.Nagata.Finite
public import Aglib.RingTheory.Nagata.Normalization
public import Aglib.RingTheory.Length.Torsion
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors

/-!
# Uniform scalar torsion on original proper birational surface cohomology

For a normal Noetherian Nagata local domain of dimension two, each nonzero
base scalar has one finite length bound on its original H1 torsion, uniform
over all proper birational normal integral models. The scalar action is the
one induced by the original structural coefficient map.

The proof uses the literal total principal divisor. Its proper global
sections map through the original punctured restriction into the integral
closure of the principal quotient in its total quotient ring. The quotient
projection, base scalars and restriction maps are retained. A finite proper
transform or an embedding of all divisor sections is not required.
-/

@[expose] public noncomputable section Lower

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open IsLocalRing
open scoped nonZeroDivisors

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

/-- Proper coherent H0 finiteness applies to the original structural ring map,
with the scalar action induced by that same ring map. -/
theorem structuralCoefficients_finite_of_proper
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f] :
    (f.appTop.hom.comp (Scheme.ΓSpecIso (.of A)).inv.hom).Finite := by
  let α : A →+* Γ(X, ⊤) := f.appTop.hom.comp (Scheme.ΓSpecIso (.of A)).inv.hom
  let O : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let : Algebra A Γ(X, ⊤) := α.toAlgebra
  let := moduleCohomologyModuleOfHom X α O 0
  let : Module.Finite A (Sheaf.H.{u + 1} (moduleAddSheaf X O) 0) :=
    moduleCohomology_finite_of_proper A f O (affineLocallyFiniteType_unit X) 0
  let e₀ : Sheaf.H.{u + 1} (moduleAddSheaf X O) 0 ≃+ Γ(X, ⊤) :=
    Sheaf.H.equiv₀ (moduleAddSheaf X O) isTerminalTop
  let e : Sheaf.H.{u + 1} (moduleAddSheaf X O) 0 ≃ₗ[A] Γ(X, ⊤) :=
    { __ := e₀
      map_smul' := fun a x => by
        have h := (Sheaf.H.equiv₀_naturality
          (isTerminalTop (α := X.Opens)) (moduleScalarOfGlobal X O (α a)) x).symm
        change e₀ (Sheaf.H.map (moduleScalarOfGlobal X O (α a)) 0 x) =
          globalRestriction X ⊤ (α a) * e₀ x at h
        change e₀ (Sheaf.H.map (moduleScalarOfGlobal X O (α a)) 0 x) = α a * e₀ x
        simpa only [globalRestriction_top_apply] using h }
  change Module.Finite A Γ(X, ⊤)
  exact Module.Finite.of_surjective e.toLinearMap e.surjective

private theorem presheafRestriction_injective_of_geometric
    (X : Scheme.{u}) (U : X.Opens) (M : X.Modules) (N : U.toScheme.Modules)
    (φ : M ⟶ (Scheme.Modules.pushforward U.ι).obj N) (n : ℕ)
    (hφ : Function.Injective (moduleCohomologyMapAlong U.ι φ n)) :
    Function.Injective (((moduleAddSheaf X M).cohomologyPresheaf n).map
      (homOfLE (show U ≤ ⊤ from le_top)).op) := by
  let A := moduleAddSheaf X M
  let B := moduleAddSheaf U.toScheme N
  let P : X.Opensᵒᵖ ⥤ AddCommGrpCat.{u + 1} := A.cohomologyPresheaf n
  let Q : U.toScheme.Opensᵒᵖ ⥤ AddCommGrpCat.{u + 1} := B.cohomologyPresheaf n
  let i : U ⟶ (⊤ : X.Opens) := homOfLE le_top
  let k := (Opens.map U.ι.base).map i
  let θ : P ⟶ (Opens.map U.ι.base).op ⋙ Q :=
    zariskiCohomologyOpenMap U.ι A B (moduleCoefficientPullback U.ι φ) n
  have hk : IsIso k := by
    apply (PartialOrder.isIso_iff_eq k).mpr
    change U.ι ⁻¹ᵁ U = U.ι ⁻¹ᵁ ⊤
    simp
  let : IsIso k := hk
  have hkinj : Function.Injective (Q.map k.op) :=
    (ConcreteCategory.bijective_of_isIso (Q.map k.op)).1
  let eA := sheafHPrimeTopAddEquiv X A n
  let eB := sheafHPrimeTopAddEquiv U.toScheme B n
  have htop (z : Sheaf.H'.{u + 1} A n ⊤) :
      eB (θ.app (op ⊤) z) = moduleCohomologyMapAlong U.ι φ n (eA z) :=
    sheafHPrimeTopAddEquiv_geometric U.ι A B (moduleCoefficientPullback U.ι φ) n z
  intro x y hxy
  have hθ : θ.app (op ⊤) x = θ.app (op ⊤) y := by
    apply hkinj
    have hx := ConcreteCategory.congr_hom (θ.naturality i.op) x
    have hy := ConcreteCategory.congr_hom (θ.naturality i.op) y
    change θ.app (op U) (P.map i.op x) = Q.map k.op (θ.app (op ⊤) x) at hx
    change θ.app (op U) (P.map i.op y) = Q.map k.op (θ.app (op ⊤) y) at hy
    exact hx.symm.trans ((congrArg (θ.app (op U)) hxy).trans hy)
  apply eA.injective
  apply hφ
  exact (htop x).symm.trans ((congrArg eB hθ).trans (htop y))

/-- The original Nagata-surface V1 theorem makes the actual cohomology-presheaf
restriction injective, in precisely the presentation used by KernelLength. -/
theorem structureH1_puncturedPresheafRestriction_injective_of_isNagata
    {A : Type u} [CommRing A] [IsDomain A] [IsLocalRing A]
    [IsNoetherianRing A] [IsIntegrallyClosed A]
    {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f] [IsDominant f]
    (hff : IsIso (CommRingCat.ofHom (Scheme.functionFieldMap f)))
    (hdim : ringKrullDim A = 2) (hX : Scheme.NormalStalks X)
    (hA : IsNagataRing.{u, 0} A) :
    Function.Injective
      (((moduleAddSheaf X (SheafOfModules.unit X.ringCatSheaf)).cohomologyPresheaf 1).map
        (homOfLE (show f ⁻¹ᵁ Scheme.localPuncturedSpectrum A ≤ ⊤ from le_top)).op) := by
  let U := f ⁻¹ᵁ Scheme.localPuncturedSpectrum A
  exact presheafRestriction_injective_of_geometric X U
    (SheafOfModules.unit X.ringCatSheaf) (SheafOfModules.unit U.toScheme.ringCatSheaf)
    (Scheme.Hom.structureModuleMap U.ι) 1
    (structureH1_puncturedRestriction_injective_of_isNagata f hff hdim hX hA)

end AlgebraicGeometry.Scheme.Cohomology

end Lower

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open IsLocalRing
open scoped nonZeroDivisors

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

private theorem scalarCokernel_principal_annihilation
    (X : Scheme.{u}) {A : Type u} [CommRing A] (α : A →+* Γ(X, ⊤))
    (M : X.Modules) (c : A) (a : Ideal.span {c}) :
    globalScalarEndomorphism X M (α a) ≫
      cokernel.π (globalScalarEndomorphism X M (α c)) = 0 := by
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton.mp a.property
  have he : globalScalarEndomorphism X M (α a) =
      globalScalarEndomorphism X M (α r) ≫ globalScalarEndomorphism X M (α c) := by
    change ((globalScalarCenter X) (α a)).app M =
      ((globalScalarCenter X) (α r)).app M ≫ ((globalScalarCenter X) (α c)).app M
    rw [hr, map_mul, map_mul, CatCenter.mul_app']
  rw [he, Category.assoc, cokernel.condition, comp_zero]

private def scalarCokernelIdealQuotientIso
    (X : Scheme.{u}) {A : Type u} [CommRing A] (α : A →+* Γ(X, ⊤))
    (M : X.Modules) (c : A) :
    cokernel (globalScalarEndomorphism X M (α c)) ≅
      idealQuotient X α M (Ideal.span {c}) := by
  let s := globalScalarEndomorphism X M (α c)
  let J : Ideal A := Ideal.span {c}
  have hz : s ≫ idealQuotientπ X α M J = 0 := by
    change globalScalarEndomorphism X M (α c) ≫ idealQuotientπ X α M J = 0
    rw [← idealMultipleScalar_ι X α M J ⟨c, Ideal.mem_span_singleton_self c⟩,
      Category.assoc, idealMultipleι_quotientπ, comp_zero]
  let i := cokernel.desc s (idealQuotientπ X α M J) hz
  let j := idealQuotientDesc X α J (cokernel.π s)
    (scalarCokernel_principal_annihilation X α M c)
  have hi : cokernel.π s ≫ i = idealQuotientπ X α M J := cokernel.π_desc _ _ _
  have hj : idealQuotientπ X α M J ≫ j = cokernel.π s := idealQuotientπ_desc _ _ _ _ _
  refine ⟨i, j, ?_, ?_⟩
  · apply (cancel_epi (cokernel.π s)).mp
    rw [← Category.assoc, hi, hj, Category.comp_id]
  · apply (cancel_epi (idealQuotientπ X α M J)).mp
    rw [← Category.assoc, hj, hi, Category.comp_id]

private theorem scalarCokernelIdealQuotientIso_π
    (X : Scheme.{u}) {A : Type u} [CommRing A] (α : A →+* Γ(X, ⊤))
    (M : X.Modules) (c : A) :
    cokernel.π (globalScalarEndomorphism X M (α c)) ≫
      (scalarCokernelIdealQuotientIso X α M c).hom =
        idealQuotientπ X α M (Ideal.span {c}) := by
  change cokernel.π _ ≫ cokernel.desc _ _ _ = _
  exact cokernel.π_desc _ _ _

private def scalarCokernelTotalDivisorIso
    {A : Type u} [CommRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A)) (c : A) :
    cokernel (globalScalarEndomorphism X (SheafOfModules.unit X.ringCatSheaf)
      (idealThickeningBaseScalar f c)) ≅
      (Scheme.Modules.pushforward (idealThickeningι f (Ideal.span {c}))).obj
        (SheafOfModules.unit (idealThickeningSpace f (Ideal.span {c})).ringCatSheaf) := by
  let O : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let : O.IsQuasicoherent :=
    quasicoherent_of_affineCharts O (fun B j _ => ((affineLocallyFiniteType_unit X) B j).1)
  exact scalarCokernelIdealQuotientIso X (idealThickeningBaseScalar f) O c ≪≫
    idealQuotientThickeningIso f O (Ideal.span {c}) ≪≫
      (Scheme.Modules.pushforward (idealThickeningι f (Ideal.span {c}))).mapIso
        (pullbackUnitIso (idealThickeningι f (Ideal.span {c})))

private theorem scalarCokernelTotalDivisorIso_π
    {A : Type u} [CommRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A)) (c : A) :
    cokernel.π (globalScalarEndomorphism X (SheafOfModules.unit X.ringCatSheaf)
      (idealThickeningBaseScalar f c)) ≫ (scalarCokernelTotalDivisorIso f c).hom =
      Scheme.Hom.structureModuleMap (idealThickeningι f (Ideal.span {c})) := by
  let j := idealThickeningι f (Ideal.span {c})
  let O : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let : O.IsQuasicoherent :=
    quasicoherent_of_affineCharts O (fun B k _ => ((affineLocallyFiniteType_unit X) B k).1)
  have hunit := pullbackUnitIso_homEquiv j
  change (pullbackPushforwardAdjunction j).unit.app O ≫
      (Scheme.Modules.pushforward j).map (pullbackUnitIso j).hom =
        Scheme.Hom.structureModuleMap j at hunit
  have compose {P M₀ M₁ M₂ M₃ : X.Modules} (π : P ⟶ M₀)
      (e₀ : M₀ ≅ M₁) (e₁ : M₁ ≅ M₂) (e₂ : M₂ ≅ M₃)
      (q : P ⟶ M₁) (r : P ⟶ M₂) (t : P ⟶ M₃)
      (h₀ : π ≫ e₀.hom = q) (h₁ : q ≫ e₁.hom = r) (h₂ : r ≫ e₂.hom = t) :
      π ≫ (e₀ ≪≫ e₁ ≪≫ e₂).hom = t := by
    simp only [Iso.trans_hom, ← Category.assoc, h₀, h₁, h₂]
  exact compose _ (scalarCokernelIdealQuotientIso X (idealThickeningBaseScalar f) O c)
    (idealQuotientThickeningIso f O (Ideal.span {c}))
    ((Scheme.Modules.pushforward j).mapIso (pullbackUnitIso j)) _ _ _
    (scalarCokernelIdealQuotientIso_π X (idealThickeningBaseScalar f) O c)
    (idealQuotientπ_thickeningIso_hom f O (Ideal.span {c})) hunit

private theorem scalarStructure_mono {X : Scheme.{u}} [IsIntegral X]
    (a : Γ(X, ⊤)) (ha : a ≠ 0) :
    Mono (globalScalarEndomorphism X (SheafOfModules.unit X.ringCatSheaf) a) := by
  have hinj (U : X.Opens) : Function.Injective
      ((globalScalarEndomorphism X (SheafOfModules.unit X.ringCatSheaf) a).val.app (op U)) := by
    by_cases hU : Nonempty U
    · let := hU
      have hres : X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op a ≠ 0 := by
        intro hz
        apply ha
        apply map_injective_of_isIntegral X (homOfLE (le_top : U ≤ ⊤))
        simpa only [map_zero] using hz
      intro x y hxy
      have formula (z : Γ(X, U)) :
          (show Γ(X, U) from
            (globalScalarEndomorphism X (SheafOfModules.unit X.ringCatSheaf) a).val.app
              (op U) z) = X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op a * z :=
        globalScalarEndomorphism_app X (SheafOfModules.unit X.ringCatSheaf) a U z
      have he : (show Γ(X, U) from x) = (show Γ(X, U) from y) :=
        mul_left_cancel₀ hres ((formula x).symm.trans (hxy.trans (formula y)))
      exact he
    · have hbot : U = ⊥ := by
        apply bot_unique
        intro x hx
        exact (hU ⟨⟨x, hx⟩⟩).elim
      let : Subsingleton Γ(X, U) :=
        CommRingCat.subsingleton_of_isTerminal (X.sheaf.isTerminalOfEqEmpty hbot)
      intro x y _
      exact Subsingleton.elim (show Γ(X, U) from x) (show Γ(X, U) from y)
  have hm : Mono (globalScalarEndomorphism X (SheafOfModules.unit X.ringCatSheaf) a).val :=
    PresheafOfModules.mono_of_injective (fun {U} => hinj U.unop)
  exact (SheafOfModules.forget X.ringCatSheaf).mono_of_mono_map hm

end AlgebraicGeometry.Scheme.Cohomology

namespace AlgebraicGeometry.Scheme.Cohomology

private theorem scalarTorsion_isIso_principalRestriction
    {A : Type u} [CommRing A] [IsDomain A] [IsLocalRing A]
    [IsNoetherianRing A] [IsIntegrallyClosed A]
    {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f] [IsDominant f]
    (hff : IsIso (CommRingCat.ofHom (Scheme.functionFieldMap f)))
    (hdim : ringKrullDim A = 2) (g : A) (hg : g ∈ maximalIdeal A) :
    IsIso (f ∣_ PrimeSpectrum.basicOpen g) := by
  apply f.isIso_restrict_of_stalk_dimension_le_one hff
    (fun p => (isIntegrallyClosed_and_isDomain_stalk_Spec A p).symm)
  intro p hp
  apply ringKrullDim_stalk_le_one_of_ne_closedPoint A hdim.le p
  intro he
  subst p
  exact hp hg

end AlgebraicGeometry.Scheme.Cohomology

namespace AlgebraicGeometry.Scheme.Cohomology

private def scalarTorsionAmbientPrincipalIso
    {A : Type u} [CommRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A)) (g : A)
    [IsIso (f ∣_ PrimeSpectrum.basicOpen g)] :
    (f ⁻¹ᵁ PrimeSpectrum.basicOpen g).toScheme ≅ Spec (.of (Localization.Away g)) :=
  asIso (f ∣_ PrimeSpectrum.basicOpen g) ≪≫ basicOpenIsoSpecAway (R := CommRingCat.of A) g

private theorem scalarTorsionAmbientPrincipalIso_hom_base
    {A : Type u} [CommRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A)) (g : A)
    [IsIso (f ∣_ PrimeSpectrum.basicOpen g)] :
    (scalarTorsionAmbientPrincipalIso f g).hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away g))) =
        (f ⁻¹ᵁ PrimeSpectrum.basicOpen g).ι ≫ f := by
  dsimp only [scalarTorsionAmbientPrincipalIso, Iso.trans_hom, asIso_hom]
  rw [Category.assoc, basicOpenIsoSpecAway_hom_SpecMap]
  exact morphismRestrict_ι f (PrimeSpectrum.basicOpen g)

private abbrev scalarTorsionTotalPrincipalOpen
    {A : Type u} [CommRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A)) (c g : A) :=
  idealThickeningι f (Ideal.span {c}) ⁻¹ᵁ (f ⁻¹ᵁ PrimeSpectrum.basicOpen g)

private theorem scalarTorsionTotalPrincipalPullback
    {A : Type u} [CommRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A)) (c g : A)
    [IsIso (f ∣_ PrimeSpectrum.basicOpen g)] :
    IsPullback
      ((idealThickeningι f (Ideal.span {c}) ∣_ (f ⁻¹ᵁ PrimeSpectrum.basicOpen g)) ≫
        (scalarTorsionAmbientPrincipalIso f g).hom)
      ((scalarTorsionTotalPrincipalOpen f c g).ι ≫
        idealThickeningStructure f (Ideal.span {c}))
      (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away g))))
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {c})))) := by
  let j := idealThickeningι f (Ideal.span {c})
  let V := f ⁻¹ᵁ PrimeSpectrum.basicOpen g
  have hglobal := IsPullback.of_hasPullback f
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {c}))))
  have hlocal := (((isPullback_morphismRestrict j V).flip).paste_horiz hglobal.flip).flip
  refine hlocal.of_iso (Iso.refl _) (scalarTorsionAmbientPrincipalIso f g)
    (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · exact (Category.id_comp _).symm
  · exact (Category.comp_id _).trans (Category.id_comp _).symm
  · simpa only [Iso.refl_hom, Category.comp_id] using
      (scalarTorsionAmbientPrincipalIso_hom_base f g).symm
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]

private def scalarTorsionTotalPrincipalIso
    {A : Type u} [CommRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A)) (c g : A)
    [IsIso (f ∣_ PrimeSpectrum.basicOpen g)] :
    (scalarTorsionTotalPrincipalOpen f c g).toScheme ≅
      Spec (.of (Localization.Away (Ideal.Quotient.mk (Ideal.span {c}) g))) :=
  (scalarTorsionTotalPrincipalPullback f c g).isoIsPullback _ _
    (Scheme.isPullback_specMap_localizationAway
      (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {c}))) g)

private theorem scalarTorsionTotalPrincipalIso_inv_structure
    {A : Type u} [CommRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A)) (c g : A)
    [IsIso (f ∣_ PrimeSpectrum.basicOpen g)] :
    (scalarTorsionTotalPrincipalIso f c g).inv ≫
        (scalarTorsionTotalPrincipalOpen f c g).ι ≫
          idealThickeningStructure f (Ideal.span {c}) =
      Spec.map (CommRingCat.ofHom
        (algebraMap (A ⧸ Ideal.span {c})
          (Localization.Away (Ideal.Quotient.mk (Ideal.span {c}) g)))) := by
  simpa only [scalarTorsionTotalPrincipalIso, Category.assoc] using
    (scalarTorsionTotalPrincipalPullback f c g).isoIsPullback_inv_snd
      (Spec (.of (Localization.Away g))) (Spec (.of (A ⧸ Ideal.span {c})))
      (Scheme.isPullback_specMap_localizationAway
        (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {c}))) g)

private theorem scalarTorsionTotalDivisor_equation
    {A : Type u} [CommRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A)) (c : A)
    (z : idealThickeningSpace f (Ideal.span {c})) :
    c ∈ (f (idealThickeningι f (Ideal.span {c}) z)).asIdeal := by
  have he := congrArg (fun k => k z)
    (pullback.condition (f := f)
      (g := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {c})))))
  change f (idealThickeningι f (Ideal.span {c}) z) =
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {c})))
      (idealThickeningStructure f (Ideal.span {c}) z) at he
  rw [he]
  change Ideal.Quotient.mk (Ideal.span {c}) c ∈
    (idealThickeningStructure f (Ideal.span {c}) z).asIdeal
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self c)]
  exact Ideal.zero_mem _

private theorem scalarTorsion_punctured_eq_basicOpen_sup
    {A : Type u} [CommRing A] [IsLocalRing A] (c g : A)
    (hc : c ∈ maximalIdeal A) (hg : g ∈ maximalIdeal A)
    (hrad : (Ideal.span {c} ⊔ Ideal.span {g}).radical = maximalIdeal A) :
    Scheme.localPuncturedSpectrum A = PrimeSpectrum.basicOpen c ⊔ PrimeSpectrum.basicOpen g := by
  ext P
  change P ≠ closedPoint A ↔ c ∉ P.asIdeal ∨ g ∉ P.asIdeal
  constructor
  · intro hP
    by_cases hcP : c ∈ P.asIdeal
    · right
      intro hgP
      have hIP : Ideal.span {c} ⊔ Ideal.span {g} ≤ P.asIdeal :=
        sup_le ((Ideal.span_singleton_le_iff_mem P.asIdeal).mpr hcP)
          ((Ideal.span_singleton_le_iff_mem P.asIdeal).mpr hgP)
      have hmP : maximalIdeal A ≤ P.asIdeal := by
        rw [← hrad]
        exact P.isPrime.radical_le_iff.mpr hIP
      exact hP (PrimeSpectrum.ext (le_antisymm (le_maximalIdeal P.isPrime.ne_top) hmP))
    · exact Or.inl hcP
  · rintro h rfl
    exact h.elim (fun h => h hc) (fun h => h hg)

private theorem scalarTorsionTotalPrincipalOpen_eq_punctured
    {A : Type u} [CommRing A] [IsLocalRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A)) (c g : A)
    (hc : c ∈ maximalIdeal A) (hg : g ∈ maximalIdeal A)
    (hrad : (Ideal.span {c} ⊔ Ideal.span {g}).radical = maximalIdeal A) :
    scalarTorsionTotalPrincipalOpen f c g =
      idealThickeningι f (Ideal.span {c}) ⁻¹ᵁ (f ⁻¹ᵁ Scheme.localPuncturedSpectrum A) := by
  ext z
  change f (idealThickeningι f (Ideal.span {c}) z) ∈ PrimeSpectrum.basicOpen g ↔
    f (idealThickeningι f (Ideal.span {c}) z) ∈ Scheme.localPuncturedSpectrum A
  rw [scalarTorsion_punctured_eq_basicOpen_sup c g hc hg hrad]
  change g ∉ (f (idealThickeningι f (Ideal.span {c}) z)).asIdeal ↔
    c ∉ (f (idealThickeningι f (Ideal.span {c}) z)).asIdeal ∨
      g ∉ (f (idealThickeningι f (Ideal.span {c}) z)).asIdeal
  exact ⟨Or.inr, fun h => h.elim
    (fun hc' => False.elim (hc' (scalarTorsionTotalDivisor_equation f c z))) id⟩

end AlgebraicGeometry.Scheme.Cohomology

namespace AlgebraicGeometry.Scheme.Cohomology

private theorem scalarTorsion_parameter_regular
    {A : Type u} [CommRing A] [IsDomain A] [IsLocalRing A]
    [IsNoetherianRing A] [IsIntegrallyClosed A]
    (hdim : ringKrullDim A = 2) (c g : A) (hc : c ≠ 0)
    (hrad : (Ideal.span {c} ⊔ Ideal.span {g}).radical = maximalIdeal A) :
    Ideal.Quotient.mk (Ideal.span {c}) g ∈ nonZeroDivisors (A ⧸ Ideal.span {c}) := by
  have hreg : IsSMulRegular (A ⧸ Ideal.span {c}) g := by
    intro x y hxy
    change g • x = g • y at hxy
    apply sub_eq_zero.mp
    by_contra hne
    obtain ⟨P, hP, hle⟩ := exists_le_isAssociatedPrime_of_isNoetherianRing A (x - y) hne
    have hcP : c ∈ P := by
      apply hle
      rw [Submodule.mem_colon_singleton]
      change Ideal.Quotient.mk (Ideal.span {c}) c * (x - y) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self c), zero_mul]
    have hgP : g ∈ P := by
      apply hle
      rw [Submodule.mem_colon_singleton]
      change g • (x - y) = 0
      rw [smul_sub, hxy, sub_self]
    have hIP : Ideal.span {c} ⊔ Ideal.span {g} ≤ P :=
      sup_le ((Ideal.span_singleton_le_iff_mem P).mpr hcP)
        ((Ideal.span_singleton_le_iff_mem P).mpr hgP)
    have hmP : maximalIdeal A ≤ P := by
      rw [← hrad]
      exact hP.isPrime.radical_le_iff.mpr hIP
    have he : P = maximalIdeal A := le_antisymm (le_maximalIdeal hP.isPrime.ne_top) hmP
    have hh := hP.height_le_one_of_principal hc
    have hheight : (maximalIdeal A).height = 2 :=
      WithBot.coe_injective (maximalIdeal_height_eq_ringKrullDim.trans hdim)
    rw [he, hheight] at hh
    norm_num at hh
  apply mem_nonZeroDivisors_iff_left.mpr
  intro x hx
  apply hreg
  change Ideal.Quotient.mk (Ideal.span {c}) g * x =
    Ideal.Quotient.mk (Ideal.span {c}) g * 0
  simpa only [mul_zero] using hx

private theorem scalarTorsion_exists_parameter
    {A : Type u} [CommRing A] [IsDomain A] [IsLocalRing A]
    [IsNoetherianRing A] [IsIntegrallyClosed A]
    (hdim : ringKrullDim A = 2) (c : A) (hc : c ≠ 0) (hcm : c ∈ maximalIdeal A) :
    ∃ g : A, g ∈ maximalIdeal A ∧
      (Ideal.span {c} ⊔ Ideal.span {g}).radical = maximalIdeal A ∧
      Ideal.Quotient.mk (Ideal.span {c}) g ∈ nonZeroDivisors (A ⧸ Ideal.span {c}) := by
  let : Ring.KrullDimLE 2 A := Ring.krullDimLE_iff.mpr hdim.le
  obtain ⟨g, hg, hrad⟩ := IsLocalRing.exists_parameter_pair_containing A c hc hcm
  exact ⟨g, hg, hrad, scalarTorsion_parameter_regular hdim c g hc hrad⟩

private def scalarTorsionAwayToFractionRing
    (C : Type u) [CommRing C] (g : C) (hg : g ∈ nonZeroDivisors C) :
    Localization.Away g →+* FractionRing C :=
  IsLocalization.Away.lift g (IsLocalization.map_units (FractionRing C) ⟨g, hg⟩)

private theorem scalarTorsionAwayToFractionRing_algebraMap
    (C : Type u) [CommRing C] (g : C) (hg : g ∈ nonZeroDivisors C) (a : C) :
    scalarTorsionAwayToFractionRing C g hg (algebraMap C (Localization.Away g) a) =
      algebraMap C (FractionRing C) a :=
  IsLocalization.Away.lift_eq _ _ _

private theorem scalarTorsionAwayToFractionRing_injective
    (C : Type u) [CommRing C] (g : C) (hg : g ∈ nonZeroDivisors C) :
    Function.Injective (scalarTorsionAwayToFractionRing C g hg) := by
  have hM : Submonoid.powers g ≤ nonZeroDivisors C := by
    rintro _ ⟨n, rfl⟩
    exact pow_mem hg n
  apply (IsLocalization.injective_iff_map_algebraMap_eq (Submonoid.powers g)
    (scalarTorsionAwayToFractionRing C g hg)).mpr
  intro x y
  rw [scalarTorsionAwayToFractionRing_algebraMap,
    scalarTorsionAwayToFractionRing_algebraMap]
  exact (IsLocalization.injective (Localization.Away g) hM).eq_iff.trans
    (IsFractionRing.injective C (FractionRing C)).eq_iff.symm

end AlgebraicGeometry.Scheme.Cohomology

namespace AlgebraicGeometry.Scheme.Cohomology

private theorem scalarTorsion_open_appTop_topIso (Y : Scheme.{u}) (W : Y.Opens) :
    W.ι.appTop ≫ W.topIso.hom = Y.presheaf.map (homOfLE (show W ≤ ⊤ from le_top)).op := by
  rw [Scheme.Opens.ι_appTop]
  change Y.presheaf.map (homOfLE (show W.ι ''ᵁ ⊤ ≤ ⊤ from le_top)).op ≫
    Y.presheaf.map (eqToHom W.ι_image_top.symm).op = _
  rw [← Y.presheaf.map_comp]
  congr 1

private def scalarTorsionTotalRestrictionToAway
    {A : Type u} [CommRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A)) (c g : A)
    [IsIso (f ∣_ PrimeSpectrum.basicOpen g)] :
    Γ(idealThickeningSpace f (Ideal.span {c}), ⊤) →+*
      Localization.Away (Ideal.Quotient.mk (Ideal.span {c}) g) :=
  (((scalarTorsionTotalPrincipalIso f c g).inv ≫
    (scalarTorsionTotalPrincipalOpen f c g).ι).appTop ≫
      (Scheme.ΓSpecIso (.of (Localization.Away (Ideal.Quotient.mk (Ideal.span {c}) g)))).hom).hom

private theorem scalarTorsionTotalRestrictionToAway_base
    {A : Type u} [CommRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A)) (c g : A)
    [IsIso (f ∣_ PrimeSpectrum.basicOpen g)] (r : A ⧸ Ideal.span {c}) :
    scalarTorsionTotalRestrictionToAway f c g
        (idealThickeningBaseScalar (idealThickeningStructure f (Ideal.span {c})) r) =
      algebraMap (A ⧸ Ideal.span {c})
        (Localization.Away (Ideal.Quotient.mk (Ideal.span {c}) g)) r := by
  let C := A ⧸ Ideal.span {c}
  let Cg := Localization.Away (Ideal.Quotient.mk (Ideal.span {c}) g)
  let a := (scalarTorsionTotalPrincipalIso f c g).inv ≫
    (scalarTorsionTotalPrincipalOpen f c g).ι
  have hw : a ≫ idealThickeningStructure f (Ideal.span {c}) =
      (𝟙 (Spec (.of Cg))) ≫ Spec.map (CommRingCat.ofHom (algebraMap C Cg)) := by
    simpa only [a, Category.assoc, Category.id_comp] using
      scalarTorsionTotalPrincipalIso_inv_structure f c g
  have hs := congrArg (fun φ => φ r)
    (moduleSectionsBaseChangeScalars a (𝟙 (Spec (.of Cg)))
      (idealThickeningStructure f (Ideal.span {c})) (algebraMap C Cg) hw)
  change a.appTop
      (idealThickeningBaseScalar (idealThickeningStructure f (Ideal.span {c})) r) =
    (Scheme.ΓSpecIso (.of Cg)).inv (algebraMap C Cg r) at hs
  change (Scheme.ΓSpecIso (.of Cg)).hom (a.appTop
      (idealThickeningBaseScalar (idealThickeningStructure f (Ideal.span {c})) r)) = _
  rw [hs]
  exact (Scheme.ΓSpecIso (.of Cg)).commRingCatIsoToRingEquiv.apply_symm_apply _

private def scalarTorsionTotalPrincipalSectionsEquiv
    {A : Type u} [CommRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A)) (c g : A)
    [IsIso (f ∣_ PrimeSpectrum.basicOpen g)] :
    Γ(idealThickeningSpace f (Ideal.span {c}), scalarTorsionTotalPrincipalOpen f c g) ≃+*
      Localization.Away (Ideal.Quotient.mk (Ideal.span {c}) g) :=
  Iso.commRingCatIsoToRingEquiv
    ((scalarTorsionTotalPrincipalOpen f c g).topIso.symm ≪≫
    Scheme.Γ.mapIso (scalarTorsionTotalPrincipalIso f c g).symm.op ≪≫
      Scheme.ΓSpecIso (.of (Localization.Away (Ideal.Quotient.mk (Ideal.span {c}) g))))

private theorem scalarTorsionTotalRestrictionToAway_restriction
    {A : Type u} [CommRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A)) (c g : A)
    [IsIso (f ∣_ PrimeSpectrum.basicOpen g)]
    (s : Γ(idealThickeningSpace f (Ideal.span {c}), ⊤)) :
    scalarTorsionTotalRestrictionToAway f c g s =
      scalarTorsionTotalPrincipalSectionsEquiv f c g
        ((idealThickeningSpace f (Ideal.span {c})).presheaf.map
          (homOfLE (show scalarTorsionTotalPrincipalOpen f c g ≤ ⊤ from le_top)).op s) := by
  let Z := idealThickeningSpace f (Ideal.span {c})
  let W := scalarTorsionTotalPrincipalOpen f c g
  let E := scalarTorsionTotalPrincipalIso f c g
  let S := CommRingCat.of (Localization.Away (Ideal.Quotient.mk (Ideal.span {c}) g))
  let r := Z.presheaf.map (homOfLE (show W ≤ ⊤ from le_top)).op
  have h : W.ι.appTop ≫ W.topIso.hom = r := scalarTorsion_open_appTop_topIso Z W
  have hr : r ≫ W.topIso.inv = W.ι.appTop := by
    rw [← h, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hm : (E.inv ≫ W.ι).appTop ≫ (Scheme.ΓSpecIso S).hom =
      r ≫ (W.topIso.symm ≪≫ Scheme.Γ.mapIso E.symm.op ≪≫ Scheme.ΓSpecIso S).hom := by
    change (E.inv ≫ W.ι).appTop ≫ (Scheme.ΓSpecIso S).hom =
      r ≫ W.topIso.inv ≫ E.inv.appTop ≫ (Scheme.ΓSpecIso S).hom
    simp only [Scheme.Hom.comp_appTop, ← Category.assoc, hr]
  change ((E.inv ≫ W.ι).appTop ≫ (Scheme.ΓSpecIso S).hom).hom s =
    (W.topIso.symm ≪≫ Scheme.Γ.mapIso E.symm.op ≪≫ Scheme.ΓSpecIso S).hom.hom (r.hom s)
  exact congrArg (fun k : Γ(Z, ⊤) ⟶ S => k.hom s) hm

private def scalarTorsionTotalRestrictionToFraction
    {A : Type u} [CommRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A)) (c g : A)
    [IsIso (f ∣_ PrimeSpectrum.basicOpen g)]
    (hg : Ideal.Quotient.mk (Ideal.span {c}) g ∈ nonZeroDivisors (A ⧸ Ideal.span {c})) :
    let C := A ⧸ Ideal.span {c}
    letI : Algebra C Γ(idealThickeningSpace f (Ideal.span {c}), ⊤) :=
      (idealThickeningBaseScalar (idealThickeningStructure f (Ideal.span {c}))).toAlgebra
    Γ(idealThickeningSpace f (Ideal.span {c}), ⊤) →ₐ[C] FractionRing C := by
  let C := A ⧸ Ideal.span {c}
  let : Algebra C Γ(idealThickeningSpace f (Ideal.span {c}), ⊤) :=
    (idealThickeningBaseScalar (idealThickeningStructure f (Ideal.span {c}))).toAlgebra
  exact {
    toRingHom := (scalarTorsionAwayToFractionRing C (Ideal.Quotient.mk (Ideal.span {c}) g) hg).comp
      (scalarTorsionTotalRestrictionToAway f c g)
    commutes' := fun r => by
      change scalarTorsionAwayToFractionRing C _ hg
        (scalarTorsionTotalRestrictionToAway f c g
          (idealThickeningBaseScalar (idealThickeningStructure f (Ideal.span {c})) r)) = _
      rw [scalarTorsionTotalRestrictionToAway_base,
        scalarTorsionAwayToFractionRing_algebraMap] }

private def scalarTorsionTotalNormalizationMap
    {A : Type u} [CommRing A] [IsNoetherianRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f] (c g : A)
    [IsIso (f ∣_ PrimeSpectrum.basicOpen g)]
    (hg : Ideal.Quotient.mk (Ideal.span {c}) g ∈ nonZeroDivisors (A ⧸ Ideal.span {c})) :
    let C := A ⧸ Ideal.span {c}
    letI : Algebra C Γ(idealThickeningSpace f (Ideal.span {c}), ⊤) :=
      (idealThickeningBaseScalar (idealThickeningStructure f (Ideal.span {c}))).toAlgebra
    Γ(idealThickeningSpace f (Ideal.span {c}), ⊤) →ₐ[C] integralClosure C (FractionRing C) := by
  let C := A ⧸ Ideal.span {c}
  let Z := idealThickeningSpace f (Ideal.span {c})
  let : Algebra C Γ(Z, ⊤) :=
    (idealThickeningBaseScalar (idealThickeningStructure f (Ideal.span {c}))).toAlgebra
  let : Module.Finite C Γ(Z, ⊤) :=
    structuralCoefficients_finite_of_proper C (idealThickeningStructure f (Ideal.span {c}))
  let φ := scalarTorsionTotalRestrictionToFraction f c g hg
  exact φ.codRestrict (integralClosure C (FractionRing C)) (fun s => by
    change _root_.IsIntegral C (φ s)
    exact (_root_.IsIntegral.of_finite C s).map φ)

private theorem scalarTorsionTotalNormalizationMap_restriction_zero
    {A : Type u} [CommRing A] [IsNoetherianRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f] (c g : A)
    [IsIso (f ∣_ PrimeSpectrum.basicOpen g)]
    (hg : Ideal.Quotient.mk (Ideal.span {c}) g ∈ nonZeroDivisors (A ⧸ Ideal.span {c}))
    (s : Γ(idealThickeningSpace f (Ideal.span {c}), ⊤))
    (hs : scalarTorsionTotalNormalizationMap f c g hg s = 0) :
    (idealThickeningSpace f (Ideal.span {c})).presheaf.map
      (homOfLE (show scalarTorsionTotalPrincipalOpen f c g ≤ ⊤ from le_top)).op s = 0 := by
  have hQ := congrArg Subtype.val hs
  change scalarTorsionAwayToFractionRing (A ⧸ Ideal.span {c})
    (Ideal.Quotient.mk (Ideal.span {c}) g) hg
      (scalarTorsionTotalRestrictionToAway f c g s) = 0 at hQ
  have haway : scalarTorsionTotalRestrictionToAway f c g s = 0 := by
    apply scalarTorsionAwayToFractionRing_injective (A ⧸ Ideal.span {c}) _ hg
    simpa only [map_zero] using hQ
  apply (scalarTorsionTotalPrincipalSectionsEquiv f c g).injective
  rw [map_zero, ← scalarTorsionTotalRestrictionToAway_restriction]
  exact haway

private theorem scalarTorsionTotalBaseSquare
    {A : Type u} [CommRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A)) (c : A) (a : A) :
    (idealThickeningι f (Ideal.span {c})).appTop (idealThickeningBaseScalar f a) =
      idealThickeningBaseScalar (idealThickeningStructure f (Ideal.span {c}))
        (Ideal.Quotient.mk (Ideal.span {c}) a) :=
  DFunLike.congr_fun
    (moduleSectionsBaseChangeScalars (idealThickeningι f (Ideal.span {c}))
      (idealThickeningStructure f (Ideal.span {c})) f
      (Ideal.Quotient.mk (Ideal.span {c})) pullback.condition) a

private def scalarCokernelNormalizationComparison
    {A : Type u} [CommRing A] [IsNoetherianRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f] (c g : A)
    [IsIso (f ∣_ PrimeSpectrum.basicOpen g)]
    (hg : Ideal.Quotient.mk (Ideal.span {c}) g ∈ nonZeroDivisors (A ⧸ Ideal.span {c})) :
    let Q := cokernel (globalScalarEndomorphism X (SheafOfModules.unit X.ringCatSheaf)
      (idealThickeningBaseScalar f c))
    letI : Module Γ(X, ⊤) (Q.val.obj (op ⊤)) := (Q.val.obj (op ⊤)).isModule
    letI : Module A (Q.val.obj (op ⊤)) := Module.compHom _ (idealThickeningBaseScalar f)
    Q.val.obj (op ⊤) →ₗ[A]
      integralClosure (A ⧸ Ideal.span {c}) (FractionRing (A ⧸ Ideal.span {c})) := by
  let C := A ⧸ Ideal.span {c}
  let B := integralClosure C (FractionRing C)
  let α := idealThickeningBaseScalar f
  let Q := cokernel (globalScalarEndomorphism X (SheafOfModules.unit X.ringCatSheaf) (α c))
  let : Module Γ(X, ⊤) (Q.val.obj (op ⊤)) := (Q.val.obj (op ⊤)).isModule
  let : Module A (Q.val.obj (op ⊤)) := Module.compHom _ α
  let β := idealThickeningBaseScalar (idealThickeningStructure f (Ideal.span {c}))
  let : Algebra C Γ(idealThickeningSpace f (Ideal.span {c}), ⊤) := β.toAlgebra
  let F := scalarTorsionTotalNormalizationMap f c g hg
  let e := scalarCokernelTotalDivisorIso f c
  let l : Q.val.obj (op ⊤) →+ Γ(idealThickeningSpace f (Ideal.span {c}), ⊤) :=
    (e.hom.val.app (op ⊤)).hom.toAddMonoidHom
  refine {
    __ := F.toAddMonoidHom.comp l
    map_smul' := ?_ }
  intro a s
  have he : l (a • s) =
      (idealThickeningι f (Ideal.span {c})).appTop (α a) * l s :=
    (e.hom.val.app (op ⊤)).hom.map_smul (α a) s
  change F (l (a • s)) = a • F (l s)
  calc
    F (l (a • s)) =
        F ((idealThickeningι f (Ideal.span {c})).appTop (α a) * l s) :=
      congrArg F he
    _ = F ((idealThickeningι f (Ideal.span {c})).appTop (α a)) * F (l s) :=
      F.map_mul _ _
    _ = F (β (Ideal.Quotient.mk (Ideal.span {c}) a)) * F (l s) :=
      congrArg (fun z => F z * F (l s)) (scalarTorsionTotalBaseSquare f c a)
    _ = algebraMap C B (Ideal.Quotient.mk (Ideal.span {c}) a) * F (l s) :=
      congrArg (fun b : B => b * F (l s)) (F.commutes _)
    _ = algebraMap A B a * F (l s) :=
      congrArg (fun b : B => b * F (l s))
        (IsScalarTower.algebraMap_apply A C B a).symm
    _ = a • F (l s) := (Algebra.smul_def a (F (l s))).symm

private theorem scalarCokernelNormalizationComparison_apply
    {A : Type u} [CommRing A] [IsNoetherianRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f] (c g : A)
    [IsIso (f ∣_ PrimeSpectrum.basicOpen g)]
    (hg : Ideal.Quotient.mk (Ideal.span {c}) g ∈ nonZeroDivisors (A ⧸ Ideal.span {c}))
    (s : (cokernel (globalScalarEndomorphism X (SheafOfModules.unit X.ringCatSheaf)
      (idealThickeningBaseScalar f c))).val.obj (op ⊤)) :
    scalarCokernelNormalizationComparison f c g hg s =
      scalarTorsionTotalNormalizationMap f c g hg
        (show Γ(idealThickeningSpace f (Ideal.span {c}), ⊤) from
          (scalarCokernelTotalDivisorIso f c).hom.val.app (op ⊤) s) := rfl

private theorem scalarCokernelNormalizationComparison_constants
    {A : Type u} [CommRing A] [IsNoetherianRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f] (c g : A)
    [IsIso (f ∣_ PrimeSpectrum.basicOpen g)]
    (hg : Ideal.Quotient.mk (Ideal.span {c}) g ∈ nonZeroDivisors (A ⧸ Ideal.span {c}))
    (a : A) :
    scalarCokernelNormalizationComparison f c g hg
        ((cokernel.π (globalScalarEndomorphism X (SheafOfModules.unit X.ringCatSheaf)
          (idealThickeningBaseScalar f c))).val.app (op ⊤) (idealThickeningBaseScalar f a)) =
      algebraMap A (integralClosure (A ⧸ Ideal.span {c})
        (FractionRing (A ⧸ Ideal.span {c}))) a := by
  let C := A ⧸ Ideal.span {c}
  let B := integralClosure C (FractionRing C)
  let β := idealThickeningBaseScalar (idealThickeningStructure f (Ideal.span {c}))
  let : Algebra C Γ(idealThickeningSpace f (Ideal.span {c}), ⊤) := β.toAlgebra
  let F := scalarTorsionTotalNormalizationMap f c g hg
  let t := globalScalarEndomorphism X (SheafOfModules.unit X.ringCatSheaf)
    (idealThickeningBaseScalar f c)
  have hπ := congrArg (fun k => k.val.app (op ⊤) (idealThickeningBaseScalar f a))
    (scalarCokernelTotalDivisorIso_π f c)
  change (scalarCokernelTotalDivisorIso f c).hom.val.app (op ⊤)
      ((cokernel.π t).val.app (op ⊤) (idealThickeningBaseScalar f a)) =
    (idealThickeningι f (Ideal.span {c})).appTop (idealThickeningBaseScalar f a) at hπ
  exact (scalarCokernelNormalizationComparison_apply f c g hg _).trans
    ((congrArg F hπ).trans
      ((congrArg F (scalarTorsionTotalBaseSquare f c a)).trans
        ((F.commutes (Ideal.Quotient.mk (Ideal.span {c}) a)).trans
          (IsScalarTower.algebraMap_apply A C B a).symm)))

private theorem scalarCokernelNormalizationComparison_restriction_zero
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f] (c g : A)
    [IsIso (f ∣_ PrimeSpectrum.basicOpen g)]
    (hg : Ideal.Quotient.mk (Ideal.span {c}) g ∈ nonZeroDivisors (A ⧸ Ideal.span {c}))
    (hcm : c ∈ maximalIdeal A) (hgm : g ∈ maximalIdeal A)
    (hrad : (Ideal.span {c} ⊔ Ideal.span {g}).radical = maximalIdeal A)
    (s : (cokernel (globalScalarEndomorphism X (SheafOfModules.unit X.ringCatSheaf)
      (idealThickeningBaseScalar f c))).val.obj (op ⊤))
    (hs : scalarCokernelNormalizationComparison f c g hg s = 0) :
    (cokernel (globalScalarEndomorphism X (SheafOfModules.unit X.ringCatSheaf)
      (idealThickeningBaseScalar f c))).val.map
        (homOfLE (show f ⁻¹ᵁ Scheme.localPuncturedSpectrum A ≤ ⊤ from le_top)).op s = 0 := by
  let U := f ⁻¹ᵁ Scheme.localPuncturedSpectrum A
  let e := scalarCokernelTotalDivisorIso f c
  have hzero := scalarTorsionTotalNormalizationMap_restriction_zero f c g hg
    (show Γ(idealThickeningSpace f (Ideal.span {c}), ⊤) from e.hom.val.app (op ⊤) s)
    ((scalarCokernelNormalizationComparison_apply f c g hg s).symm.trans hs)
  rw [scalarTorsionTotalPrincipalOpen_eq_punctured f c g hcm hgm hrad] at hzero
  have hn := PresheafOfModules.naturality_apply e.hom.val
    (homOfLE (show U ≤ ⊤ from le_top)).op s
  have hi : Function.Injective (e.hom.val.app (op U)) :=
    (ConcreteCategory.bijective_of_isIso (e.hom.app U)).1
  exact hi ((hn.trans hzero).trans (e.hom.val.app (op U)).hom.map_zero.symm)

private theorem scalarTorsionNormalizationConstants_kernel
    {A : Type u} [CommRing A] (c a : A)
    (ha : algebraMap A (integralClosure (A ⧸ Ideal.span {c})
      (FractionRing (A ⧸ Ideal.span {c}))) a = 0) : c ∣ a := by
  let C := A ⧸ Ideal.span {c}
  have hQ := congrArg Subtype.val ha
  change algebraMap A (FractionRing C) a = 0 at hQ
  rw [IsScalarTower.algebraMap_apply A C (FractionRing C)] at hQ
  have hquot : algebraMap A C = Ideal.Quotient.mk (Ideal.span {c}) :=
    Ideal.Quotient.algebraMap_eq _
  rw [hquot] at hQ
  have hc : Ideal.Quotient.mk (Ideal.span {c}) a = 0 := by
    apply IsFractionRing.injective C (FractionRing C)
    exact hQ.trans (map_zero (algebraMap C (FractionRing C))).symm
  exact Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hc)

private theorem scalarTorsionNormalizationColength_ne_top
    {A : Type u} [CommRing A] [IsDomain A]
    (hA : IsNagataRing.{u, 0} A) (hdim : ringKrullDim A = 2)
    (c : A) (hc : c ≠ 0) [_root_.IsReduced (A ⧸ Ideal.span {c})] :
    Module.length A
      (integralClosure (A ⧸ Ideal.span {c}) (FractionRing (A ⧸ Ideal.span {c})) ⧸
        LinearMap.range (Algebra.linearMap A
          (integralClosure (A ⧸ Ideal.span {c}) (FractionRing (A ⧸ Ideal.span {c}))))) ≠ ⊤ := by
  let C := A ⧸ Ideal.span {c}
  have hC := hA.quotient (Ideal.span {c})
  let : IsNoetherianRing C := hC.isNoetherianRing
  let : Ring.KrullDimLE 1 C := by
    apply Ring.krullDimLE_iff.mpr
    apply ENat.WithBot.add_le_add_one_right_iff.mp
    have h : ringKrullDim C + 1 ≤ (2 : WithBot ℕ∞) :=
      (ringKrullDim_quotient_succ_le_of_nonZeroDivisor
        (mem_nonZeroDivisors_iff_ne_zero.mpr hc)).trans_eq hdim
    exact h.trans_eq (by norm_num)
  let : Module.Finite C (integralClosure C (FractionRing C)) :=
    integralClosure.finite_of_isNagataRing C hC (FractionRing C)
  exact integralClosure.quotient_original_length_ne_top C (FractionRing C) A
    (Ideal.Quotient.mk_surjective)

/-- The original scalar torsion on H1 is bounded by the colength of the
literal normalization of the original principal quotient. -/
public theorem structureH1_scalarTorsion_length_le_normalizationColength
    {A : Type u} [CommRing A] [IsDomain A] [IsLocalRing A]
    [IsNoetherianRing A] [IsIntegrallyClosed A]
    {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f] [IsDominant f]
    (hff : IsIso (CommRingCat.ofHom (Scheme.functionFieldMap f)))
    (hdim : ringKrullDim A = 2) (hX : Scheme.NormalStalks X)
    (hA : IsNagataRing.{u, 0} A) (c : A) (hc : c ≠ 0) (hcm : c ∈ maximalIdeal A) :
    letI := moduleCohomologyModuleOfHom X
      (f.appTop.hom.comp (Scheme.ΓSpecIso (.of A)).inv.hom)
      (SheafOfModules.unit X.ringCatSheaf) 1
    Module.length A
      (Submodule.torsionBy A
        (Sheaf.H.{u + 1} (moduleAddSheaf X (SheafOfModules.unit X.ringCatSheaf)) 1) c) ≤
      Module.length A
        (integralClosure (A ⧸ Ideal.span {c}) (FractionRing (A ⧸ Ideal.span {c})) ⧸
          LinearMap.range (Algebra.linearMap A
            (integralClosure (A ⧸ Ideal.span {c}) (FractionRing (A ⧸ Ideal.span {c}))))) := by
  obtain ⟨g, hgm, hrad, hg⟩ := scalarTorsion_exists_parameter hdim c hc hcm
  let : IsIso (f ∣_ PrimeSpectrum.basicOpen g) :=
    scalarTorsion_isIso_principalRestriction f hff hdim g hgm
  let α := idealThickeningBaseScalar f
  let O : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let s := globalScalarEndomorphism X O (α c)
  let Q := cokernel s
  have hbij : Function.Bijective α :=
    f.bijective_structuralCoefficients_of_isProper_birational A
      (fun p => (isIntegrallyClosed_and_isDomain_stalk_Spec A p).symm) hff
  let : Mono s := scalarStructure_mono (α c)
    (fun hz => hc (hbij.injective (hz.trans α.map_zero.symm)))
  have hS : (ShortComplex.mk s (cokernel.π s) (cokernel.condition s)).ShortExact :=
    { exact := ShortComplex.exact_cokernel s }
  let : Module Γ(X, ⊤) (O.val.obj (op ⊤)) := (O.val.obj (op ⊤)).isModule
  let : Module A (O.val.obj (op ⊤)) := Module.compHom _ α
  let σ : A →ₗ[A] O.val.obj (op ⊤) :=
    { toFun := α
      map_add' := α.map_add
      map_smul' := fun a b => α.map_mul a b }
  exact h1Torsion_length_le_of_comparisonKernel X α O Q c (cokernel.π s)
    (cokernel.condition s) hS (f ⁻¹ᵁ Scheme.localPuncturedSpectrum A)
    (scalarCokernelNormalizationComparison f c g hg) σ hbij.surjective
    (Algebra.linearMap A
      (integralClosure (A ⧸ Ideal.span {c}) (FractionRing (A ⧸ Ideal.span {c}))))
    (scalarCokernelNormalizationComparison_constants f c g hg)
    (scalarTorsionNormalizationConstants_kernel c)
    (structureH1_puncturedPresheafRestriction_injective_of_isNagata f hff hdim hX hA)
    (scalarCokernelNormalizationComparison_restriction_zero f c g hg hcm hgm hrad)

/-- For each nonzero base scalar, one finite bound works for the literal
H1 scalar torsion of every original proper birational normal integral model. -/
public theorem exists_uniform_structureH1_scalarTorsion_length_bound
    (A : Type u) [CommRing A] [IsDomain A] [IsLocalRing A]
    [IsNoetherianRing A] [IsIntegrallyClosed A]
    (hA : IsNagataRing.{u, 0} A) (hdim : ringKrullDim A = 2) (a : A) (ha : a ≠ 0) :
    ∃ N : ℕ, ∀ {X : Scheme.{u}} [IsIntegral X]
      (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f] [IsDominant f]
      (_hff : IsIso (CommRingCat.ofHom (Scheme.functionFieldMap f)))
      (_hX : Scheme.NormalStalks X),
      letI := moduleCohomologyModuleOfHom X
        (f.appTop.hom.comp (Scheme.ΓSpecIso (.of A)).inv.hom)
        (SheafOfModules.unit X.ringCatSheaf) 1
      Module.length A
        (Submodule.torsionBy A
          (Sheaf.H.{u + 1} (moduleAddSheaf X (SheafOfModules.unit X.ringCatSheaf)) 1) a) ≤
        (N : ℕ∞) := by
  by_cases hu : IsUnit a
  · refine ⟨0, ?_⟩
    intro X hIntegral f hProper hDominant _hff _hX
    let := moduleCohomologyModuleOfHom X
      (f.appTop.hom.comp (Scheme.ΓSpecIso (.of A)).inv.hom)
      (SheafOfModules.unit X.ringCatSheaf) 1
    have ht : Submodule.torsionBy A
        (Sheaf.H.{u + 1} (moduleAddSheaf X (SheafOfModules.unit X.ringCatSheaf)) 1) a = ⊥ :=
      (isSMulRegular_iff_torsionBy_eq_bot _ a).mp (hu.isSMulRegular _)
    have hz := congrArg (fun T : Submodule A
      (Sheaf.H.{u + 1} (moduleAddSheaf X (SheafOfModules.unit X.ringCatSheaf)) 1) =>
        Module.length A T) ht
    exact (hz.trans Module.length_bot).le
  obtain ⟨c, hc, hcm, hred, r, _, hdiv⟩ :=
    IsLocalRing.exists_reduced_principal_cover hdim a ha hu
  let : _root_.IsReduced (A ⧸ Ideal.span {c}) := hred
  let B := integralClosure (A ⧸ Ideal.span {c}) (FractionRing (A ⧸ Ideal.span {c}))
  let L := Module.length A (B ⧸ LinearMap.range (Algebra.linearMap A B))
  have hL : L ≠ ⊤ := scalarTorsionNormalizationColength_ne_top hA hdim c hc
  refine ⟨r * L.toNat, ?_⟩
  intro X hIntegral f hProper hDominant hff hX
  let := moduleCohomologyModuleOfHom X
    (f.appTop.hom.comp (Scheme.ΓSpecIso (.of A)).inv.hom)
    (SheafOfModules.unit X.ringCatSheaf) 1
  calc
    Module.length A
        (Submodule.torsionBy A
          (Sheaf.H.{u + 1} (moduleAddSheaf X (SheafOfModules.unit X.ringCatSheaf)) 1) a) ≤
        (r : ℕ∞) * Module.length A
          (Submodule.torsionBy A
            (Sheaf.H.{u + 1} (moduleAddSheaf X (SheafOfModules.unit X.ringCatSheaf)) 1) c) :=
      Submodule.length_torsionBy_le_of_dvd_pow a c r hdiv
    _ ≤ (r : ℕ∞) * L := mul_le_mul_right
      (structureH1_scalarTorsion_length_le_normalizationColength f hff hdim hX hA c hc hcm) _
    _ = (r * L.toNat : ℕ) := by rw [Nat.cast_mul, ENat.natCast_toNat hL]

end AlgebraicGeometry.Scheme.Cohomology
