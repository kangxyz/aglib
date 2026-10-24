/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.InternalHom.Coherent
public import Aglib.AlgebraicGeometry.Modules.Invertible.Affine
public import Aglib.AlgebraicGeometry.Modules.Invertible.Bidual
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Coherent
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Affine.Flat
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.FreeCover
public import Aglib.RingTheory.Reflexive.DoubleDual
public import Aglib.RingTheory.Reflexive.Localization
public import Aglib.RingTheory.Localization.ModulePresentation
public import Mathlib.RingTheory.Localization.Free

/-!
# Original affine sections of actual sheaf biduals

The equivalences use the original restricted
internal Hom, the actual restriction of the structure module, and its original
affine section isomorphism. Bidual evaluation becomes exactly Module.Dual.eval.
On a locally Noetherian scheme, coherence of both duals is derived from
coherence of the original source.
At prime localizations of a regular surface ring, the original generic rank
then gives singleton bases of the actual double dual. Finite presentation
spreads those bases and constructs the original restricted sheaf as a line.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open _root_.Module

universe u

namespace AlgebraicGeometry.Scheme.Modules.Invertible

variable {X : Scheme.{u}} {R : CommRingCat.{u}}
  (j : Spec R ⟶ X) [IsOpenImmersion j]

/-- Original scalar sections on an affine restriction, through the original
restriction-unit isomorphism and the original affine structure sections. -/
def affineRestrictionUnitSectionsEquiv :
    moduleSpecΓFunctor.obj
      ((show X.Modules from SheafOfModules.unit X.ringCatSheaf).restrict j) ≃ₗ[R] R :=
  ((moduleSpecΓFunctor.mapIso (Scheme.Modules.restrictUnitIso j)) ≪≫
    (globalSectionsUnitIso (R := R))).toLinearEquiv

variable (M : X.Modules) [(M.restrict j).IsQuasicoherent]

/-- Sections of the original dual sheaf are the actual linear dual of sections. -/
def affineDualSectionsEquiv :
    moduleSpecΓFunctor.obj ((show X.Modules from dualSheaf X M).restrict j) ≃ₗ[R]
      Module.Dual R (moduleSpecΓFunctor.obj (M.restrict j)) :=
  (InternalHom.affineRestrictionSectionsEquiv j M
    (SheafOfModules.unit X.ringCatSheaf)).trans
      ((LinearEquiv.refl R (moduleSpecΓFunctor.obj (M.restrict j))).arrowCongr
        (affineRestrictionUnitSectionsEquiv j))

/-- The affine dual comparison evaluates on the original image open. -/
theorem affineDualSectionsEquiv_apply
    (s : moduleSpecΓFunctor.obj ((show X.Modules from dualSheaf X M).restrict j))
    (m : moduleSpecΓFunctor.obj (M.restrict j)) :
    affineDualSectionsEquiv j M s m = affineRestrictionUnitSectionsEquiv j
      (s.val.app (op (Over.mk (𝟙 (j ''ᵁ ⊤)))) m) := by
  change affineRestrictionUnitSectionsEquiv j
    (InternalHom.affineRestrictionSectionsEquiv j M
      (SheafOfModules.unit X.ringCatSheaf) s m) = _
  exact congrArg (affineRestrictionUnitSectionsEquiv j)
    (InternalHom.affineRestrictionSectionsEquiv_apply j M
      (SheafOfModules.unit X.ringCatSheaf) s m)

variable [((show X.Modules from dualSheaf X M).restrict j).IsQuasicoherent]

/-- Apply the actual affine Hom comparison twice, retaining the same scalar map. -/
def affineBidualSectionsEquiv :
    moduleSpecΓFunctor.obj
      ((show X.Modules from dualSheaf X (dualSheaf X M)).restrict j) ≃ₗ[R]
      Module.Dual R (Module.Dual R (moduleSpecΓFunctor.obj (M.restrict j))) :=
  (affineDualSectionsEquiv j (dualSheaf X M)).trans
    ((affineDualSectionsEquiv j M).arrowCongr (LinearEquiv.refl R R))

/-- The second comparison is evaluation on the actual inverse dual section. -/
theorem affineBidualSectionsEquiv_apply
    (s : moduleSpecΓFunctor.obj
      ((show X.Modules from dualSheaf X (dualSheaf X M)).restrict j))
    (l : Module.Dual R (moduleSpecΓFunctor.obj (M.restrict j))) :
    affineBidualSectionsEquiv j M s l = affineRestrictionUnitSectionsEquiv j
      (s.val.app (op (Over.mk (𝟙 (j ''ᵁ ⊤)))) ((affineDualSectionsEquiv j M).symm l)) := by
  change affineDualSectionsEquiv j (dualSheaf X M) s
    ((affineDualSectionsEquiv j M).symm l) = _
  exact affineDualSectionsEquiv_apply j (dualSheaf X M) s _

/-- The original sheaf bidual evaluation becomes the original module evaluation. -/
theorem affineBidualSectionsEquiv_evaluation
    (m : moduleSpecΓFunctor.obj (M.restrict j)) :
    affineBidualSectionsEquiv j M
        ((moduleSpecΓFunctor.map ((Scheme.Modules.restrictFunctor j).map
          (bidualMap X M))).hom m) =
      Module.Dual.eval R (moduleSpecΓFunctor.obj (M.restrict j)) m := by
  apply LinearMap.ext
  intro l
  let ell := (affineDualSectionsEquiv j M).symm l
  have hfirst := affineBidualSectionsEquiv_apply j M
    ((moduleSpecΓFunctor.map ((Scheme.Modules.restrictFunctor j).map
      (bidualMap X M))).hom m) l
  have heval := congrArg (affineRestrictionUnitSectionsEquiv j)
    (bidualMap_evaluate X M (j ''ᵁ ⊤) m ell)
  have hdual := (affineDualSectionsEquiv_apply j M ell m).symm
  have hinverse := congrArg
    (fun a : Module.Dual R (moduleSpecΓFunctor.obj (M.restrict j)) => a m)
    ((affineDualSectionsEquiv j M).apply_symm_apply l)
  exact hfirst.trans (heval.trans (hdual.trans hinverse))

end AlgebraicGeometry.Scheme.Modules.Invertible

namespace AlgebraicGeometry.Scheme.Modules

open _root_.AlgebraicGeometry.Scheme.Modules.Invertible

/-- The original structure module is affine-locally finite, through its actual
singleton free presentation. -/
theorem affineLocallyFiniteType_structureModule (X : Scheme.{u}) :
    affineLocallyFiniteType X (SheafOfModules.unit X.ringCatSheaf) := by
  let L := trivialLineBundle X
  have hL : affineLocallyFiniteType X L.val := coherent_of_finiteLocallyFree L.val
  exact (affineLocallyFiniteType X).prop_of_iso
    (coproductUniqueIso (fun _ : PUnit.{u + 1} => SheafOfModules.unit X.ringCatSheaf)) hL

/-- Coherence of the actual dual follows from coherence of the original sheaf. -/
theorem affineLocallyFiniteType_dualSheaf {X : Scheme.{u}} [IsLocallyNoetherian X]
    (M : X.Modules) (hM : affineLocallyFiniteType X M) :
    affineLocallyFiniteType X (dualSheaf X M) :=
  InternalHom.affineLocallyFiniteType_internalHom M
    (SheafOfModules.unit X.ringCatSheaf) hM (affineLocallyFiniteType_structureModule X)

/-- Both applications of internal Hom retain the actual coherent bidual sheaf. -/
theorem affineLocallyFiniteType_bidualSheaf {X : Scheme.{u}} [IsLocallyNoetherian X]
    (M : X.Modules) (hM : affineLocallyFiniteType X M) :
    affineLocallyFiniteType X (dualSheaf X (dualSheaf X M)) :=
  affineLocallyFiniteType_dualSheaf _ (affineLocallyFiniteType_dualSheaf M hM)

end AlgebraicGeometry.Scheme.Modules

namespace Module

/-- At every actual prime localization of a regular surface ring, the original
double dual has a singleton basis derived from its original generic rank. -/
theorem doubleDual_localized_singleton_basis
    {R K M V : Type u} [CommRing R] [IsDomain R] [IsRegularRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]
    (f : M →ₗ[R] V) [IsLocalizedModule (nonZeroDivisors R) f]
    (hV : Module.finrank K V = 1) (p : PrimeSpectrum R)
    (hd : ringKrullDim (Localization.AtPrime p.asIdeal) ≤ 2) :
    Nonempty (Basis PUnit.{u + 1} (Localization.AtPrime p.asIdeal)
      (LocalizedModule p.asIdeal.primeCompl (Dual R (Dual R M)))) := by
  let D := Dual R (Dual R M)
  let Rₚ := Localization.AtPrime p.asIdeal
  let Dₚ := LocalizedModule p.asIdeal.primeCompl D
  let l : D →ₗ[R] Dₚ := LocalizedModule.mkLinearMap p.asIdeal.primeCompl D
  let : IsNoetherian R (Dual R M) := isNoetherian_linearMap R R M
  let : Module.Finite R (Dual R M) := Module.IsNoetherian.finite R _
  let : IsNoetherian R D := isNoetherian_linearMap R R (Dual R M)
  let : Module.Finite R D := Module.IsNoetherian.finite R _
  let : FinitePresentation R D := finitePresentation_of_finite R D
  let : IsNoetherian R (Dual R D) := isNoetherian_linearMap R R D
  let : Module.Finite R (Dual R D) := Module.IsNoetherian.finite R _
  let : FinitePresentation R (Dual R D) := finitePresentation_of_finite R _
  let : IsReflexive R D := IsReflexive.dual_of_finite
  let : IsReflexive Rₚ Dₚ :=
    IsReflexive.of_isLocalizedModule (R := R) (M := D) (Mₛ := Dₚ)
      p.asIdeal.primeCompl Rₚ l
  let : Module.Finite Rₚ Dₚ := Module.Finite.of_isLocalizedModule p.asIdeal.primeCompl l
  let : IsRegularLocalRing Rₚ := (isRegularRing_iff.mp ‹IsRegularRing R›) p.asIdeal
  let : Module.Free Rₚ Dₚ := free_of_isReflexive_of_dimension_le_two Rₚ hd Dₚ
  have hp : p.asIdeal.primeCompl ≤ nonZeroDivisors R := by
    intro s hs
    apply mem_nonZeroDivisors_iff_ne_zero.mpr
    intro hzero
    exact (Ideal.mem_primeCompl_iff.mp hs) (hzero ▸ p.asIdeal.zero_mem)
  have hrank : Module.finrank Rₚ Dₚ = 1 := by
    calc
      Module.finrank Rₚ Dₚ = Module.finrank R Dₚ :=
        IsLocalization.finrank_eq (N := Dₚ) Rₚ p.asIdeal.primeCompl hp
      _ = Module.finrank R D :=
        IsLocalizedModule.finrank_eq (M := D) (N := Dₚ) p.asIdeal.primeCompl l hp
      _ = 1 := finrank_doubleDual_eq_one_of_generic f hV
  let e : Rₚ ≃ₗ[Rₚ] Dₚ := (Module.nonempty_linearEquiv_of_finrank_eq_one hrank).some
  exact ⟨(Basis.singleton PUnit.{u + 1} Rₚ).map e⟩

end Module

namespace AlgebraicGeometry.Scheme.Modules.Invertible

open TopologicalSpace

/-- Singleton bases of the original localized section modules produce actual
singleton local sheaf bases. Finite presentation performs the spreading. -/
theorem affine_isLocallyRankOne_of_localized_singleton_basis
    (R : CommRingCat.{u}) (M : (Spec R).Modules) [M.IsQuasicoherent]
    [Module.FinitePresentation R (moduleSpecΓFunctor.obj M)]
    (hb : ∀ p : PrimeSpectrum R, Nonempty
      (Basis PUnit.{u + 1} (Localization.AtPrime p.asIdeal)
        (LocalizedModule p.asIdeal.primeCompl (moduleSpecΓFunctor.obj M)))) :
    IsLocallyRankOne (Spec R) M := by
  classical
  let N := moduleSpecΓFunctor.obj M
  have hprincipal (p : PrimeSpectrum R) :
      ∃ r : R, r ∉ p.asIdeal ∧ Nonempty
        (Basis PUnit.{u + 1} (Localization.Away r) (LocalizedModule.Away r N)) := by
    obtain ⟨r, hr, b, -⟩ := Module.FinitePresentation.exists_basis_localizedModule_powers
      p.asIdeal.primeCompl (LocalizedModule.mkLinearMap p.asIdeal.primeCompl N)
      (Localization.AtPrime p.asIdeal) (hb p).some
    exact ⟨r, Ideal.mem_primeCompl_iff.mp hr, ⟨b⟩⟩
  let ι := {r : R // Nonempty
    (Basis PUnit.{u + 1} (Localization.Away r) (LocalizedModule.Away r N))}
  let U : ι → (Spec R).Opens := fun r => PrimeSpectrum.basicOpen r.val
  have hcover : IsOpenCover U := .mk (by
    apply top_le_iff.mp
    intro p _
    obtain ⟨r, hr, hb⟩ := hprincipal p
    exact Opens.mem_iSup.mpr ⟨⟨r, hb⟩, hr⟩)
  let q := localGeneratorsOfCoverFreeIso U hcover (fun _ => PUnit.{u + 1})
    (fun r => affineBasicOpenLocalizedBasisIso M r.val r.property.some)
  exact ⟨q, inferInstance, fun _ => ⟨Equiv.refl _⟩⟩

/-- On an original affine chart of a coherent sheaf, its actual bidual is a
line when the chart ring is regular of local dimension at most two and the
original source sections have generic rank one. No reflexivity is assumed. -/
theorem affineRestrictionBidual_isLocallyRankOne
    {X : Scheme.{u}} [IsLocallyNoetherian X] {R : CommRingCat.{u}}
    [IsDomain R] [IsRegularRing R]
    (j : Spec R ⟶ X) [IsOpenImmersion j]
    (M : X.Modules) (hM : affineLocallyFiniteType X M)
    {K V : Type u} [Field K] [Algebra R K] [IsFractionRing R K]
    [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]
    (f : moduleSpecΓFunctor.obj (M.restrict j) →ₗ[R] V)
    [IsLocalizedModule (nonZeroDivisors R) f]
    (hV : Module.finrank K V = 1)
    (hd : ∀ p : PrimeSpectrum R, ringKrullDim (Localization.AtPrime p.asIdeal) ≤ 2) :
    IsLocallyRankOne (Spec R)
      ((show X.Modules from dualSheaf X (dualSheaf X M)).restrict j) := by
  let hD := affineLocallyFiniteType_dualSheaf M hM
  let hDD := affineLocallyFiniteType_bidualSheaf M hM
  let : (M.restrict j).IsQuasicoherent := (hM R j).1
  let : Module.Finite R (moduleSpecΓFunctor.obj (M.restrict j)) := (hM R j).2
  let : ((show X.Modules from dualSheaf X M).restrict j).IsQuasicoherent := (hD R j).1
  let N : (Spec R).Modules := (show X.Modules from dualSheaf X (dualSheaf X M)).restrict j
  let : N.IsQuasicoherent := (hDD R j).1
  let : Module.Finite R (moduleSpecΓFunctor.obj N) := (hDD R j).2
  let : Module.FinitePresentation R (moduleSpecΓFunctor.obj N) :=
    Module.finitePresentation_of_finite R _
  apply affine_isLocallyRankOne_of_localized_singleton_basis R N
  intro p
  let e := affineBidualSectionsEquiv j M
  let eₚ := LocalizedModule.localizedModuleEquiv p.asIdeal.primeCompl e
  obtain ⟨b⟩ := Module.doubleDual_localized_singleton_basis f hV p (hd p)
  exact ⟨b.map eₚ.symm⟩

end AlgebraicGeometry.Scheme.Modules.Invertible
