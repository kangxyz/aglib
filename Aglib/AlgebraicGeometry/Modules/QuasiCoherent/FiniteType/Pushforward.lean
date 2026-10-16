/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.FGModuleCat.RestrictScalars
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.Pushforward
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.FiniteTypeComparison
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.Restriction
public import Aglib.AlgebraicGeometry.Modules.BaseChange.OpenImmersion
public import Aglib.AlgebraicGeometry.Modules.Pushforward.Isomorphism
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
/-!
# Finite direct image of finite-type quasicoherent sheaves

The actual module-sheaf direct image along a finite scheme morphism
preserves the chart-based finite-type quasicoherent predicate over arbitrary
schemes. Its restricted functor retains the native sheaf action and its
identity, composition and open-base-change comparisons. On affine schemes,
actual global sections give the finite scalar-restriction square.

No local Noetherianity or general-coherence bridge is assumed here. The
coherent exact specialization is supplied by the separate coherent layer.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ModuleCat ModuleCat.FiniteRestrictionScalars
open Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules.QuasiCoherent.FiniteMorphism
variable {R S : CommRingCat.{u}} (φ : R ⟶ S) (hφ : φ.hom.Finite)

include hφ in
/-- The actual finite affine direct image preserves the finite-type
quasicoherent predicate. -/
theorem affineLocallyFiniteType_pushforward_spec {M : (Spec S).Modules}
    (hM : affineLocallyFiniteType (Spec S) M) :
    affineLocallyFiniteType (Spec R) ((Scheme.Modules.pushforward (Spec.map φ)).obj M) := by
  obtain ⟨hQC, hFG⟩ := (affineLocallyFiniteType_spec_iff S M).mp hM
  let : M.IsQuasicoherent := hQC
  apply (affineLocallyFiniteType_spec_iff R _).mpr
  refine ⟨Scheme.Modules.isQuasicoherent_pushforward φ M, ?_⟩
  let N : FGModuleCat S := ⟨moduleSpecΓFunctor.obj M, hFG⟩
  have : Module.Finite R ((moduleSpecΓFunctor ⋙ ModuleCat.restrictScalars φ.hom).obj M) :=
    ((moduleRestriction φ hφ).obj N).property
  exact Module.Finite.equiv ((Scheme.Modules.pushforwardGlobalSectionsIso φ).app
    M).symm.toLinearEquiv


/-- A finite map into an affine scheme has an actual finite coordinate
presentation, retaining the original scheme map. -/
theorem exists_affine_presentation {Z : Scheme.{u}} (R : CommRingCat.{u})
    (f : Z ⟶ Spec R) [AlgebraicGeometry.IsFinite f] :
    ∃ (S : CommRingCat.{u}) (φ : R ⟶ S), φ.hom.Finite ∧
      ∃ e : Z ≅ Spec S, f = e.hom ≫ Spec.map φ := by
  have : IsAffine Z := isAffine_of_isAffineHom f
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (Z.isoSpec.inv ≫ f)
  have hf : AlgebraicGeometry.IsFinite (Spec.map φ) := by
    rw [hφ]
    infer_instance
  refine ⟨_, φ, (AlgebraicGeometry.IsFinite.SpecMap_iff φ).mp hf, Z.isoSpec, ?_⟩
  rw [hφ, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]

/-- Actual direct image to an affine target preserves the finite-type
quasicoherent predicate, using the genuine finite coordinate presentation. -/
theorem affineLocallyFiniteType_pushforward_affine {Z : Scheme.{u}} (R : CommRingCat.{u})
    (f : Z ⟶ Spec R) [AlgebraicGeometry.IsFinite f] {M : Z.Modules}
    (hM : affineLocallyFiniteType Z M) :
    affineLocallyFiniteType (Spec R) ((pushforward f).obj M) := by
  obtain ⟨S, φ, hφ, e, hf⟩ := exists_affine_presentation R f
  rw [hf]
  apply (affineLocallyFiniteType (Spec R)).prop_of_iso ((pushforwardComp e.hom (Spec.map φ)).app M)
  apply affineLocallyFiniteType_pushforward_spec φ hφ
  exact (affineLocallyFiniteType (Spec S)).prop_of_iso
    ((Scheme.Modules.pushforwardIsoRestrict e).app M).symm
    (affineLocallyFiniteType_restrict e.inv hM)

/-- Direct image along any finite morphism preserves the actual all-chart
finite-type quasicoherent predicate. No noetherianity is needed here. -/
theorem affineLocallyFiniteType_pushforward {Z X : Scheme.{u}} (f : Z ⟶ X)
    [AlgebraicGeometry.IsFinite f] {M : Z.Modules} (hM : affineLocallyFiniteType Z M) :
    affineLocallyFiniteType X ((pushforward f).obj M) := by
  intro R a _
  have h : affineLocallyFiniteType (Spec R)
      ((pushforward (pullback.snd f a)).obj ((restrictFunctor (pullback.fst f a)).obj M)) :=
    affineLocallyFiniteType_pushforward_affine R (pullback.snd f a)
      (affineLocallyFiniteType_restrict _ hM)
  exact (affineFiniteSheaf R).prop_of_iso ((openBaseChange f a).app M).symm
    ((affineLocallyFiniteType_spec_iff R _).mp h)

end AlgebraicGeometry.Scheme.Modules.QuasiCoherent.FiniteMorphism

namespace AlgebraicGeometry.Scheme.Modules.QuasiCoherent
variable {Z X : Scheme.{u}} (f : Z ⟶ X) [AlgebraicGeometry.IsFinite f]

/-- The unchanged sheaf direct image restricted to actual finite-type quasicoherent objects. -/
def finiteTypePushforward : FiniteTypeSheaves Z ⥤ FiniteTypeSheaves X :=
  ObjectProperty.lift _ (finiteTypeSheavesToModules Z ⋙ pushforward f)
    (fun M ↦ FiniteMorphism.affineLocallyFiniteType_pushforward f M.property)

/-- The underlying functor remains the original module-sheaf pushforward. -/
@[simp] theorem finiteTypePushforward_comp_inclusion :
    finiteTypePushforward f ⋙ finiteTypeSheavesToModules X =
      finiteTypeSheavesToModules Z ⋙ pushforward f := rfl

instance finiteTypePushforward_additive : (finiteTypePushforward f).Additive where
  map_add := by
    intro M N a b
    apply ObjectProperty.hom_ext
    exact (pushforward f).map_add

/-- Actual open base change restricts to the original finite-type quasicoherent subcategories. -/
def finiteTypePushforwardOpenBaseChange {V : Scheme.{u}} (a : V ⟶ X) [IsOpenImmersion a] :
    finiteTypePushforward f ⋙ finiteTypeSheavesRestriction a ≅
      finiteTypeSheavesRestriction (pullback.fst f a) ⋙ finiteTypePushforward (pullback.snd f a) :=
  Functor.fullyFaithfulCancelRight (finiteTypeSheavesToModules V)
    (Functor.isoWhiskerLeft (finiteTypeSheavesToModules Z) (openBaseChange f a))


variable {R S : CommRingCat.{u}} (φ : R ⟶ S) (hφ : φ.hom.Finite)

/-- The affine-coordinate specialization of the canonical finite-morphism direct image. -/
abbrev finiteTypePushforwardSpec : FiniteTypeSheaves (Spec S) ⥤ FiniteTypeSheaves (Spec R) :=
  letI : AlgebraicGeometry.IsFinite (Spec.map φ) :=
    (AlgebraicGeometry.IsFinite.SpecMap_iff φ).mpr hφ
  finiteTypePushforward (Spec.map φ)

@[simp] theorem finiteTypePushforwardSpec_comp_inclusion :
    finiteTypePushforwardSpec φ hφ ⋙ finiteTypeSheavesToModules (Spec R) =
      finiteTypeSheavesToModules (Spec S) ⋙ Scheme.Modules.pushforward (Spec.map φ) := rfl

/-- Genuine global sections identify the original direct image with finite scalar restriction. -/
def finiteTypePushforwardSpecSquare :
    finiteTypePushforwardSpec φ hφ ⋙ (finiteTypeSheavesSpecModuleEquivalence R).functor ≅
      (finiteTypeSheavesSpecModuleEquivalence S).functor ⋙ moduleRestriction φ hφ :=
  ((finiteModule R).fullyFaithfulι.whiskeringRight _).preimageIso
    (Functor.isoWhiskerLeft (finiteTypeSheavesToModules (Spec S))
      (Scheme.Modules.pushforwardGlobalSectionsIso φ))

/-- The finite affine presentation comparison retains the source isomorphism
and the original coordinate-map direct image. -/
def finiteTypePushforwardAffinePresentationComparison {Z : Scheme.{u}} (R S : CommRingCat.{u})
    (f : Z ⟶ Spec R) [AlgebraicGeometry.IsFinite f] (φ : R ⟶ S) (hφ : φ.hom.Finite)
    (e : Z ≅ Spec S) (hf : f = e.hom ≫ Spec.map φ) :
    finiteTypePushforward f ≅
      finiteTypeSheavesRestriction e.inv ⋙ finiteTypePushforwardSpec φ hφ :=
  Functor.fullyFaithfulCancelRight (finiteTypeSheavesToModules (Spec R))
    (Functor.isoWhiskerLeft (finiteTypeSheavesToModules Z)
      (pushforwardCongr hf ≪≫ (pushforwardComp e.hom (Spec.map φ)).symm ≪≫
        Functor.isoWhiskerRight (Scheme.Modules.pushforwardIsoRestrict e) _))


variable {X Y Z : Scheme.{u}}

/-- Identity pushforward on actual finite-type quasicoherent sheaves,
from the original sheaf comparison. -/
def finiteTypePushforwardIdIso (X : Scheme.{u}) :
    finiteTypePushforward (𝟙 X) ≅ 𝟭 (FiniteTypeSheaves X) :=
  Functor.fullyFaithfulCancelRight (finiteTypeSheavesToModules X)
    (Functor.isoWhiskerLeft (finiteTypeSheavesToModules X) (Scheme.Modules.pushforwardId X) ≪≫
      Functor.rightUnitor _)

/-- Composition of the actual finite-type quasicoherent direct images,
retaining the original sheaf comparison. -/
def finiteTypePushforwardCompIso (f : X ⟶ Y) (g : Y ⟶ Z)
    [AlgebraicGeometry.IsFinite f] [AlgebraicGeometry.IsFinite g] :
    finiteTypePushforward f ⋙ finiteTypePushforward g ≅ finiteTypePushforward (f ≫ g) :=
  Functor.fullyFaithfulCancelRight (finiteTypeSheavesToModules Z)
    (Functor.isoWhiskerLeft (finiteTypeSheavesToModules X) (Scheme.Modules.pushforwardComp f g))


variable {R S T : CommRingCat.{u}}

/-- The actual finite direct image retains the original sheaf identity comparison. -/
def finiteTypePushforwardSpecIdIso (R : CommRingCat.{u}) :
    finiteTypePushforwardSpec (𝟙 R) (RingHom.Finite.id R) ≅ 𝟭 (FiniteTypeSheaves (Spec R)) :=
  Functor.fullyFaithfulCancelRight (finiteTypeSheavesToModules (Spec R))
    (Functor.isoWhiskerLeft (finiteTypeSheavesToModules (Spec R))
      (show Scheme.Modules.pushforward (Spec.map (𝟙 R)) ≅ 𝟭 (Spec R).Modules by
        simpa only [Spec.map_id] using Scheme.Modules.pushforwardId (Spec R)) ≪≫
      Functor.rightUnitor _)

/-- The original finite affine direct images compose with the genuine sheaf comparison. -/
def finiteTypePushforwardSpecCompIso (φ : R ⟶ S) (hφ : φ.hom.Finite)
    (ψ : S ⟶ T) (hψ : ψ.hom.Finite) :
    finiteTypePushforwardSpec ψ hψ ⋙ finiteTypePushforwardSpec φ hφ ≅
      finiteTypePushforwardSpec (φ ≫ ψ) (hψ.comp hφ) :=
  Functor.fullyFaithfulCancelRight (finiteTypeSheavesToModules (Spec R))
    (Functor.isoWhiskerLeft (finiteTypeSheavesToModules (Spec T))
      (show Scheme.Modules.pushforward (Spec.map ψ) ⋙ Scheme.Modules.pushforward (Spec.map φ) ≅
        Scheme.Modules.pushforward (Spec.map (φ ≫ ψ)) by
        simpa only [Spec.map_comp] using Scheme.Modules.pushforwardComp (Spec.map ψ) (Spec.map φ)))

/-- The established closed-immersion comparison is unchanged whenever this finite affine map is
  closed. -/
def finiteTypePushforwardSpecClosedIso (φ : R ⟶ S) (hφ : φ.hom.Finite)
    [IsClosedImmersion (Spec.map φ)] :
    finiteTypePushforwardSpec φ hφ ≅ finiteTypePushforward (Spec.map φ) :=
  Functor.fullyFaithfulCancelRight (finiteTypeSheavesToModules (Spec R)) (Iso.refl _)


end AlgebraicGeometry.Scheme.Modules.QuasiCoherent
