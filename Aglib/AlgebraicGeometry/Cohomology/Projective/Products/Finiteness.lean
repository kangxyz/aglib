/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Projective.Products.Finite

/-!
# Finite original cohomology over a finite projective product

A finite morphism to the original finite native product of polynomial
projective spaces over a Noetherian ring has finite unchanged cohomology
for every coherent coefficient. The derived-image proof uses the original
finite map and native product projection tower. The affine section comparison
retains the actual structural action of a separately specified factored map.
The same uniform sum-of-dimensions bound gives original cohomology vanishing.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.ProjectiveSpace
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open scoped BigOperators

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

/-- The installed ambient derived categories of actual scheme modules. -/
local instance finiteProductCohomologyStandardDerived (X : Scheme.{u}) :
    HasDerivedCategory.{u + 1} X.Modules := HasDerivedCategory.standard _

variable (R : Type u) [CommRing R] [IsNoetherianRing R]
  {m : ℕ} (ι : Fin m → Type u) (d : Fin m → ℕ) (e : ∀ i, ι i ≃ Fin (d i + 1))
  {Z : Scheme.{u}}
  (q : Z ⟶ (finiteProductOver (fun i => Over.mk (toSpec R (ι i)))).left)
  [AlgebraicGeometry.IsFinite q] (f : Z ⟶ Spec (.of R))
  (hf : q ≫ (finiteProductOver (fun i => Over.mk (toSpec R (ι i)))).hom = f)

include e hf

/-- The original factored map of a finite scheme over a projective product
has bounded coherent derived image on every coherent single. -/
theorem finiteToProjectiveProduct_derivedSingle_bounded_coherent
    (M : Z.Modules) (hM : affineLocallyFiniteType Z M) (k : ℤ) :
    Scheme.Modules.coherentHomologyObjects (Spec (.of R))
        ((Scheme.Modules.derivedPushforwardPlus f).obj
          ((DerivedCategory.Plus.singleFunctor Z.Modules k).obj M)) ∧
      ((Scheme.Modules.derivedPushforwardPlus f).obj
        ((DerivedCategory.Plus.singleFunctor Z.Modules k).obj M)).IsGE k ∧
        ((Scheme.Modules.derivedPushforwardPlus f).obj
          ((DerivedCategory.Plus.singleFunctor Z.Modules k).obj M)).IsLE (k + ∑ i, d i) := by
  let P : Fin m → Over (Spec (.of R)) := fun i => Over.mk (toSpec R (ι i))
  let : ∀ i, Fintype (ι i) := fun i => Fintype.ofEquiv (Fin (d i + 1)) (e i).symm
  let : ∀ i, IsProper (P i).hom := fun i => by
    change IsProper (toSpec R (ι i))
    infer_instance
  let : IsProper (finiteProductOver P).hom := isProper_finiteProductOver P
  let : IsLocallyNoetherian (finiteProductOver P).left :=
    LocallyOfFiniteType.isLocallyNoetherian (finiteProductOver P).hom
  let : M.IsQuasicoherent := quasicoherent_of_affineCharts M (fun A j _ => (hM A j).1)
  let K := (DerivedCategory.Plus.singleFunctor Z.Modules k).obj M
  let N := (Scheme.Modules.derivedPushforwardPlus q).obj K
  have hN := finite_derivedSingle_coherent q M hM k
  let : N.IsGE k := (Scheme.Modules.pushforward q).rightDerivedFunctorPlus_isGE K k
  let : N.IsLE k := finite_derivedSingle_isLE q M k
  have H (i : Fin m) : IsPullback (𝟙 (P i).left) (P i).hom
      (toSpec R (ι i)) (𝟙 (Spec (.of R))) := IsPullback.of_id_fst
  have ht := finiteProjectiveProduct_derived_bounded_coherent R (𝟙 _) P ι d e
    (fun i => 𝟙 (P i).left) H N k k hN
  let E : (Scheme.Modules.derivedPushforwardPlus f).obj K ≅
      (Scheme.Modules.derivedPushforwardPlus (finiteProductOver P).hom).obj N := by
    rw [← hf]
    exact (Scheme.Modules.derivedPushforwardPlusCompIso q (finiteProductOver P).hom).app K
  let : ((Scheme.Modules.derivedPushforwardPlus (finiteProductOver P).hom).obj N).IsGE k :=
    ht.2.1
  let : ((Scheme.Modules.derivedPushforwardPlus (finiteProductOver P).hom).obj N).IsLE
      (k + ∑ i, d i) := ht.2.2
  exact ⟨(Scheme.Modules.coherentHomologyObjects (Spec (.of R))).prop_of_iso E.symm ht.1,
    DerivedCategory.Plus.TStructure.t.isGE_of_iso E.symm k,
    DerivedCategory.Plus.TStructure.t.isLE_of_iso E.symm (k + ∑ i, d i)⟩

/-- Finite over the original projective product gives finite unchanged `Sheaf.H`
in every degree, with the structural action of the original factored map. -/
theorem moduleCohomology_finite_of_finiteToProjectiveProduct
    (M : Z.Modules) (hM : affineLocallyFiniteType Z M) (j : ℕ) :
    let α : R →+* Γ(Z, ⊤) := f.appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
    letI := moduleCohomologyModuleOfHom Z α M j
    Module.Finite R (Sheaf.H.{u + 1} (moduleAddSheaf Z M) j) := by
  let P : Fin m → Over (Spec (.of R)) := fun i => Over.mk (toSpec R (ι i))
  let : ∀ i, Fintype (ι i) := fun i => Fintype.ofEquiv (Fin (d i + 1)) (e i).symm
  let : ∀ i, IsProper (P i).hom := fun i => by
    change IsProper (toSpec R (ι i))
    infer_instance
  let : IsProper (finiteProductOver P).hom := isProper_finiteProductOver P
  let : IsProper f := by rw [← hf]; infer_instance
  let : M.IsQuasicoherent := quasicoherent_of_affineCharts M (fun A t _ => (hM A t).1)
  let α := f.appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
  let := moduleCohomologyModuleOfHom Z α M j
  have hc := (finiteToProjectiveProduct_derivedSingle_bounded_coherent
    R ι d e q f hf M hM 0).1 (j : ℤ)
  let : Module.Finite R (moduleSpecΓFunctor.obj
      ((DerivedCategory.Plus.homologyFunctor (Spec (.of R)).Modules (j : ℤ)).obj
        ((Scheme.Modules.pushforward f).rightDerivedFunctorPlus.obj
          ((DerivedCategory.Plus.singleFunctor Z.Modules 0).obj M)))) :=
    ((affineLocallyFiniteType_spec_iff (.of R) _).mp hc).2
  exact Module.Finite.equiv
    (moduleDerivedPushforwardSingleAffineSectionsLinearEquiv f M (injectiveResolution M) j)

end AlgebraicGeometry.Scheme.Cohomology
