/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.Smooth.Trace
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.ClosedEmbedding.Linear

/-!
# Coherent Serre duality for a chosen smooth closed embedding

The same original normalized comparison is bijective for coherent sources
over a Noetherian separated base. Its construction and all-degree trace
identity are supplied by the independent smooth-trace module.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicGeometry.Scheme.Cohomology

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Differentials
open RelativeCanonicalReindex RelativeCanonicalUnit RelativeCanonicalDimension
universe u

attribute [local instance] AlgebraicGeometry.Scheme.Modules.standardHasDerivedCategory

local instance relativeSmoothDualityUnitQuasicoherent (Z : Scheme.{u}) :
    (SheafOfModules.unit Z.ringCatSheaf).IsQuasicoherent := by
  let := unit_isLocallyFree Z
  infer_instance

variable {X P Y : Scheme.{u}} (i : X ⟶ P) [IsClosedImmersion i] (p : P ⟶ Y)
  (R : Type u) [CommRing R] (ι : Type u)
  (a : P ⟶ ProjectiveSpace R ι) (f : Y ⟶ Spec (.of R))
  (h : IsPullback a p (ProjectiveSpace.toSpec R ι) f) [Y.IsSeparated]
  (n d : ℕ) (e : ι ≃ Fin (n + 1)) [SmoothOfRelativeDimension d (i ≫ p)]

local notation "Ω" => moduleExteriorPower X (relativeDifferentialSheaf (i ≫ p)) d
local notation "O" => SheafOfModules.unit Y.ringCatSheaf
local notation "D(" M ")" => Functor.obj
  (derivedPushforwardPlus (i ≫ p) ⋙ DerivedCategory.Plus.ι)
  (Functor.obj (DerivedCategory.Plus.singleFunctor X.Modules 0) M)

/-- Coherent duality of the same forward comparison, with the empty case
proved from the actual local dimension equation. -/
theorem relativeSmoothClosedEmbeddingSerreLinearMap_bijective [IsNoetherian Y]
    {S : Type u} [CommRing S] (α : S →+* Γ(Y, ⊤)) (M : X.Modules)
    (hM : Scheme.Modules.QuasiCoherent.affineLocallyFiniteType X M) (r : ℕ) :
    letI := moduleCategoryLinearOfHom X (i.appTop.hom.comp (p.appTop.hom.comp α))
    letI := moduleCategoryLinearOfHom Y α
    Function.Bijective
      (relativeSmoothClosedEmbeddingSerreLinearMap i p R ι a f h n d e α M r) := by
  classical
  let := moduleCategoryLinearOfHom X (i.appTop.hom.comp (p.appTop.hom.comp α))
  let := moduleCategoryLinearOfHom Y α
  by_cases hd : d ≤ n
  · simp only [relativeSmoothClosedEmbeddingSerreLinearMap, dite_eq_left hd]
    apply serreLinearMapOfPurity_bijective
    exact relativeClosedEmbeddingSerreMap_bijective i p R ι a f h n e O M hM
      (r + (n - d))
  · let : SmoothOfRelativeDimension n p :=
      ProjectiveSpace.smoothOfRelativeDimension_of_isPullback R ι n e a p f h
    let : IsEmpty X := source_isEmpty i p n d (Nat.lt_of_not_ge hd)
    exact comparison_bijective_of_zero_source M Ω r
      (module_isZero_of_empty M)
      (derivedPushforwardSingle_isZero_of_empty (i ≫ p) M) _

/-- Coherent smooth duality retains the same transported original forward map. -/
def relativeSmoothClosedEmbeddingSerreDuality [IsNoetherian Y]
    {S : Type u} [CommRing S] (α : S →+* Γ(Y, ⊤)) (M : X.Modules)
    (hM : Scheme.Modules.QuasiCoherent.affineLocallyFiniteType X M) (r : ℕ) :
    letI := moduleCategoryLinearOfHom X (i.appTop.hom.comp (p.appTop.hom.comp α))
    letI := moduleCategoryLinearOfHom Y α
    Ext.{u + 1} M Ω r ≃ₗ[S]
      (D(M) ⟶ ((DerivedCategory.singleFunctor Y.Modules 0).obj O)⟦(r : ℤ) - d⟧) := by
  let := moduleCategoryLinearOfHom X (i.appTop.hom.comp (p.appTop.hom.comp α))
  let := moduleCategoryLinearOfHom Y α
  exact LinearEquiv.ofBijective
    (relativeSmoothClosedEmbeddingSerreLinearMap i p R ι a f h n d e α M r)
    (relativeSmoothClosedEmbeddingSerreLinearMap_bijective i p R ι a f h n d e α M hM r)

/-- The equivalence retains the original transported comparison as forward map. -/
theorem relativeSmoothClosedEmbeddingSerreDuality_apply [IsNoetherian Y]
    {S : Type u} [CommRing S] (α : S →+* Γ(Y, ⊤)) (M : X.Modules)
    (hM : Scheme.Modules.QuasiCoherent.affineLocallyFiniteType X M)
    (r : ℕ) (β : Ext.{u + 1} M Ω r) :
    relativeSmoothClosedEmbeddingSerreDuality i p R ι a f h n d e α M hM r β =
      relativeSmoothClosedEmbeddingSerreLinearMap i p R ι a f h n d e α M r β := rfl

/-- In every Ext degree, the coherent equivalence is pushforward followed by
one and the same original normalized smooth trace. -/
theorem relativeSmoothClosedEmbeddingSerreDuality_eq_trace [IsNoetherian Y]
    {S : Type u} [CommRing S] (α : S →+* Γ(Y, ⊤)) (M : X.Modules)
    (hM : Scheme.Modules.QuasiCoherent.affineLocallyFiniteType X M)
    (r : ℕ) (β : Ext.{u + 1} M Ω r) :
    relativeSmoothClosedEmbeddingSerreDuality i p R ι a f h n d e α M hM r β =
      (β.homPlus.map (derivedPushforwardPlus (i ≫ p) ⋙ DerivedCategory.Plus.ι)).comp
        (relativeSmoothClosedEmbeddingTrace i p R ι a f h n d e) (by omega) := by
  rw [relativeSmoothClosedEmbeddingSerreDuality_apply]
  exact relativeSmoothClosedEmbeddingSerreLinearMap_eq_trace i p R ι a f h n d e α M r β

end AlgebraicGeometry.Scheme.Cohomology
