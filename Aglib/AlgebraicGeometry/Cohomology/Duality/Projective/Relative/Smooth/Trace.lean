/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.SerreTransport
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.ClosedEmbedding.Structural

/-!
# The original normalized trace for a chosen smooth closed embedding

The actual canonical comparison and native shifts transport the original
closed Serre map and identify one trace in every Ext degree. Construction
and this identity use separatedness, with arbitrary commutative bases.
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

universe uA vA wA eA uB vB wB tS

private theorem singleReindexIso_output_inv_of_degree
    {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
    (N : B) (n d c q r z : ℤ) (hc : c = n - d) (hq : c + r = q)
    (hz : z = -d) :
    (shiftFunctorAdd' (DerivedCategory B) c r q hq).inv.app
        ((DerivedCategory.singleFunctor B n).obj N) ≫
        (singleReindexIso N n q (r - d) (by omega)).inv =
      ((singleReindexIso N n c z (by omega)).inv)⟦r⟧' ≫
        (shiftFunctorAdd' (DerivedCategory B) z r (r - d) (by omega)).inv.app
          ((DerivedCategory.singleFunctor B 0).obj N) := by
  subst z
  exact singleReindexIso_output_inv N n d c q r hc hq

private theorem purity_transport_eq_single_trace
    {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
    [HasExt.{eA} A]
    {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
    {S : Type tS} [CommRing S] [Linear S A] [Linear S B]
    (F : DerivedCategory.Plus A ⥤ DerivedCategory B) [F.CommShift ℤ]
    (Ω : A) (K : DerivedCategory A) (N : B) (n d c₀ : ℕ)
    (hc : (c₀ : ℤ) = (n : ℤ) - d)
    (E : K ≅ (DerivedCategory.singleFunctor A ((n : ℤ) - d)).obj Ω)
    (Φ : ∀ (T : A) (q : ℕ),
      ((DerivedCategory.singleFunctor A 0).obj T ⟶ K⟦(q : ℤ)⟧) →ₗ[S]
        (F.obj ((DerivedCategory.Plus.singleFunctor A 0).obj T) ⟶
          ((DerivedCategory.singleFunctor B (n : ℤ)).obj N)⟦(q : ℤ)⟧))
    (hΦ : ∀ (T T' : A) (r j q : ℕ) (η : Ext.{eA} T T' r)
      (g : (DerivedCategory.singleFunctor A 0).obj T' ⟶ K⟦(j : ℤ)⟧)
      (hrj : r + j = q),
      Φ T q (η.hom.comp g (by omega)) =
        (η.homPlus.map F).comp (Φ T' j g) (by omega))
    (M : A) (r : ℕ) (β : Ext.{eA} M Ω r) :
    serreLinearMapOfPurity (S := S) M Ω K
        (F.obj ((DerivedCategory.Plus.singleFunctor A 0).obj M)) N
        n d (r + c₀) r (by omega) E (Φ M (r + c₀)) β =
      (β.homPlus.map F).comp
        (serreLinearMapOfPurity (S := S) Ω Ω K
          (F.obj ((DerivedCategory.Plus.singleFunctor A 0).obj Ω)) N
          n d (0 + c₀) 0 (by omega) E (Φ Ω (0 + c₀)) (Ext.mk₀ (𝟙 Ω)))
        (by omega) := by
  let δ := purityInputLinearEquiv (S := S) Ω Ω K ((n : ℤ) - d) E (0 + c₀) 0
    (by omega) (Ext.mk₀ (𝟙 Ω))
  have hinput := purityInputLinearEquiv_eq_hom_comp_of_degree (S := S)
    M Ω K ((n : ℤ) - d) (0 + c₀) (r + c₀) r (by omega) (by omega) E β
  have hout := singleReindexIso_output_inv_of_degree N (n : ℤ) (d : ℤ)
    ((0 + c₀ : ℕ) : ℤ) ((r + c₀ : ℕ) : ℤ) (r : ℤ) ((0 : ℤ) - d)
    (by omega) (by omega) (by omega)
  rw [serreLinearMapOfPurity_apply, serreLinearMapOfPurity_apply]
  change Φ M (r + c₀)
      (purityInputLinearEquiv (S := S) M Ω K ((n : ℤ) - d) E (r + c₀) r
        (by omega) β) ≫
      (singleReindexIso N (n : ℤ) ((r + c₀ : ℕ) : ℤ) ((r : ℤ) - d)
        (by omega)).inv =
    (β.homPlus.map F).comp
      (Φ Ω (0 + c₀) δ ≫
        (singleReindexIso N (n : ℤ) ((0 + c₀ : ℕ) : ℤ) ((0 : ℤ) - d)
          (by omega)).inv) (by omega)
  rw [hinput, hΦ M Ω r (0 + c₀) (r + c₀) β δ (by omega)]
  simp only [ShiftedHom.comp, Functor.map_comp, Category.assoc]
  rw [hout]


local instance relativeSmoothTraceUnitQuasicoherent (Z : Scheme.{u}) :
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
local notation "K" => Functor.obj DerivedCategory.Plus.ι
  (Functor.obj (derivedClosedImmersionRightAdjointPlus i)
    (Functor.obj (DerivedCategory.Plus.singleFunctor P.Modules 0)
      (Functor.obj (relativeTopDifferentialCoefficientsFunctor p n) O)))
local notation "D(" M ")" => Functor.obj
  (derivedPushforwardPlus (i ≫ p) ⋙ DerivedCategory.Plus.ι)
  (Functor.obj (DerivedCategory.Plus.singleFunctor X.Modules 0) M)

/-- The degree-bound branch is the original closed comparison transported by
the actual canonical isomorphism and the installed single-shift maps. -/
def relativeSmoothClosedEmbeddingSerreLinearMapOfLE
    {S : Type u} [CommRing S] (α : S →+* Γ(Y, ⊤))
    (M : X.Modules) (r : ℕ) (hd : d ≤ n) :
    letI := moduleCategoryLinearOfHom X (i.appTop.hom.comp (p.appTop.hom.comp α))
    letI := moduleCategoryLinearOfHom Y α
    Ext.{u + 1} M Ω r →ₗ[S]
      (D(M) ⟶ ((DerivedCategory.singleFunctor Y.Modules 0).obj O)⟦(r : ℤ) - d⟧) := by
  let := moduleCategoryLinearOfHom X (i.appTop.hom.comp (p.appTop.hom.comp α))
  let := moduleCategoryLinearOfHom Y α
  let E := unitPurityIso i p n d
    (projectiveClosedImmersionCanonicalIso i p n d R ι e a f h)
  exact serreLinearMapOfPurity M Ω K D(M) O n d (r + (n - d)) r
    (serreDegree_eq n d r hd) E
    (relativeClosedEmbeddingSerreLinearMap i p R ι a f h α n e O M (r + (n - d)))

/-- The forward arrow uses the original closed Serre map and the actual
integer-indexed canonical isomorphism. Its value is independent of the
structural scalar presentation. -/
theorem relativeSmoothClosedEmbeddingSerreLinearMapOfLE_apply
    {S : Type u} [CommRing S] (α : S →+* Γ(Y, ⊤))
    (M : X.Modules) (r : ℕ) (hd : d ≤ n) (β : Ext.{u + 1} M Ω r) :
    let E := unitPurityIso i p n d
      (projectiveClosedImmersionCanonicalIso i p n d R ι e a f h)
    relativeSmoothClosedEmbeddingSerreLinearMapOfLE i p R ι a f h n d e α M r hd β =
      relativeClosedEmbeddingSerreMap i p R ι a f h n e O M (r + (n - d))
        (β.hom ≫
          (@singleReindexIso X.Modules _ _
            (AlgebraicGeometry.Scheme.Modules.standardHasDerivedCategory X)
            Ω ((n : ℤ) - d) ((r + (n - d) : ℕ) : ℤ) (r : ℤ)
            (serreDegree_eq n d r hd)).hom ≫ (E.inv)⟦((r + (n - d) : ℕ) : ℤ)⟧') ≫
        (@singleReindexIso Y.Modules _ _
          (AlgebraicGeometry.Scheme.Modules.standardHasDerivedCategory Y)
          O (n : ℤ) ((r + (n - d) : ℕ) : ℤ)
          ((r : ℤ) - d) (by omega)).inv := rfl

private theorem relativeSmoothClosedEmbeddingSerreLinearMapOfLE_eq_zero
    {S : Type u} [CommRing S] (α : S →+* Γ(Y, ⊤))
    (M : X.Modules) (r : ℕ) (hd : d ≤ n) (β : Ext.{u + 1} M Ω r) :
    relativeSmoothClosedEmbeddingSerreLinearMapOfLE i p R ι a f h n d e α M r hd β =
      (β.homPlus.map (derivedPushforwardPlus (i ≫ p) ⋙ DerivedCategory.Plus.ι)).comp
        (relativeSmoothClosedEmbeddingSerreLinearMapOfLE i p R ι a f h n d e α
          Ω 0 hd (Ext.mk₀ (𝟙 Ω))) (by omega) := by
  let := moduleCategoryLinearOfHom X (i.appTop.hom.comp (p.appTop.hom.comp α))
  let := moduleCategoryLinearOfHom Y α
  exact purity_transport_eq_single_trace (S := S)
    (derivedPushforwardPlus (i ≫ p) ⋙ DerivedCategory.Plus.ι) Ω K O n d (n - d)
    (by omega)
    (unitPurityIso i p n d (projectiveClosedImmersionCanonicalIso i p n d R ι e a f h))
    (fun T q => relativeClosedEmbeddingSerreLinearMap i p R ι a f h α n e O T q)
    (by
      intro T T' r j q η g hrj
      erw [relativeClosedEmbeddingSerreLinearMap_apply (S := S) i p R ι a f h α n e O T q
          (η.hom.comp g (by omega)),
        relativeClosedEmbeddingSerreLinearMap_apply (S := S) i p R ι a f h α n e O T' j g]
      exact relativeClosedEmbeddingSerreMap_comp i p R ι a f h n e O η g hrj)
    M r β

/-- The empty-source branch has its unique zero comparison. No global
dimension inequality is imposed on the canonical-bundle statement. -/
def relativeSmoothClosedEmbeddingSerreLinearMap
    {S : Type u} [CommRing S] (α : S →+* Γ(Y, ⊤)) (M : X.Modules) (r : ℕ) :
    letI := moduleCategoryLinearOfHom X (i.appTop.hom.comp (p.appTop.hom.comp α))
    letI := moduleCategoryLinearOfHom Y α
    Ext.{u + 1} M Ω r →ₗ[S]
      (D(M) ⟶ ((DerivedCategory.singleFunctor Y.Modules 0).obj O)⟦(r : ℤ) - d⟧) := by
  classical
  let := moduleCategoryLinearOfHom X (i.appTop.hom.comp (p.appTop.hom.comp α))
  let := moduleCategoryLinearOfHom Y α
  exact if hd : d ≤ n then
    relativeSmoothClosedEmbeddingSerreLinearMapOfLE i p R ι a f h n d e α M r hd
  else 0

/-- This is the original normalized trace evaluated at the actual canonical
identity class; no Noetherian or coherence premise is used to construct it. -/
def relativeSmoothClosedEmbeddingTrace :
    D(Ω) ⟶ ((DerivedCategory.singleFunctor Y.Modules 0).obj O)⟦(0 : ℤ) - d⟧ :=
  relativeSmoothClosedEmbeddingSerreLinearMap i p R ι a f h n d e
    (RingHom.id Γ(Y, ⊤)) Ω 0 (Ext.mk₀ (𝟙 Ω))

private theorem relativeSmoothClosedEmbeddingTrace_eq_ofLE
    {S : Type u} [CommRing S] (α : S →+* Γ(Y, ⊤)) (hd : d ≤ n) :
    relativeSmoothClosedEmbeddingTrace i p R ι a f h n d e =
      relativeSmoothClosedEmbeddingSerreLinearMapOfLE i p R ι a f h n d e α
        Ω 0 hd (Ext.mk₀ (𝟙 Ω)) := by
  simp only [relativeSmoothClosedEmbeddingTrace,
    relativeSmoothClosedEmbeddingSerreLinearMap, dite_eq_left hd]
  exact (relativeSmoothClosedEmbeddingSerreLinearMapOfLE_apply i p R ι a f h n d e
    (RingHom.id Γ(Y, ⊤)) Ω 0 hd (Ext.mk₀ (𝟙 Ω))).trans
    (relativeSmoothClosedEmbeddingSerreLinearMapOfLE_apply i p R ι a f h n d e
      α Ω 0 hd (Ext.mk₀ (𝟙 Ω))).symm

/-- All Ext degrees use the same original normalized trace. The construction
and this identity require neither Noetherianity nor coherence. -/
theorem relativeSmoothClosedEmbeddingSerreLinearMap_eq_trace
    {S : Type u} [CommRing S] (α : S →+* Γ(Y, ⊤))
    (M : X.Modules) (r : ℕ) (β : Ext.{u + 1} M Ω r) :
    relativeSmoothClosedEmbeddingSerreLinearMap i p R ι a f h n d e α M r β =
      (β.homPlus.map (derivedPushforwardPlus (i ≫ p) ⋙ DerivedCategory.Plus.ι)).comp
        (relativeSmoothClosedEmbeddingTrace i p R ι a f h n d e) (by omega) := by
  classical
  by_cases hd : d ≤ n
  · simp only [relativeSmoothClosedEmbeddingSerreLinearMap, dite_eq_left hd]
    rw [relativeSmoothClosedEmbeddingTrace_eq_ofLE i p R ι a f h n d e α hd]
    exact relativeSmoothClosedEmbeddingSerreLinearMapOfLE_eq_zero
      i p R ι a f h n d e α M r hd β
  · let : SmoothOfRelativeDimension n p :=
      ProjectiveSpace.smoothOfRelativeDimension_of_isPullback R ι n e a p f h
    let : IsEmpty X := source_isEmpty i p n d (Nat.lt_of_not_ge hd)
    exact (derivedPushforwardSingle_isZero_of_empty (i ≫ p) M).eq_of_src _ _

end AlgebraicGeometry.Scheme.Cohomology
