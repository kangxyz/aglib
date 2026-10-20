/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.StructureSheaf.Pushforward
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.FiniteFlat
public import Aglib.AlgebraicGeometry.Morphisms.Finite.GeometricDegree
public import Aglib.AlgebraicGeometry.Morphisms.FiniteFlat.Affine
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Aglib.AlgebraicGeometry.Morphisms.Finite.GeometricFiber
public import Mathlib.RingTheory.TotallySplit
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Aglib.AlgebraicGeometry.SchemeOverField

/-!
Native migration from `R5Lab.Aglib.AlgebraicGeometry.Morphisms.FiniteFlat.Basic` at R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`4708f65d2300b44a8ee73fe8a86ededcab22f08a325da7ea3abbd6e4f224815a`.
Original objects, maps, universes and explicit hypotheses are retained.
Native providers replace duplicate implementations.
-/

@[expose] public section

open _root_.AlgebraicGeometry.Scheme.Modules (pushforwardStructureSheaf)
open _root_.AlgebraicGeometry.Scheme.OverField (Base FScheme)

/- Interface migration basis: 46f53465aaf3b0167049e9c8e9e2294111bb4281.
Original mathematical and construction source identities are retained. -/

/-!
# Finite locally free degree on the actual direct image of the structure sheaf

Application owner: `K2-018#prop:k2018-arithmetic-characters`,
`research/exposes/K2/018/expose.tex`, lines 341–445, mathematical snapshot
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`.
Frozen engineering basis: `7f86e4a1763cc4ec35e9b0a8acd659750355a0de`,
Lean 4.34.1, mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.

This file constructs `f_* O_X` as a sheaf of modules and defines rank through
local free presentations with bases indexed by `Fin n`. Geometric fibre counts
are deliberately not part of the definition. For finite étale maps, the rank
of the actual geometric-fibre algebra is proved equal to the full geometric
point count. The comparison with local-freeness rank is proved downstream in Degree.Fibres;
the function-field comparison is in Degree.FunctionField. Each retains only
its separately disclosed general background families.
-/
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Hom
universe u
variable {X Y : Scheme.{u}}

/- The actual module sheaf `f_* O_X`, with scalar restriction along `f`. -/

/-- Finite local freeness via local free presentations of the actual direct
image module sheaf. Finite indexing of each basis is required separately. -/
def FiniteLocallyFree (f : X ⟶ Y) : Prop :=
  IsAffineHom f ∧ ∃ q : SheafOfModules.LocalGeneratorsData.{u} (pushforwardStructureSheaf f),
    q.IsLocallyFreeData ∧ ∀ i, Finite (q.generators i).I

/-- Constant rank `n` through genuine local bases of `f_* O_X`.
The explicit bijection to `Fin n` excludes infinite bases, even at rank zero. -/
def HasLocallyFreeRank (f : X ⟶ Y) (n : ℕ) : Prop :=
  IsAffineHom f ∧ ∃ q : SheafOfModules.LocalGeneratorsData.{u} (pushforwardStructureSheaf f),
    q.IsLocallyFreeData ∧ ∀ i, Nonempty ((q.generators i).I ≃ Fin n)

/-- Constant finite rank gives finite local freeness. -/
theorem _root_.AlgebraicGeometry.Scheme.Hom.HasLocallyFreeRank.finiteLocallyFree {f : X ⟶ Y} {n : ℕ}
    (h : HasLocallyFreeRank f n) : FiniteLocallyFree f := by
  obtain ⟨haff, q, hq, hn⟩ := h
  refine ⟨haff, q, hq, fun i ↦ ?_⟩
  exact Finite.of_equiv (Fin n) (hn i).some.symm

/-- Both rank predicates concern mathlib's actual locally free module sheaf. -/
theorem _root_.AlgebraicGeometry.Scheme.Hom.FiniteLocallyFree.isLocallyFree {f : X ⟶ Y} (h :
    FiniteLocallyFree f) :
    (pushforwardStructureSheaf f).IsLocallyFree := by
  obtain ⟨_, q, hq, _⟩ := h
  letI := hq
  exact q.isLocallyFree

/-- The named general finite-flat-finite-presentation theorem on actual
morphisms and actual direct image module sheaves. Source: Stacks 02K9,
Lemma 29.49.2, with no Noetherian assumption. Retained premise, not an axiom.
The source identification is checked separately from the Lean application. -/
def FiniteFlatPresentationLocallyFree : Prop :=
  ∀ (X Y : Scheme.{u}) (f : X ⟶ Y), IsFinite f → Flat f →
    LocallyOfFinitePresentation f → FiniteLocallyFree f

/-- A finite étale map satisfies all hypotheses of the general local-freeness
family. No geometric point count or degree is assumed in this application. -/
theorem finiteLocallyFree_of_finite_etale
    (hfree : FiniteFlatPresentationLocallyFree.{u}) (f : X ⟶ Y)
    [IsFinite f] [Etale f] : FiniteLocallyFree f :=
  hfree X Y f inferInstance inferInstance inferInstance

/-- Native finite-flat finite-presentation geometry supplies the exact local-basis interface. -/
theorem finiteFlatPresentationLocallyFree : FiniteFlatPresentationLocallyFree.{u} := by
  intro X Y f hf hflat hfp
  letI := hf
  letI := hflat
  letI := hfp
  obtain ⟨q, hq, hfin⟩ :=
    (Scheme.Modules.finiteFlat_pushforwardStructureSheaf_isFiniteLocallyFree f).exists_localBasis
  exact ⟨inferInstance, q, hq, fun i ↦ (hfin.isFiniteType i).finite⟩

end AlgebraicGeometry.Scheme.Hom


open Algebra
namespace AlgebraicGeometry.Scheme.Hom
universe u v
/-- Algebraic geometric-fibre calculation: for an actual finite étale algebra
over a separably closed field, vector-space rank equals the full algebra-map
point count. The reduced/étale hypothesis is essential. -/
theorem etaleAlgebra_finrank_eq_card_algHom
    (K : Type u) [Field K] [IsSepClosed K]
    (A : Type v) [CommRing A] [Algebra K A]
    [EssFiniteType K A] [FormallyEtale K A] :
    Module.finrank K A = Nat.card (A →ₐ[K] K) := by
  letI := FormallyUnramified.finite_of_free K A
  letI : IsArtinianRing A := .of_finite K A
  letI := Fintype.ofFinite (PrimeSpectrum A)
  calc
    Module.finrank K A = Module.finrank K (PrimeSpectrum A → K) :=
      (FormallyEtale.equivPiOfIsSepClosed K A).toLinearEquiv.finrank_eq
    _ = Nat.card (PrimeSpectrum A) := by
      rw [Module.finrank_fintype_fun_eq_card, Nat.card_eq_fintype_card]
    _ = Nat.card (A →ₐ[K] K) :=
      (Nat.card_congr (IsFiniteSplit.algHomEquivPrimeSpectrum K A)).symm
end AlgebraicGeometry.Scheme.Hom

open CategoryTheory Limits AlgebraicGeometry
open _root_.AlgebraicGeometry.Scheme.FiniteEtale.GeometricFibres
namespace AlgebraicGeometry.Scheme.Hom
universe u
variable (K : Type u) [Field K]
variable (X : Over (Spec (CommRingCat.of K)))
/-- Canonical algebra on global sections, independently of cohomology. -/
abbrev coordinateAlgebra : Algebra K Γ(X.left, ⊤) :=
  (((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ X.hom.appTop).hom).toAlgebra
attribute [local instance] coordinateAlgebra

/-- The actual affine rational-point/coordinate-algebra equivalence. -/
def affineRationalPointEquiv [IsAffine X.left] :
    (Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ X) ≃ (Γ(X.left, ⊤) →ₐ[K] K) where
  toFun p := {
    toRingHom := coordinates K K (𝟙 _) X p
    commutes' := fun a ↦ by
      have he : ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ X.hom.appTop) ≫
          (p.left.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of K)).hom) = 𝟙 (CommRingCat.of K) := by
        rw [Category.assoc, ← Category.assoc X.hom.appTop p.left.appTop,
          ← Scheme.Hom.comp_appTop, Over.w p]
        simp
      exact congrArg (fun q : CommRingCat.of K ⟶ CommRingCat.of K ↦ q.hom a) he }
  invFun φ := Over.homMk (Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ X.left.isoSpec.inv) (by
    change (Spec.map _ ≫ X.left.isoSpec.inv) ≫ X.hom = 𝟙 _
    have hs : X.left.isoSpec.inv ≫ X.hom =
        Spec.map ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ X.hom.appTop) := by
      rw [← Scheme.isoSpec_inv_naturality, Scheme.isoSpec_Spec_inv, ← Spec.map_comp]
    rw [Category.assoc, hs, ← Spec.map_comp, Spec.map_eq_id]
    ext a
    exact φ.commutes a)
  left_inv p := by
    apply Over.OverMorphism.ext
    exact point_from_coordinates K K (𝟙 _) X p
  right_inv φ := by
    let p : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ X := Over.homMk
      (Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ X.left.isoSpec.inv) (by
        change (Spec.map _ ≫ X.left.isoSpec.inv) ≫ X.hom = 𝟙 _
        have hs : X.left.isoSpec.inv ≫ X.hom =
            Spec.map ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ X.hom.appTop) := by
          rw [← Scheme.isoSpec_inv_naturality, Scheme.isoSpec_Spec_inv, ← Spec.map_comp]
        rw [Category.assoc, hs, ← Spec.map_comp, Spec.map_eq_id]
        ext a
        exact φ.commutes a)
    have hp := point_from_coordinates K K (𝟙 _) X p
    have he : Spec.map (CommRingCat.ofHom (coordinates K K (𝟙 _) X p)) =
        Spec.map (CommRingCat.ofHom φ.toRingHom) :=
      (cancel_mono X.left.isoSpec.inv).mp hp
    have hh := Spec.map_injective he
    ext a
    exact congrArg (fun q : Γ(X.left, ⊤) ⟶ CommRingCat.of K ↦ q.hom a) hh
end AlgebraicGeometry.Scheme.Hom
namespace AlgebraicGeometry.Scheme.Hom
open CategoryTheory AlgebraicGeometry Algebra
attribute [local instance] coordinateAlgebra
universe u
variable (K : Type u) [Field K] (X : Over (Spec (CommRingCat.of K)))
theorem coordinateAlgebra_etale [IsAffine X.left] [AlgebraicGeometry.Etale X.hom] :
    Algebra.Etale K Γ(X.left, ⊤) := by
  have hA : X.hom.appTop.hom.Etale :=
    HasRingHomProperty.appTop (@AlgebraicGeometry.Etale) X.hom inferInstance
  have hi : (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom.Etale :=
    RingHom.Etale.of_bijective (ConcreteCategory.bijective_of_isIso _)
  exact RingHom.Etale.stableUnderComposition _ _ hi hA
end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry.Scheme.Hom
open CategoryTheory AlgebraicGeometry Algebra
attribute [local instance] coordinateAlgebra
universe u
/-- Actual affine étale field-scheme rank equals its full rational-point count. -/
theorem affineEtale_finrank_eq_card_rationalPoints
    (K : Type u) [Field K] [IsSepClosed K] (X : Over (Spec (CommRingCat.of K)))
    [IsAffine X.left] [AlgebraicGeometry.Etale X.hom] :
    Module.finrank K Γ(X.left, ⊤) = Nat.card (Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ X) := by
  letI := coordinateAlgebra_etale K X
  exact (etaleAlgebra_finrank_eq_card_algHom K Γ(X.left, ⊤)).trans
    (Nat.card_congr (affineRationalPointEquiv K X)).symm
end AlgebraicGeometry.Scheme.Hom

open AlgebraicGeometry.Scheme.OverField
namespace AlgebraicGeometry.Scheme.Hom
universe u
variable {F : Type u} [Field F] {X Y : FScheme F}
/-- The full fibre of an actual Over-morphism, viewed as lifts through its
underlying scheme map. This retains all source structural-map constraints. -/
def pointFibreEquivOver (f : X ⟶ Y) (K : Type u) [Field K]
    (s : Spec (CommRingCat.of K) ⟶ Base F) (y : Over.mk s ⟶ Y) :
    {x : Over.mk s ⟶ X // x ≫ f = y} ≃ (Over.mk y.left ⟶ Over.mk f.left) where
  toFun x := Over.homMk x.val.left (by
    exact congrArg (fun q : Over.mk s ⟶ Y ↦ q.left) x.property)
  invFun q := ⟨Over.homMk q.left (by
    change q.left ≫ X.hom = s
    have hq : q.left ≫ f.left = y.left := Over.w q
    rw [← Over.w f, ← Category.assoc, hq, Over.w y]
    rfl), by
      apply Over.OverMorphism.ext
      exact Over.w q⟩
  left_inv x := by
    apply Subtype.ext
    apply Over.OverMorphism.ext
    rfl
  right_inv q := by
    apply Over.OverMorphism.ext
    rfl

/-- The exact full Over-morphism fibre as rational points of its actual
scheme-theoretic geometric fibre, for an arbitrary structural field map. -/
def pointFibreEquivPullback (f : X ⟶ Y) (K : Type u) [Field K]
    (s : Spec (CommRingCat.of K) ⟶ Base F) (y : Over.mk s ⟶ Y) :
    {x : Over.mk s ⟶ X // x ≫ f = y} ≃
      (Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶
        (Over.pullback y.left).obj (Over.mk f.left)) :=
  (pointFibreEquivOver f K s y).trans (rationalPullbackEquiv K y.left (Over.mk f.left))
end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry.Scheme.Hom
attribute [local instance] coordinateAlgebra
universe u
variable {F : Type u} [Field F] {X Y : FScheme F}
/-- The actual scheme-theoretic geometric fibre as a K-scheme. -/
abbrev geometricFibre (f : X ⟶ Y) (K : Type u) [Field K]
    (s : Spec (CommRingCat.of K) ⟶ Base F) (y : Over.mk s ⟶ Y) :
    Over (Spec (CommRingCat.of K)) :=
  (Over.pullback y.left).obj (Over.mk f.left)

/-- Geometric degree calculated as vector-space rank of the actual geometric
fibre algebra, for every K,s,y in the frozen interface. This theorem uses the
étale/reduced-fibre hypothesis and no new general theorem premise. -/
theorem card_pointFibre_eq_finrank
    (f : X ⟶ Y) [IsFinite f.left] [Etale f.left]
    (K : Type u) [Field K] [IsAlgClosed K]
    (s : Spec (CommRingCat.of K) ⟶ Base F) (y : Over.mk s ⟶ Y) :
    Nat.card {x : Over.mk s ⟶ X // x ≫ f = y} =
      Module.finrank K Γ((geometricFibre f K s y).left, ⊤) := by
  let Z := geometricFibre f K s y
  letI : IsFinite Z.hom := by dsimp [Z, geometricFibre]; infer_instance
  letI : Etale Z.hom := by dsimp [Z, geometricFibre]; infer_instance
  letI : IsAffine Z.left := isAffine_of_isAffineHom Z.hom
  exact (Nat.card_congr (pointFibreEquivPullback f K s y)).trans
    (affineEtale_finrank_eq_card_rationalPoints K Z).symm

/-- Actual geometric-fibre algebra rank; this is distinct from local-freeness
rank of the module sheaf f_*O_X. Their comparison remains an obligation. -/
def HasGeometricFibreRank (f : X ⟶ Y) (n : ℕ) : Prop :=
  ∀ (K : Type u) [Field K] [IsAlgClosed K]
    (s : Spec (CommRingCat.of K) ⟶ Base F) (y : Over.mk s ⟶ Y),
    Module.finrank K Γ((geometricFibre f K s y).left, ⊤) = n

/-- Full all-geometric-points comparison, without replacing arbitrary field
maps by one algebraic-closure fibre. No local-free-rank equivalence is asserted. -/
theorem hasGeometricFibreRank_iff_hasGeometricDegree
    (f : X ⟶ Y) [IsFinite f.left] [Etale f.left] (n : ℕ) :
    HasGeometricFibreRank f n ↔ HasGeometricDegree f n := by
  constructor
  · intro h K _ _ s y
    rw [card_pointFibre_eq_finrank f K s y]
    exact h K s y
  · intro h K _ _ s y
    rw [← card_pointFibre_eq_finrank f K s y]
    exact h K s y
end AlgebraicGeometry.Scheme.Hom

open Opposite
namespace AlgebraicGeometry.Scheme.Hom
universe u
variable {X Y : Scheme.{u}}
/-- On each actual open of the target, the direct-image module sheaf has
precisely the source sections, with scalars restricted through f.app U. -/
def pushforwardStructureSectionsEquiv (f : X ⟶ Y) (U : Y.Opens) :
    letI : Module Γ(Y, U) Γ(X, f ⁻¹ᵁ U) := (f.app U).hom.toModule
    ((pushforwardStructureSheaf f).val.obj (op U)) ≃ₗ[Γ(Y, U)] Γ(X, f ⁻¹ᵁ U) :=
  LinearEquiv.refl _ _
end AlgebraicGeometry.Scheme.Hom
