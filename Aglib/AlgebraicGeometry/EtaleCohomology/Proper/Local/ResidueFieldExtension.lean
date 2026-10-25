/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Proper.Local.ProjectiveLineModels
public import Aglib.AlgebraicGeometry.EtaleCohomology.Fields.SeparableExtension.FiniteConstants.NativeLineComparison

/-! # Original local P1 comparison at a separably closed residue-field extension

The actual closed-fibre comparison is transported to the original native line
through its original over-base-change isomorphism. Composition with the native
field-line map keeps the actual inverse-image coefficient comparison and the
literal composite ring homomorphism.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Proper

universe u

attribute [local instance] hasSheafifyLarge HasExt.standard

open AlgebraicGeometry.ProjectiveSpace.BinaryFormProduct

private theorem bijective_from_comparison {A B C D : Type*}
    (a : A → B) (b : B → C) (c : A → D) (d : D → C)
    (ha : Function.Bijective a) (hb : Function.Bijective b) (hd : Function.Bijective d)
    (h : ∀ x, d (c x) = b (a x)) : Function.Bijective c := by
  constructor
  · intro x y hxy
    exact ha.injective (hb.injective
      ((h x).symm.trans ((congrArg d hxy).trans (h y))))
  · intro y
    obtain ⟨x, hx⟩ := (hb.comp ha).surjective (d y)
    exact ⟨x, hd.injective ((h x).trans hx)⟩

private theorem pullback_bijective_of_factors
    {X S T : Scheme.{u}} (f : S ⟶ X) (g : T ⟶ S) (h : T ⟶ X)
    (he : g ≫ f = h) (F : AbelianSheaf.{u, u + 1} X) (q : ℕ)
    (hf : Function.Bijective (cohomologyPullback.{u, u + 2, u + 2} f F q))
    (hg : Function.Bijective
      (cohomologyPullback.{u, u + 2, u + 2} g ((inverseImage f).obj F) q)) :
    Function.Bijective (cohomologyPullback.{u, u + 2, u + 2} h F q) := by
  subst h
  let E : (inverseImage (g ≫ f)).obj F ≅
      (inverseImage g).obj ((inverseImage f).obj F) := (inverseImageComp f g).app F
  exact bijective_from_comparison
    (cohomologyPullback.{u, u + 2, u + 2} f F q)
    (cohomologyPullback.{u, u + 2, u + 2} g ((inverseImage f).obj F) q)
    (cohomologyPullback.{u, u + 2, u + 2} (g ≫ f) F q)
    (Sheaf.H.map E.hom q) hf hg (cohomologyMapIso_bijective E q)
    (cohomologyPullback_comp f g F q)

private theorem pullback_bijective_of_iso_factor
    {X S T : Scheme.{u}} (f : S ⟶ X) (e : T ≅ S) (h : T ⟶ X)
    (he : e.hom ≫ f = h) (F : AbelianSheaf.{u, u + 1} X) (q : ℕ)
    (hf : Function.Bijective (cohomologyPullback.{u, u + 2, u + 2} f F q)) :
    Function.Bijective (cohomologyPullback.{u, u + 2, u + 2} h F q) :=
  pullback_bijective_of_factors f e.hom h he F q hf
    (cohomologyPullback_bijective_of_isEquivalence e.hom ((inverseImage f).obj F) q)

private theorem pullback_bijective_cancel_iso_factor
    {X S T : Scheme.{u}} (f : S ⟶ X) (e : T ≅ S) (h : T ⟶ X)
    (he : e.hom ≫ f = h) (F : AbelianSheaf.{u, u + 1} X) (q : ℕ)
    (hh : Function.Bijective (cohomologyPullback.{u, u + 2, u + 2} h F q)) :
    Function.Bijective (cohomologyPullback.{u, u + 2, u + 2} f F q) := by
  subst h
  let E : (inverseImage (e.hom ≫ f)).obj F ≅
      (inverseImage e.hom).obj ((inverseImage f).obj F) := (inverseImageComp f e.hom).app F
  exact bijective_from_comparison
    (cohomologyPullback.{u, u + 2, u + 2} (e.hom ≫ f) F q)
    (Sheaf.H.map E.hom q)
    (cohomologyPullback.{u, u + 2, u + 2} f F q)
    (cohomologyPullback.{u, u + 2, u + 2} e.hom ((inverseImage f).obj F) q)
    hh (cohomologyMapIso_bijective E q)
    (cohomologyPullback_bijective_of_isEquivalence e.hom ((inverseImage f).obj F) q)
    (fun x => (cohomologyPullback_comp f e.hom F q x).symm)

private theorem iso_composite_projection {C : Type*} [Category* C] {A B D E : C}
    (a : A ≅ B) (b : B ≅ D) (p : D ⟶ E) (q : B ⟶ E) (f : A ⟶ E)
    (hb : b.hom ≫ p = q) (ha : a.hom ≫ q = f) : (a ≪≫ b).hom ≫ p = f :=
  (Category.assoc a.hom b.hom p).trans
    ((congrArg (fun k => a.hom ≫ k) hb).trans ha)

private theorem conjugated_maps_comp {C : Type*} [Category* C]
    {A₀ A₁ A₂ B₀ B₁ B₂ : C} (e₀ : A₀ ≅ B₀) (e₁ : A₁ ≅ B₁) (e₂ : A₂ ≅ B₂)
    (f : B₁ ⟶ B₀) (g : B₂ ⟶ B₁) (h : B₂ ⟶ B₀) (hh : g ≫ f = h) :
    (e₂.hom ≫ g ≫ e₁.inv) ≫ (e₁.hom ≫ f ≫ e₀.inv) = e₂.hom ≫ h ≫ e₀.inv := by
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Category.assoc g f e₀.inv, hh]

/-- Composition of the literal original native projective-line maps is induced
by composition of the same original ring homomorphisms. -/
theorem projectiveLine_nativeBaseChangeMap_comp
    {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    (φ : R →+* S) (ψ : S →+* T) :
    lineBaseChangeMap ψ ≫ lineBaseChangeMap φ = lineBaseChangeMap (ψ.comp φ) :=
  conjugated_maps_comp (AlgebraicGeometry.ProjectiveSpace.finUliftIso R 2)
    (AlgebraicGeometry.ProjectiveSpace.finUliftIso S 2)
    (AlgebraicGeometry.ProjectiveSpace.finUliftIso T 2)
    (AlgebraicGeometry.ProjectiveSpace.map φ (ULift.{u} (Fin 2)))
    (AlgebraicGeometry.ProjectiveSpace.map ψ (ULift.{u} (Fin 2)))
    (AlgebraicGeometry.ProjectiveSpace.map (ψ.comp φ) (ULift.{u} (Fin 2)))
    (AlgebraicGeometry.ProjectiveSpace.map_comp ψ φ (ULift.{u} (Fin 2))).symm

private theorem killed_functor_obj {C D : Type*} [Category* C] [Category* D]
    [Preadditive C] [Preadditive D] (L : C ⥤ D) [L.Additive]
    (n : ℕ) (F : C) (hF : n • 𝟙 F = 0) : n • 𝟙 (L.obj F) = 0 := by
  simpa using congrArg L.map hF

variable (R : Type u) [CommRing R] [HenselianLocalRing R]
  [IsSepClosed (IsLocalRing.ResidueField R)]

/-- The original categorical closed-fibre comparison gives bijectivity for the
same original residue ring map on the native projective line. -/
theorem projectiveLine_nativeResiduePullback_bijective_of_killed
    (n : ℕ) (hn : n ≠ 0)
    (F : AbelianSheaf.{u, u + 1} (ProjectiveLine.projectiveP1 R))
    (hF : n • 𝟙 F = 0) (q : ℕ) :
    Function.Bijective (cohomologyPullback.{u, u + 2, u + 2}
      (lineBaseChangeMap (IsLocalRing.residue R)) F q) := by
  let f : pullback (ProjectiveLine.structureMap R) (LocalRing.residueSpecMap R) ⟶
      ProjectiveLine.projectiveP1 R :=
    pullback.fst (ProjectiveLine.structureMap R) (LocalRing.residueSpecMap R)
  let e : ProjectiveLine.projectiveP1 (IsLocalRing.ResidueField R) ≅
      pullback (ProjectiveLine.structureMap R) (LocalRing.residueSpecMap R) :=
    (Over.forget (Spec (.of (IsLocalRing.ResidueField R)))).mapIso
      (lineOverBaseChangeIso (IsLocalRing.residue R))
  exact pullback_bijective_of_iso_factor f e
    (lineBaseChangeMap (IsLocalRing.residue R))
    (lineOverBaseChangeIso_hom_fst (IsLocalRing.residue R)) F q
    (projectiveLine_residuePullback_bijective_of_killed R n hn F hF q)

/-- Original native P1 pullback along the residue quotient followed by the
specified separably closed field embedding is bijective in every degree.
No order-invertibility or Noetherian hypothesis is imposed. -/
theorem projectiveLine_residueFieldExtension_bijective_of_killed
    (Ω : Type u) [Field Ω] [IsSepClosed Ω]
    (ι : IsLocalRing.ResidueField R →+* Ω) (n : ℕ) (hn : n ≠ 0)
    (F : AbelianSheaf.{u, u + 1} (ProjectiveLine.projectiveP1 R))
    (hF : n • 𝟙 F = 0) (q : ℕ) :
    Function.Bijective (cohomologyPullback.{u, u + 2, u + 2}
      (lineBaseChangeMap (ι.comp (IsLocalRing.residue R))) F q) := by
  let G := (inverseImage (lineBaseChangeMap (IsLocalRing.residue R))).obj F
  have hG : n • 𝟙 G = 0 :=
    killed_functor_obj (inverseImage (lineBaseChangeMap (IsLocalRing.residue R))) n F hF
  let : Algebra (IsLocalRing.ResidueField R) Ω := ι.toAlgebra
  have hι : Function.Bijective
      (cohomologyPullback.{u, u + 2, u + 2} (lineBaseChangeMap ι) G q) :=
    projectiveLine_fieldMap_cohomologyPullback_bijective_of_killed
      (IsLocalRing.ResidueField R) Ω n hn G hG q
  exact pullback_bijective_of_factors
    (lineBaseChangeMap (IsLocalRing.residue R)) (lineBaseChangeMap ι)
    (lineBaseChangeMap (ι.comp (IsLocalRing.residue R)))
    (projectiveLine_nativeBaseChangeMap_comp (IsLocalRing.residue R) ι) F q
    (projectiveLine_nativeResiduePullback_bijective_of_killed R n hn F hF q) hι

/-- The original projection from the reversed categorical geometric fibre has
bijective cohomology pullback along the specified residue-field extension. -/
theorem projectiveLine_residueFieldFiberPullback_bijective_of_killed
    (Ω : Type u) [Field Ω] [IsSepClosed Ω]
    (ι : IsLocalRing.ResidueField R →+* Ω) (n : ℕ) (hn : n ≠ 0)
    (F : AbelianSheaf.{u, u + 1} (ProjectiveLine.projectiveP1 R))
    (hF : n • 𝟙 F = 0) (q : ℕ) :
    Function.Bijective (cohomologyPullback.{u, u + 2, u + 2}
      (pullback.snd (Spec.map (CommRingCat.ofHom (ι.comp (IsLocalRing.residue R))))
        (ProjectiveLine.structureMap R)) F q) := by
  let φ := ι.comp (IsLocalRing.residue R)
  let η : Spec (.of Ω) ⟶ Spec (.of R) := Spec.map (CommRingCat.ofHom φ)
  let p := ProjectiveLine.structureMap R
  let e₀ : ProjectiveLine.projectiveP1 Ω ≅ pullback p η :=
    (Over.forget (Spec (.of Ω))).mapIso (lineOverBaseChangeIso φ)
  let e : ProjectiveLine.projectiveP1 Ω ≅ pullback η p :=
    e₀ ≪≫ pullbackSymmetry p η
  have he : e.hom ≫ pullback.snd η p = lineBaseChangeMap φ :=
    iso_composite_projection e₀ (pullbackSymmetry p η) (pullback.snd η p)
      (pullback.fst p η) (lineBaseChangeMap φ)
      (pullbackSymmetry_hom_comp_snd p η) (lineOverBaseChangeIso_hom_fst φ)
  exact pullback_bijective_cancel_iso_factor (pullback.snd η p) e
    (lineBaseChangeMap φ) he F q
    (projectiveLine_residueFieldExtension_bijective_of_killed R Ω ι n hn F hF q)

end AlgebraicGeometry.Scheme.EtaleCohomology.Proper
