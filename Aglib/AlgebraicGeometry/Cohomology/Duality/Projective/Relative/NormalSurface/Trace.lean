/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.NormalSurface
public import
  Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.ClosedEmbedding.UnitTrace
public import Aglib.AlgebraicGeometry.Modules.Linear

/-!
# The original chosen-embedding trace on canonical sections

The actual homology-normalized concentration isomorphism identifies literal
sections of the original canonical module with the original derived Hom
source of the chosen-embedding Serre map. The map from sections uses the
native structure-module Hom equivalence and the installed single/shift
comparison. Its inverse evaluates the original coefficient morphism at one.

Transporting the existing source-local trace retains its original counit,
structural unit, scalar restriction and native coinduced coefficient. No
invertibility of the canonical module or independent trace compatibility
is assumed. The original geometric triangle derives the scalar identity.
This is a chosen-embedding trace statement, before a GR vanishing argument.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.Scheme.Modules Opposite

universe u

attribute [local instance] AlgebraicGeometry.Scheme.Modules.standardHasDerivedCategory

/-- Transport original sections through a fully faithful additive functor
and the given target isomorphism. -/
def CategoryTheory.Functor.sectionsHomAddEquiv
    {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
    (F : C ⥤ D) [F.Additive] [F.Full] [F.Faithful]
    {O M : C} {N : D} {S : Type*} [AddCommGroup S]
    (G : (O ⟶ M) ≃+ S) (E : N ≅ F.obj M) : S ≃+ (F.obj O ⟶ N) where
  toFun s := F.map (G.symm s) ≫ E.inv
  invFun t := G (F.preimage (t ≫ E.hom))
  left_inv s := by
    change G (F.preimage ((F.map (G.symm s) ≫ E.inv) ≫ E.hom)) = s
    rw [Category.assoc, E.inv_hom_id, Category.comp_id, F.preimage_map,
      G.apply_symm_apply]
  right_inv t := by
    change F.map (G.symm (G (F.preimage (t ≫ E.hom)))) ≫ E.inv = t
    rw [G.symm_apply_apply, F.map_preimage, Category.assoc, E.hom_inv_id, Category.comp_id]
  map_add' s t := by
    rw [G.symm.map_add, F.map_add, Preadditive.add_comp]

/-- The same transport is linear for the original source and target scalar structures. -/
def CategoryTheory.Functor.sectionsHomLinearEquiv
    {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
    {A : Type*} [CommRing A] [CategoryTheory.Linear A C] [CategoryTheory.Linear A D]
    (F : C ⥤ D) [F.Additive] [F.Full] [F.Faithful] [F.Linear A]
    {O M : C} {N : D} {S : Type*} [AddCommGroup S] [Module A S]
    (G : (O ⟶ M) ≃ₗ[A] S) (E : N ≅ F.obj M) : S ≃ₗ[A] (F.obj O ⟶ N) :=
  { F.sectionsHomAddEquiv G.toAddEquiv E with
    map_smul' a s := by
      change F.map (G.symm (a • s)) ≫ E.inv = a • (F.map (G.symm s) ≫ E.inv)
      rw [G.symm.map_smul, F.map_smul, CategoryTheory.Linear.smul_comp] }

private theorem sectionsHom_normalization
    {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
    (F : C ⥤ D) [F.Additive] [F.Full] [F.Faithful]
    {O M : C} {N : D} {S : Type*} [AddCommGroup S]
    (G : (O ⟶ M) ≃+ S) (E : N ≅ F.obj M) (s : S) :
    F.sectionsHomAddEquiv G E s ≫ E.hom = F.map (G.symm s) := by
  change (F.map (G.symm s) ≫ E.inv) ≫ E.hom = _
  rw [Category.assoc, E.inv_hom_id, Category.comp_id]

private theorem scalar_precomp_map
    {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
    {A : Type*} [CommRing A] [Linear A C] [Linear A D]
    (F : C ⥤ D) [F.Linear A] (O : C) {N : D} (s : F.obj O ⟶ N) (a : A) :
    F.map (a • 𝟙 O) ≫ s = a • s := by
  rw [F.map_smul, F.map_id, Linear.smul_comp, Category.id_comp]

namespace AlgebraicGeometry.Scheme.Cohomology

/-- The standard derived-category model for modules over the coefficient ring. -/
local instance normalSurfaceTraceModuleDerived (B : Type u) [CommRing B] :
    HasDerivedCategory.{u + 1} (ModuleCat.{u} B) := HasDerivedCategory.standard _

variable (R : Type u) [CommRing R] [IsDomain R] [IsRegularLocalRing R]
    (ι : Type u) {X : Scheme.{u}} [IsIntegral X]
    (i : X ⟶ ProjectiveSpace R ι) [IsClosedImmersion i]
    [IsDominant (i ≫ toSpec R ι)]
    (hX : NormalStalks X) (hXdim : topologicalKrullDim X ≤ 2)
    (n : ℕ) (e : ι ≃ Fin (n + 1))
    (hfin : (genericImageBaseMap R ι i).Finite)

/-- The original concentration isomorphism followed by the actual native target shift.
The coefficient and the degree-n homology are exactly those of the original object. -/
def normalSurfaceCanonicalShiftIso :
    (DerivedCategory.Plus.ι.obj (normalSurfaceDualizingObject R ι i n))⟦(n : ℤ)⟧ ≅
      (DerivedCategory.singleFunctor X.Modules 0).obj
        (normalSurfaceCanonicalModule R ι i n) :=
  (shiftFunctor (DerivedCategory X.Modules) (n : ℤ)).mapIso
      (DerivedCategory.Plus.ι.mapIso (normalSurfaceCanonicalIso R ι i hX hXdim n e hfin)) ≪≫
    relativeClosedEmbeddingTraceTargetIso n (normalSurfaceCanonicalModule R ι i n)

/-- Literal canonical sections and the original derived Hom source are additively equivalent.
The forward map is the native section morphism, the native single, and the inverse
of the actual homology-normalized concentration and shift comparison. -/
def normalSurfaceCanonicalSectionsAddEquiv :
    Γ(normalSurfaceCanonicalModule R ι i n, ⊤) ≃+
      chosenEmbeddingUnitTraceSource R i (toSpec R ι) n := by
  let O : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let ω : X.Modules := normalSurfaceCanonicalModule R ι i n
  let F := DerivedCategory.singleFunctor X.Modules 0
  let E := normalSurfaceCanonicalShiftIso R ι i hX hXdim n e hfin
  let G : (@Quiver.Hom X.Modules _ O ω) ≃+ Γ(ω, ⊤) := unitHomGlobalSectionsAddEquiv X ω
  exact F.sectionsHomAddEquiv G E

/-- The forward map displays the original section, single, concentration and shift factors. -/
theorem normalSurfaceCanonicalSectionsAddEquiv_apply
    (s : Γ(normalSurfaceCanonicalModule R ι i n, ⊤)) :
    let O : X.Modules := SheafOfModules.unit X.ringCatSheaf
    let ω : X.Modules := normalSurfaceCanonicalModule R ι i n
    let G : (@Quiver.Hom X.Modules _ O ω) ≃+ Γ(ω, ⊤) := unitHomGlobalSectionsAddEquiv X ω
    normalSurfaceCanonicalSectionsAddEquiv R ι i hX hXdim n e hfin s =
      (DerivedCategory.singleFunctor X.Modules 0).map (G.symm s) ≫
        (normalSurfaceCanonicalShiftIso R ι i hX hXdim n e hfin).inv := rfl

/-- The inverse recovers the literal original section by evaluation of its coefficient
morphism at one, after the same canonical and shift normalization. -/
theorem normalSurfaceCanonicalSectionsAddEquiv_symm_apply
    (t : chosenEmbeddingUnitTraceSource R i (toSpec R ι) n) :
    let O : X.Modules := SheafOfModules.unit X.ringCatSheaf
    let ω : X.Modules := normalSurfaceCanonicalModule R ι i n
    (normalSurfaceCanonicalSectionsAddEquiv R ι i hX hXdim n e hfin).symm t =
      ((DerivedCategory.singleFunctor X.Modules 0).preimage (X := O) (Y := ω)
        (t ≫ (normalSurfaceCanonicalShiftIso R ι i hX hXdim n e hfin).hom)).val.app
          (op ⊤) (1 : Γ(X, ⊤)) := rfl

/-- Applying the actual canonical reconstruction to a lifted section gives its original
native single morphism. The reconstruction is normalized on original H^n. -/
theorem normalSurfaceCanonicalSectionsAddEquiv_normalization
    (s : Γ(normalSurfaceCanonicalModule R ι i n, ⊤)) :
    let O : X.Modules := SheafOfModules.unit X.ringCatSheaf
    let ω : X.Modules := normalSurfaceCanonicalModule R ι i n
    let G : (@Quiver.Hom X.Modules _ O ω) ≃+ Γ(ω, ⊤) := unitHomGlobalSectionsAddEquiv X ω
    normalSurfaceCanonicalSectionsAddEquiv R ι i hX hXdim n e hfin s ≫
        (DerivedCategory.Plus.ι.map
          (normalSurfaceCanonicalIso R ι i hX hXdim n e hfin).hom)⟦(n : ℤ)⟧' ≫
        (relativeClosedEmbeddingTraceTargetIso n (normalSurfaceCanonicalModule R ι i n)).hom =
      (DerivedCategory.singleFunctor X.Modules 0).map (G.symm s) := by
  let O : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let ω : X.Modules := normalSurfaceCanonicalModule R ι i n
  let G : (@Quiver.Hom X.Modules _ O ω) ≃+ Γ(ω, ⊤) := unitHomGlobalSectionsAddEquiv X ω
  let E := normalSurfaceCanonicalShiftIso R ι i hX hXdim n e hfin
  exact sectionsHom_normalization (DerivedCategory.singleFunctor X.Modules 0) G E s

variable {A : Type u} [CommRing A] (α : A →+* Γ(X, ⊤))

/-- The same section equivalence is linear for the original structural A-action on X. -/
def normalSurfaceCanonicalSectionsLinearEquiv :
    letI := moduleCategoryLinearOfHom X α
    letI : Module A Γ(normalSurfaceCanonicalModule R ι i n, ⊤) := Module.compHom _ α
    Γ(normalSurfaceCanonicalModule R ι i n, ⊤) ≃ₗ[A]
      chosenEmbeddingUnitTraceSource R i (toSpec R ι) n := by
  let := moduleCategoryLinearOfHom X α
  let : Module A Γ(normalSurfaceCanonicalModule R ι i n, ⊤) := Module.compHom _ α
  let O : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let ω : X.Modules := normalSurfaceCanonicalModule R ι i n
  let G : (@Quiver.Hom X.Modules _ O ω) ≃ₗ[A] Γ(ω, ⊤) :=
    unitHomGlobalSectionsLinearEquivOfHom X α ω
  let F := DerivedCategory.singleFunctor X.Modules 0
  let E := normalSurfaceCanonicalShiftIso R ι i hX hXdim n e hfin
  exact F.sectionsHomLinearEquiv G E

/-- Linearity changes no underlying section or derived morphism. -/
theorem normalSurfaceCanonicalSectionsLinearEquiv_apply
    (s : Γ(normalSurfaceCanonicalModule R ι i n, ⊤)) :
    normalSurfaceCanonicalSectionsLinearEquiv R ι i hX hXdim n e hfin α s =
      normalSurfaceCanonicalSectionsAddEquiv R ι i hX hXdim n e hfin s := rfl

include α in
/-- Actual section scalars become the same scalars on the original derived Hom source. -/
theorem normalSurfaceCanonicalSectionsAddEquiv_smul (a : A) :
    letI := moduleCategoryLinearOfHom X α
    letI : Module A Γ(normalSurfaceCanonicalModule R ι i n, ⊤) := Module.compHom _ α
    ∀ s : Γ(normalSurfaceCanonicalModule R ι i n, ⊤),
      normalSurfaceCanonicalSectionsAddEquiv R ι i hX hXdim n e hfin (a • s) =
        a • normalSurfaceCanonicalSectionsAddEquiv R ι i hX hXdim n e hfin s := by
  let := moduleCategoryLinearOfHom X α
  let : Module A Γ(normalSurfaceCanonicalModule R ι i n, ⊤) := Module.compHom _ α
  intro s
  simpa only [normalSurfaceCanonicalSectionsLinearEquiv_apply] using
    (normalSurfaceCanonicalSectionsLinearEquiv R ι i hX hXdim n e hfin α).map_smul a s

include α in
/-- The source scalar is the original multiplication endomorphism of the structure module. -/
theorem normalSurfaceCanonicalSectionsAddEquiv_source_scalar (a : A) :
    let O : X.Modules := SheafOfModules.unit X.ringCatSheaf
    letI := moduleCategoryLinearOfHom X α
    letI : Module A Γ(normalSurfaceCanonicalModule R ι i n, ⊤) := Module.compHom _ α
    ∀ s : Γ(normalSurfaceCanonicalModule R ι i n, ⊤),
      normalSurfaceCanonicalSectionsAddEquiv R ι i hX hXdim n e hfin (a • s) =
        (DerivedCategory.singleFunctor X.Modules 0).map
            (a • 𝟙 O) ≫
          normalSurfaceCanonicalSectionsAddEquiv R ι i hX hXdim n e hfin s := by
  let := moduleCategoryLinearOfHom X α
  let : Module A Γ(normalSurfaceCanonicalModule R ι i n, ⊤) := Module.compHom _ α
  let O : X.Modules := SheafOfModules.unit X.ringCatSheaf
  change ∀ s : Γ(normalSurfaceCanonicalModule R ι i n, ⊤),
    normalSurfaceCanonicalSectionsAddEquiv R ι i hX hXdim n e hfin (a • s) =
      (DerivedCategory.singleFunctor X.Modules 0).map (a • 𝟙 O) ≫
        normalSurfaceCanonicalSectionsAddEquiv R ι i hX hXdim n e hfin s
  intro s
  exact (normalSurfaceCanonicalSectionsAddEquiv_smul R ι i hX hXdim n e hfin α a s).trans
    (scalar_precomp_map (DerivedCategory.singleFunctor X.Modules 0) O
      (normalSurfaceCanonicalSectionsAddEquiv R ι i hX hXdim n e hfin s) a).symm

end AlgebraicGeometry.Scheme.Cohomology

namespace AlgebraicGeometry.Scheme.Cohomology

/-- The standard derived-category model for modules over the coefficient ring. -/
local instance normalSurfaceTraceTargetDerived (B : Type u) [CommRing B] :
    HasDerivedCategory.{u + 1} (ModuleCat.{u} B) := HasDerivedCategory.standard _

/-- The original structural A-action from the supplied map to Spec A. -/
abbrev normalSurfaceTraceScalar {A : Type u} [CommRing A] {X : Scheme.{u}}
    (g : X ⟶ Spec (.of A)) : A →+* Γ(X, ⊤) :=
  g.appTop.hom.comp (ΓSpecIso (.of A)).inv.hom

variable (R : Type u) [CommRing R] [IsDomain R] [IsRegularLocalRing R]
    (ι : Type u) {X : Scheme.{u}} [IsIntegral X]
    (i : X ⟶ ProjectiveSpace R ι) [IsClosedImmersion i]
    [IsDominant (i ≫ toSpec R ι)]
    (hX : NormalStalks X) (hXdim : topologicalKrullDim X ≤ 2)
    (n : ℕ) (e : ι ≃ Fin (n + 1))
    (hfin : (genericImageBaseMap R ι i).Finite)

/-- The original chosen-embedding base trace on literal canonical sections. -/
def normalSurfaceSectionsTraceBase :
    Γ(normalSurfaceCanonicalModule R ι i n, ⊤) →+ R :=
  (chosenEmbeddingTraceBase R ι i (toSpec R ι) (𝟙 (ProjectiveSpace R ι))
      (IsPullback.id_horiz (toSpec R ι)) n e).comp
    (normalSurfaceCanonicalSectionsAddEquiv R ι i hX hXdim n e hfin).toAddMonoidHom

/-- The base trace uses the exact section lift and unchanged source-local trace. -/
theorem normalSurfaceSectionsTraceBase_apply
    (s : Γ(normalSurfaceCanonicalModule R ι i n, ⊤)) :
    normalSurfaceSectionsTraceBase R ι i hX hXdim n e hfin s =
      chosenEmbeddingTraceBase R ι i (toSpec R ι) (𝟙 (ProjectiveSpace R ι))
        (IsPullback.id_horiz (toSpec R ι)) n e
        (normalSurfaceCanonicalSectionsAddEquiv R ι i hX hXdim n e hfin s) := rfl

variable {A : Type u} [CommRing A] (σ : R →+* A) (g : X ⟶ Spec (.of A))
    (hg : i ≫ toSpec R ι = g ≫ Spec.map (CommRingCat.ofHom σ))

omit [IsDomain R] [IsRegularLocalRing R] [IsIntegral X] [IsClosedImmersion i]
  [IsDominant (i ≫ toSpec R ι)] in
include hg in
/-- The original scheme triangle supplies the scalar identity required by the trace. -/
theorem normalSurfaceTraceScalar_compatibility :
    chosenEmbeddingBaseScalar R i (toSpec R ι) = (normalSurfaceTraceScalar g).comp σ :=
  chosenEmbeddingBaseScalar_eq_of_triangle R i (toSpec R ι) σ g hg

/-- The original canonical-section trace takes values in the actual native coinduced
coefficient and is A-linear for the original structural action. -/
def normalSurfaceSectionsTraceCoinduced :
    letI := moduleCategoryLinearOfHom X (normalSurfaceTraceScalar g)
    letI : Module A Γ(normalSurfaceCanonicalModule R ι i n, ⊤) :=
      Module.compHom _ (normalSurfaceTraceScalar g)
    Γ(normalSurfaceCanonicalModule R ι i n, ⊤) →ₗ[A]
      (ModuleCat.coextendScalars σ).obj (ModuleCat.of R R) := by
  let α := normalSurfaceTraceScalar g
  let := moduleCategoryLinearOfHom X α
  let : Module A Γ(normalSurfaceCanonicalModule R ι i n, ⊤) := Module.compHom _ α
  exact (chosenEmbeddingTraceCoinduced R ι i (toSpec R ι) (𝟙 (ProjectiveSpace R ι))
      (IsPullback.id_horiz (toSpec R ι)) n e σ α
      (normalSurfaceTraceScalar_compatibility R ι i σ g hg)).comp
    (normalSurfaceCanonicalSectionsLinearEquiv R ι i hX hXdim n e hfin α).toLinearMap

/-- The transported coinduced trace has the original source-local trace as its forward map. -/
theorem normalSurfaceSectionsTraceCoinduced_apply
    (s : Γ(normalSurfaceCanonicalModule R ι i n, ⊤)) :
    normalSurfaceSectionsTraceCoinduced R ι i hX hXdim n e hfin σ g hg s =
      chosenEmbeddingTraceCoinduced R ι i (toSpec R ι) (𝟙 (ProjectiveSpace R ι))
        (IsPullback.id_horiz (toSpec R ι)) n e σ (normalSurfaceTraceScalar g)
        (normalSurfaceTraceScalar_compatibility R ι i σ g hg)
        (normalSurfaceCanonicalSectionsAddEquiv R ι i hX hXdim n e hfin s) := by
  let α := normalSurfaceTraceScalar g
  let τ := chosenEmbeddingTraceCoinduced R ι i (toSpec R ι) (𝟙 (ProjectiveSpace R ι))
    (IsPullback.id_horiz (toSpec R ι)) n e σ α
    (normalSurfaceTraceScalar_compatibility R ι i σ g hg)
  change τ (normalSurfaceCanonicalSectionsLinearEquiv R ι i hX hXdim n e hfin α s) =
    τ (normalSurfaceCanonicalSectionsAddEquiv R ι i hX hXdim n e hfin s)
  exact congrArg τ (normalSurfaceCanonicalSectionsLinearEquiv_apply
    R ι i hX hXdim n e hfin α s)

/-- On actual canonical sections, the original coinduced trace evaluates the original
base trace at the original section scalar. -/
theorem normalSurfaceSectionsTraceCoinduced_evaluation (a : A) :
    letI := moduleCategoryLinearOfHom X (normalSurfaceTraceScalar g)
    letI : Module A Γ(normalSurfaceCanonicalModule R ι i n, ⊤) :=
      Module.compHom _ (normalSurfaceTraceScalar g)
    ∀ s : Γ(normalSurfaceCanonicalModule R ι i n, ⊤),
      ModuleCat.CoextendScalars.equiv σ (ModuleCat.of R R)
          (normalSurfaceSectionsTraceCoinduced R ι i hX hXdim n e hfin σ g hg s) a =
        normalSurfaceSectionsTraceBase R ι i hX hXdim n e hfin (a • s) := by
  let α := normalSurfaceTraceScalar g
  let := moduleCategoryLinearOfHom X α
  let : Module A Γ(normalSurfaceCanonicalModule R ι i n, ⊤) := Module.compHom _ α
  intro s
  rw [normalSurfaceSectionsTraceCoinduced_apply, chosenEmbeddingTraceCoinduced_apply,
    normalSurfaceSectionsTraceBase_apply,
    normalSurfaceCanonicalSectionsAddEquiv_smul R ι i hX hXdim n e hfin α]

/-- The A-action on the output is native coinduction, namely precomposition with multiplication. -/
theorem normalSurfaceSectionsTraceCoinduced_smul_apply (a b : A) :
    letI := moduleCategoryLinearOfHom X (normalSurfaceTraceScalar g)
    letI : Module A Γ(normalSurfaceCanonicalModule R ι i n, ⊤) :=
      Module.compHom _ (normalSurfaceTraceScalar g)
    ∀ s : Γ(normalSurfaceCanonicalModule R ι i n, ⊤),
      ModuleCat.CoextendScalars.equiv σ (ModuleCat.of R R)
          (normalSurfaceSectionsTraceCoinduced R ι i hX hXdim n e hfin σ g hg (a • s)) b =
        ModuleCat.CoextendScalars.equiv σ (ModuleCat.of R R)
          (normalSurfaceSectionsTraceCoinduced R ι i hX hXdim n e hfin σ g hg s) (b * a) := by
  let α := normalSurfaceTraceScalar g
  let := moduleCategoryLinearOfHom X α
  let : Module A Γ(normalSurfaceCanonicalModule R ι i n, ⊤) := Module.compHom _ α
  intro s
  let τ := normalSurfaceSectionsTraceCoinduced R ι i hX hXdim n e hfin σ g hg
  have hτ := τ.map_smul a s
  exact congrArg (fun z : (ModuleCat.coextendScalars σ).obj (ModuleCat.of R R) =>
    ModuleCat.CoextendScalars.equiv σ (ModuleCat.of R R) z
      (show (ModuleCat.restrictScalars σ).obj (ModuleCat.of A A) from b)) hτ

include hg in
/-- The same base trace is R-linear for the original action restricted through sigma. -/
theorem normalSurfaceSectionsTraceBase_restricted_smul (r : R) :
    letI := moduleCategoryLinearOfHom X (normalSurfaceTraceScalar g)
    letI : Module A Γ(normalSurfaceCanonicalModule R ι i n, ⊤) :=
      Module.compHom _ (normalSurfaceTraceScalar g)
    ∀ s : Γ(normalSurfaceCanonicalModule R ι i n, ⊤),
      normalSurfaceSectionsTraceBase R ι i hX hXdim n e hfin (σ r • s) =
        r • normalSurfaceSectionsTraceBase R ι i hX hXdim n e hfin s := by
  let α := normalSurfaceTraceScalar g
  let := moduleCategoryLinearOfHom X α
  let : Module A Γ(normalSurfaceCanonicalModule R ι i n, ⊤) := Module.compHom _ α
  intro s
  rw [normalSurfaceSectionsTraceBase_apply,
    normalSurfaceCanonicalSectionsAddEquiv_smul R ι i hX hXdim n e hfin α,
    normalSurfaceSectionsTraceBase_apply]
  exact chosenEmbeddingTraceBase_restricted_smul R ι i (toSpec R ι)
    (𝟙 (ProjectiveSpace R ι)) (IsPullback.id_horiz (toSpec R ι)) n e σ α
    (normalSurfaceTraceScalar_compatibility R ι i σ g hg) r
    (normalSurfaceCanonicalSectionsAddEquiv R ι i hX hXdim n e hfin s)

/-- Phi0 on literal canonical sections is the same source-local map after the exact section lift. -/
def normalSurfaceSectionsPhi0 :
    Γ(normalSurfaceCanonicalModule R ι i n, ⊤) →+
      ((ModuleCat.restrictScalars σ).mapDerivedCategory.obj
          (DerivedCategory.Plus.ι.obj (moduleDerivedStructure X (normalSurfaceTraceScalar g))) ⟶
        (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R)) :=
  (chosenEmbeddingModulePhi0 R ι i (toSpec R ι) (𝟙 (ProjectiveSpace R ι))
      (IsPullback.id_horiz (toSpec R ι)) n e σ (normalSurfaceTraceScalar g)
      (normalSurfaceTraceScalar_compatibility R ι i σ g hg)).comp
    (normalSurfaceCanonicalSectionsAddEquiv R ι i hX hXdim n e hfin).toAddMonoidHom

/-- The original section trace is the dual of the original eta_A under the same Phi0,
with the native exact-single comparison retained explicitly. -/
theorem normalSurfaceSectionsTraceCoinduced_eq_original_unit (a : A)
    (s : Γ(normalSurfaceCanonicalModule R ι i n, ⊤)) :
    ModuleCat.CoextendScalars.equiv σ (ModuleCat.of R R)
        (normalSurfaceSectionsTraceCoinduced R ι i hX hXdim n e hfin σ g hg s) a =
      ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).preimage
        (((ModuleCat.restrictScalars σ).mapDerivedCategorySingleFunctor 0).inv.app
            (ModuleCat.of A A) ≫
          (ModuleCat.restrictScalars σ).mapDerivedCategory.map
            (DerivedCategory.Plus.ι.map
              (moduleDerivedStructureUnit X (normalSurfaceTraceScalar g))) ≫
          normalSurfaceSectionsPhi0 R ι i hX hXdim n e hfin σ g hg s)) a := by
  rw [normalSurfaceSectionsTraceCoinduced_apply]
  exact chosenEmbeddingTraceCoinduced_eq_original_unit R ι i (toSpec R ι)
    (𝟙 (ProjectiveSpace R ι)) (IsPullback.id_horiz (toSpec R ι)) n e σ
    (normalSurfaceTraceScalar g) (normalSurfaceTraceScalar_compatibility R ι i σ g hg) a
    (normalSurfaceCanonicalSectionsAddEquiv R ι i hX hXdim n e hfin s)

end AlgebraicGeometry.Scheme.Cohomology
