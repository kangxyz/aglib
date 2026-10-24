/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.RegularLocalRing.FiniteComplexModel
public import Aglib.Algebra.Homology.ModuleCat.HomComplex.Perfect
public import Aglib.Algebra.Homology.DerivedCategory.KProjective.Representative
public import Aglib.Algebra.Homology.DerivedCategory.Plus.Postnikov.Unit
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.RingTheory.Finiteness.Prod

/-!
# Finite-projective models of the original two-layer triangle

The original connecting morphism is represented from a finite-projective
resolution of H1. Its shifted native cone supplies a model of the actual
middle object, including all triangle faces and their rotation signs.
Exact scalar restriction then discharges the model premise of the original
A-derived evaluation. No splitting or assumed perfect model is used.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated HomologicalComplex

universe u v w

namespace CochainComplex

variable {R : Type u} [CommRing R]

private theorem finite_projective_single_terms
    (M : ModuleCat.{max u v} R) [Module.Finite R M] [Module.Projective R M]
    (s i : ℤ) :
    Module.Finite R (((singleFunctor (ModuleCat.{max u v} R) s).obj M).X i) ∧
      Module.Projective R (((singleFunctor (ModuleCat.{max u v} R) s).obj M).X i) := by
  by_cases hi : i = s
  · subst i
    let e := singleObjXSelf (.up ℤ) s M
    exact ⟨Module.Finite.equiv e.symm.toLinearEquiv,
      Module.Projective.of_equiv' e.symm.toLinearEquiv⟩
  · let := ModuleCat.subsingleton_of_isZero (isZero_single_obj_X (.up ℤ) s M i hi)
    exact ⟨inferInstance, inferInstance⟩

end CochainComplex

namespace CochainComplex

variable {R : Type u} [CommRing R]
  [HasDerivedCategory.{w} (ModuleCat.{max u v} R)]

/-- The endpoint comparison for the actual shifted H0 single. -/
def postnikovFirstShiftIso (U : ModuleCat.{max u v} R)
    (T : Triangle (DerivedCategory (ModuleCat.{max u v} R)))
    (e₀ : DerivedCategory.Q.obj
      ((singleFunctor (ModuleCat.{max u v} R) 0).obj U) ≅ T.obj₁) :
    DerivedCategory.Q.obj (((singleFunctor (ModuleCat.{max u v} R) 0).obj U)⟦(1 : ℤ)⟧) ≅
      T.obj₁⟦(1 : ℤ)⟧ :=
  (DerivedCategory.Q.commShiftIso (1 : ℤ)).app _ ≪≫
    (CategoryTheory.shiftFunctor (DerivedCategory (ModuleCat.{max u v} R)) (1 : ℤ)).mapIso e₀

/-- Actual resolution and cone data, produced below from the original
distinguished triangle. The connecting arrow and both endpoint faces are retained. -/
structure TwoLayerConeModel (d : ℕ) (U H : ModuleCat.{max u v} R)
    (T : Triangle (DerivedCategory (ModuleCat.{max u v} R)))
    (e₀ : DerivedCategory.Q.obj
      ((singleFunctor (ModuleCat.{max u v} R) 0).obj U) ≅ T.obj₁)
    (e₁ : DerivedCategory.Q.obj
      ((singleFunctor (ModuleCat.{max u v} R) 1).obj H) ≅ T.obj₃) where
  /-- The finite-projective source complex resolving the degree-one single of `H`. -/
  source : CochainComplex (ModuleCat.{max u v} R) ℤ
  source_ge : source.IsStrictlyGE (1 - (d : ℤ))
  source_le : source.IsStrictlyLE 1
  source_finite : ∀ i, Module.Finite R (source.X i)
  source_projective : ∀ i, Module.Projective R (source.X i)
  /-- The quasi-isomorphism to the original degree-one single of `H`. -/
  π : source ⟶ (singleFunctor (ModuleCat.{max u v} R) 1).obj H
  quasiIso_π : QuasiIso π
  /-- The chain map representing the original Postnikov connecting morphism. -/
  connecting : source ⟶ ((singleFunctor (ModuleCat.{max u v} R) 0).obj U)⟦(1 : ℤ)⟧
  connecting_Q : DerivedCategory.Q.map connecting =
    DerivedCategory.Q.map π ≫ e₁.hom ≫ T.mor₃ ≫ (postnikovFirstShiftIso U T e₀).inv
  /-- The comparison of the localized cone triangle with the twice-rotated original triangle. -/
  triangleIso : DerivedCategory.Q.mapTriangle.obj (mappingCone.triangle connecting) ≅
    T.rotate.rotate
  triangleIso_first : triangleIso.hom.hom₁ = DerivedCategory.Q.map π ≫ e₁.hom
  triangleIso_second : triangleIso.hom.hom₂ = (postnikovFirstShiftIso U T e₀).hom

section Regular

variable [IsRegularLocalRing R]

/-- Construct the cone from the actual Postnikov connecting morphism. No
splitting, vanishing of that morphism or pre-existing perfect model is assumed. -/
theorem nonempty_twoLayerConeModel (d : ℕ) (hd : ringKrullDim R = (d : ℕ))
    (U H : ModuleCat.{max u v} R) [Module.Finite R H]
    (T : Triangle (DerivedCategory (ModuleCat.{max u v} R))) (hT : T ∈ distTriang _)
    (e₀ : DerivedCategory.Q.obj
      ((singleFunctor (ModuleCat.{max u v} R) 0).obj U) ≅ T.obj₁)
    (e₁ : DerivedCategory.Q.obj
      ((singleFunctor (ModuleCat.{max u v} R) 1).obj H) ≅ T.obj₃) :
    Nonempty (TwoLayerConeModel d U H T e₀ e₁) := by
  obtain ⟨P, hge, hle, hf, hp, π, hπ⟩ :=
    IsRegularLocalRing.exists_finiteProjective_single_model d hd H 1
  let : P.IsStrictlyLE 1 := hle
  let (i : ℤ) : Module.Projective R (P.X i) := hp i
  let : P.IsKProjective := isKProjective_of_projective P 1
  let : QuasiIso π := hπ
  let U₁ : CochainComplex (ModuleCat.{max u v} R) ℤ :=
    ((singleFunctor (ModuleCat.{max u v} R) 0).obj U)⟦(1 : ℤ)⟧
  let eH : DerivedCategory.Q.obj P ≅ T.obj₃ := asIso (DerivedCategory.Q.map π) ≪≫ e₁
  let eU : DerivedCategory.Q.obj U₁ ≅ T.obj₁⟦(1 : ℤ)⟧ := postnikovFirstShiftIso U T e₀
  obtain ⟨δ, hδQ⟩ := (IsKProjective.Q_map_surjective P U₁)
    (DerivedCategory.Q.map π ≫ e₁.hom ≫ T.mor₃ ≫ eU.inv)
  have hcomm : DerivedCategory.Q.map δ ≫ eU.hom = eH.hom ≫ T.mor₃ := by
    rw [hδQ]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, eH, Iso.trans_hom,
      asIso_hom]
  let S : Triangle (DerivedCategory (ModuleCat.{max u v} R)) :=
    DerivedCategory.Q.mapTriangle.obj (mappingCone.triangle δ)
  let E : S ≅ T.rotate.rotate := isoTriangleOfIso₁₂ S T.rotate.rotate
    (DerivedCategory.mappingCone_triangle_distinguished δ)
    (rot_of_distTriang _ (rot_of_distTriang _ hT)) eH eU hcomm
  refine ⟨
    { source := P
      source_ge := hge
      source_le := hle
      source_finite := hf
      source_projective := hp
      π := π
      quasiIso_π := hπ
      connecting := δ
      connecting_Q := hδQ
      triangleIso := E
      triangleIso_first := ?_
      triangleIso_second := ?_ }⟩
  · change E.hom.hom₁ = eH.hom
    exact isoTriangleOfIso₁₂_hom_hom₁ S T.rotate.rotate
      (DerivedCategory.mappingCone_triangle_distinguished δ)
      (rot_of_distTriang _ (rot_of_distTriang _ hT)) eH eU hcomm
  · change E.hom.hom₂ = eU.hom
    exact isoTriangleOfIso₁₂_hom_hom₂ S T.rotate.rotate
      (DerivedCategory.mappingCone_triangle_distinguished δ)
      (rot_of_distTriang _ (rot_of_distTriang _ hT)) eH eU hcomm

end Regular

namespace TwoLayerConeModel

variable {d : ℕ} {U H : ModuleCat.{max u v} R}
  {T : Triangle (DerivedCategory (ModuleCat.{max u v} R))}
  {e₀ : DerivedCategory.Q.obj
    ((singleFunctor (ModuleCat.{max u v} R) 0).obj U) ≅ T.obj₁}
  {e₁ : DerivedCategory.Q.obj
    ((singleFunctor (ModuleCat.{max u v} R) 1).obj H) ≅ T.obj₃}
  (M : TwoLayerConeModel d U H T e₀ e₁)

/-- The shifted cone of the represented original connecting map. -/
def complex : CochainComplex (ModuleCat.{max u v} R) ℤ :=
  (mappingCone M.connecting)⟦-1⟧

/-- The native cone triangle comparison identifies this model with the actual middle object. -/
def derivedIso : DerivedCategory.Q.obj M.complex ≅ T.obj₂ :=
  (DerivedCategory.Q.commShiftIso (-1)).app (mappingCone M.connecting) ≪≫
    (CategoryTheory.shiftFunctor (DerivedCategory (ModuleCat.{max u v} R)) (-1)).mapIso
      (Triangle.π₃.mapIso M.triangleIso) ≪≫
    (shiftFunctorCompIsoId (DerivedCategory (ModuleCat.{max u v} R))
      (1 : ℤ) (-1) (by omega)).app T.obj₂

/-- The second face of the rotated comparison retains the original unit,
with exactly the minus sign supplied by two native rotations. -/
theorem original_unit_face :
    DerivedCategory.Q.map (mappingCone.inr M.connecting) ≫ M.triangleIso.hom.hom₃ =
      (postnikovFirstShiftIso U T e₀).hom ≫ (-(T.mor₁⟦(1 : ℤ)⟧')) := by
  have h := M.triangleIso.hom.comm₂
  change DerivedCategory.Q.map (mappingCone.inr M.connecting) ≫
      M.triangleIso.hom.hom₃ = M.triangleIso.hom.hom₂ ≫ (-(T.mor₁⟦(1 : ℤ)⟧')) at h
  rw [M.triangleIso_second] at h
  exact h

/-- The final triangle face retains the original H1 map and native rotation sign. -/
theorem original_homology_face :
    (DerivedCategory.Q.mapTriangle.obj (mappingCone.triangle M.connecting)).mor₃ ≫
      (DerivedCategory.Q.map M.π ≫ e₁.hom)⟦(1 : ℤ)⟧' =
        M.triangleIso.hom.hom₃ ≫ (-(T.mor₂⟦(1 : ℤ)⟧')) := by
  have h := M.triangleIso.hom.comm₃
  change (DerivedCategory.Q.mapTriangle.obj (mappingCone.triangle M.connecting)).mor₃ ≫
      M.triangleIso.hom.hom₁⟦(1 : ℤ)⟧' =
        M.triangleIso.hom.hom₃ ≫ (-(T.mor₂⟦(1 : ℤ)⟧')) at h
  rw [M.triangleIso_first] at h
  exact h

/-- The lower support bound includes both the resolved H1 term and the H0 term. -/
theorem isStrictlyGE : M.complex.IsStrictlyGE (min (1 - (d : ℤ)) 0) := by
  let : M.source.IsStrictlyGE (1 - (d : ℤ)) := M.source_ge
  let U₀ := (singleFunctor (ModuleCat.{max u v} R) 0).obj U
  let : (U₀⟦(1 : ℤ)⟧).IsStrictlyGE (-1) :=
    CochainComplex.isStrictlyGE_shift U₀ 0 1 (-1) (by omega)
  have hc : (mappingCone M.connecting).IsStrictlyGE (min (-(d : ℤ)) (-1)) := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro i hi
    rw [mappingCone.isZero_X_iff]
    exact ⟨M.source.isZero_of_isStrictlyGE (1 - (d : ℤ)) (i + 1) (by omega),
      (U₀⟦(1 : ℤ)⟧).isZero_of_isStrictlyGE (-1) i (by omega)⟩
  let : (mappingCone M.connecting).IsStrictlyGE (min (-(d : ℤ)) (-1)) := hc
  exact CochainComplex.isStrictlyGE_shift (mappingCone M.connecting)
    (min (-(d : ℤ)) (-1)) (-1) (min (1 - (d : ℤ)) 0) (by omega)

/-- The original two-layer model has no terms above degree one. -/
theorem isStrictlyLE : M.complex.IsStrictlyLE 1 := by
  let : M.source.IsStrictlyLE 1 := M.source_le
  let U₀ := (singleFunctor (ModuleCat.{max u v} R) 0).obj U
  let : (U₀⟦(1 : ℤ)⟧).IsStrictlyLE (-1) :=
    CochainComplex.isStrictlyLE_shift U₀ 0 1 (-1) (by omega)
  have hc : (mappingCone M.connecting).IsStrictlyLE 0 := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    rw [mappingCone.isZero_X_iff]
    exact ⟨M.source.isZero_of_isStrictlyLE 1 (i + 1) (by omega),
      (U₀⟦(1 : ℤ)⟧).isZero_of_isStrictlyLE (-1) i (by omega)⟩
  let : (mappingCone M.connecting).IsStrictlyLE 0 := hc
  exact CochainComplex.isStrictlyLE_shift (mappingCone M.connecting) 0 (-1) 1 (by omega)

/-- The native cone biproduct transports finiteness and projectivity termwise. -/
theorem finite_projective_terms [Module.Finite R U] [Module.Projective R U] (i : ℤ) :
    Module.Finite R (M.complex.X i) ∧ Module.Projective R (M.complex.X i) := by
  let (n : ℤ) : Module.Finite R (M.source.X n) := M.source_finite n
  let (n : ℤ) : Module.Projective R (M.source.X n) := M.source_projective n
  let U₀ := (singleFunctor (ModuleCat.{max u v} R) 0).obj U
  let (n : ℤ) : Module.Finite R (U₀.X n) := (finite_projective_single_terms U 0 n).1
  let (n : ℤ) : Module.Projective R (U₀.X n) := (finite_projective_single_terms U 0 n).2
  let (n : ℤ) : Module.Finite R ((U₀⟦(1 : ℤ)⟧).X n) :=
    Module.Finite.equiv (U₀.shiftFunctorObjXIso 1 n (n + 1) rfl).symm.toLinearEquiv
  let (n : ℤ) : Module.Projective R ((U₀⟦(1 : ℤ)⟧).X n) :=
    Module.Projective.of_equiv'
      (U₀.shiftFunctorObjXIso 1 n (n + 1) rfl).symm.toLinearEquiv
  let e : M.complex.X i ≅ ModuleCat.of R
      (M.source.X ((i + (-1)) + 1) × (U₀⟦(1 : ℤ)⟧).X (i + (-1))) :=
    (mappingCone M.connecting).shiftFunctorObjXIso (-1) i (i + (-1)) rfl ≪≫
      homotopyCofiber.XIsoBiprod M.connecting (i + (-1)) ((i + (-1)) + 1) rfl ≪≫
      ModuleCat.biprodIsoProd _ _
  exact ⟨Module.Finite.equiv e.symm.toLinearEquiv,
    Module.Projective.of_equiv' e.symm.toLinearEquiv⟩

/-- A native chain representative retains the very derived cone comparison
constructed from the original Postnikov connecting map. -/
theorem exists_quasiIso_to_representative [Module.Finite R U] [Module.Projective R U]
    (K : CochainComplex (ModuleCat.{max u v} R) ℤ)
    (eK : DerivedCategory.Q.obj K ≅ T.obj₂) :
    ∃ q : M.complex ⟶ K, QuasiIso q ∧
      DerivedCategory.Q.map q = M.derivedIso.hom ≫ eK.inv := by
  let : M.complex.IsStrictlyLE 1 := M.isStrictlyLE
  let (i : ℤ) : Module.Projective R (M.complex.X i) := (M.finite_projective_terms i).2
  let : M.complex.IsKProjective := isKProjective_of_projective M.complex 1
  exact IsKProjective.exists_quasiIso_of_derivedIso M.complex K (M.derivedIso ≪≫ eK.symm)

end TwoLayerConeModel

end CochainComplex

universe a c dA dR

namespace CochainComplex.HomComplex

variable {R : Type u} {A : Type a} [CommRing R] [CommRing A] [IsRegularLocalRing R]
  [HasDerivedCategory.{dA} (ModuleCat.{max u a c} A)]

/-- Finite restricted modules in every native single degree obtain their
actual evaluation theorem from the constructed finite resolution. -/
theorem derivedEvaluation_single_isIso_of_restrictFinite
    (σ : R →+* A) (d : ℕ) (hd : ringKrullDim R = (d : ℕ))
    (M : ModuleCat.{max u a c} A)
    [Module.Finite R ((ModuleCat.restrictScalars σ).obj M)] (n : ℤ)
    (W : ModuleCat.{max u a c} R) (eW : W ≃ₗ[R] R)
    (I : CochainComplex (ModuleCat.{max u a c} R) ℤ) [I.IsKInjective]
    [CochainComplex.IsKInjective
      (show CochainComplex (ModuleCat.{max u a c} A) ℤ from
        ((ModuleCat.coextendScalars σ).mapHomologicalComplex (.up ℤ)).obj I)]
    (u : ((singleFunctor (ModuleCat.{max u a c} R) 0).obj W) ⟶ I) [QuasiIso u] :
    IsIso ((derivedEvaluation
      (((ModuleCat.coextendScalars σ).mapHomologicalComplex (.up ℤ)).obj I)).app
        ((DerivedCategory.singleFunctor (ModuleCat.{max u a c} A) n).obj M)) := by
  let F : ModuleCat.{max u a c} A ⥤ ModuleCat.{max u a c} R :=
    ModuleCat.restrictScalars σ
  let K := (singleFunctor (ModuleCat.{max u a c} A) n).obj M
  obtain ⟨P, hge, hle, hf, hp, q₀, hq₀⟩ :=
    IsRegularLocalRing.exists_finiteProjective_single_model.{u, max a c}
      d hd (F.obj M) n
  let : P.IsStrictlyGE (n - d) := hge
  let : P.IsStrictlyLE n := hle
  let (i : ℤ) : Module.Finite R (P.X i) := hf i
  let (i : ℤ) : Module.Projective R (P.X i) := hp i
  let : QuasiIso q₀ := hq₀
  let q : P ⟶ (F.mapHomologicalComplex (.up ℤ)).obj K :=
    q₀ ≫ (F.mapCochainComplexSingleFunctor n).inv.app M
  let : QuasiIso q := inferInstance
  let eK : DerivedCategory.Q.obj K ≅
      (DerivedCategory.singleFunctor (ModuleCat.{max u a c} A) n).obj M :=
    ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{max u a c} A) n).app M).symm
  exact derivedEvaluation_isIso_of_model.{u, a, c, dA}
    σ K P W eW I u (n - d) n q _ eK

/-- The actual restricted Postnikov triangle constructs the model consumed
by the original A-derived evaluation theorem; no perfect-model premise occurs. -/
theorem derivedEvaluation_isIso_of_twoLayer
    [HasDerivedCategory.{dR} (ModuleCat.{max u a c} R)]
    (σ : R →+* A) (d : ℕ) (hd : ringKrullDim R = (d : ℕ))
    (U H : ModuleCat.{max u a c} A)
    [Module.Finite R ((ModuleCat.restrictScalars σ).obj U)]
    [Module.Projective R ((ModuleCat.restrictScalars σ).obj U)]
    [Module.Finite R ((ModuleCat.restrictScalars σ).obj H)]
    (K : CochainComplex (ModuleCat.{max u a c} A) ℤ)
    (T : Triangle (DerivedCategory (ModuleCat.{max u a c} A)))
    (hT : T ∈ distTriang _)
    (e₀ : (DerivedCategory.singleFunctor (ModuleCat.{max u a c} A) 0).obj U ≅ T.obj₁)
    (e₁ : (DerivedCategory.singleFunctor (ModuleCat.{max u a c} A) 1).obj H ≅ T.obj₃)
    (eK : DerivedCategory.Q.obj K ≅ T.obj₂)
    (W : ModuleCat.{max u a c} R) (eW : W ≃ₗ[R] R)
    (I : CochainComplex (ModuleCat.{max u a c} R) ℤ) [I.IsKInjective]
    [CochainComplex.IsKInjective
      (show CochainComplex (ModuleCat.{max u a c} A) ℤ from
        ((ModuleCat.coextendScalars σ).mapHomologicalComplex (.up ℤ)).obj I)]
    (u : ((singleFunctor (ModuleCat.{max u a c} R) 0).obj W) ⟶ I) [QuasiIso u] :
    IsIso ((derivedEvaluation
      (((ModuleCat.coextendScalars σ).mapHomologicalComplex (.up ℤ)).obj I)).app T.obj₂) := by
  let F : ModuleCat.{max u a c} A ⥤ ModuleCat.{max u a c} R :=
    ModuleCat.restrictScalars σ
  let Fd : DerivedCategory (ModuleCat.{max u a c} A) ⥤
      DerivedCategory (ModuleCat.{max u a c} R) := F.mapDerivedCategory
  let TR : Triangle (DerivedCategory (ModuleCat.{max u a c} R)) := Fd.mapTriangle.obj T
  have hTR : TR ∈ distTriang _ := Fd.map_distinguished T hT
  let e₀R : DerivedCategory.Q.obj
      ((singleFunctor (ModuleCat.{max u a c} R) 0).obj (F.obj U)) ≅ TR.obj₁ :=
    ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{max u a c} R) 0).app (F.obj U)).symm ≪≫
      ((F.mapDerivedCategorySingleFunctor 0).app U).symm ≪≫ Fd.mapIso e₀
  let e₁R : DerivedCategory.Q.obj
      ((singleFunctor (ModuleCat.{max u a c} R) 1).obj (F.obj H)) ≅ TR.obj₃ :=
    ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{max u a c} R) 1).app (F.obj H)).symm ≪≫
      ((F.mapDerivedCategorySingleFunctor 1).app H).symm ≪≫ Fd.mapIso e₁
  let L : CochainComplex (ModuleCat.{max u a c} R) ℤ :=
    (F.mapHomologicalComplex (.up ℤ)).obj K
  let eKR : DerivedCategory.Q.obj L ≅ TR.obj₂ :=
    (F.mapDerivedCategoryFactors.app K).symm ≪≫ Fd.mapIso eK
  obtain ⟨M⟩ := CochainComplex.nonempty_twoLayerConeModel.{u, max a c, dR}
    d hd (F.obj U) (F.obj H) TR hTR e₀R e₁R
  let : M.complex.IsStrictlyGE (min (1 - (d : ℤ)) 0) := M.isStrictlyGE
  let : M.complex.IsStrictlyLE 1 := M.isStrictlyLE
  let (i : ℤ) : Module.Finite R (M.complex.X i) := (M.finite_projective_terms i).1
  let (i : ℤ) : Module.Projective R (M.complex.X i) := (M.finite_projective_terms i).2
  obtain ⟨q, hq, _⟩ := M.exists_quasiIso_to_representative L eKR
  let : QuasiIso q := hq
  exact derivedEvaluation_isIso_of_model.{u, a, c, dA}
    σ K M.complex W eW I u (min (1 - (d : ℤ)) 0) 1 q T.obj₂ eK

/-- Apply the constructed model to the native triangle of the specified unit
and original H1. The geometric unit, bounds and finite H1 remain actual inputs. -/
theorem derivedEvaluation_isIso_of_unitPostnikov
    [HasDerivedCategory.{dR} (ModuleCat.{max u a c} R)]
    (σ : R →+* A) (d : ℕ) (hd : ringKrullDim R = (d : ℕ))
    (U : ModuleCat.{max u a c} A)
    [Module.Finite R ((ModuleCat.restrictScalars σ).obj U)]
    [Module.Projective R ((ModuleCat.restrictScalars σ).obj U)]
    (X : DerivedCategory.Plus (ModuleCat.{max u a c} A)) [X.IsGE 0] [X.IsLE 1]
    [Module.Finite R ((ModuleCat.restrictScalars σ).obj
      ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{max u a c} A) 1).obj X))]
    (η : (DerivedCategory.Plus.singleFunctor (ModuleCat.{max u a c} A) 0).obj U ⟶ X)
    [IsIso ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{max u a c} A) 0).map η)]
    (K : CochainComplex (ModuleCat.{max u a c} A) ℤ)
    (eK : DerivedCategory.Q.obj K ≅ DerivedCategory.Plus.ι.obj X)
    (W : ModuleCat.{max u a c} R) (eW : W ≃ₗ[R] R)
    (I : CochainComplex (ModuleCat.{max u a c} R) ℤ) [I.IsKInjective]
    [CochainComplex.IsKInjective
      (show CochainComplex (ModuleCat.{max u a c} A) ℤ from
        ((ModuleCat.coextendScalars σ).mapHomologicalComplex (.up ℤ)).obj I)]
    (u : ((singleFunctor (ModuleCat.{max u a c} R) 0).obj W) ⟶ I) [QuasiIso u] :
    IsIso ((derivedEvaluation
      (((ModuleCat.coextendScalars σ).mapHomologicalComplex (.up ℤ)).obj I)).app
        (DerivedCategory.Plus.ι.obj X)) := by
  let H := (DerivedCategory.Plus.homologyFunctor (ModuleCat.{max u a c} A) 1).obj X
  let E : DerivedCategory.Plus (ModuleCat.{max u a c} A) ⥤
      DerivedCategory (ModuleCat.{max u a c} A) := DerivedCategory.Plus.ι
  let T := E.mapTriangle.obj (DerivedCategory.Plus.unitPostnikovTriangle η)
  have hT : T ∈ distTriang _ := E.map_distinguished _
    (DerivedCategory.Plus.unitPostnikovTriangle_distinguished η)
  exact derivedEvaluation_isIso_of_twoLayer.{u, a, c, dA, dR} σ d hd U H K T hT
    ((DerivedCategory.Plus.singleFunctorιIso (ModuleCat.{max u a c} A) 0).app U).symm
    ((DerivedCategory.Plus.singleFunctorιIso (ModuleCat.{max u a c} A) 1).app H).symm
    eK W eW I u

end CochainComplex.HomComplex
