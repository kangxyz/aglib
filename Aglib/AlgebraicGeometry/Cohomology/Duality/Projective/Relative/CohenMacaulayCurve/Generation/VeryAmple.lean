/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Generators.GlobalSections
public import Aglib.AlgebraicGeometry.Modules.Coherent.Support.FinitePushforward
public import Aglib.AlgebraicGeometry.Cohomology.Modules.DegreeZero
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Modules.Qcqs
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Modules.Map.Naturality
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.AffineTrace
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.CohenMacaulayCurve.Coefficients.Serre
public import Aglib.AlgebraicGeometry.ProjectiveSpace.BaseChange.Cartesian
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Aglib.AlgebraicGeometry.ProjectiveSpace.BaseChange.Twisting
public import Aglib.AlgebraicGeometry.Modules.Pullback.Tensor.Pairing
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.Pullback

/-!
# Original evaluation maps for very-ample canonical generation

The evaluation used in descent is the original all-sections evaluation, not
an independently chosen presentation. Its map on global sections is always
surjective, even when the sheaf is not globally generated. This is the input
to flat H0 base change; generation of the pulled-back target then forces
surjectivity of the pulled-back original evaluation.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
/-- The original all-sections evaluation is surjective on global sections.
No coherence, finiteness or global-generation hypothesis is required. -/
theorem globalSectionsEval_sections_surjective {X : Scheme.{u}} (M : X.Modules) :
    Function.Surjective ((globalSectionsEval M).val.app (op ⊤)) := by
  intro x
  let s : 𝟙_ X.Modules ⟶ M := (unitHomGlobalSectionsEquiv X M).symm x
  let g := Sigma.ι (fun _ : (𝟙_ X.Modules ⟶ M) => 𝟙_ X.Modules) s
  refine ⟨unitHomGlobalSectionsEquiv X _ g, ?_⟩
  change unitHomGlobalSectionsEquiv X M (g ≫ globalSectionsEval M) = x
  rw [show g ≫ globalSectionsEval M = s from ι_globalSectionsEval M s]
  exact (unitHomGlobalSectionsEquiv X M).apply_symm_apply x

/-- Global generation transports along the specified original sheaf
isomorphism, retaining the all-sections evaluations on both sides. -/
theorem epi_globalSectionsEval_of_iso {X : Scheme.{u}} {M N : X.Modules}
    (e : M ≅ N) [Epi (globalSectionsEval M)] : Epi (globalSectionsEval N) := by
  let f := Sigma.desc fun s : 𝟙_ X.Modules ⟶ M =>
    Sigma.ι (fun _ : (𝟙_ X.Modules ⟶ N) => 𝟙_ X.Modules) (s ≫ e.hom)
  apply epi_of_epi_fac (f := f) (h := globalSectionsEval M ≫ e.hom)
  apply Sigma.hom_ext
  intro s
  simp only [f, Sigma.ι_comp_desc_assoc, ι_globalSectionsEval,
    ι_globalSectionsEval_assoc]

/-- Actual faithfully flat geometric pullback detects epimorphisms of
arbitrary module sheaves. No finiteness assumption on the evaluation source
or its cokernel is needed. -/
theorem epi_of_surjective_flat_pullback {Y X : Scheme.{u}} (p : Y ⟶ X)
    [Flat p] (hp : Function.Surjective p) {M N : X.Modules} (f : M ⟶ N)
    [Epi ((pullback p).map f)] : Epi f := by
  let : PreservesColimitsOfSize.{u, u} (pullback p) :=
    (pullbackPushforwardAdjunction p).leftAdjoint_preservesColimits
  have hz : IsZero ((pullback p).obj (cokernel f)) :=
    (isZero_cokernel_of_epi ((pullback p).map f)).of_iso
      (PreservesCokernel.iso (pullback p) f)
  apply Preadditive.epi_of_isZero_cokernel
  apply (isZero_iff_stalks _).mpr
  intro x
  obtain ⟨y, rfl⟩ := hp x
  exact Coherent.Support.stalk_isZero_of_flat_pullback p (cokernel f) hz y

/-- Transport an actual evaluation-plus-section epimorphism along a specified
isomorphism of its target. All global sections are sent by literal composition. -/
theorem epi_globalSectionsEval_sum_of_iso {X : Scheme.{u}} {M N B : X.Modules}
    (e : M ≅ N) (b : B ⟶ M)
    [Epi (coprod.desc (globalSectionsEval M) b)] :
    Epi (coprod.desc (globalSectionsEval N) (b ≫ e.hom)) := by
  let f := Sigma.desc fun s : 𝟙_ X.Modules ⟶ M =>
    Sigma.ι (fun _ : (𝟙_ X.Modules ⟶ N) => 𝟙_ X.Modules) (s ≫ e.hom)
  have hf : f ≫ globalSectionsEval N = globalSectionsEval M ≫ e.hom := by
    apply Sigma.hom_ext
    intro s
    simp only [f, Sigma.ι_comp_desc_assoc, ι_globalSectionsEval,
      ι_globalSectionsEval_assoc]
  apply epi_of_epi_fac (f := coprod.map f (𝟙 B))
    (h := coprod.desc (globalSectionsEval M) b ≫ e.hom)
  apply coprod.hom_ext
  · simp only [coprod.inl_map_assoc, coprod.inl_desc_assoc, coprod.inl_desc, hf]
  · simp only [coprod.inr_map_assoc, coprod.inr_desc_assoc, Category.id_comp, coprod.inr_desc]

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Cohomology

/-- A map is surjective on sections exactly when its original degree-zero
cohomology map is epi, with the specified original structural scalars. -/
theorem sections_surjective_iff_h0_epi {X : Scheme.{u}}
    {R : Type u} [CommRing R] (α : R →+* Γ(X, ⊤))
    {M N : X.Modules} (φ : M ⟶ N) :
    Function.Surjective (φ.val.app (op ⊤)) ↔
      Epi ((moduleCohomologyFunctorOfHom X α 0).map φ) := by
  rw [ModuleCat.epi_iff_surjective]
  let eM := Sheaf.H.equiv₀ (moduleAddSheaf X M) isTerminalTop
  let eN := Sheaf.H.equiv₀ (moduleAddSheaf X N) isTerminalTop
  constructor
  · intro h y
    obtain ⟨x, hx⟩ := h (eN y)
    refine ⟨eM.symm x, eN.injective ?_⟩
    change eN (moduleCohomologyMapOfHom X α φ 0 (eM.symm x)) = eN y
    rw [equiv₀_moduleCohomologyMapOfHom]
    exact (congrArg (φ.val.app (op ⊤)) (eM.apply_symm_apply x)).trans hx
  · intro h y
    obtain ⟨x, hx⟩ := h (eN.symm y)
    refine ⟨eM x, ?_⟩
    have he := equiv₀_moduleCohomologyMapOfHom α φ x
    change eN (((moduleCohomologyFunctorOfHom X α 0).map φ) x) =
      φ.val.app (op ⊤) (eM x) at he
    rw [hx] at he
    exact he.symm.trans (eN.apply_symm_apply y)

/-- Flat base change transports surjectivity on global sections. Only the
target coefficient must be quasicoherent: the source comparison need not
be invertible, since its composite is already epi. -/
theorem sections_surjective_flat_baseChange
    {X Y : Scheme.{u}} {R S : Type u} [CommRing R] [CommRing S]
    (p : Y ⟶ X) (q : Y ⟶ Spec (CommRingCat.of S))
    (f : X ⟶ Spec (CommRingCat.of R)) [QuasiCompact f] [QuasiSeparated f]
    (σ : R →+* S) (h : IsPullback p q f (Spec.map (CommRingCat.ofHom σ)))
    (hflat : σ.Flat) {M N : X.Modules} [N.IsQuasicoherent] (φ : M ⟶ N)
    (hφ : Function.Surjective (φ.val.app (op ⊤))) :
    Function.Surjective (((Scheme.Modules.pullback p).map φ).val.app (op ⊤)) := by
  let α := f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
  let β := q.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom
  let hs := moduleSectionsBaseChangeScalars p q f σ h.w
  let A := Scheme.Modules.pullbackPushforwardAdjunction p
  let μ := (moduleCohomologyFunctorOfHom X α 0).map φ
  let ν := (moduleCohomologyFunctorOfHom Y β 0).map ((Scheme.Modules.pullback p).map φ)
  let : Epi μ := (sections_surjective_iff_h0_epi α φ).mp hφ
  let : IsIso (moduleCohomologyTensorMap p σ α β hs (A.unit.app N) 0) :=
    moduleCohomologyTensorMap_isIso_of_quasiSeparated_of_isPullback p q f σ h hflat N 0
  have hc := moduleCohomologyTensorMap_naturality p σ α β hs
    (A.unit.app M) (A.unit.app N) φ ((Scheme.Modules.pullback p).map φ)
    (A.unit.naturality φ) 0
  let : (ModuleCat.extendScalars.{u,u,u+1} σ).IsLeftAdjoint :=
    (ModuleCat.extendRestrictScalarsAdj.{u+1,u,u} σ).isLeftAdjoint
  have hμ : Epi ((ModuleCat.extendScalars.{u,u,u+1} σ).map μ) := by infer_instance
  have he : Epi (moduleCohomologyTensorMap p σ α β hs (A.unit.app M) 0 ≫ ν) := by
    rw [← hc]
    change Epi ((ModuleCat.extendScalars.{u,u,u+1} σ).map μ ≫
      moduleCohomologyTensorMap p σ α β hs (A.unit.app N) 0)
    exact epi_comp' hμ (inferInstance : Epi
      (moduleCohomologyTensorMap p σ α β hs (A.unit.app N) 0))
  let : Epi ν := epi_of_epi (moduleCohomologyTensorMap p σ α β hs (A.unit.app M) 0) ν
  exact (sections_surjective_iff_h0_epi β ((Scheme.Modules.pullback p).map φ)).mpr inferInstance

end AlgebraicGeometry.Scheme.Cohomology

namespace AlgebraicGeometry.Scheme.Modules

/-- Global generation descends along an actual surjective flat affine-base
change of a qcqs scheme. The proof uses the pullback of the original
all-sections evaluation, not an assumed evaluation comparison. -/
theorem globalSectionsEval_epi_of_flat_baseChange
    {X Y : Scheme.{u}} {R S : Type u} [CommRing R] [CommRing S]
    (p : Y ⟶ X) [Flat p] (hp : Function.Surjective p)
    (q : Y ⟶ Spec (CommRingCat.of S))
    (f : X ⟶ Spec (CommRingCat.of R)) [QuasiCompact f] [QuasiSeparated f]
    (σ : R →+* S) (h : IsPullback p q f (Spec.map (CommRingCat.ofHom σ)))
    (hflat : σ.Flat) (M : X.Modules) [M.IsQuasicoherent]
    [Epi (globalSectionsEval ((pullback p).obj M))] :
    Epi (globalSectionsEval M) := by
  have hs := Cohomology.sections_surjective_flat_baseChange p q f σ h hflat
    (globalSectionsEval M) (globalSectionsEval_sections_surjective M)
  let : Epi ((pullback p).map (globalSectionsEval M)) :=
    epi_of_unitHom_factor _ (exists_unitHom_factor_of_surjective _ hs)
  exact epi_of_surjective_flat_pullback p hp (globalSectionsEval M)

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Cohomology

open AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.Scheme.Modules

/-- The original ordered projective differential coefficient under scalar
extension. The same ordered determinant comparison is used on both sides;
no basis or trivialization of the coefficient module is chosen. -/
def cmCurveCoefficientAmbientBaseChangeIso
    {R S : Type u} [Field R] [Field S] (σ : R →+* S)
    (ι : Type u) (n : ℕ) (e : ι ≃ Fin (n + 1)) (V : ModuleCat.{u} R) :
    (Scheme.Modules.pullback (ProjectiveSpace.map σ ι)).obj
      (cmCurveCoefficientAmbient R ι n V) ≅
      cmCurveCoefficientAmbient S ι n ((ModuleCat.extendScalars σ).obj V) := by
  let : Fintype ι := Fintype.ofEquiv (Fin (n + 1)) e.symm
  let g := ProjectiveSpace.map σ ι
  let a := Spec.map (CommRingCat.ofHom σ)
  let p := toSpec R ι
  let q := toSpec S ι
  let t := twistingSheaf R ι (-(Fintype.card ι : ℤ))
  let c : (Scheme.Modules.pullback g).obj
      ((Scheme.Modules.pullback p).obj (tilde V)) ≅
      (Scheme.Modules.pullback q).obj (tilde ((ModuleCat.extendScalars σ).obj V)) :=
    (pullbackComp g p).app (tilde V) ≪≫
      (pullbackCongr (ProjectiveSpace.map_toSpec σ ι)).app (tilde V) ≪≫
      ((pullbackComp q a).app (tilde V)).symm ≪≫
      (Scheme.Modules.pullback q).mapIso ((tildePullbackIso (CommRingCat.ofHom σ)).app V)
  exact (Scheme.Modules.pullback g).mapIso
      (projectiveDifferentialCoefficientsTwistingIso R ι n e V) ≪≫
    pullbackTensorMapIso g t ((Scheme.Modules.pullback p).obj (tilde V)) ≪≫
    tensorSheafIso (ProjectiveSpace S ι)
      (ProjectiveSpace.twistingPullbackIso σ ι (-(Fintype.card ι : ℤ))) c ≪≫
    (projectiveDifferentialCoefficientsTwistingIso S ι n e
      ((ModuleCat.extendScalars σ).obj V)).symm

/-- If the actual structural H0 has dimension one, its original structural
map is bijective. The unital section formula prevents replacing it by an
arbitrary linear isomorphism. -/
theorem cmCurveSerreStructuralH0Map_bijective_of_finrank_one
    (k : Type u) [Field k] (ι : Type u) {C : Scheme.{u}}
    (j : C ⟶ ProjectiveSpace k ι)
    [Module.Finite k (cmCurveSerreCohomology k ι j (cmCurveSerreUnit C) 0)]
    (hd : Module.finrank k (cmCurveSerreCohomology k ι j (cmCurveSerreUnit C) 0) = 1) :
    Function.Bijective (cmCurveSerreStructuralH0Map k ι j) := by
  let α := cmCurveSerreScalar k ι j
  let O := cmCurveSerreUnit C
  let : Module k Γ(C, ⊤) := Module.compHom _ α
  let E := moduleH0EquivOfHom C α O
  let : Nontrivial (cmCurveSerreCohomology k ι j O 0) :=
    Module.nontrivial_of_finrank_pos (R := k)
      (show 0 < Module.finrank k (cmCurveSerreCohomology k ι j O 0) from
        hd.symm ▸ Nat.zero_lt_one)
  let : Nontrivial (Sheaf.H.{u + 1} (moduleAddSheaf C O) 0) :=
    inferInstanceAs (Nontrivial (cmCurveSerreCohomology k ι j O 0))
  let : Nontrivial Γ(C, ⊤) := E.injective.nontrivial
  have hi : Function.Injective (cmCurveSerreStructuralH0Map k ι j) := by
    intro x y h
    apply α.injective
    rw [← cmCurveSerreStructuralH0Map_sections k ι j x,
      ← cmCurveSerreStructuralH0Map_sections k ι j y, h]
  refine ⟨hi, ?_⟩
  apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (show Module.finrank k k = Module.finrank k
      (cmCurveSerreCohomology k ι j O 0) by rw [Module.finrank_self, hd])).mp hi

/-- The chosen projective base-changed curve is also the original Cartesian
square over the structural fields, by pasting the actual projective square. -/
theorem cmCurveFieldExtension_isPullback
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    (ι : Type u) {C : Scheme.{u}} (j : C ⟶ ProjectiveSpace k ι) :
    IsPullback (Limits.pullback.fst j (ProjectiveSpace.map (algebraMap k K) ι))
      (Limits.pullback.snd j (ProjectiveSpace.map (algebraMap k K) ι) ≫ toSpec K ι)
      (j ≫ toSpec k ι) (Spec.map (CommRingCat.ofHom (algebraMap k K))) :=
  (IsPullback.of_hasPullback j (ProjectiveSpace.map (algebraMap k K) ι)).paste_vert
    (ProjectiveSpace.isPullback_map (algebraMap k K) ι)

/-- Original cohomology base change on the same chosen embedded curve used
by the closed-parameter and generation theorems. No second fibre model is chosen. -/
def cmCurveCohomologyFieldExtensionIso
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    (ι : Type u) [Finite ι] {C : Scheme.{u}}
    (j : C ⟶ ProjectiveSpace k ι) [IsClosedImmersion j]
    (M : C.Modules) [M.IsQuasicoherent] (r : ℕ) :
    (ModuleCat.extendScalars (algebraMap k K)).obj
        (cmCurveSerreCohomology k ι j M r) ≅
      cmCurveSerreCohomology K ι
        (Limits.pullback.snd j (ProjectiveSpace.map (algebraMap k K) ι))
        ((Scheme.Modules.pullback
          (Limits.pullback.fst j (ProjectiveSpace.map (algebraMap k K) ι))).obj M) r := by
  let p := Limits.pullback.fst j (ProjectiveSpace.map (algebraMap k K) ι)
  let q := Limits.pullback.snd j (ProjectiveSpace.map (algebraMap k K) ι) ≫ toSpec K ι
  let f := j ≫ toSpec k ι
  let h := cmCurveFieldExtension_isPullback k K ι j
  let α := cmCurveSerreScalar k ι j
  let β := cmCurveSerreScalar K ι
    (Limits.pullback.snd j (ProjectiveSpace.map (algebraMap k K) ι))
  let A : ModuleCat.{u + 1} k := cmCurveSerreCohomology k ι j M r
  let B : ModuleCat.{u + 1} K := cmCurveSerreCohomology K ι
    (Limits.pullback.snd j (ProjectiveSpace.map (algebraMap k K) ι))
    ((Scheme.Modules.pullback p).obj M) r
  let φ : (ModuleCat.extendScalars.{u,u,u + 1} (algebraMap k K)).obj A ⟶ B :=
    moduleCohomologyTensorMap p (algebraMap k K) α β
      (moduleSectionsBaseChangeScalars p q f (algebraMap k K) h.w)
      ((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app M) r
  let : IsIso φ := moduleCohomologyTensorMap_isIso_of_quasiSeparated_of_isPullback
    p q f (algebraMap k K) h (RingHom.Flat.of_isField (Field.toIsField k) _) M r
  exact asIso φ

/-- Original field-extension cohomology preserves vanishing, on the same chosen curve. -/
theorem cmCurveCohomologyFieldExtension_subsingleton
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    (ι : Type u) [Finite ι] {C : Scheme.{u}}
    (j : C ⟶ ProjectiveSpace k ι) [IsClosedImmersion j]
    (M : C.Modules) [M.IsQuasicoherent] (r : ℕ)
    [Subsingleton (cmCurveSerreCohomology k ι j M r)] :
    Subsingleton (cmCurveSerreCohomology K ι
      (Limits.pullback.snd j (ProjectiveSpace.map (algebraMap k K) ι))
      ((Modules.pullback
        (Limits.pullback.fst j (ProjectiveSpace.map (algebraMap k K) ι))).obj M) r) := by
  let H : ModuleCat.{u + 1} k := cmCurveSerreCohomology k ι j M r
  have hz : IsZero H := ModuleCat.isZero_of_subsingleton H
  have h : IsZero ((ModuleCat.extendScalars.{u, u, u + 1} (algebraMap k K)).obj H) :=
    (ModuleCat.extendScalars (algebraMap k K)).map_isZero hz
  exact ModuleCat.subsingleton_of_isZero
    (h.of_iso (cmCurveCohomologyFieldExtensionIso k K ι j M r).symm)

/-- Every cohomology dimension is unchanged on that actual chosen curve,
through the original scalar-extension map, without finite-dimensional assumptions. -/
theorem cmCurveCohomology_finrank_fieldExtension
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    (ι : Type u) [Finite ι] {C : Scheme.{u}}
    (j : C ⟶ ProjectiveSpace k ι) [IsClosedImmersion j]
    (M : C.Modules) [M.IsQuasicoherent] (r : ℕ) :
    Module.finrank K (cmCurveSerreCohomology K ι
      (Limits.pullback.snd j (ProjectiveSpace.map (algebraMap k K) ι))
      ((Scheme.Modules.pullback
        (Limits.pullback.fst j (ProjectiveSpace.map (algebraMap k K) ι))).obj M) r) =
      Module.finrank k (cmCurveSerreCohomology k ι j M r) := by
  exact (cmCurveCohomologyFieldExtensionIso k K ι j M r).toLinearEquiv.finrank_eq.symm.trans
    ((ModuleCat.extendScalarsAlgebraObjIso k K
      (cmCurveSerreCohomology k ι j M r)).toLinearEquiv.finrank_eq.trans
      Module.finrank_baseChange)

/-- The literal pulled-back twisting module on the original curve becomes
the same twisting module on its chosen base-changed projective embedding. -/
def cmCurveTwistingFieldExtensionIso
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    (ι : Type u) {C : Scheme.{u}} (j : C ⟶ ProjectiveSpace k ι) (d : ℤ) :
    (Scheme.Modules.pullback
        (Limits.pullback.fst j (ProjectiveSpace.map (algebraMap k K) ι))).obj
      ((Scheme.Modules.pullback j).obj (twistingSheaf k ι d)) ≅
    (Scheme.Modules.pullback
        (Limits.pullback.snd j (ProjectiveSpace.map (algebraMap k K) ι))).obj
      (twistingSheaf K ι d) :=
  (pullbackComp _ j).app (twistingSheaf k ι d) ≪≫
    (pullbackCongr (Limits.pullback.condition (f := j)
      (g := ProjectiveSpace.map (algebraMap k K) ι))).app (twistingSheaf k ι d) ≪≫
    ((pullbackComp _ (ProjectiveSpace.map (algebraMap k K) ι)).app
      (twistingSheaf k ι d)).symm ≪≫
    (Scheme.Modules.pullback (Limits.pullback.snd j
      (ProjectiveSpace.map (algebraMap k K) ι))).mapIso
      (ProjectiveSpace.twistingPullbackIso (algebraMap k K) ι d)

end AlgebraicGeometry.Scheme.Cohomology
