/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.AlgebraicGeometry.Modules.Differentials.Relative.Affine
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.Pullback
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.TildeExact
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.Morphisms
public import Mathlib.RingTheory.RingHom.Smooth
public import Mathlib.RingTheory.Etale.Kaehler
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.RingTheory.Localization.Algebra
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# The actual affine relative conormal sequence

For original ring maps `α : R ⟶ A` and surjective `σ : A ⟶ B`, the native
extension of `B` by `A` supplies its original conormal module and arrows.
The actual relative differential sheaves are identified by the original
`relativeDifferentialAffineIso` and `tildePullbackIso`. The resulting short
complex has terms `tilde(ker σ / (ker σ)^2)`, the actual pullback of
`Ω_(Spec A/Spec R)`, and the actual `Ω_(Spec B/Spec R)`.

The sequence is exact and right epic for every such surjection. It is
`ShortExact` under native formal smoothness of the two original base maps.
The original kernel-class, principal-open differential and adjunction-unit
equations retain the positive `class(a) ↦ 1 ⊗ D(a)` convention. Principal
localization uses the original localized surjection, native Extension tensor
maps, and the actual module-sheaf pullback and restriction functors.

All rings are arbitrary commutative rings in the native scheme universe.
Identity maps and zero rings are included. Global conormal gluing,
regular-generator existence, conormal determinants and geometric purity are
later consumers; conormal vectors retain the first position in that order.
-/

@[expose] public section
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules TensorProduct KaehlerDifferential
universe u
namespace AlgebraicGeometry.Scheme.Modules.Differentials
variable {R A B : CommRingCat.{u}} (α : R ⟶ A) (σ : A ⟶ B)
variable (hσ : Function.Surjective σ)

/-- The original surjective extension with its composed base action. -/
def relativeConormalAffineExtension :
    letI := α.hom.toAlgebra
    letI := (α ≫ σ).hom.toAlgebra
    Algebra.Extension R B := by
  letI := α.hom.toAlgebra
  letI := (α ≫ σ).hom.toAlgebra
  exact Algebra.Extension.ofSurjective
    { __ := σ.hom, commutes' := fun _ => rfl } hσ

/-- The original kernel modulo its square, with its native quotient-module action. -/
def relativeConormalAffineModule : ModuleCat.{u} B := by
  letI := α.hom.toAlgebra
  letI := (α ≫ σ).hom.toAlgebra
  exact ModuleCat.of B (relativeConormalAffineExtension α σ hσ).Cotangent

/-- The original native cotangent-complex arrow. -/
def relativeConormalAffineLinearF :
    relativeConormalAffineModule α σ hσ ⟶
      (ModuleCat.extendScalars σ.hom).obj (CommRingCat.KaehlerDifferential α) := by
  letI := α.hom.toAlgebra
  letI := (α ≫ σ).hom.toAlgebra
  exact ModuleCat.ofHom (relativeConormalAffineExtension α σ hσ).cotangentComplex

/-- The original scalar-extended Kähler differential map. -/
def relativeConormalAffineLinearG :
    (ModuleCat.extendScalars σ.hom).obj (CommRingCat.KaehlerDifferential α) ⟶
      CommRingCat.KaehlerDifferential (α ≫ σ) := by
  letI := α.hom.toAlgebra
  letI := (α ≫ σ).hom.toAlgebra
  exact ModuleCat.ofHom (relativeConormalAffineExtension α σ hσ).toKaehler

/-- The native module conormal short complex of the original surjection. -/
def relativeConormalAffineLinearComplex : ShortComplex (ModuleCat.{u} B) :=
  ShortComplex.mk (relativeConormalAffineLinearF α σ hσ)
    (relativeConormalAffineLinearG α σ hσ) (by
      let := α.hom.toAlgebra
      let := (α ≫ σ).hom.toAlgebra
      let E := relativeConormalAffineExtension α σ hσ
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      exact (Algebra.Extension.exact_cotangentComplex_toKaehler
        (P := E) (E.cotangentComplex x)).mpr ⟨x, rfl⟩)

/-- Exactness of the original module conormal short complex. -/
theorem relativeConormalAffineLinearComplex_exact :
    (relativeConormalAffineLinearComplex α σ hσ).Exact := by
  let := α.hom.toAlgebra
  let := (α ≫ σ).hom.toAlgebra
  apply ModuleCat.shortComplex_exact
  exact Algebra.Extension.exact_cotangentComplex_toKaehler

/-- The original module differential map is an epimorphism. -/
theorem relativeConormalAffineLinearComplex_epi :
    Epi (relativeConormalAffineLinearComplex α σ hσ).g := by
  let := α.hom.toAlgebra
  let := (α ≫ σ).hom.toAlgebra
  apply (ModuleCat.epi_iff_surjective _).mpr
  exact Algebra.Extension.toKaehler_surjective

/-- Native formal smoothness gives the original short exact module sequence. -/
theorem relativeConormalAffineLinearComplex_shortExact
    (hA : α.hom.FormallySmooth) (hB : (α ≫ σ).hom.FormallySmooth) :
    (relativeConormalAffineLinearComplex α σ hσ).ShortExact := by
  let := α.hom.toAlgebra
  let := (α ≫ σ).hom.toAlgebra
  let : Algebra.FormallySmooth R A := hA
  let : Algebra.FormallySmooth R B := hB
  let E := relativeConormalAffineExtension α σ hσ
  let : Algebra.FormallySmooth R E.Ring := by
    change @Algebra.FormallySmooth R A _ _ α.hom.toAlgebra
    exact hA
  exact ModuleCat.shortComplex_shortExact _
    (Algebra.Extension.exact_cotangentComplex_toKaehler (P := E))
    ((Algebra.Extension.cotangentComplex_injective_iff E).mpr inferInstance)
    (Algebra.Extension.toKaehler_surjective (P := E))

/-- The original affine differential and tilde pullback comparison. -/
def relativeConormalAffineMiddleIso :
    (pullback (Spec.map σ)).obj (relativeDifferentialSheaf (Spec.map α)) ≅
      tilde ((ModuleCat.extendScalars σ.hom).obj (CommRingCat.KaehlerDifferential α)) :=
  (pullback (Spec.map σ)).mapIso (relativeDifferentialAffineIso α) ≪≫
    (tildePullbackIso σ).app (CommRingCat.KaehlerDifferential α)

private theorem conormal_conjugate_zero {C D : Type*} [Category C] [Category D]
    [HasZeroMorphisms C] [HasZeroMorphisms D] (F : C ⥤ D) [F.PreservesZeroMorphisms]
    {X₁ X₂ X₃ : C} (f : X₁ ⟶ X₂) (g : X₂ ⟶ X₃) (h : f ≫ g = 0)
    {Y₂ Y₃ : D} (e₂ : Y₂ ≅ F.obj X₂) (e₃ : Y₃ ≅ F.obj X₃) :
    (F.map f ≫ e₂.inv) ≫ (e₂.hom ≫ F.map g ≫ e₃.inv) = 0 := by
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Category.assoc, ← Functor.map_comp, h, Functor.map_zero, zero_comp]

/-- The actual relative conormal short complex on the original `Spec B`. -/
def relativeConormalAffineComplex : ShortComplex (Spec B).Modules :=
  ShortComplex.mk
    ((tilde.functor B).map (relativeConormalAffineLinearF α σ hσ) ≫
      (relativeConormalAffineMiddleIso α σ).inv)
    ((relativeConormalAffineMiddleIso α σ).hom ≫
      (tilde.functor B).map (relativeConormalAffineLinearG α σ hσ) ≫
        (relativeDifferentialAffineIso (α ≫ σ)).inv) (by
      exact conormal_conjugate_zero (tilde.functor B) _ _
        (relativeConormalAffineLinearComplex α σ hσ).zero
        (relativeConormalAffineMiddleIso α σ) (relativeDifferentialAffineIso (α ≫ σ)))

/-- Identification with tilde of the original native module short complex. -/
def relativeConormalAffineComplexIso :
    relativeConormalAffineComplex α σ hσ ≅
      (relativeConormalAffineLinearComplex α σ hσ).map (tilde.functor B) :=
  ShortComplex.isoMk (Iso.refl _) (relativeConormalAffineMiddleIso α σ)
    (relativeDifferentialAffineIso (α ≫ σ)) (by
      simp [relativeConormalAffineComplex, relativeConormalAffineLinearComplex])
    (by simp [relativeConormalAffineComplex, relativeConormalAffineLinearComplex])

/-- Exactness of the actual affine relative conormal sequence. -/
theorem relativeConormalAffineComplex_exact :
    (relativeConormalAffineComplex α σ hσ).Exact :=
  ShortComplex.exact_of_iso (relativeConormalAffineComplexIso α σ hσ).symm
    ((relativeConormalAffineLinearComplex_exact α σ hσ).map (tilde.functor B))

/-- Exactness and right epimorphy of the actual conormal sequence. -/
theorem relativeConormalAffineComplex_exact_epi :
    (relativeConormalAffineComplex α σ hσ).Exact ∧
      Epi (relativeConormalAffineComplex α σ hσ).g := by
  let : Epi (relativeConormalAffineLinearComplex α σ hσ).g :=
    relativeConormalAffineLinearComplex_epi α σ hσ
  have hg : Epi ((relativeConormalAffineLinearComplex α σ hσ).map (tilde.functor B)).g := by
    change Epi ((tilde.functor B).map (relativeConormalAffineLinearComplex α σ hσ).g)
    infer_instance
  exact (ShortComplex.exact_and_epi_g_iff_of_iso
    (relativeConormalAffineComplexIso α σ hσ)).mpr
      ⟨(relativeConormalAffineLinearComplex_exact α σ hσ).map (tilde.functor B), hg⟩

/-- The actual conormal sequence is short exact under native formal smoothness. -/
theorem relativeConormalAffineComplex_shortExact
    (hA : α.hom.FormallySmooth) (hB : (α ≫ σ).hom.FormallySmooth) :
    (relativeConormalAffineComplex α σ hσ).ShortExact :=
  ShortComplex.shortExact_of_iso (relativeConormalAffineComplexIso α σ hσ).symm
    ((relativeConormalAffineLinearComplex_shortExact α σ hσ hA hB).map_of_exact
      (tilde.functor B))

/-- The class of an original kernel element in its native conormal module. -/
def relativeConormalAffineClass (x : RingHom.ker σ.hom) :
    relativeConormalAffineModule α σ hσ := by
  letI := α.hom.toAlgebra
  letI := (α ≫ σ).hom.toAlgebra
  exact Algebra.Extension.Cotangent.mk (P := relativeConormalAffineExtension α σ hσ) x

/-- The original positive class-to-differential formula. -/
theorem relativeConormalAffineLinearF_class (x : RingHom.ker σ.hom) :
    letI := σ.hom.toAlgebra
    relativeConormalAffineLinearF α σ hσ (relativeConormalAffineClass α σ hσ x) =
      (1 : B) ⊗ₜ[A] (CommRingCat.KaehlerDifferential.d (f := α) x.val) := by
  let := σ.hom.toAlgebra
  rfl

/-- The original differential map on a scalar multiple of a differential. -/
theorem relativeConormalAffineLinearG_tmul (b : B) (a : A) :
    letI := σ.hom.toAlgebra
    relativeConormalAffineLinearG α σ hσ
      (b ⊗ₜ[A] (CommRingCat.KaehlerDifferential.d (f := α) a)) =
        b • CommRingCat.KaehlerDifferential.d (f := α ≫ σ) (σ a) := by
  let := α.hom.toAlgebra
  let := (α ≫ σ).hom.toAlgebra
  let := σ.hom.toAlgebra
  let : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq' rfl
  change KaehlerDifferential.mapBaseChange R A B
    (b ⊗ₜ[A] KaehlerDifferential.D R A a) = b • KaehlerDifferential.D R B (σ a)
  rw [KaehlerDifferential.mapBaseChange_tmul, KaehlerDifferential.map_D]
  rfl

private theorem conormal_tilde_toOpen {S : CommRingCat.{u}} {M N : ModuleCat.{u} S}
    (f : M ⟶ N) (U : (Spec S).Opens) (m : M) :
    ((tilde.functor S).map f).val.app (op U) (tilde.toOpen M U m) =
      tilde.toOpen N U (f m) :=
  ConcreteCategory.congr_hom (tilde.toOpen_map_app f U) m

/-- The first arrow after the original middle comparison. -/
theorem relativeConormalAffineComplex_f_middle :
    (relativeConormalAffineComplex α σ hσ).f ≫ (relativeConormalAffineMiddleIso α σ).hom =
      (tilde.functor B).map (relativeConormalAffineLinearF α σ hσ) := by
  change (_ ≫ (relativeConormalAffineMiddleIso α σ).inv) ≫
    (relativeConormalAffineMiddleIso α σ).hom = _
  simp

/-- The second arrow after the original affine comparisons. -/
theorem relativeConormalAffineComplex_g_middle :
    (relativeConormalAffineMiddleIso α σ).inv ≫
      (relativeConormalAffineComplex α σ hσ).g ≫
        (relativeDifferentialAffineIso (α ≫ σ)).hom =
      (tilde.functor B).map (relativeConormalAffineLinearG α σ hσ) := by
  change (relativeConormalAffineMiddleIso α σ).inv ≫
    ((relativeConormalAffineMiddleIso α σ).hom ≫ _ ≫
      (relativeDifferentialAffineIso (α ≫ σ)).inv) ≫ _ = _
  simp

/-- The original kernel-class formula on every principal open. -/
theorem relativeConormalAffineComplex_f_class (r : B) (x : RingHom.ker σ.hom) :
    letI := σ.hom.toAlgebra
    (relativeConormalAffineMiddleIso α σ).hom.val.app (op (PrimeSpectrum.basicOpen r))
      ((relativeConormalAffineComplex α σ hσ).f.val.app (op (PrimeSpectrum.basicOpen r))
        (tilde.toOpen (relativeConormalAffineModule α σ hσ) (PrimeSpectrum.basicOpen r)
          (relativeConormalAffineClass α σ hσ x))) =
    tilde.toOpen ((ModuleCat.extendScalars σ.hom).obj (CommRingCat.KaehlerDifferential α))
      (PrimeSpectrum.basicOpen r)
      ((1 : B) ⊗ₜ[A] (CommRingCat.KaehlerDifferential.d (f := α) x.val)) := by
  let := σ.hom.toAlgebra
  have h := ConcreteCategory.congr_hom
    (congrArg (fun f => f.val.app (op (PrimeSpectrum.basicOpen r)))
      (relativeConormalAffineComplex_f_middle α σ hσ))
        (tilde.toOpen (relativeConormalAffineModule α σ hσ) (PrimeSpectrum.basicOpen r)
          (relativeConormalAffineClass α σ hσ x))
  exact h.trans ((conormal_tilde_toOpen _ _ _).trans
    (congrArg (tilde.toOpen
      ((ModuleCat.extendScalars σ.hom).obj (CommRingCat.KaehlerDifferential α))
        (PrimeSpectrum.basicOpen r)) (relativeConormalAffineLinearF_class α σ hσ x)))

/-- The original differential image on every principal open. -/
theorem relativeConormalAffineComplex_g_d (r : B) (a : A) :
    letI := σ.hom.toAlgebra
    (relativeConormalAffineComplex α σ hσ).g.val.app (op (PrimeSpectrum.basicOpen r))
      ((relativeConormalAffineMiddleIso α σ).inv.val.app (op (PrimeSpectrum.basicOpen r))
        (tilde.toOpen ((ModuleCat.extendScalars σ.hom).obj (CommRingCat.KaehlerDifferential α))
          (PrimeSpectrum.basicOpen r)
          ((1 : B) ⊗ₜ[A] CommRingCat.KaehlerDifferential.d (f := α) a))) =
    (relativeDifferentialDerivation (Spec.map (α ≫ σ))).d
      (algebraMap B Γ(Spec B, PrimeSpectrum.basicOpen r) (σ a)) := by
  let := σ.hom.toAlgebra
  change (relativeDifferentialAffineIso (α ≫ σ)).inv.val.app _
    (((tilde.functor B).map (relativeConormalAffineLinearG α σ hσ)).val.app _
      ((relativeConormalAffineMiddleIso α σ).hom.val.app _
        ((relativeConormalAffineMiddleIso α σ).inv.val.app _ _))) = _
  rw [← relativeDifferentialAffineIso_inv_d]
  congr 1
  have hm := ConcreteCategory.congr_hom
    (congrArg (fun f => f.val.app (op (PrimeSpectrum.basicOpen r)))
      (relativeConormalAffineMiddleIso α σ).inv_hom_id)
      (tilde.toOpen ((ModuleCat.extendScalars σ.hom).obj (CommRingCat.KaehlerDifferential α))
        (PrimeSpectrum.basicOpen r)
          ((1 : B) ⊗ₜ[A] CommRingCat.KaehlerDifferential.d (f := α) a))
  change (relativeConormalAffineMiddleIso α σ).hom.val.app _
    ((relativeConormalAffineMiddleIso α σ).inv.val.app _
      (tilde.toOpen ((ModuleCat.extendScalars σ.hom).obj (CommRingCat.KaehlerDifferential α))
        (PrimeSpectrum.basicOpen r)
        ((1 : B) ⊗ₜ[A] CommRingCat.KaehlerDifferential.d (f := α) a))) =
    tilde.toOpen ((ModuleCat.extendScalars σ.hom).obj (CommRingCat.KaehlerDifferential α))
      (PrimeSpectrum.basicOpen r)
      ((1 : B) ⊗ₜ[A] CommRingCat.KaehlerDifferential.d (f := α) a) at hm
  rw [hm, conormal_tilde_toOpen]
  congr 1
  simpa only [one_smul] using relativeConormalAffineLinearG_tmul α σ hσ 1 a

private theorem conormal_adjoint_conjugate {C D : Type*} [Category C] [Category D]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) {X X' : C} {Y Y' : D}
    (e : X ≅ X') (t : Y ≅ Y') (k : F.obj X' ⟶ Y') :
    e.inv ≫ adj.unit.app X ≫ G.map (F.map e.hom ≫ k ≫ t.inv) ≫ G.map t.hom =
      adj.homEquiv X' Y' k := by
  have he : e.inv ≫ adj.unit.app X = adj.unit.app X' ≫ G.map (F.map e.inv) :=
    adj.unit.naturality e.inv
  calc
    _ = (e.inv ≫ adj.unit.app X) ≫ G.map (F.map e.hom ≫ k ≫ t.inv) ≫ G.map t.hom := by
      simp only [Category.assoc]
    _ = (adj.unit.app X' ≫ G.map (F.map e.inv)) ≫
        G.map (F.map e.hom ≫ k ≫ t.inv) ≫ G.map t.hom := by rw [he]
    _ = adj.unit.app X' ≫ G.map (F.map e.inv ≫ (F.map e.hom ≫ k ≫ t.inv) ≫ t.hom) := by
      simp only [Functor.map_comp, Category.assoc]
    _ = adj.unit.app X' ≫ G.map k := by simp [Category.assoc]
    _ = adj.homEquiv X' Y' k := (adj.homEquiv_unit X' Y' k).symm

/-- Compatibility with the original geometric, scalar and tilde adjunction units. -/
theorem relativeConormalAffineComplex_unit :
    let M := CommRingCat.KaehlerDifferential α
    let N := CommRingCat.KaehlerDifferential (α ≫ σ)
    let adj := pullbackPushforwardAdjunction (Spec.map σ)
    (tilde.adjunction (R := A)).homEquiv M _
      ((relativeDifferentialAffineIso α).inv ≫
        adj.unit.app (relativeDifferentialSheaf (Spec.map α)) ≫
        (pushforward (Spec.map σ)).map (relativeConormalAffineComplex α σ hσ).g ≫
        (pushforward (Spec.map σ)).map (relativeDifferentialAffineIso (α ≫ σ)).hom) ≫
      (pushforwardGlobalSectionsIso σ).hom.app (tilde N) =
    (ModuleCat.extendRestrictScalarsAdj σ.hom).homEquiv M
      (moduleSpecΓFunctor.obj (tilde N))
      (relativeConormalAffineLinearG α σ hσ ≫ (tilde.adjunction (R := B)).unit.app N) := by
  intro M N adj
  let k := ((tildePullbackIso σ).app M).hom ≫
    (tilde.functor B).map (relativeConormalAffineLinearG α σ hσ)
  have hg : (relativeConormalAffineComplex α σ hσ).g =
      (pullback (Spec.map σ)).map (relativeDifferentialAffineIso α).hom ≫ k ≫
        (relativeDifferentialAffineIso (α ≫ σ)).inv := by
    simp only [relativeConormalAffineComplex, relativeConormalAffineMiddleIso,
      Iso.trans_hom, Functor.mapIso_hom, k, M, Category.assoc]
  have hp : (relativeDifferentialAffineIso α).inv ≫
        adj.unit.app (relativeDifferentialSheaf (Spec.map α)) ≫
        (pushforward (Spec.map σ)).map (relativeConormalAffineComplex α σ hσ).g ≫
        (pushforward (Spec.map σ)).map (relativeDifferentialAffineIso (α ≫ σ)).hom =
      adj.homEquiv (tilde M) (tilde N) k := by
    rw [hg]
    exact conormal_adjoint_conjugate adj (relativeDifferentialAffineIso α)
      (relativeDifferentialAffineIso (α ≫ σ)) k
  refine (congrArg (fun f => (tilde.adjunction (R := A)).homEquiv M _ f ≫
    (pushforwardGlobalSectionsIso σ).hom.app (tilde N)) hp).trans ?_
  refine (tildePullbackIso_homEquiv σ M (tilde N)
    ((tilde.functor B).map (relativeConormalAffineLinearG α σ hσ))).trans ?_
  congr 1
  rw [Adjunction.homEquiv_unit]
  exact ((tilde.adjunction (R := B)).unit.naturality
    (relativeConormalAffineLinearG α σ hσ)).symm

/-- The original principal-localized ring map. -/
def relativeConormalAffineLocalizationMap (r : A) :
    CommRingCat.of (Localization.Away r) ⟶ CommRingCat.of (Localization.Away (σ r)) := by
  letI : IsLocalization ((Submonoid.powers r).map σ.hom) (Localization.Away (σ r)) := by
    rw [Submonoid.map_powers]
    infer_instance
  exact CommRingCat.ofHom (IsLocalization.map (Localization.Away (σ r)) σ.hom
    (Submonoid.le_comap_map (Submonoid.powers r)))

/-- The original localization square commutes. -/
theorem relativeConormalAffineLocalizationMap_square (r : A) :
    CommRingCat.ofHom (algebraMap A (Localization.Away r)) ≫
      relativeConormalAffineLocalizationMap σ r =
    σ ≫ CommRingCat.ofHom (algebraMap B (Localization.Away (σ r))) := by
  ext a
  simp [relativeConormalAffineLocalizationMap]

include hσ in
/-- The original localized ring map remains surjective. -/
theorem relativeConormalAffineLocalizationMap_surjective (r : A) :
    Function.Surjective (relativeConormalAffineLocalizationMap σ r) := by
  let : IsLocalization ((Submonoid.powers r).map σ.hom) (Localization.Away (σ r)) := by
    rw [Submonoid.map_powers]
    infer_instance
  exact IsLocalization.map_surjective_of_surjective
    (S := Localization.Away r) (Q := Localization.Away (σ r))
    (M := Submonoid.powers r) (g := σ.hom) hσ

/-- The original localized ring map on an original ring element. -/
theorem relativeConormalAffineLocalizationMap_algebraMap (r : A) (a : A) :
    relativeConormalAffineLocalizationMap σ r (algebraMap A (Localization.Away r) a) =
      algebraMap B (Localization.Away (σ r)) (σ a) := by
  simp [relativeConormalAffineLocalizationMap]

/-- The native extension morphism of the original localized surjection. -/
def relativeConormalAffineLocalizationExtensionHom (r : A) :
    let A' := CommRingCat.of (Localization.Away r)
    let B' := CommRingCat.of (Localization.Away (σ r))
    let ιA : A ⟶ A' := CommRingCat.ofHom (algebraMap A A')
    let ιB : B ⟶ B' := CommRingCat.ofHom (algebraMap B B')
    let α' := α ≫ ιA
    let σ' := relativeConormalAffineLocalizationMap σ r
    let E := relativeConormalAffineExtension α σ hσ
    let Q := relativeConormalAffineExtension α' σ'
      (relativeConormalAffineLocalizationMap_surjective σ hσ r)
    @Algebra.Extension.Hom R B _ _ (α ≫ σ).hom.toAlgebra E
      R B' _ _ (α' ≫ σ').hom.toAlgebra Q (Algebra.id R) ιB.hom.toAlgebra := by
  intro A' B' ιA ιB α' σ' E Q
  letI := α.hom.toAlgebra
  letI := (α ≫ σ).hom.toAlgebra
  letI := α'.hom.toAlgebra
  letI := (α' ≫ σ').hom.toAlgebra
  letI := ιB.hom.toAlgebra
  refine {
    toRingHom := ιA.hom
    toRingHom_algebraMap := ?_
    algebraMap_toRingHom := ?_ }
  · intro a
    change ιA (α a) = α' a
    rfl
  · intro a
    change σ' (ιA a) = ιB (σ a)
    exact relativeConormalAffineLocalizationMap_algebraMap σ r a

private theorem conormal_toKaehler_natural
    {R₀ S T : Type u} [CommRing R₀] [CommRing S] [CommRing T]
    [Algebra R₀ S] [Algebra R₀ T] [Algebra S T] [IsScalarTower R₀ S T]
    (E : Algebra.Extension.{u} R₀ S) (Q : Algebra.Extension.{u} R₀ T) (f : E.Hom Q) :
    (KaehlerDifferential.map R₀ R₀ S T).comp E.toKaehler =
      (Q.toKaehler.restrictScalars S).comp (Algebra.Extension.CotangentSpace.map f) := by
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
  | tmul b y =>
    obtain ⟨y, rfl⟩ := KaehlerDifferential.tensorProductTo_surjective R₀ E.Ring y
    induction y using TensorProduct.inductionOn with
    | add x y hx hy =>
      simpa only [map_add, tmul_add] using congrArg₂ (· + ·) hx hy
    | tmul c a =>
      simp only [Derivation.tensorProductTo_tmul, tmul_smul, smul_tmul',
        LinearMap.coe_comp, LinearMap.coe_restrictScalars, Function.comp_apply,
        KaehlerDifferential.mapBaseChange_tmul, _root_.map_smul, KaehlerDifferential.map_D,
        Algebra.Extension.CotangentSpace.map_tmul, Algebra.Extension.Hom.toAlgHom_apply]
      rw [f.algebraMap_toRingHom, algebraMap_smul]

private theorem conormal_tensor_cotangent_square
    {R₀ S T : Type u} [CommRing R₀] [CommRing S] [CommRing T]
    [Algebra R₀ S] [Algebra R₀ T] [Algebra S T] [IsScalarTower R₀ S T]
    (E : Algebra.Extension.{u} R₀ S) (Q : Algebra.Extension.{u} R₀ T) (f : E.Hom Q)
    [Algebra E.Ring Q.Ring] (halg : algebraMap E.Ring Q.Ring = f.toRingHom)
    (hker : Function.Bijective ((f.mapKer halg).liftBaseChange Q.Ring))
    (hetale : f.toRingHom.FormallyEtale) :
    let eC := Algebra.Extension.tensorCotangent f halg hker
    let eT := Algebra.Extension.tensorCotangentSpaceOfFormallyEtale f hetale
    eT.toLinearMap.comp (E.cotangentComplex.baseChange T) =
      Q.cotangentComplex.comp eC.toLinearMap := by
  intro eC eT
  ext x
  change (1 : T) • Algebra.Extension.CotangentSpace.map f (E.cotangentComplex x) =
    Q.cotangentComplex ((1 : T) • Algebra.Extension.Cotangent.map f x)
  simp only [one_smul, Algebra.Extension.CotangentSpace.map_cotangentComplex]

private theorem conormal_tensor_toKaehler_square
    {R₀ S T : Type u} [CommRing R₀] [CommRing S] [CommRing T]
    [Algebra R₀ S] [Algebra R₀ T] [Algebra S T] [IsScalarTower R₀ S T]
    (E : Algebra.Extension.{u} R₀ S) (Q : Algebra.Extension.{u} R₀ T) (f : E.Hom Q)
    (hetale : f.toRingHom.FormallyEtale) [Algebra.FormallyEtale S T] :
    let eT := Algebra.Extension.tensorCotangentSpaceOfFormallyEtale f hetale
    let eD := KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R₀ S T
    eD.toLinearMap.comp (E.toKaehler.baseChange T) = Q.toKaehler.comp eT.toLinearMap := by
  intro eT eD
  ext y
  simp only [TensorProduct.AlgebraTensorModule.curry_apply, TensorProduct.curry_apply,
    LinearMap.restrictScalars_apply]
  change eD (E.toKaehler.baseChange T ((1 : T) ⊗ₜ[S] y)) =
    Q.toKaehler (eT ((1 : T) ⊗ₜ[S] y))
  rw [LinearMap.baseChange_tmul]
  change KaehlerDifferential.mapBaseChange R₀ S T ((1 : T) ⊗ₜ[S] E.toKaehler y) =
    Q.toKaehler ((1 : T) • Algebra.Extension.CotangentSpace.map f y)
  rw [KaehlerDifferential.mapBaseChange_tmul]
  simp only [one_smul]
  exact LinearMap.congr_fun (conormal_toKaehler_natural E Q f) y

private theorem conormal_extension_kernel_baseChange
    {R₀ S T : Type u} [CommRing R₀] [CommRing S] [CommRing T]
    [Algebra R₀ S] [Algebra R₀ T] [Algebra S T]
    (E : Algebra.Extension.{u} R₀ S) (Q : Algebra.Extension.{u} R₀ T) (f : E.Hom Q)
    [Algebra E.Ring Q.Ring] (halg : algebraMap E.Ring Q.Ring = f.toRingHom)
    (M : Submonoid E.Ring) [IsLocalization M Q.Ring]
    [IsLocalization (M.map (algebraMap E.Ring S)) T] :
    Function.Bijective ((f.mapKer halg).liftBaseChange Q.Ring) := by
  let g : Q.Ring →+* T :=
    IsLocalization.map T (algebraMap E.Ring S) (Submonoid.le_comap_map M)
  have hg : algebraMap Q.Ring T = g := by
    refine IsLocalization.ringHom_ext M (RingHom.ext fun x => ?_)
    change algebraMap Q.Ring T (algebraMap E.Ring Q.Ring x) =
      g (algebraMap E.Ring Q.Ring x)
    rw [IsLocalization.map_eq]
    exact (congrArg (algebraMap Q.Ring T) (RingHom.congr_fun halg x)).trans
      (f.algebraMap_toRingHom x)
  let e : RingHom.ker g ≃ₗ[Q.Ring] Q.ker :=
    LinearEquiv.ofEq _ _ (congrArg RingHom.ker hg).symm
  have hf : f.mapKer halg = (e.restrictScalars E.Ring).toLinearMap.comp
      (RingHom.toKerIsLocalization Q.Ring T (algebraMap E.Ring S)
        (Submonoid.le_comap_map M)) := by
    ext x
    exact (RingHom.congr_fun halg x.val).symm
  let hloc := RingHom.toKerIsLocalization_isLocalizedModule
    (S := Q.Ring) (M := M) T (algebraMap E.Ring S) rfl
  let : IsLocalizedModule M (f.mapKer halg) := by
    rw [hf]
    exact IsLocalizedModule.of_linearEquiv M _ (e.restrictScalars E.Ring)
  exact IsLocalizedModule.isBaseChange M Q.Ring (f.mapKer halg)

private def conormal_linear_complex_iso
    {R A B A' B' : CommRingCat.{u}} (α : R ⟶ A) (σ : A ⟶ B)
    (hσ : Function.Surjective σ) (α' : R ⟶ A') (σ' : A' ⟶ B')
    (hσ' : Function.Surjective σ') (μ : B ⟶ B') :
    letI := α.hom.toAlgebra
    letI := (α ≫ σ).hom.toAlgebra
    letI := α'.hom.toAlgebra
    letI := (α' ≫ σ').hom.toAlgebra
    letI := μ.hom.toAlgebra
    let E := relativeConormalAffineExtension α σ hσ
    let Q := relativeConormalAffineExtension α' σ' hσ'
    (eC : B' ⊗[B] E.Cotangent ≃ₗ[B'] Q.Cotangent) →
    (eT : B' ⊗[B] E.CotangentSpace ≃ₗ[B'] Q.CotangentSpace) →
    (eD : B' ⊗[B] Ω[B⁄R] ≃ₗ[B'] Ω[B'⁄R]) →
    eT.toLinearMap.comp (E.cotangentComplex.baseChange B') =
      Q.cotangentComplex.comp eC.toLinearMap →
    eD.toLinearMap.comp (E.toKaehler.baseChange B') =
      Q.toKaehler.comp eT.toLinearMap →
    ((relativeConormalAffineLinearComplex α σ hσ).map (ModuleCat.extendScalars μ.hom) ≅
      relativeConormalAffineLinearComplex α' σ' hσ') := by
  intro E Q eC eT eD hF hG
  letI := α.hom.toAlgebra
  letI := (α ≫ σ).hom.toAlgebra
  letI := α'.hom.toAlgebra
  letI := (α' ≫ σ').hom.toAlgebra
  letI := μ.hom.toAlgebra
  refine ShortComplex.isoMk eC.toModuleIso eT.toModuleIso eD.toModuleIso ?_ ?_
  · apply ModuleCat.hom_ext
    exact hF.symm
  · apply ModuleCat.hom_ext
    simp only [relativeConormalAffineLinearComplex, ShortComplex.map_g, ModuleCat.hom_comp,
      ModuleCat.extendScalars, ModuleCat.ExtendScalars.map', ModuleCat.hom_ofHom]
    dsimp only [relativeConormalAffineLinearG]
    simp only [LinearEquiv.toModuleIso, ModuleCat.hom_ofHom]
    dsimp only [E, Q] at hG
    apply LinearMap.ext
    intro x
    exact LinearMap.congr_fun hG.symm x

private def conormal_sheaf_complex_pullback_iso
    {S T : CommRingCat.{u}} (μ : S ⟶ T)
    (C : ShortComplex (Spec S).Modules) (P : ShortComplex (ModuleCat.{u} S))
    (D : ShortComplex (Spec T).Modules) (Q : ShortComplex (ModuleCat.{u} T))
    (e : C ≅ P.map (tilde.functor S)) (e' : D ≅ Q.map (tilde.functor T))
    (a : P.map (ModuleCat.extendScalars μ.hom) ≅ Q) :
    C.map (pullback (Spec.map μ)) ≅ D := by
  let e₁ : C.map (pullback (Spec.map μ)) ≅
      (P.map (tilde.functor S)).map (pullback (Spec.map μ)) :=
    (pullback (Spec.map μ)).mapShortComplex.mapIso e
  let e₂ : (P.map (tilde.functor S)).map (pullback (Spec.map μ)) ≅
      (P.map (ModuleCat.extendScalars μ.hom)).map (tilde.functor T) :=
    P.mapNatIso (tildePullbackIso μ)
  let e₃ : (P.map (ModuleCat.extendScalars μ.hom)).map (tilde.functor T) ≅
      Q.map (tilde.functor T) :=
    (tilde.functor T).mapShortComplex.mapIso a
  exact e₁ ≪≫ e₂ ≪≫ e₃ ≪≫ e'.symm

private def conormal_sheaf_complex_restrict_iso
    {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
    (C : ShortComplex Y.Modules) (D : ShortComplex X.Modules)
    (e : C.map (pullback j) ≅ D) : C.map (restrictFunctor j) ≅ D :=
  C.mapNatIso (restrictFunctorIsoPullback j) ≪≫ e

/-- Native scalar extension identifies the original localized module sequence. -/
def relativeConormalAffineLinearLocalizationIso (r : A) :
    let A' := CommRingCat.of (Localization.Away r)
    let B' := CommRingCat.of (Localization.Away (σ r))
    let α' := α ≫ CommRingCat.ofHom (algebraMap A A')
    let σ' := relativeConormalAffineLocalizationMap σ r
    (relativeConormalAffineLinearComplex α σ hσ).map
      (ModuleCat.extendScalars (algebraMap B B')) ≅
    relativeConormalAffineLinearComplex α' σ'
      (relativeConormalAffineLocalizationMap_surjective σ hσ r) := by
  intro A' B' α' σ'
  let ιA : A →+* A' := algebraMap A A'
  let ιB : B →+* B' := algebraMap B B'
  have hAetale : ιA.FormallyEtale := RingHom.formallyEtale_algebraMap.mpr
    (Algebra.FormallyEtale.of_isLocalization (Submonoid.powers r))
  have hBetale : ιB.FormallyEtale := RingHom.formallyEtale_algebraMap.mpr
    (Algebra.FormallyEtale.of_isLocalization (Submonoid.powers (σ r)))
  have hAloc : @IsLocalization A _ (Submonoid.powers r) A' _ ιA.toAlgebra := by
    rw [show ιA.toAlgebra = (inferInstanceAs (Algebra A A')) from toAlgebra_algebraMap]
    infer_instance
  have hBloc : @IsLocalization B _ (Submonoid.powers (σ r)) B' _ ιB.toAlgebra := by
    rw [show ιB.toAlgebra = (inferInstanceAs (Algebra B B')) from toAlgebra_algebraMap]
    infer_instance
  letI : Algebra R A := α.hom.toAlgebra
  letI : Algebra R B := (α ≫ σ).hom.toAlgebra
  let aRA' : Algebra R A' := α'.hom.toAlgebra
  let aRB' : Algebra R B' := (α' ≫ σ').hom.toAlgebra
  let aBB' : Algebra B B' := ιB.toAlgebra
  letI : Algebra R A' := aRA'
  letI : Algebra R B' := aRB'
  letI : Algebra B B' := aBB'
  letI : Module R A' := @Algebra.toModule R A' _ _ aRA'
  letI : Module R B' := @Algebra.toModule R B' _ _ aRB'
  letI : Module B B' := @Algebra.toModule B B' _ _ aBB'
  letI : SMul R A' := aRA'.toSMul
  letI : SMul R B' := aRB'.toSMul
  letI : SMul B B' := aBB'.toSMul
  let : IsScalarTower R B B' := IsScalarTower.of_algebraMap_eq fun t =>
    relativeConormalAffineLocalizationMap_algebraMap σ r (α t)
  let E := relativeConormalAffineExtension α σ hσ
  let Q := relativeConormalAffineExtension α' σ'
    (relativeConormalAffineLocalizationMap_surjective σ hσ r)
  let f := relativeConormalAffineLocalizationExtensionHom α σ hσ r
  letI := f.toRingHom.toAlgebra
  letI : Module E.Ring Q.Ring := Algebra.toModule
  letI : @IsLocalization E.Ring _ (Submonoid.powers (show E.Ring from r)) Q.Ring _
      f.toRingHom.toAlgebra := by
    have hι : f.toRingHom = ιA := rfl
    change @IsLocalization A _ (Submonoid.powers r) A' _ f.toRingHom.toAlgebra
    rw [hι]
    exact hAloc
  letI : @IsLocalization B _
      ((Submonoid.powers (show E.Ring from r)).map (algebraMap E.Ring B)) B' _ aBB' := by
    change @IsLocalization B _ ((Submonoid.powers r).map σ.hom) B' _ aBB'
    rw [Submonoid.map_powers]
    exact hBloc
  have hker : Function.Bijective ((f.mapKer (by rfl)).liftBaseChange Q.Ring) :=
    private_decl% (conormal_extension_kernel_baseChange (R₀ := R) (S := B) (T := B')
      E Q f (by rfl) (Submonoid.powers (show E.Ring from r)))
  have hetale : f.toRingHom.FormallyEtale := hAetale
  let : Algebra.FormallyEtale B B' := hBetale
  let eC := Algebra.Extension.tensorCotangent f (by rfl) hker
  let eT := Algebra.Extension.tensorCotangentSpaceOfFormallyEtale f hetale
  let eD := KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R B B'
  have hfirst : eT.toLinearMap.comp (E.cotangentComplex.baseChange B') =
      Q.cotangentComplex.comp eC.toLinearMap :=
    private_decl% (conormal_tensor_cotangent_square (R₀ := R) (S := B) (T := B')
      E Q f (by rfl) hker hetale)
  have hsecond : eD.toLinearMap.comp (E.toKaehler.baseChange B') =
      Q.toKaehler.comp eT.toLinearMap :=
    private_decl% (conormal_tensor_toKaehler_square (R₀ := R) (S := B) (T := B') E Q f hetale)
  exact private_decl% (conormal_linear_complex_iso α σ hσ α' σ'
    (relativeConormalAffineLocalizationMap_surjective σ hσ r)
    (CommRingCat.ofHom ιB) eC eT eD hfirst hsecond)

/-- Pullback along the original target principal localization preserves this conormal sequence. -/
def relativeConormalAffinePullbackLocalizationIso (r : A) :
    let A' := CommRingCat.of (Localization.Away r)
    let B' := CommRingCat.of (Localization.Away (σ r))
    let α' := α ≫ CommRingCat.ofHom (algebraMap A A')
    let σ' := relativeConormalAffineLocalizationMap σ r
    (relativeConormalAffineComplex α σ hσ).map
      (pullback (Spec.map (CommRingCat.ofHom (algebraMap B B')))) ≅
    relativeConormalAffineComplex α' σ'
      (relativeConormalAffineLocalizationMap_surjective σ hσ r) := by
  intro A' B' α' σ'
  let μ : B ⟶ B' := CommRingCat.ofHom (algebraMap B B')
  exact private_decl% (conormal_sheaf_complex_pullback_iso μ
    (relativeConormalAffineComplex α σ hσ) (relativeConormalAffineLinearComplex α σ hσ)
    (relativeConormalAffineComplex α' σ'
      (relativeConormalAffineLocalizationMap_surjective σ hσ r))
    (relativeConormalAffineLinearComplex α' σ'
      (relativeConormalAffineLocalizationMap_surjective σ hσ r))
    (relativeConormalAffineComplexIso α σ hσ)
    (relativeConormalAffineComplexIso α' σ'
      (relativeConormalAffineLocalizationMap_surjective σ hσ r))
    (relativeConormalAffineLinearLocalizationIso α σ hσ r))

/-- The native open restriction along the original principal localization. -/
def relativeConormalAffineRestrictionLocalizationIso (r : A) :
    let A' := CommRingCat.of (Localization.Away r)
    let B' := CommRingCat.of (Localization.Away (σ r))
    let α' := α ≫ CommRingCat.ofHom (algebraMap A A')
    let σ' := relativeConormalAffineLocalizationMap σ r
    (relativeConormalAffineComplex α σ hσ).map
      (restrictFunctor (Spec.map (CommRingCat.ofHom (algebraMap B B')))) ≅
    relativeConormalAffineComplex α' σ'
      (relativeConormalAffineLocalizationMap_surjective σ hσ r) := by
  intro A' B' α' σ'
  let μ : B ⟶ B' := CommRingCat.ofHom (algebraMap B B')
  exact private_decl% (conormal_sheaf_complex_restrict_iso (Spec.map μ)
    (relativeConormalAffineComplex α σ hσ)
    (relativeConormalAffineComplex α' σ'
      (relativeConormalAffineLocalizationMap_surjective σ hσ r))
    (relativeConormalAffinePullbackLocalizationIso α σ hσ r))

open scoped ChangeOfRings

/-- The original kernel class after principal localization. -/
def relativeConormalAffineLocalizedClass (r : A) (x : RingHom.ker σ.hom) :
    let A' := CommRingCat.of (Localization.Away r)
    let α' := α ≫ CommRingCat.ofHom (algebraMap A A')
    let σ' := relativeConormalAffineLocalizationMap σ r
    relativeConormalAffineModule α' σ'
      (relativeConormalAffineLocalizationMap_surjective σ hσ r) := by
  intro A' α' σ'
  apply relativeConormalAffineClass α' σ'
    (relativeConormalAffineLocalizationMap_surjective σ hσ r)
  refine ⟨algebraMap A A' x.val, ?_⟩
  change relativeConormalAffineLocalizationMap σ r (algebraMap A A' x.val) = 0
  rw [relativeConormalAffineLocalizationMap_algebraMap]
  simp only [show σ x.val = 0 from x.property, map_zero]

/-- The literal original class image under the native tensor comparison. -/
theorem relativeConormalAffineLinearLocalizationIso_class
    (r : A) (x : RingHom.ker σ.hom) :
    (relativeConormalAffineLinearLocalizationIso α σ hσ r).hom.τ₁
      ((1 : Localization.Away (σ r)) ⊗ₜ[B, algebraMap B (Localization.Away (σ r))]
        relativeConormalAffineClass α σ hσ x) =
        relativeConormalAffineLocalizedClass α σ hσ r x := by
  let A' := CommRingCat.of (Localization.Away r)
  let B' := CommRingCat.of (Localization.Away (σ r))
  let α' := α ≫ CommRingCat.ofHom (algebraMap A A')
  let σ' := relativeConormalAffineLocalizationMap σ r
  let : Algebra R A := α.hom.toAlgebra
  let : Algebra R B := (α ≫ σ).hom.toAlgebra
  let aRA' : Algebra R A' := α'.hom.toAlgebra
  let aRB' : Algebra R B' := (α' ≫ σ').hom.toAlgebra
  let aBB' : Algebra B B' := (algebraMap B B').toAlgebra
  let : Algebra R A' := aRA'
  let : Algebra R B' := aRB'
  let : Algebra B B' := aBB'
  let : Module R A' := @Algebra.toModule R A' _ _ aRA'
  let : Module R B' := @Algebra.toModule R B' _ _ aRB'
  let : Module B B' := @Algebra.toModule B B' _ _ aBB'
  let : SMul R A' := aRA'.toSMul
  let : SMul R B' := aRB'.toSMul
  let : SMul B B' := aBB'.toSMul
  let : IsScalarTower R R B' := IsScalarTower.of_algebraMap_eq' rfl
  change (1 : B') • Algebra.Extension.Cotangent.map
    (relativeConormalAffineLocalizationExtensionHom α σ hσ r)
    (relativeConormalAffineClass α σ hσ x) = _
  rw [one_smul]
  rfl

/-- The literal middle differential image under the same native tensor comparison. -/
theorem relativeConormalAffineLinearLocalizationIso_middle_d (r : A) (a : A) :
    letI : Algebra A B := σ.hom.toAlgebra
    let A' := CommRingCat.of (Localization.Away r)
    let B' := CommRingCat.of (Localization.Away (σ r))
    let α' := α ≫ CommRingCat.ofHom (algebraMap A A')
    let σ' := relativeConormalAffineLocalizationMap σ r
    letI : Algebra A' B' := σ'.hom.toAlgebra
    (relativeConormalAffineLinearLocalizationIso α σ hσ r).hom.τ₂
      ((1 : B') ⊗ₜ[B, algebraMap B B']
        ((1 : B) ⊗ₜ[A] CommRingCat.KaehlerDifferential.d (f := α) a)) =
      (1 : B') ⊗ₜ[A']
        CommRingCat.KaehlerDifferential.d (f := α') (algebraMap A A' a) := by
  intro A' B' α' σ'
  let : Algebra R A := α.hom.toAlgebra
  let : Algebra R B := (α ≫ σ).hom.toAlgebra
  let aRA' : Algebra R A' := α'.hom.toAlgebra
  let aRB' : Algebra R B' := (α' ≫ σ').hom.toAlgebra
  let aBB' : Algebra B B' := (algebraMap B B').toAlgebra
  let : Algebra R A' := aRA'
  let : Algebra R B' := aRB'
  let : Algebra B B' := aBB'
  let : Module R A' := @Algebra.toModule R A' _ _ aRA'
  let : Module R B' := @Algebra.toModule R B' _ _ aRB'
  let : Module B B' := @Algebra.toModule B B' _ _ aBB'
  let : SMul R A' := aRA'.toSMul
  let : SMul R B' := aRB'.toSMul
  let : SMul B B' := aBB'.toSMul
  let : IsScalarTower R R B' := IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra A B := σ.hom.toAlgebra
  let : Algebra A' B' := σ'.hom.toAlgebra
  change (1 : B') • Algebra.Extension.CotangentSpace.map
    (relativeConormalAffineLocalizationExtensionHom α σ hσ r)
    ((1 : B) ⊗ₜ[(relativeConormalAffineExtension α σ hσ).Ring]
      KaehlerDifferential.D R (relativeConormalAffineExtension α σ hσ).Ring a) = _
  rw [one_smul, Algebra.Extension.CotangentSpace.map_tmul, map_one]
  rfl

/-- The literal target differential image under the same native tensor comparison. -/
theorem relativeConormalAffineLinearLocalizationIso_right_d (r : A) (b : B) :
    let A' := CommRingCat.of (Localization.Away r)
    let B' := CommRingCat.of (Localization.Away (σ r))
    let α' := α ≫ CommRingCat.ofHom (algebraMap A A')
    let σ' := relativeConormalAffineLocalizationMap σ r
    (relativeConormalAffineLinearLocalizationIso α σ hσ r).hom.τ₃
      ((1 : B') ⊗ₜ[B, algebraMap B B'] CommRingCat.KaehlerDifferential.d (f := α ≫ σ) b) =
      CommRingCat.KaehlerDifferential.d (f := α' ≫ σ') (algebraMap B B' b) := by
  intro A' B' α' σ'
  let : Algebra R A := α.hom.toAlgebra
  let : Algebra R B := (α ≫ σ).hom.toAlgebra
  let aRA' : Algebra R A' := α'.hom.toAlgebra
  let aRB' : Algebra R B' := (α' ≫ σ').hom.toAlgebra
  let aBB' : Algebra B B' := (algebraMap B B').toAlgebra
  let : Algebra R A' := aRA'
  let : Algebra R B' := aRB'
  let : Algebra B B' := aBB'
  let : Module R A' := @Algebra.toModule R A' _ _ aRA'
  let : Module R B' := @Algebra.toModule R B' _ _ aRB'
  let : Module B B' := @Algebra.toModule B B' _ _ aBB'
  let : SMul R A' := aRA'.toSMul
  let : SMul R B' := aRB'.toSMul
  let : SMul B B' := aBB'.toSMul
  let : IsScalarTower R R B' := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower R B B' := IsScalarTower.of_algebraMap_eq fun t =>
    relativeConormalAffineLocalizationMap_algebraMap σ r (α t)
  change KaehlerDifferential.mapBaseChange R B B'
    ((1 : B') ⊗ₜ[B] KaehlerDifferential.D R B b) = _
  rw [KaehlerDifferential.mapBaseChange_tmul, one_smul, KaehlerDifferential.map_D]
  rfl

/-- The whole original first arrow commutes with native open restriction. -/
theorem relativeConormalAffineRestrictionLocalizationIso_f (r : A) :
    let A' := CommRingCat.of (Localization.Away r)
    let B' := CommRingCat.of (Localization.Away (σ r))
    let α' := α ≫ CommRingCat.ofHom (algebraMap A A')
    let σ' := relativeConormalAffineLocalizationMap σ r
    let τ := relativeConormalAffineRestrictionLocalizationIso α σ hσ r
    (restrictFunctor (Spec.map (CommRingCat.ofHom (algebraMap B B')))).map
        (relativeConormalAffineComplex α σ hσ).f ≫ τ.hom.τ₂ =
      τ.hom.τ₁ ≫ (relativeConormalAffineComplex α' σ'
        (relativeConormalAffineLocalizationMap_surjective σ hσ r)).f := by
  intro A' B' α' σ' τ
  exact τ.hom.comm₁₂.symm

/-- The whole original second arrow commutes with native open restriction. -/
theorem relativeConormalAffineRestrictionLocalizationIso_g (r : A) :
    let A' := CommRingCat.of (Localization.Away r)
    let B' := CommRingCat.of (Localization.Away (σ r))
    let α' := α ≫ CommRingCat.ofHom (algebraMap A A')
    let σ' := relativeConormalAffineLocalizationMap σ r
    let τ := relativeConormalAffineRestrictionLocalizationIso α σ hσ r
    (restrictFunctor (Spec.map (CommRingCat.ofHom (algebraMap B B')))).map
        (relativeConormalAffineComplex α σ hσ).g ≫ τ.hom.τ₃ =
      τ.hom.τ₂ ≫ (relativeConormalAffineComplex α' σ'
        (relativeConormalAffineLocalizationMap_surjective σ hσ r)).g := by
  intro A' B' α' σ' τ
  exact τ.hom.comm₂₃.symm

end AlgebraicGeometry.Scheme.Modules.Differentials
