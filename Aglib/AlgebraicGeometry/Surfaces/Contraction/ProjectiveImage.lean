/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Surfaces.Contraction.ProjectiveSections
public import Aglib.AlgebraicGeometry.ProjectiveSpace.FromSections.Naturality
public import Aglib.AlgebraicGeometry.Picard.Comparison.Endomorphisms
public import Aglib.AlgebraicGeometry.ProjectiveSpace.GlobalFunctions
public import Aglib.AlgebraicGeometry.Modules.Tensor.Monoidal.Sections
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import Aglib.AlgebraicGeometry.Modules.Stalk.Exactness
public import Aglib.AlgebraicGeometry.Modules.Pullback.FlatMorphism

/-!
# The actual projective image of exceptional-curve section systems

The proved Cartier finite-family theorem constructs the generating family.
Coherent cohomological finiteness adds a finite family spanning all original
global sections over the structural base ring. Original mixed ample sections
are retained as literal coordinates. The native section constructor gives the
actual projective morphism, its pullback of `O(1)`, and every original coordinate
map. The target below is its actual scheme-theoretic image.

The image construction alone does not identify its exceptional fibre or prove
that the complement map is an isomorphism. These properties require the actual
restriction, coordinate-recovery and first-order ideal comparisons.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Invertible
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent MvPolynomial

namespace AlgebraicGeometry.Scheme.Surfaces.Contraction

universe u

variable {A : Type u} [CommRing A] [IsNoetherianRing A]
  {ι : Type u} {X : Scheme.{u}}
  (p : X ⟶ ProjectiveSpace A ι) [IsClosedImmersion p]

/-- The original base-ring map belonging to the specified projective embedding. -/
abbrev projectiveStructuralScalars : A →+* Γ(X, ⊤) :=
  (p ≫ toSpec A ι).appTop.hom.comp (Scheme.ΓSpecIso (.of A)).inv.hom

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The canonical module on original global sections, with the original base action. -/
abbrev projectiveGlobalSectionsModule (M : X.Modules) : Module A Γ(M, ⊤) := by
  change Module A (M.val.obj (op ⊤))
  exact Module.compHom _ (projectiveStructuralScalars p)

set_option backward.isDefEq.respectTransparency false in
/-- A family spans the actual global sections for the original structural action. -/
def sectionFamilySpans (L : LineBundle X) {J : Type u}
    (s : J → (𝟙_ X.Modules ⟶ (show X.Modules from L.val))) : Prop :=
  let _ := projectiveGlobalSectionsModule p L.val
  Submodule.span A (Set.range fun j => unitHomGlobalSectionsEquiv X L.val (s j)) = ⊤

set_option backward.isDefEq.respectTransparency false in
/-- Coherent finiteness controls all original global sections of the actual line bundle. -/
theorem lineBundleGlobalSections_finite (r : ℕ) (e : ι ≃ Fin (r + 1))
    (L : LineBundle X) :
    let _ := projectiveGlobalSectionsModule p L.val
    Module.Finite A Γ(L.val, ⊤) := by
  let α := projectiveStructuralScalars p
  let := Cohomology.moduleCohomologyModuleOfHom X α L.val 0
  let := projectiveGlobalSectionsModule p L.val
  let := lineBundle_isFinitePresentation X L
  have hL : affineLocallyFiniteType X L.val :=
    affineLocallyFiniteType_of_finitePresentation L.val
  let : Module.Finite A (Sheaf.H.{u + 1} (Cohomology.moduleAddSheaf X L.val) 0) :=
    Cohomology.projectiveEmbeddingCohomology_finite A ι p r e L.val hL 0
  exact Module.Finite.equiv (Cohomology.moduleH0EquivOfHom X α L.val)

set_option backward.isDefEq.respectTransparency false in
/-- A finite base-ring family of actual global sections is realized by the original
morphisms from the structure module. -/
theorem exists_finite_base_section_family (r : ℕ) (e : ι ≃ Fin (r + 1))
    (L : LineBundle X) :
    ∃ (m : ℕ) (s : ULift.{u} (Fin m) →
      (𝟙_ X.Modules ⟶ (show X.Modules from L.val))), sectionFamilySpans p L s := by
  let := projectiveGlobalSectionsModule p L.val
  let : Module.Finite A Γ(L.val, ⊤) := lineBundleGlobalSections_finite p r e L
  obtain ⟨m, a, ha⟩ := Module.Finite.exists_fin (R := A) (M := Γ(L.val, ⊤))
  refine ⟨m, fun j => (unitHomGlobalSectionsEquiv X L.val).symm (a j.down), ?_⟩
  dsimp only [sectionFamilySpans]
  simp only [Equiv.apply_symm_apply]
  have hrange : Set.range (fun j : ULift.{u} (Fin m) => a j.down) = Set.range a := by
    ext x
    constructor
    · rintro ⟨j, rfl⟩
      exact ⟨j.down, rfl⟩
    · rintro ⟨j, rfl⟩
      exact ⟨⟨j⟩, rfl⟩
  rw [hrange]
  exact ha

/-- The actual mixed polynomial `X_a^(n-1) X_b`, with its proved homogeneous degree. -/
def mixedPolynomial (n : ℕ) (hn : 1 ≤ n) (a b : ι) : homogeneousSubmodule ι A n :=
  ⟨MvPolynomial.X a ^ (n - 1) * MvPolynomial.X b, by
    simpa only [mem_homogeneousSubmodule, one_mul, Nat.sub_add_cancel hn] using
      ((isHomogeneous_X A a).pow (n - 1)).mul (isHomogeneous_X A b)⟩

/-- The original native twist section belonging to the mixed homogeneous polynomial. -/
def mixedTwistSection (n : ℕ) (hn : 1 ≤ n) (a b : ι) :
    𝟙_ (ProjectiveSpace A ι).Modules ⟶ twistingSheaf A ι (n : ℤ) :=
  (unitHomGlobalSectionsEquiv (ProjectiveSpace A ι) (twistingSheaf A ι (n : ℤ))).symm
    (homogeneousSection A ι n (mixedPolynomial (A := A) n hn a b))

variable {k : Type u} [CommRing k]
  (i : ProjectiveSpace k (ULift.{u} (Fin 2)) ⟶ X) [IsClosedImmersion i]
  (hI : IsLocallyRankOne X (Hom.idealModule i)) (H : LineBundle X)
  (eP : H.val ≅ (Scheme.Modules.pullback p).obj (twistingSheaf A ι 1))
  (d : ℕ)

set_option backward.isDefEq.respectTransparency false in
/-- The original mixed ample section, followed by the actual common Cartier inclusion. -/
def mixedCartierSection (n : ℕ) (hn : 1 ≤ n) (a b : ι) :
    𝟙_ X.Modules ⟶ (show X.Modules from (cartierPowerTwist i hI H n (n * d)).val) := by
  let T : (ProjectiveSpace A ι).Modules ⥤ X.Modules := Scheme.Modules.pullback p
  let eU : T.obj (𝟙_ (ProjectiveSpace A ι).Modules) ≅ 𝟙_ X.Modules := pullbackUnitIso p
  exact eU.inv ≫ T.map (mixedTwistSection (A := A) n hn a b) ≫
    (projectivePowerIso p H eP n).inv ≫ cartierPowerInclusion i hI H n (n * d)

/-- A constructed actual section system. The projective morphism and its image
are definitions from this system; no map or contraction is a field. -/
structure CartierProjectivePresentation (n : ℕ) (hn : 1 ≤ n) where
  /-- The original finite coordinate index. -/
  index : Type u
  /-- Finiteness of that actual index. -/
  finiteIndex : Finite index
  /-- The original morphisms from the structure module to the actual Cartier coefficient. -/
  sections : index → (𝟙_ X.Modules ⟶
    (show X.Modules from (cartierPowerTwist i hI H n (n * d)).val))
  /-- The actual free map is epimorphic, as proved from Cartier cohomology. -/
  epiSections : Epi (Sigma.desc sections)
  /-- The same family spans every global section over the original base ring. -/
  spansSections : sectionFamilySpans p (cartierPowerTwist i hI H n (n * d)) sections
  /-- The original mixed ample coordinates occur at these literal positions. -/
  mixedIndex : (ι × ι) ↪ index
  /-- Their original section maps are unchanged. -/
  mixedEq : ∀ a, sections (mixedIndex a) =
    mixedCartierSection p i hI H eP d n hn a.1 a.2

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The cohomology theorem constructs the generating system, augmented by all
base-ring global generators and the prescribed original mixed ample coordinates. -/
theorem exists_cartier_projective_presentation
    (r : ℕ) (e : ι ≃ Fin (r + 1))
    (eI : (Scheme.Modules.pullback i).obj (Hom.idealModule i) ≅
      twistingSheaf k (ULift.{u} (Fin 2)) 1)
    (eH : (Scheme.Modules.pullback i).obj H.val ≅
      twistingSheaf k (ULift.{u} (Fin 2)) (d : ℤ)) :
    ∃ (B : ℕ) (hB : 1 ≤ B), ∀ (n : ℕ) (hn : B ≤ n),
      Nonempty (CartierProjectivePresentation p i hI H eP d n (hB.trans hn)) := by
  let : Finite ι := Finite.of_equiv _ e.symm
  obtain ⟨B, hB, hgen⟩ := exists_cartier_finite_section_families p i r e H eP hI d eI eH
  refine ⟨B, hB, fun n hn => ?_⟩
  let hn1 : 1 ≤ n := hB.trans hn
  let L := cartierPowerTwist i hI H n (n * d)
  obtain ⟨J, hJ, s, hs⟩ := hgen n hn (n * d) le_rfl
  let : Finite J := hJ
  obtain ⟨m, b, hb⟩ := exists_finite_base_section_family p r e L
  let extra : ULift.{u} (Fin m) ⊕ (ι × ι) → (𝟙_ X.Modules ⟶ L.val) :=
    Sum.elim b (fun a => mixedCartierSection p i hI H eP d n hn1 a.1 a.2)
  obtain ⟨v, hv, hextra⟩ := Cohomology.CartierCurve.augment_finite_family s hs extra
  refine ⟨⟨J ⊕ (ULift.{u} (Fin m) ⊕ (ι × ι)), inferInstance, v, hv, ?_,
    ⟨fun a => Sum.inr (Sum.inr a), fun _ _ h => Sum.inr_injective (Sum.inr_injective h)⟩,
    ?_⟩⟩
  · let := projectiveGlobalSectionsModule p L.val
    change Submodule.span A (Set.range fun j => unitHomGlobalSectionsEquiv X L.val (v j)) = ⊤
    have hbspan : Submodule.span A
        (Set.range fun j => unitHomGlobalSectionsEquiv X L.val (b j)) = ⊤ := hb
    apply top_unique
    rw [← hbspan]
    apply Submodule.span_mono
    rintro x ⟨a, rfl⟩
    refine ⟨Sum.inr (Sum.inl a), ?_⟩
    have heq : v (Sum.inr (Sum.inl a)) = b a := by
      simpa only [extra, Sum.elim_inl] using hextra (Sum.inl a)
    exact congrArg (unitHomGlobalSectionsEquiv X L.val) heq
  · intro a
    change v (Sum.inr (Sum.inr a)) = mixedCartierSection p i hI H eP d n hn1 a.1 a.2
    simpa only [extra, Sum.elim_inr] using hextra (Sum.inr a)

namespace CartierProjectivePresentation

variable {p i hI H eP d} {n : ℕ} {hn : 1 ≤ n}
  (F : CartierProjectivePresentation p i hI H eP d n hn)

/-- Use the constructed presentation's actual finite index locally. -/
local instance presentationFiniteIndex : Finite F.index := F.finiteIndex

/-- Use the constructed presentation's actual epimorphic free map locally. -/
local instance presentationEpiSections : Epi (Sigma.desc F.sections) := F.epiSections

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual native morphism constructed from the original section family. -/
def toProjective : X ⟶ ProjectiveSpace A F.index := by
  let : Epi (Sigma.desc F.sections) := F.epiSections
  exact FromSections.mapOfFiniteFamily (p ≫ toSpec A ι)
    (cartierPowerTwist i hI H n (n * d)).val
    (cartierPowerTwist i hI H n (n * d)).property F.sections

omit [IsNoetherianRing A] [IsClosedImmersion p] in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual structural triangle is unchanged. -/
@[reassoc]
theorem toProjective_toSpec : F.toProjective ≫ toSpec A F.index = p ≫ toSpec A ι := by
  let : Epi (Sigma.desc F.sections) := F.epiSections
  exact FromSections.mapOfFiniteFamily_toSpec (p ≫ toSpec A ι)
    (cartierPowerTwist i hI H n (n * d)).val
    (cartierPowerTwist i hI H n (n * d)).property F.sections

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Pullback of the native `O(1)` is the actual original Cartier coefficient. -/
def twistingPullbackIso :
    (Scheme.Modules.pullback F.toProjective).obj (twistingSheaf A F.index 1) ≅
      (cartierPowerTwist i hI H n (n * d)).val := by
  let : Epi (Sigma.desc F.sections) := F.epiSections
  exact FromSections.twistingPullbackIsoOfFiniteFamily (p ≫ toSpec A ι)
    (cartierPowerTwist i hI H n (n * d)).val
    (cartierPowerTwist i hI H n (n * d)).property F.sections

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The original pulled-back homogeneous coordinate map. -/
def coordinateMap (a : F.index) : 𝟙_ X.Modules ⟶
    (Scheme.Modules.pullback F.toProjective).obj (twistingSheaf A F.index 1) := by
  let : Epi (Sigma.desc F.sections) := F.epiSections
  exact FromSections.pulledCoordinateMapOfFiniteFamily (p ≫ toSpec A ι)
    (cartierPowerTwist i hI H n (n * d)).val
    (cartierPowerTwist i hI H n (n * d)).property F.sections a

omit [IsNoetherianRing A] [IsClosedImmersion p] in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Every actual coordinate map is exactly the prescribed original section map. -/
@[reassoc]
theorem coordinateMap_comp (a : F.index) :
    F.coordinateMap a ≫ F.twistingPullbackIso.hom = F.sections a := by
  let : Epi (Sigma.desc F.sections) := F.epiSections
  exact FromSections.pulledCoordinateMapOfFiniteFamily_comp (p ≫ toSpec A ι)
    (cartierPowerTwist i hI H n (n * d)).val
    (cartierPowerTwist i hI H n (n * d)).property F.sections a

omit [IsNoetherianRing A] [IsClosedImmersion p] in
/-- In particular all actual mixed ample section maps occur as original coordinates. -/
@[reassoc]
theorem coordinateMap_comp_mixed (a b : ι) :
    F.coordinateMap (F.mixedIndex (a, b)) ≫ F.twistingPullbackIso.hom =
      mixedCartierSection p i hI H eP d n hn a b := by
  rw [coordinateMap_comp, F.mixedEq]

/-- The actual scheme-theoretic image, defined by the original map's kernel ideal. -/
abbrev image : Scheme.{u} := F.toProjective.image

/-- The original canonical map to that actual image. -/
def toImage : X ⟶ F.image := F.toProjective.toImage

/-- Its original closed immersion into the original target projective scheme. -/
abbrev imageInclusion : F.image ⟶ ProjectiveSpace A F.index := F.toProjective.imageι

/-- The structural map of the actual image. -/
def imageStructureMap : F.image ⟶ Spec (.of A) := F.imageInclusion ≫ toSpec A F.index

omit [IsNoetherianRing A] [IsClosedImmersion p] in
/-- The image factorization retains the original projective morphism. -/
@[reassoc]
theorem toImage_imageInclusion : F.toImage ≫ F.imageInclusion = F.toProjective :=
  F.toProjective.toImage_imageι

omit [IsNoetherianRing A] [IsClosedImmersion p] in
/-- The image factorization retains the original structural morphism. -/
@[reassoc]
theorem toImage_toSpec : F.toImage ≫ F.imageStructureMap = p ≫ toSpec A ι := by
  calc
    F.toImage ≫ F.imageStructureMap =
        (F.toImage ≫ F.imageInclusion) ≫ toSpec A F.index := (Category.assoc _ _ _).symm
    _ = F.toProjective ≫ toSpec A F.index := by rw [toImage_imageInclusion]
    _ = p ≫ toSpec A ι := F.toProjective_toSpec

/-- The image is genuinely closed in the original projective scheme. -/
instance isClosedImmersionImageInclusion : IsClosedImmersion F.imageInclusion := inferInstance

omit [IsNoetherianRing A] [IsClosedImmersion p] in
/-- The actual image is proper over the original base. -/
theorem imageStructureMap_isProper : IsProper F.imageStructureMap := by
  unfold imageStructureMap
  infer_instance

omit [IsNoetherianRing A] in
/-- The constructed map is proper, by its actual triangle and separated projective target. -/
theorem toProjective_isProper (r : ℕ) (e : ι ≃ Fin (r + 1)) : IsProper F.toProjective := by
  let : Finite ι := Finite.of_equiv _ e.symm
  have : IsProper (F.toProjective ≫ toSpec A F.index) := by
    rw [F.toProjective_toSpec]
    infer_instance
  exact IsProper.of_comp F.toProjective (toSpec A F.index)

omit [IsNoetherianRing A] in
/-- The actual map to the scheme-theoretic image is proper. -/
theorem toImage_isProper (r : ℕ) (e : ι ≃ Fin (r + 1)) : IsProper F.toImage := by
  let : IsProper F.toProjective := F.toProjective_isProper r e
  have : IsProper (F.toImage ≫ F.imageInclusion) := by
    rw [F.toImage_imageInclusion]
    infer_instance
  exact IsProper.of_comp F.toImage F.imageInclusion

omit [IsNoetherianRing A] in
/-- Properness makes the original map onto its actual schematic image surjective. -/
theorem toImage_surjective (r : ℕ) (e : ι ≃ Fin (r + 1)) : Surjective F.toImage := by
  let : IsProper F.toProjective := F.toProjective_isProper r e
  let : IsProper F.toImage := F.toImage_isProper r e
  change Surjective F.toProjective.toImage
  infer_instance

end CartierProjectivePresentation

omit [IsNoetherianRing A] [IsClosedImmersion p] [IsClosedImmersion i] in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The original images span every quotient section when its original section map is onto. -/
theorem sectionFamilySpans_after_surjective (L : LineBundle X) {N : X.Modules}
    (g : (show X.Modules from L.val) ⟶ N)
    (hg : Function.Surjective (g.val.app (op ⊤))) {J : Type u}
    (s : J → (𝟙_ X.Modules ⟶ (show X.Modules from L.val)))
    (hs : sectionFamilySpans p L s) :
    let _ := projectiveGlobalSectionsModule p N
    Submodule.span A
      (Set.range fun j => unitHomGlobalSectionsEquiv X N (s j ≫ g)) = ⊤ := by
  let α := projectiveStructuralScalars p
  let := projectiveGlobalSectionsModule p L.val
  let := projectiveGlobalSectionsModule p N
  let φ : Γ(L.val, ⊤) →ₗ[A] Γ(N, ⊤) := {
    toFun := g.val.app (op ⊤)
    map_add' := fun x y => (g.val.app (op ⊤)).hom.map_add x y
    map_smul' := fun a x => by
      change (g.val.app (op ⊤)) (α a • x) = α a • (g.val.app (op ⊤)) x
      exact (g.val.app (op ⊤)).hom.map_smul (α a) x }
  have hspan : Submodule.span A
      (Set.range fun j => unitHomGlobalSectionsEquiv X L.val (s j)) = ⊤ := hs
  change Submodule.span A
    (Set.range fun j => φ (unitHomGlobalSectionsEquiv X L.val (s j))) = ⊤
  have himage :
      Set.range (fun j => φ (unitHomGlobalSectionsEquiv X L.val (s j))) =
        φ '' Set.range (fun j => unitHomGlobalSectionsEquiv X L.val (s j)) := by
    ext y
    constructor
    · rintro ⟨j, rfl⟩
      exact ⟨_, ⟨j, rfl⟩, rfl⟩
    · rintro ⟨x, ⟨j, rfl⟩, rfl⟩
      exact ⟨j, rfl⟩
  rw [himage, ← Submodule.map_span, hspan, Submodule.map_top]
  have hφ : Function.Surjective φ := hg
  exact LinearMap.range_eq_top.mpr hφ

omit [IsNoetherianRing A] [IsClosedImmersion p] [IsClosedImmersion i] in
/-- The actual original base action on the exceptional coefficient ring. -/
def exceptionalBaseHom : A →+* k :=
  (globalFunctionsRingEquiv k (ULift.{u} (Fin 2))).symm.toRingHom.comp
    (i.appTop.hom.comp (projectiveStructuralScalars p))

omit [IsNoetherianRing A] [IsClosedImmersion p] [IsClosedImmersion i] in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The original structural map of the exceptional curve factors through its actual k. -/
theorem exceptionalBaseHom_triangle :
    i ≫ p ≫ toSpec A ι = toSpec k (ULift.{u} (Fin 2)) ≫
      Spec.map (CommRingCat.ofHom (exceptionalBaseHom p i)) := by
  apply ext_to_Spec
  calc
    (Scheme.ΓSpecIso (.of A)).inv ≫ (i ≫ p ≫ toSpec A ι).appTop =
        CommRingCat.ofHom (exceptionalBaseHom p i) ≫
          (Scheme.ΓSpecIso (.of k)).inv ≫
            (toSpec k (ULift.{u} (Fin 2))).appTop := by
      rw [Scheme.Hom.comp_appTop]
      apply CommRingCat.hom_ext
      ext a
      change i.appTop (projectiveStructuralScalars p a) =
        ((toSpec k (ULift.{u} (Fin 2))).appTop.hom.comp
          (Scheme.ΓSpecIso (.of k)).inv.hom) (exceptionalBaseHom p i a)
      exact (coefficient_globalFunctionsRingEquiv_symm k (ULift.{u} (Fin 2))
        ((i.appTop.hom.comp (projectiveStructuralScalars p)) a)).symm
    _ = (Scheme.ΓSpecIso (.of A)).inv ≫
        (toSpec k (ULift.{u} (Fin 2)) ≫
          Spec.map (CommRingCat.ofHom (exceptionalBaseHom p i))).appTop := by
      rw [Scheme.Hom.comp_appTop]
      rw [← Scheme.ΓSpecIso_inv_naturality_assoc]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual first-order Cartier quotient, retaining the original restriction map. -/
def firstOrderQuotientIso
    (eI : (Scheme.Modules.pullback i).obj (Hom.idealModule i) ≅
      twistingSheaf k (ULift.{u} (Fin 2)) 1)
    (eH : (Scheme.Modules.pullback i).obj H.val ≅
      twistingSheaf k (ULift.{u} (Fin 2)) (d : ℤ))
    (n : ℕ) (hn : 2 ≤ n * d) :
    (cartierStepSequence i hI (cartierPowerTwist i hI H n (n * d - 2))).X₃ ≅
      (Scheme.Modules.pushforward i).obj (twistingSheaf k (ULift.{u} (Fin 2)) 1) := by
  change (Scheme.Modules.pushforward i).obj ((Scheme.Modules.pullback i).obj
    (cartierPowerTwist i hI H n (n * d - 2 + 1)).val) ≅ _
  refine (Scheme.Modules.pushforward i).mapIso
    (cartierTwistRestrictionIso i (cartierIdealLineBundle i hI)
      (tensorPowerLineBundle X H n) ((n : ℤ) * d) eI
      (tensorPowerRestrictionIso i H (d : ℤ) eH n) (n * d - 2 + 1) ≪≫ ?_)
  have hidx : n * d - 2 + 1 + 1 = n * d := by omega
  have hc : ((n * d - 2 + 1 : ℕ) : ℤ) + 1 = (n : ℤ) * d := by
    exact_mod_cast hidx
  exact eqToIso (congrArg (twistingSheaf k (ULift.{u} (Fin 2))) (by omega))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The original pair of coordinate sections on the native exceptional projective line. -/
def exceptionalCoordinate (a : ULift.{u} (Fin 2)) :
    𝟙_ (ProjectiveSpace k (ULift.{u} (Fin 2))).Modules ⟶
      twistingSheaf k (ULift.{u} (Fin 2)) 1 :=
  (unitHomGlobalSectionsEquiv _ _).symm
    (homogeneousSection k _ 1 (coordinatePower k _ 1 a))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Original exceptional coordinate maps, regarded as original quotient section maps on X. -/
def firstOrderQuotientCoordinate
    (eI : (Scheme.Modules.pullback i).obj (Hom.idealModule i) ≅
      twistingSheaf k (ULift.{u} (Fin 2)) 1)
    (eH : (Scheme.Modules.pullback i).obj H.val ≅
      twistingSheaf k (ULift.{u} (Fin 2)) (d : ℤ))
    (n : ℕ) (hn : 2 ≤ n * d) (a : ULift.{u} (Fin 2)) :
    𝟙_ X.Modules ⟶
      (cartierStepSequence i hI (cartierPowerTwist i hI H n (n * d - 2))).X₃ :=
  Hom.structureModuleMap i ≫
    (Scheme.Modules.pushforward i).map (exceptionalCoordinate (k := k) a) ≫
      (firstOrderQuotientIso i hI H d eI eH n hn).inv

include p eP in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Both original O(1) coordinates lift through the actual first-order restriction map. -/
theorem exists_firstOrder_coordinate_lifts
    (r : ℕ) (e : ι ≃ Fin (r + 1))
    (eI : (Scheme.Modules.pullback i).obj (Hom.idealModule i) ≅
      twistingSheaf k (ULift.{u} (Fin 2)) 1)
    (eH : (Scheme.Modules.pullback i).obj H.val ≅
      twistingSheaf k (ULift.{u} (Fin 2)) (d : ℤ)) :
    ∃ B : ℕ, ∀ (n : ℕ), B ≤ n → ∀ hn : 2 ≤ n * d,
      ∃ t : ULift.{u} (Fin 2) → (𝟙_ X.Modules ⟶
        (cartierStepSequence i hI (cartierPowerTwist i hI H n (n * d - 2))).X₂),
        ∀ a, t a ≫
          (cartierStepSequence i hI (cartierPowerTwist i hI H n (n * d - 2))).g =
            firstOrderQuotientCoordinate i hI H d eI eH n hn a := by
  obtain ⟨B, hB⟩ := exists_cartier_vanishing_and_section_lifts p i r e H eP hI d eI eH
  refine ⟨B, fun n hn hn2 => ?_⟩
  let S := cartierStepSequence i hI (cartierPowerTwist i hI H n (n * d - 2))
  have hg : Function.Surjective (S.g.val.app (op ⊤)) :=
    (hB n hn).2 (n * d - 2) (by omega)
  choose t ht using fun a => exists_unitHom_factor_of_surjective S.g hg
    (firstOrderQuotientCoordinate i hI H d eI eH n hn2 a)
  exact ⟨t, ht⟩

omit [IsNoetherianRing A] [IsClosedImmersion p] in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual Cartier quotient arrow is the original pullback/pushforward unit. -/
theorem cartierStepSequence_g_eq_unit (M : LineBundle X) :
    (cartierStepSequence i hI M).g =
      (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app
        (tensorLineBundle X (dualLineBundle X (cartierIdealLineBundle i hI)) M).val := by
  let N := tensorLineBundle X (dualLineBundle X (cartierIdealLineBundle i hI)) M
  change (rightUnitor (C := X.Modules) N.val).inv ≫
      (moduleTensorLeftFunctor X N.val).map (Hom.structureModuleMap i) ≫
      (closedImmersionProjectionFormulaIso i N.val
        (SheafOfModules.unit (ProjectiveSpace k (ULift.{u} (Fin 2))).ringCatSheaf)).hom ≫
      (Scheme.Modules.pushforward i).map
        (rightUnitor (C := (ProjectiveSpace k (ULift.{u} (Fin 2))).Modules)
          ((Scheme.Modules.pullback i).obj N.val)).hom =
    (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app N.val
  apply Scheme.Modules.hom_ext
  intro U
  ext m
  change (rightUnitor (C := (ProjectiveSpace k (ULift.{u} (Fin 2))).Modules)
      ((Scheme.Modules.pullback i).obj N.val)).hom.val.app (op (i ⁻¹ᵁ U))
      ((closedImmersionProjectionFormulaIso i N.val
        (SheafOfModules.unit (ProjectiveSpace k (ULift.{u} (Fin 2))).ringCatSheaf)).hom.app U
        (((moduleTensorLeftFunctor X N.val).map (Hom.structureModuleMap i)).app U
          ((rightUnitor (C := X.Modules) N.val).inv.val.app (op U) m))) = _
  rw [rightUnitor_inv_moduleTensorSection, moduleTensorLeftFunctor_map_section]
  have hstructure : (Hom.structureModuleMap i).app U (1 : Γ(X, U)) =
      (1 : Γ(ProjectiveSpace k (ULift.{u} (Fin 2)), i ⁻¹ᵁ U)) := by
    change i.app U 1 = 1
    exact map_one _
  rw [hstructure, closedImmersionProjectionFormulaIso_section]
  rw [rightUnitor_eq_tensorRightUnitIso]
  exact (tensorRightUnitIso_hom_section _ _ _ _ 1).trans (one_smul _ _)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The given comparisons trivialize the actual final coefficient on E. -/
def cartierFinalRestrictionIso
    (eI : (Scheme.Modules.pullback i).obj (Hom.idealModule i) ≅
      twistingSheaf k (ULift.{u} (Fin 2)) 1)
    (eH : (Scheme.Modules.pullback i).obj H.val ≅
      twistingSheaf k (ULift.{u} (Fin 2)) (d : ℤ)) (n : ℕ) :
    (Scheme.Modules.pullback i).obj (cartierPowerTwist i hI H n (n * d)).val ≅
      SheafOfModules.unit (ProjectiveSpace k (ULift.{u} (Fin 2))).ringCatSheaf := by
  refine cartierTwistRestrictionIso i (cartierIdealLineBundle i hI)
    (tensorPowerLineBundle X H n) ((n : ℤ) * d) eI
    (tensorPowerRestrictionIso i H (d : ℤ) eH n) (n * d) ≪≫ ?_
  have hzero : (n : ℤ) * d - ((n * d : ℕ) : ℤ) = 0 := by push_cast; ring
  exact eqToIso (congrArg (twistingSheaf k (ULift.{u} (Fin 2))) hzero) ≪≫
    twistingZeroIso k (ULift.{u} (Fin 2))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The original restriction map followed by the given actual final trivialization. -/
def cartierResidueMap
    (eI : (Scheme.Modules.pullback i).obj (Hom.idealModule i) ≅
      twistingSheaf k (ULift.{u} (Fin 2)) 1)
    (eH : (Scheme.Modules.pullback i).obj H.val ≅
      twistingSheaf k (ULift.{u} (Fin 2)) (d : ℤ)) (n : ℕ) :
    (show X.Modules from (cartierPowerTwist i hI H n (n * d)).val) ⟶
      (Scheme.Modules.pushforward i).obj
        (SheafOfModules.unit (ProjectiveSpace k (ULift.{u} (Fin 2))).ringCatSheaf) :=
  (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app
      (cartierPowerTwist i hI H n (n * d)).val ≫
    (Scheme.Modules.pushforward i).map (cartierFinalRestrictionIso i hI H d eI eH n).hom

include p eP in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The original restriction onto all residue sections is surjective for large n and nd≥1. -/
theorem exists_cartierResidueMap_sections_surjective
    (r : ℕ) (e : ι ≃ Fin (r + 1))
    (eI : (Scheme.Modules.pullback i).obj (Hom.idealModule i) ≅
      twistingSheaf k (ULift.{u} (Fin 2)) 1)
    (eH : (Scheme.Modules.pullback i).obj H.val ≅
      twistingSheaf k (ULift.{u} (Fin 2)) (d : ℤ)) :
    ∃ B : ℕ, ∀ n : ℕ, B ≤ n → 1 ≤ n * d →
      Function.Surjective ((cartierResidueMap i hI H d eI eH n).val.app (op ⊤)) := by
  obtain ⟨B, hB⟩ := exists_cartier_vanishing_and_section_lifts p i r e H eP hI d eI eH
  refine ⟨B, fun n hn hn1 => ?_⟩
  let M := cartierPowerTwist i hI H n (n * d - 1)
  let N := tensorLineBundle X (dualLineBundle X (cartierIdealLineBundle i hI)) M
  let S := cartierStepSequence i hI M
  have hg : Function.Surjective (S.g.val.app (op ⊤)) :=
    (hB n hn).2 (n * d - 1) (by omega)
  have heq : S.g = (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app N.val :=
    cartierStepSequence_g_eq_unit i hI M
  have hunitN : Function.Surjective
      (((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app N.val).val.app (op ⊤)) :=
    (congrArg (fun f : N.val ⟶ (Scheme.Modules.pushforward i).obj
      ((Scheme.Modules.pullback i).obj N.val) => Function.Surjective (f.val.app (op ⊤))) heq).mp hg
  have hidx : n * d - 1 + 1 = n * d := by omega
  have hline : N = cartierPowerTwist i hI H n (n * d) :=
    congrArg (cartierPowerTwist i hI H n) hidx
  have hunit : Function.Surjective
      (((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app
        (cartierPowerTwist i hI H n (n * d)).val).val.app (op ⊤)) :=
    (congrArg (fun L : LineBundle X => Function.Surjective
      (((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app L.val).val.app (op ⊤)))
        hline).mp hunitN
  let χ := (Scheme.Modules.pushforward i).map (cartierFinalRestrictionIso i hI H d eI eH n).hom
  have hχ : Function.Surjective (χ.val.app (op ⊤)) :=
    (ConcreteCategory.bijective_of_isIso
      ((SheafOfModules.evaluation X.ringCatSheaf (op ⊤)).map χ)).2
  exact hχ.comp hunit

omit [IsNoetherianRing A] [IsClosedImmersion p] [IsClosedImmersion i] in
/-- The actual A-module structure on the exceptional coefficient ring. -/
abbrev exceptionalCoefficientModule : Module A k :=
  Module.compHom k (exceptionalBaseHom p i)

omit [IsNoetherianRing A] [IsClosedImmersion p] [IsClosedImmersion i] in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Original pushed structure sections identify linearly with the original k,
with its displayed original A-action. -/
def exceptionalGlobalSectionsLinearEquiv :
    let _ := projectiveGlobalSectionsModule p
      ((Scheme.Modules.pushforward i).obj
        (SheafOfModules.unit (ProjectiveSpace k (ULift.{u} (Fin 2))).ringCatSheaf))
    let _ := exceptionalCoefficientModule p i
    Γ((Scheme.Modules.pushforward i).obj
      (SheafOfModules.unit (ProjectiveSpace k (ULift.{u} (Fin 2))).ringCatSheaf), ⊤) ≃ₗ[A] k := by
  let _ := projectiveGlobalSectionsModule p
    ((Scheme.Modules.pushforward i).obj
      (SheafOfModules.unit (ProjectiveSpace k (ULift.{u} (Fin 2))).ringCatSheaf))
  let _ := exceptionalCoefficientModule p i
  let γ := globalFunctionsRingEquiv k (ULift.{u} (Fin 2))
  refine {
    toFun := fun t => γ.symm t
    invFun := fun a => γ a
    left_inv := fun t => γ.apply_symm_apply t
    right_inv := fun a => γ.symm_apply_apply a
    map_add' := fun t u => γ.symm.map_add t u
    map_smul' := ?_ }
  intro a t
  change γ.symm ((i.appTop.hom (projectiveStructuralScalars p a)) *
      (show Γ(ProjectiveSpace k (ULift.{u} (Fin 2)), ⊤) from t)) =
    exceptionalBaseHom p i a * γ.symm t
  exact γ.symm.map_mul _ _

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The coefficient of an original section after its actual restriction to E. -/
def cartierResidueCoefficient
    (eI : (Scheme.Modules.pullback i).obj (Hom.idealModule i) ≅
      twistingSheaf k (ULift.{u} (Fin 2)) 1)
    (eH : (Scheme.Modules.pullback i).obj H.val ≅
      twistingSheaf k (ULift.{u} (Fin 2)) (d : ℤ)) (n : ℕ)
    (s : 𝟙_ X.Modules ⟶ (show X.Modules from
      (cartierPowerTwist i hI H n (n * d)).val)) : k :=
  (globalFunctionsRingEquiv k (ULift.{u} (Fin 2))).symm
    (unitHomGlobalSectionsEquiv (ProjectiveSpace k (ULift.{u} (Fin 2))) _
      (FromSections.pullbackSection i s ≫ (cartierFinalRestrictionIso i hI H d eI eH n).hom))

omit [IsClosedImmersion i] in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- This coefficient is the original quotient-section value, with no change of map. -/
theorem cartierResidueCoefficient_eq
    (eI : (Scheme.Modules.pullback i).obj (Hom.idealModule i) ≅
      twistingSheaf k (ULift.{u} (Fin 2)) 1)
    (eH : (Scheme.Modules.pullback i).obj H.val ≅
      twistingSheaf k (ULift.{u} (Fin 2)) (d : ℤ)) (n : ℕ)
    (s : 𝟙_ X.Modules ⟶ (show X.Modules from
      (cartierPowerTwist i hI H n (n * d)).val)) :
    cartierResidueCoefficient i hI H d eI eH n s =
      (globalFunctionsRingEquiv k (ULift.{u} (Fin 2))).symm
        (unitHomGlobalSectionsEquiv X _ (s ≫ cartierResidueMap i hI H d eI eH n)) := by
  unfold cartierResidueCoefficient
  apply congrArg (globalFunctionsRingEquiv k (ULift.{u} (Fin 2))).symm
  rw [unitHomGlobalSectionsEquiv_naturality, FromSections.pullbackSection_global]
  rfl

namespace CartierProjectivePresentation

variable {p i hI H eP d} {n : ℕ} {hn : 1 ≤ n}
  (F : CartierProjectivePresentation p i hI H eP d n hn)
  (eI : (Scheme.Modules.pullback i).obj (Hom.idealModule i) ≅
    twistingSheaf k (ULift.{u} (Fin 2)) 1)
  (eH : (Scheme.Modules.pullback i).obj H.val ≅
    twistingSheaf k (ULift.{u} (Fin 2)) (d : ℤ))

omit [IsNoetherianRing A] [IsClosedImmersion p] in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The same original projective coordinates restrict to a family spanning all k over A. -/
theorem residueCoefficients_span
    (hρ : Function.Surjective ((cartierResidueMap i hI H d eI eH n).val.app (op ⊤))) :
    let _ := exceptionalCoefficientModule p i
    Submodule.span A
      (Set.range fun j => cartierResidueCoefficient i hI H d eI eH n (F.sections j)) = ⊤ := by
  let N := (Scheme.Modules.pushforward i).obj
    (SheafOfModules.unit (ProjectiveSpace k (ULift.{u} (Fin 2))).ringCatSheaf)
  let _ := projectiveGlobalSectionsModule p N
  let _ := exceptionalCoefficientModule p i
  let ψ : Γ(N, ⊤) ≃ₗ[A] k := exceptionalGlobalSectionsLinearEquiv p i
  let φ : Γ(N, ⊤) →ₗ[A] k := ψ.toLinearMap
  change Submodule.span A
    (Set.range fun j => cartierResidueCoefficient i hI H d eI eH n (F.sections j)) = ⊤
  have hspan : Submodule.span A
      (Set.range fun j => unitHomGlobalSectionsEquiv X N
        (F.sections j ≫ cartierResidueMap i hI H d eI eH n)) = ⊤ :=
    sectionFamilySpans_after_surjective p (cartierPowerTwist i hI H n (n * d))
      (cartierResidueMap i hI H d eI eH n) hρ F.sections F.spansSections
  have hvalues :
      (fun j => cartierResidueCoefficient i hI H d eI eH n (F.sections j)) =
        (fun j => φ (unitHomGlobalSectionsEquiv X N
          (F.sections j ≫ cartierResidueMap i hI H d eI eH n))) := by
    funext j
    change cartierResidueCoefficient i hI H d eI eH n (F.sections j) =
      (globalFunctionsRingEquiv k (ULift.{u} (Fin 2))).symm
        (unitHomGlobalSectionsEquiv X N (F.sections j ≫ cartierResidueMap i hI H d eI eH n))
    exact cartierResidueCoefficient_eq i hI H d eI eH n (F.sections j)
  rw [hvalues]
  have himage :
      Set.range (fun j => φ (unitHomGlobalSectionsEquiv X N
        (F.sections j ≫ cartierResidueMap i hI H d eI eH n))) =
        φ '' Set.range (fun j => unitHomGlobalSectionsEquiv X N
          (F.sections j ≫ cartierResidueMap i hI H d eI eH n)) := by
    ext y
    constructor
    · rintro ⟨j, rfl⟩
      exact ⟨_, ⟨j, rfl⟩, rfl⟩
    · rintro ⟨x, ⟨j, rfl⟩, rfl⟩
      exact ⟨j, rfl⟩
  rw [himage, ← Submodule.map_span, hspan, Submodule.map_top]
  exact LinearMap.range_eq_top.mpr ψ.surjective

omit [IsNoetherianRing A] [IsClosedImmersion p] in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A field residue coefficient is nonzero among the actual original coordinates. -/
theorem exists_residueCoefficient_ne_zero (hk : IsField k)
    (hρ : Function.Surjective ((cartierResidueMap i hI H d eI eH n).val.app (op ⊤))) :
    ∃ j : F.index, cartierResidueCoefficient i hI H d eI eH n (F.sections j) ≠ 0 := by
  classical
  let _ : Nontrivial k := hk.nontrivial
  let _ := exceptionalCoefficientModule p i
  by_contra! hzero
  have hspan := F.residueCoefficients_span eI eH hρ
  have hle : Submodule.span A
      (Set.range fun j => cartierResidueCoefficient i hI H d eI eH n (F.sections j)) ≤ ⊥ := by
    apply Submodule.span_le.mpr
    rintro x ⟨j, rfl⟩
    exact hzero j
  have hone : (1 : k) ∈ (⊥ : Submodule A k) := hle (by rw [hspan]; trivial)
  exact one_ne_zero hone

end CartierProjectivePresentation

/-- The original structure module is locally free of rank one. -/
theorem structureModule_rankOne (Y : Scheme.{u}) :
    IsLocallyRankOne Y (SheafOfModules.unit Y.ringCatSheaf) :=
  isLocallyRankOne_of_iso Y
    (Limits.coproductUniqueIso (fun _ : PUnit.{u + 1} => SheafOfModules.unit Y.ringCatSheaf))
    (trivialLineBundle Y).property

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem pullbackUnitMul {Y T : Scheme.{u}} (g : T ⟶ Y) (a : Γ(Y, ⊤)) :
    FromSections.pullbackSection g (unitMul Y a) ≫ (pullbackUnitIso g).hom =
      unitMul T (g.appTop.hom a) := by
  unfold FromSections.pullbackSection
  rw [← globalScalarEndomorphism_unit, pullback_map_globalScalarEndomorphism,
    globalScalarEndomorphism_conj (pullbackUnitIso g)]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
  exact globalScalarEndomorphism_unit T _

namespace CartierProjectivePresentation

variable {p i hI H eP d} {n : ℕ} {hn : 1 ≤ n}
  (F : CartierProjectivePresentation p i hI H eP d n hn)
  (eI : (Scheme.Modules.pullback i).obj (Hom.idealModule i) ≅
    twistingSheaf k (ULift.{u} (Fin 2)) 1)
  (eH : (Scheme.Modules.pullback i).obj H.val ≅
    twistingSheaf k (ULift.{u} (Fin 2)) (d : ℤ))

/-- Literal original residue coefficients, as section maps on the actual Spec k. -/
def residuePointFamily (j : F.index) :
    𝟙_ (Spec (.of k)).Modules ⟶ (𝟙_ (Spec (.of k)).Modules) :=
  unitMul (Spec (.of k)) ((Scheme.ΓSpecIso (.of k)).inv.hom
    (cartierResidueCoefficient i hI H d eI eH n (F.sections j)))

omit [IsNoetherianRing A] [IsClosedImmersion p] in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- An actual unit coefficient makes the original Spec k family epimorphic. -/
theorem residuePointFamily_epi (j₀ : F.index)
    (h₀ : IsUnit (cartierResidueCoefficient i hI H d eI eH n (F.sections j₀))) :
    Epi (Sigma.desc (F.residuePointFamily eI eH)) := by
  obtain ⟨v, hv⟩ := h₀.map (Scheme.ΓSpecIso (.of k)).inv.hom
  have hj : F.residuePointFamily eI eH j₀ = (unitMulIso (Spec (.of k)) v).hom := by
    change unitMul (Spec (.of k)) _ = unitMul (Spec (.of k)) v
    exact congrArg (unitMul (Spec (.of k))) hv.symm
  let _ : Epi (F.residuePointFamily eI eH j₀) := by rw [hj]; infer_instance
  exact epi_of_epi_fac (Sigma.ι_comp_desc (F.residuePointFamily eI eH) j₀)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual native projective morphism on Spec k, using the same original index. -/
def residuePoint (j₀ : F.index)
    (h₀ : IsUnit (cartierResidueCoefficient i hI H d eI eH n (F.sections j₀))) :
    Spec (.of k) ⟶ ProjectiveSpace A F.index := by
  let _ : Finite F.index := F.finiteIndex
  let _ : Epi (Sigma.desc (F.residuePointFamily eI eH)) := F.residuePointFamily_epi eI eH j₀ h₀
  exact FromSections.mapOfFiniteFamily
    (Spec.map (CommRingCat.ofHom (exceptionalBaseHom p i)))
    (SheafOfModules.unit (Spec (.of k)).ringCatSheaf)
    (structureModule_rankOne (Spec (.of k))) (F.residuePointFamily eI eH)

omit [IsNoetherianRing A] [IsClosedImmersion p] in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The point morphism preserves the original structural ring map A to k. -/
@[reassoc]
theorem residuePoint_toSpec (j₀ : F.index)
    (h₀ : IsUnit (cartierResidueCoefficient i hI H d eI eH n (F.sections j₀))) :
    F.residuePoint eI eH j₀ h₀ ≫ toSpec A F.index =
      Spec.map (CommRingCat.ofHom (exceptionalBaseHom p i)) := by
  let _ : Finite F.index := F.finiteIndex
  let _ : Epi (Sigma.desc (F.residuePointFamily eI eH)) := F.residuePointFamily_epi eI eH j₀ h₀
  exact FromSections.mapOfFiniteFamily_toSpec _ _ _ _

omit [IsNoetherianRing A] [IsClosedImmersion p] in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Every restricted original section is the pullback of its actual k coefficient. -/
theorem residuePointFamily_pullback (j : F.index) :
    FromSections.pulledFamily (toSpec k (ULift.{u} (Fin 2)))
        (F.residuePointFamily eI eH) j ≫
      (pullbackUnitIso (toSpec k (ULift.{u} (Fin 2)))).hom =
    FromSections.pulledFamily i F.sections j ≫
      (cartierFinalRestrictionIso i hI H d eI eH n).hom := by
  rw [FromSections.pulledFamily, residuePointFamily, pullbackUnitMul]
  apply (unitHomGlobalSectionsEquiv (ProjectiveSpace k (ULift.{u} (Fin 2))) _).injective
  rw [unitHomGlobalSectionsEquiv_unitMul]
  exact (globalFunctionsRingEquiv k (ULift.{u} (Fin 2))).apply_symm_apply _

omit [IsNoetherianRing A] [IsClosedImmersion p] in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual projective restriction to E factors through its original Spec k,
with every original projective coordinate retained. -/
theorem exceptional_toProjective_eq (j₀ : F.index)
    (h₀ : IsUnit (cartierResidueCoefficient i hI H d eI eH n (F.sections j₀))) :
    i ≫ F.toProjective = toSpec k (ULift.{u} (Fin 2)) ≫ F.residuePoint eI eH j₀ h₀ := by
  let _ : Finite F.index := F.finiteIndex
  let _ : Epi (Sigma.desc F.sections) := F.epiSections
  let _ : Epi (Sigma.desc (F.residuePointFamily eI eH)) := F.residuePointFamily_epi eI eH j₀ h₀
  let E := ProjectiveSpace k (ULift.{u} (Fin 2))
  let U := SheafOfModules.unit E.ringCatSheaf
  let t := fun j => FromSections.pulledFamily i F.sections j ≫
    (cartierFinalRestrictionIso i hI H d eI eH n).hom
  let v := fun j => FromSections.pulledFamily (toSpec k (ULift.{u} (Fin 2)))
    (F.residuePointFamily eI eH) j ≫
      (pullbackUnitIso (toSpec k (ULift.{u} (Fin 2)))).hom
  let β := Spec.map (CommRingCat.ofHom (exceptionalBaseHom p i))
  have hleft := FromSections.mapOfFiniteFamily_pullback_iso i (p ≫ toSpec A ι)
    (cartierPowerTwist i hI H n (n * d)).val
    (cartierPowerTwist i hI H n (n * d)).property F.sections U
    (cartierFinalRestrictionIso i hI H d eI eH n)
  have hright := FromSections.mapOfFiniteFamily_pullback_iso (toSpec k (ULift.{u} (Fin 2))) β
    (SheafOfModules.unit (Spec (.of k)).ringCatSheaf) (structureModule_rankOne (Spec (.of k)))
    (F.residuePointFamily eI eH) U (pullbackUnitIso (toSpec k (ULift.{u} (Fin 2))))
  change i ≫ F.toProjective =
      FromSections.mapOfFiniteFamily (i ≫ p ≫ toSpec A ι) U (structureModule_rankOne E) t at hleft
  change toSpec k (ULift.{u} (Fin 2)) ≫ F.residuePoint eI eH j₀ h₀ =
      FromSections.mapOfFiniteFamily (toSpec k (ULift.{u} (Fin 2)) ≫ β) U
        (structureModule_rankOne E) v at hright
  rw [exceptionalBaseHom_triangle p i] at hleft
  refine hleft.trans ((FromSections.mapOfFiniteFamily_iso _ U U
    (structureModule_rankOne E) (structureModule_rankOne E) t v (Iso.refl U) ?_).trans hright.symm)
  intro j
  change t j ≫ 𝟙 U = v j
  rw [Category.comp_id]
  exact (F.residuePointFamily_pullback eI eH j).symm

omit [IsNoetherianRing A] [IsClosedImmersion p] in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The original cohomology and actual field condition provide a usable point chart. -/
theorem exists_residueCoefficient_isUnit (hk : IsField k)
    (hρ : Function.Surjective ((cartierResidueMap i hI H d eI eH n).val.app (op ⊤))) :
    ∃ j : F.index, IsUnit (cartierResidueCoefficient i hI H d eI eH n (F.sections j)) := by
  obtain ⟨j, hj⟩ := F.exists_residueCoefficient_ne_zero eI eH hk hρ
  obtain ⟨a, ha⟩ := hk.mul_inv_cancel hj
  exact ⟨j, isUnit_iff_exists_inv.mpr ⟨a, ha⟩⟩

end CartierProjectivePresentation

include p eP in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- For large n the proved original section family gives an actual Spec k factor
of the projective restriction to the exceptional curve. -/
theorem exists_cartier_projective_residue_factor
    (r : ℕ) (e : ι ≃ Fin (r + 1))
    (eI : (Scheme.Modules.pullback i).obj (Hom.idealModule i) ≅
      twistingSheaf k (ULift.{u} (Fin 2)) 1)
    (eH : (Scheme.Modules.pullback i).obj H.val ≅
      twistingSheaf k (ULift.{u} (Fin 2)) (d : ℤ))
    (hk : IsField k) (hd : 0 < d) :
    ∃ (B : ℕ) (hB : 1 ≤ B), ∀ (n : ℕ) (hn : B ≤ n),
      ∃ (F : CartierProjectivePresentation p i hI H eP d n (hB.trans hn))
        (j₀ : F.index)
        (h₀ : IsUnit (cartierResidueCoefficient i hI H d eI eH n (F.sections j₀))),
        i ≫ F.toProjective =
          toSpec k (ULift.{u} (Fin 2)) ≫ F.residuePoint eI eH j₀ h₀ := by
  obtain ⟨Bg, hBg, hgen⟩ := exists_cartier_projective_presentation p i hI H eP d r e eI eH
  obtain ⟨Br, hres⟩ := exists_cartierResidueMap_sections_surjective p i hI H eP d r e eI eH
  refine ⟨max Bg Br, hBg.trans (le_max_left _ _), fun n hn => ?_⟩
  have hng : Bg ≤ n := (le_max_left _ _).trans hn
  obtain ⟨F⟩ := hgen n hng
  have hn1 : 1 ≤ n := hBg.trans hng
  have hnd : 1 ≤ n * d := by simpa using Nat.mul_le_mul hn1 (Nat.succ_le_iff.mpr hd)
  have hρ := hres n ((le_max_right _ _).trans hn) hnd
  obtain ⟨j₀, h₀⟩ := F.exists_residueCoefficient_isUnit eI eH hk hρ
  exact ⟨F, j₀, h₀, F.exceptional_toProjective_eq eI eH j₀ h₀⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The original P1_k structural map is schematically dominant, for any commutative k. -/
theorem exceptional_toSpec_schemeTheoreticallyDominant :
    IsSchemeTheoreticallyDominant (toSpec k (ULift.{u} (Fin 2))) := by
  let E := ProjectiveSpace k (ULift.{u} (Fin 2))
  let γ := globalFunctionsRingEquiv k (ULift.{u} (Fin 2))
  let _ : IsIso (CommRingCat.ofHom γ.toRingHom) := γ.toCommRingCatIso.isIso_hom
  let _ : CompactSpace E := QuasiCompact.compactSpace_of_compactSpace
    (toSpec k (ULift.{u} (Fin 2)))
  let _ : IsSchemeTheoreticallyDominant E.toSpecΓ := ⟨Scheme.ker_toSpecΓ E⟩
  have hq : E.toSpecΓ ≫ Spec.map (CommRingCat.ofHom γ.toRingHom) =
      toSpec k (ULift.{u} (Fin 2)) := by
    change E.toSpecΓ ≫ Spec.map
      ((Scheme.ΓSpecIso (.of k)).inv ≫ (toSpec k (ULift.{u} (Fin 2))).appTop) = _
    rw [Spec.map_comp, ← Scheme.toSpecΓ_naturality_assoc,
      toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
  rw [← hq]
  infer_instance

namespace CartierProjectivePresentation

variable {p i hI H eP d} {n : ℕ} {hn : 1 ≤ n}
  (F : CartierProjectivePresentation p i hI H eP d n hn)
  (eI : (Scheme.Modules.pullback i).obj (Hom.idealModule i) ≅
    twistingSheaf k (ULift.{u} (Fin 2)) 1)
  (eH : (Scheme.Modules.pullback i).obj H.val ≅
    twistingSheaf k (ULift.{u} (Fin 2)) (d : ℤ))

include F in
omit [IsNoetherianRing A] [IsClosedImmersion p] in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The genuine original residue-section span makes k finite over its original base action. -/
theorem exceptionalBaseHom_finite
    (hρ : Function.Surjective ((cartierResidueMap i hI H d eI eH n).val.app (op ⊤))) :
    (exceptionalBaseHom p i).Finite := by
  classical
  let _ := exceptionalCoefficientModule p i
  let _ : Fintype F.index := @Fintype.ofFinite F.index F.finiteIndex
  let a := fun j => cartierResidueCoefficient i hI H d eI eH n (F.sections j)
  change Module.Finite A k
  refine Module.Finite.of_fg_top ⟨Finset.univ.image a, ?_⟩
  simpa only [Finset.coe_image, Finset.coe_univ, Set.image_univ] using
    F.residueCoefficients_span eI eH hρ

omit [IsNoetherianRing A] [IsClosedImmersion p] in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Schematic dominance of the original P1_k map gives actual image-kernel containment. -/
theorem residuePoint_kernel_contains (j₀ : F.index)
    (h₀ : IsUnit (cartierResidueCoefficient i hI H d eI eH n (F.sections j₀))) :
    F.imageInclusion.ker ≤ (F.residuePoint eI eH j₀ h₀).ker := by
  let _ : IsSchemeTheoreticallyDominant (toSpec k (ULift.{u} (Fin 2))) :=
    exceptional_toSpec_schemeTheoreticallyDominant (k := k)
  change F.toProjective.ker.subschemeι.ker ≤ _
  rw [Scheme.IdealSheafData.ker_subschemeι]
  calc
    F.toProjective.ker ≤ (i ≫ F.toProjective).ker := i.le_ker_comp _
    _ = (toSpec k (ULift.{u} (Fin 2)) ≫ F.residuePoint eI eH j₀ h₀).ker :=
      congrArg Scheme.Hom.ker (F.exceptional_toProjective_eq eI eH j₀ h₀)
    _ = (F.residuePoint eI eH j₀ h₀).ker := by
      rw [Scheme.Hom.ker_comp, Scheme.Hom.ker_eq_bot, Scheme.IdealSheafData.map_bot]

/-- The actual Spec k morphism into the original scheme-theoretic image. -/
def residueToImage (j₀ : F.index)
    (h₀ : IsUnit (cartierResidueCoefficient i hI H d eI eH n (F.sections j₀))) :
    Spec (.of k) ⟶ F.image :=
  IsClosedImmersion.lift F.imageInclusion (F.residuePoint eI eH j₀ h₀)
    (F.residuePoint_kernel_contains eI eH j₀ h₀)

omit [IsNoetherianRing A] [IsClosedImmersion p] in
/-- This original image factor retains the actual projective point map. -/
@[reassoc]
theorem residueToImage_imageInclusion (j₀ : F.index)
    (h₀ : IsUnit (cartierResidueCoefficient i hI H d eI eH n (F.sections j₀))) :
    F.residueToImage eI eH j₀ h₀ ≫ F.imageInclusion = F.residuePoint eI eH j₀ h₀ :=
  IsClosedImmersion.lift_fac _ _ _

omit [IsNoetherianRing A] [IsClosedImmersion p] in
/-- The original exceptional map to the actual image factors through the same Spec k. -/
theorem exceptional_toImage_eq (j₀ : F.index)
    (h₀ : IsUnit (cartierResidueCoefficient i hI H d eI eH n (F.sections j₀))) :
    i ≫ F.toImage = toSpec k (ULift.{u} (Fin 2)) ≫ F.residueToImage eI eH j₀ h₀ := by
  apply (cancel_mono F.imageInclusion).mp
  rw [Category.assoc, Category.assoc, F.toImage_imageInclusion,
    F.residueToImage_imageInclusion]
  exact F.exceptional_toProjective_eq eI eH j₀ h₀

omit [IsNoetherianRing A] [IsClosedImmersion p] in
/-- The actual image point preserves the original A to k structural map. -/
@[reassoc]
theorem residueToImage_toSpec (j₀ : F.index)
    (h₀ : IsUnit (cartierResidueCoefficient i hI H d eI eH n (F.sections j₀))) :
    F.residueToImage eI eH j₀ h₀ ≫ F.imageStructureMap =
      Spec.map (CommRingCat.ofHom (exceptionalBaseHom p i)) := by
  change F.residueToImage eI eH j₀ h₀ ≫ F.imageInclusion ≫ toSpec A F.index = _
  rw [← Category.assoc, F.residueToImage_imageInclusion, F.residuePoint_toSpec]

omit [IsNoetherianRing A] [IsClosedImmersion p] in
/-- The actual point morphism is proper once the genuine restriction is onto
all residue sections. -/
theorem residuePoint_isProper (j₀ : F.index)
    (h₀ : IsUnit (cartierResidueCoefficient i hI H d eI eH n (F.sections j₀)))
    (hρ : Function.Surjective ((cartierResidueMap i hI H d eI eH n).val.app (op ⊤))) :
    IsProper (F.residuePoint eI eH j₀ h₀) := by
  let _ : Finite F.index := F.finiteIndex
  let _ : IsFinite (Spec.map (CommRingCat.ofHom (exceptionalBaseHom p i))) :=
    (IsFinite.SpecMap_iff (CommRingCat.ofHom (exceptionalBaseHom p i))).mpr
      (F.exceptionalBaseHom_finite eI eH hρ)
  have hcomp : IsProper (F.residuePoint eI eH j₀ h₀ ≫ toSpec A F.index) := by
    rw [F.residuePoint_toSpec]
    infer_instance
  exact IsProper.of_comp _ (toSpec A F.index)

omit [IsNoetherianRing A] [IsClosedImmersion p] in
/-- The same actual Spec k map into the scheme-theoretic image is proper. -/
theorem residueToImage_isProper (j₀ : F.index)
    (h₀ : IsUnit (cartierResidueCoefficient i hI H d eI eH n (F.sections j₀)))
    (hρ : Function.Surjective ((cartierResidueMap i hI H d eI eH n).val.app (op ⊤))) :
    IsProper (F.residueToImage eI eH j₀ h₀) := by
  let _ : IsProper (F.residuePoint eI eH j₀ h₀) := F.residuePoint_isProper eI eH j₀ h₀ hρ
  have hcomp : IsProper (F.residueToImage eI eH j₀ h₀ ≫ F.imageInclusion) := by
    rw [F.residueToImage_imageInclusion]
    infer_instance
  exact IsProper.of_comp _ F.imageInclusion

end CartierProjectivePresentation

namespace CartierProjectivePresentation

variable {p i hI H eP d} {n : ℕ} {hn : 1 ≤ n}
  (F : CartierProjectivePresentation p i hI H eP d n hn)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Append prescribed actual sections, retaining both old and new literal coordinates. -/
def append {K : Type u} [Finite K]
    (t : K → (𝟙_ X.Modules ⟶
      (show X.Modules from (cartierPowerTwist i hI H n (n * d)).val))) :
    CartierProjectivePresentation p i hI H eP d n hn := by
  let v := Sum.elim F.sections t
  let _ : Epi (Sigma.desc F.sections) := F.epiSections
  let _ : Finite F.index := F.finiteIndex
  have hv : Epi (Sigma.desc v) := by
    constructor
    intro Z f g h
    apply (cancel_epi (Sigma.desc F.sections)).mp
    apply Sigma.hom_ext
    intro j
    simpa only [v, Sigma.ι_comp_desc_assoc, Sum.elim_inl] using
      congrArg (fun q => Sigma.ι (fun _ : F.index ⊕ K => 𝟙_ X.Modules) (Sum.inl j) ≫ q) h
  refine ⟨F.index ⊕ K, inferInstance, v, hv, ?_,
    ⟨fun a => Sum.inl (F.mixedIndex a), fun _ _ h => F.mixedIndex.injective (Sum.inl_injective h)⟩,
    fun a => F.mixedEq a⟩
  let _ := projectiveGlobalSectionsModule p (cartierPowerTwist i hI H n (n * d)).val
  change Submodule.span A
    (Set.range fun j => unitHomGlobalSectionsEquiv X _ (v j)) = ⊤
  have hspan : Submodule.span A
      (Set.range fun j => unitHomGlobalSectionsEquiv X _ (F.sections j)) = ⊤ := F.spansSections
  apply top_unique
  rw [← hspan]
  apply Submodule.span_mono
  rintro x ⟨j, rfl⟩
  exact ⟨Sum.inl j, rfl⟩

omit [IsNoetherianRing A] [IsClosedImmersion p] in
@[simp]
theorem append_sections_inl {K : Type u} [Finite K]
    (t : K → (𝟙_ X.Modules ⟶
      (show X.Modules from (cartierPowerTwist i hI H n (n * d)).val))) (j : F.index) :
    (F.append t).sections (Sum.inl j) = F.sections j := rfl

omit [IsNoetherianRing A] [IsClosedImmersion p] in
@[simp]
theorem append_sections_inr {K : Type u} [Finite K]
    (t : K → (𝟙_ X.Modules ⟶
      (show X.Modules from (cartierPowerTwist i hI H n (n * d)).val))) (a : K) :
    (F.append t).sections (Sum.inr a) = t a := rfl

end CartierProjectivePresentation

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Map an actual first-order lift into L_n by the next original Cartier inclusion. -/
def firstOrderCartierImage (n : ℕ) (hn2 : 2 ≤ n * d)
    (t : 𝟙_ X.Modules ⟶
      (cartierStepSequence i hI (cartierPowerTwist i hI H n (n * d - 2))).X₂) :
    𝟙_ X.Modules ⟶ (show X.Modules from (cartierPowerTwist i hI H n (n * d)).val) :=
  t ≫ (cartierStepSequence i hI
      (cartierPowerTwist i hI H n (n * d - 2 + 1))).f ≫
    eqToHom (congrArg (fun j => (cartierPowerTwist i hI H n j).val)
      (show n * d - 2 + 1 + 1 = n * d by omega))

omit [IsNoetherianRing A] [IsClosedImmersion p] in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The original first Cartier arrow is killed by the original restriction unit. -/
theorem cartierStepSequence_f_comp_unit (M : LineBundle X) :
    (cartierStepSequence i hI M).f ≫
      (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app
        (tensorLineBundle X (dualLineBundle X (cartierIdealLineBundle i hI)) M).val = 0 := by
  let S := cartierStepSequence i hI M
  let N := tensorLineBundle X (dualLineBundle X (cartierIdealLineBundle i hI)) M
  exact (congrArg (fun g : N.val ⟶ (Scheme.Modules.pushforward i).obj
      ((Scheme.Modules.pullback i).obj N.val) => S.f ≫ g)
        (cartierStepSequence_g_eq_unit i hI M)).symm.trans S.zero

omit [IsNoetherianRing A] [IsClosedImmersion p] in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- These original first-order Cartier images vanish under the actual restriction to E. -/
theorem firstOrderCartierImage_residueMap
    (eI : (Scheme.Modules.pullback i).obj (Hom.idealModule i) ≅
      twistingSheaf k (ULift.{u} (Fin 2)) 1)
    (eH : (Scheme.Modules.pullback i).obj H.val ≅
      twistingSheaf k (ULift.{u} (Fin 2)) (d : ℤ))
    (n : ℕ) (hn2 : 2 ≤ n * d)
    (t : 𝟙_ X.Modules ⟶
      (cartierStepSequence i hI (cartierPowerTwist i hI H n (n * d - 2))).X₂) :
    firstOrderCartierImage i hI H d n hn2 t ≫ cartierResidueMap i hI H d eI eH n = 0 := by
  let M := cartierPowerTwist i hI H n (n * d - 2 + 1)
  let N := tensorLineBundle X (dualLineBundle X (cartierIdealLineBundle i hI)) M
  let S := cartierStepSequence i hI M
  let hidx : n * d - 2 + 1 + 1 = n * d := by omega
  let e := eqToHom (congrArg (fun j => (cartierPowerTwist i hI H n j).val) hidx)
  have hnaturality := (Scheme.Modules.pullbackPushforwardAdjunction i).unit.naturality e
  change e ≫ (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app
      (cartierPowerTwist i hI H n (n * d)).val =
    (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app N.val ≫
      (Scheme.Modules.pushforward i).map ((Scheme.Modules.pullback i).map e) at hnaturality
  change t ≫ S.f ≫ e ≫
      (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app
        (cartierPowerTwist i hI H n (n * d)).val ≫
      (Scheme.Modules.pushforward i).map (cartierFinalRestrictionIso i hI H d eI eH n).hom = 0
  let χ := (Scheme.Modules.pushforward i).map (cartierFinalRestrictionIso i hI H d eI eH n).hom
  calc
    t ≫ S.f ≫ e ≫
        (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app
          (cartierPowerTwist i hI H n (n * d)).val ≫ χ =
      t ≫ (S.f ≫ (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app N.val) ≫
        (Scheme.Modules.pushforward i).map ((Scheme.Modules.pullback i).map e) ≫ χ := by
      simpa only [Category.assoc] using
        congrArg (fun f => t ≫ S.f ≫ f ≫ χ) hnaturality
    _ = 0 := by
      simpa only [Category.assoc, comp_zero, zero_comp] using
        congrArg (fun f => t ≫ f ≫
          (Scheme.Modules.pushforward i).map ((Scheme.Modules.pullback i).map e) ≫ χ)
            (cartierStepSequence_f_comp_unit i hI M)

include p eP in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The proved lifts of both original O_E(1) coordinates occur literally in an actual
projective family, together with all mixed ample coordinates and all global generators. -/
theorem exists_cartier_firstOrder_projective_presentation
    (r : ℕ) (e : ι ≃ Fin (r + 1))
    (eI : (Scheme.Modules.pullback i).obj (Hom.idealModule i) ≅
      twistingSheaf k (ULift.{u} (Fin 2)) 1)
    (eH : (Scheme.Modules.pullback i).obj H.val ≅
      twistingSheaf k (ULift.{u} (Fin 2)) (d : ℤ)) :
    ∃ (B : ℕ) (hB : 1 ≤ B), ∀ (n : ℕ) (hn : B ≤ n) (hn2 : 2 ≤ n * d),
      ∃ (F : CartierProjectivePresentation p i hI H eP d n (hB.trans hn))
        (t : ULift.{u} (Fin 2) → (𝟙_ X.Modules ⟶
          (cartierStepSequence i hI (cartierPowerTwist i hI H n (n * d - 2))).X₂))
        (q : ULift.{u} (Fin 2) ↪ F.index),
        (∀ a, t a ≫ (cartierStepSequence i hI
          (cartierPowerTwist i hI H n (n * d - 2))).g =
            firstOrderQuotientCoordinate i hI H d eI eH n hn2 a) ∧
        (∀ a, F.sections (q a) = firstOrderCartierImage i hI H d n hn2 (t a)) := by
  obtain ⟨Bg, hBg, hgen⟩ := exists_cartier_projective_presentation p i hI H eP d r e eI eH
  obtain ⟨Bt, hlifts⟩ := exists_firstOrder_coordinate_lifts p i hI H eP d r e eI eH
  refine ⟨max Bg Bt, hBg.trans (le_max_left _ _), fun n hn hn2 => ?_⟩
  obtain ⟨F⟩ := hgen n ((le_max_left _ _).trans hn)
  obtain ⟨t, ht⟩ := hlifts n ((le_max_right _ _).trans hn) hn2
  let u := fun a => firstOrderCartierImage i hI H d n hn2 (t a)
  refine ⟨F.append u, t, ⟨Sum.inr, Sum.inr_injective⟩, ht, fun a => ?_⟩
  exact F.append_sections_inr u a

omit [IsNoetherianRing A] [IsClosedImmersion p] in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Every original Cartier step is an isomorphism at a stalk
outside the actual exceptional curve. -/
theorem cartierStepSequence_stalk_isIso_of_not_mem (M : LineBundle X) (x : X)
    (hx : x ∉ Set.range i) :
    IsIso ((moduleStalk X x).map (cartierStepSequence i hI M).f) := by
  let N := tensorLineBundle X (dualLineBundle X (cartierIdealLineBundle i hI)) M
  have hBase := cartierStepSequence_shortExact i hI M
  let _ : Mono (cartierStepSequence i hI M).f := hBase.mono_f
  let _ : Epi (cartierStepSequence i hI M).g := hBase.epi_g
  have hS := hBase.map (moduleStalk X x)
  exact hS.isIso_f_iff.mpr
    (isZero_closedImmersion_moduleStalk_of_not_mem i x hx ((Scheme.Modules.pullback i).obj N.val))

omit [IsNoetherianRing A] [IsClosedImmersion p] in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual common Cartier multiplier is invertible at every original off-E stalk. -/
theorem cartierPowerInclusion_stalk_isIso_of_not_mem (n j : ℕ) (x : X)
    (hx : x ∉ Set.range i) :
    IsIso ((moduleStalk X x).map (cartierPowerInclusion i hI H n j)) := by
  induction j with
  | zero => change IsIso ((moduleStalk X x).map (𝟙 _)); infer_instance
  | succ j ih =>
      let _ := ih
      let _ := cartierStepSequence_stalk_isIso_of_not_mem i hI
        (cartierPowerTwist i hI H n j) x hx
      change IsIso ((moduleStalk X x).map
        (cartierPowerInclusion i hI H n j ≫ (cartierStepSequence i hI
          (cartierPowerTwist i hI H n j)).f))
      rw [Functor.map_comp]
      infer_instance

omit [IsNoetherianRing A] [IsClosedImmersion p] in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Pulling the actual common inclusion to any genuine off-E source gives an isomorphism. -/
theorem cartierPowerInclusion_pullback_isIso_of_disjoint
    {Y : Scheme.{u}} (g : Y ⟶ X) (hg : ∀ y : Y, g y ∉ Set.range i) (n j : ℕ) :
    IsIso ((Scheme.Modules.pullback g).map (cartierPowerInclusion i hI H n j)) := by
  apply isIso_of_moduleStalk
  intro y
  let e := pullbackModuleStalkIso g y
  let _ := cartierPowerInclusion_stalk_isIso_of_not_mem i hI H n j (g y) (hg y)
  have h : IsIso (((Scheme.Modules.pullback g ⋙ moduleStalk Y y).map
      (cartierPowerInclusion i hI H n j)) ≫
        e.hom.app (cartierPowerTwist i hI H n j).val) := by
    rw [e.hom.naturality]
    change IsIso (e.hom.app (show X.Modules from (tensorPowerLineBundle X H n).val) ≫
      (ModuleCat.extendScalars (g.stalkMap y).hom).map
        ((moduleStalk X (g y)).map (cartierPowerInclusion i hI H n j)))
    infer_instance
  exact (isIso_comp_right_iff _ (e.hom.app _)).mp h

/-- The actual open complement of the original exceptional closed immersion. -/
def exceptionalComplement : X.Opens :=
  ⟨(Set.range i)ᶜ, i.isClosedEmbedding.isClosed_range.isOpen_compl⟩

omit [IsNoetherianRing A] [IsClosedImmersion p] in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- In particular the actual Cartier inclusion is an isomorphism on the original complement. -/
theorem cartierPowerInclusion_complement_isIso (n j : ℕ) :
    IsIso ((Scheme.Modules.pullback (exceptionalComplement i).ι).map
      (cartierPowerInclusion i hI H n j)) :=
  cartierPowerInclusion_pullback_isIso_of_disjoint i hI H
    (exceptionalComplement i).ι (fun y => y.property) n j

omit [IsNoetherianRing A] [IsClosedImmersion p] in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Each nonempty common Cartier inclusion vanishes under the original restriction unit. -/
theorem cartierPowerInclusion_comp_unit (n j : ℕ) :
    cartierPowerInclusion i hI H n (j + 1) ≫
      (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app
        (cartierPowerTwist i hI H n (j + 1)).val = 0 := by
  let M := cartierPowerTwist i hI H n j
  let N := tensorLineBundle X (dualLineBundle X (cartierIdealLineBundle i hI)) M
  change cartierPowerInclusion i hI H n j ≫ (cartierStepSequence i hI M).f ≫
      (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app N.val = 0
  simpa only [Category.assoc, comp_zero] using
    congrArg (fun f => cartierPowerInclusion i hI H n j ≫ f)
      (cartierStepSequence_f_comp_unit i hI M)

omit [IsNoetherianRing A] [IsClosedImmersion p] in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The original common Cartier multiplier restricts to zero on E for nd≥1. -/
theorem cartierPowerInclusion_residueMap
    (eI : (Scheme.Modules.pullback i).obj (Hom.idealModule i) ≅
      twistingSheaf k (ULift.{u} (Fin 2)) 1)
    (eH : (Scheme.Modules.pullback i).obj H.val ≅
      twistingSheaf k (ULift.{u} (Fin 2)) (d : ℤ)) (n : ℕ) (hn1 : 1 ≤ n * d) :
    cartierPowerInclusion i hI H n (n * d) ≫ cartierResidueMap i hI H d eI eH n = 0 := by
  have hz : cartierPowerInclusion i hI H n (n * d) ≫
      (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app
        (cartierPowerTwist i hI H n (n * d)).val = 0 := by
    have hidx : n * d - 1 + 1 = n * d := by omega
    exact (congrArg (fun j : ℕ => cartierPowerInclusion i hI H n j ≫
      (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app
        (cartierPowerTwist i hI H n j).val = 0) hidx).mp
          (cartierPowerInclusion_comp_unit i hI H n (n * d - 1))
  change cartierPowerInclusion i hI H n (n * d) ≫
      (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app
        (cartierPowerTwist i hI H n (n * d)).val ≫ _ = 0
  rw [← Category.assoc, hz, zero_comp]

omit [IsNoetherianRing A] [IsClosedImmersion p] in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The prescribed original mixed sections really vanish on E. -/
theorem mixedCartierSection_residueMap
    (eI : (Scheme.Modules.pullback i).obj (Hom.idealModule i) ≅
      twistingSheaf k (ULift.{u} (Fin 2)) 1)
    (eH : (Scheme.Modules.pullback i).obj H.val ≅
      twistingSheaf k (ULift.{u} (Fin 2)) (d : ℤ))
    (n : ℕ) (hn : 1 ≤ n) (hn1 : 1 ≤ n * d) (a b : ι) :
    mixedCartierSection p i hI H eP d n hn a b ≫ cartierResidueMap i hI H d eI eH n = 0 := by
  simp only [mixedCartierSection, Category.assoc,
    cartierPowerInclusion_residueMap i hI H d eI eH n hn1, comp_zero]

omit [IsNoetherianRing A] [IsClosedImmersion p] in
/-- The diagonal mixed polynomial is the original coordinate nth power. -/
theorem mixedPolynomial_self (n : ℕ) (hn : 1 ≤ n) (a : ι) :
    mixedPolynomial (A := A) n hn a a = coordinatePower A ι n a := by
  apply Subtype.ext
  change MvPolynomial.X a ^ (n - 1) * MvPolynomial.X a = MvPolynomial.X a ^ n
  rw [← pow_succ, Nat.sub_add_cancel hn]

omit [IsNoetherianRing A] [IsClosedImmersion p] in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The original mixed homogeneous fraction recovers the original projective ratio. -/
theorem homogeneousChartFraction_mixed (n : ℕ) (hn : 1 ≤ n) (a b : ι) :
    homogeneousChartFraction A ι n (mixedPolynomial (A := A) n hn a b) a =
      coordinateRatio A ι a b := by
  apply HomogeneousLocalization.val_injective
  simp only [homogeneousChartFraction, mixedPolynomial, coordinateRatio,
    HomogeneousLocalization.Away.val_mk]
  rw [Localization.mk_eq_mk', IsLocalization.mk'_eq_iff_eq']
  simp only [pow_one]
  congr 1
  calc
    (MvPolynomial.X a ^ (n - 1) * MvPolynomial.X b) * MvPolynomial.X a =
        MvPolynomial.X b * (MvPolynomial.X a ^ (n - 1) * MvPolynomial.X a) := by ring
    _ = MvPolynomial.X b * MvPolynomial.X a ^ n := by
      rw [← pow_succ, Nat.sub_add_cancel hn]

end AlgebraicGeometry.Scheme.Surfaces.Contraction
