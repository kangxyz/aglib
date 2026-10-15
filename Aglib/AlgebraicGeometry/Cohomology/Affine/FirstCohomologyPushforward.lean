/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: R5Lab contributors
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Affine.SheafCohomology
public import Aglib.AlgebraicGeometry.Cohomology.Functoriality.Pullback
public import Aglib.AlgebraicGeometry.Cohomology.Exact.LongExact
public import Aglib.AlgebraicGeometry.Cohomology.Affine.PushforwardAcyclicity
public import Aglib.AlgebraicGeometry.Cohomology.Flasque.Pushforward
public import Mathlib.LinearAlgebra.Isomorphisms
/-!
# Actual first cohomology and affine direct image

The original structural-K first cohomology of a module sheaf is identified
with the global-section cokernel of an actual short exact sequence with an
acyclic middle term. For an actual affine K-morphism and a quasicoherent
module, the initial module-resolution sequence and its direct image give the
same cokernel, yielding a K-linear equivalence of the original first
cohomology groups. Direct image is not asserted to be exact on arbitrary
module or additive sheaves.

Extraction source: `R5Lab.AlgebraicGeometry.Curves.Cohomology.ProperCurves.FinitePushforward` at
  R5Lab revision
`95a3772b895fbc19a81684be4ffd519d0fdcd6b3`; all declarations are retained.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
open AlgebraicGeometry.Scheme.OverField
namespace AlgebraicGeometry.Scheme.Cohomology
universe u
variable {K : Type u} [Field K]
/-- The map on global module sections, linear for the structural field action. -/
def moduleGlobalSectionsMap (X : FScheme K) {M N : X.left.Modules} (φ : M ⟶ N) :
    M.val.obj (op ⊤) →ₗ[K] N.val.obj (op ⊤) where
  __ := (φ.val.app (op ⊤)).hom.toAddMonoidHom
  map_smul' a x := (φ.val.app (op ⊤)).hom.map_smul (constants X a) x

@[simp] theorem moduleH0Equiv_map (X : FScheme K) {M N : X.left.Modules}
    (φ : M ⟶ N) (x : moduleCohomology K X M 0) :
    moduleH0Equiv X N (moduleCohomologyMap X φ 0 x) =
      moduleGlobalSectionsMap X φ (moduleH0Equiv X M x) := by
  exact (Sheaf.H.equiv₀_naturality isTerminalTop (coefficientSheafMap X φ) x).symm

/-- Global sections of direct image, with the literal structural field action. -/
def modulePushforwardGlobalSectionsEquiv {Y X : FScheme K} (f : Y ⟶ X)
    (M : Y.left.Modules) :
    ((Scheme.Modules.pushforward f.left).obj M).val.obj (op ⊤) ≃ₗ[K]
      M.val.obj (op ⊤) where
  __ := AddEquiv.refl _
  map_smul' a x := by
    change M.val.obj (op ⊤) at x
    change (f.left.app ⊤).hom (constants X a) • x = constants Y a • x
    congr 1
    exact map_constants f a

@[simp] theorem modulePushforwardGlobalSectionsEquiv_map {Y X : FScheme K} (f : Y ⟶ X)
    {M N : Y.left.Modules} (φ : M ⟶ N)
    (x : ((Scheme.Modules.pushforward f.left).obj M).val.obj (op ⊤)) :
    modulePushforwardGlobalSectionsEquiv f N
      (moduleGlobalSectionsMap X ((Scheme.Modules.pushforward f.left).map φ) x) =
    moduleGlobalSectionsMap Y φ (modulePushforwardGlobalSectionsEquiv f M x) := rfl

/-- The common global-section cokernel used by affine direct image. -/
def modulePushforwardSectionCokernelEquiv {Y X : FScheme K} (f : Y ⟶ X)
    {M N : Y.left.Modules} (φ : M ⟶ N) :
    (((Scheme.Modules.pushforward f.left).obj N).val.obj (op ⊤) ⧸
      LinearMap.range (moduleGlobalSectionsMap X ((Scheme.Modules.pushforward f.left).map φ)))
      ≃ₗ[K] (N.val.obj (op ⊤) ⧸ LinearMap.range (moduleGlobalSectionsMap Y φ)) := by
  apply Submodule.Quotient.equiv _ _ (modulePushforwardGlobalSectionsEquiv f N)
  ext y
  constructor
  · rintro ⟨z, ⟨x, rfl⟩, rfl⟩
    exact ⟨modulePushforwardGlobalSectionsEquiv f M x,
      (modulePushforwardGlobalSectionsEquiv_map f φ x).symm⟩
  · rintro ⟨x, rfl⟩
    refine ⟨moduleGlobalSectionsMap X ((Scheme.Modules.pushforward f.left).map φ)
      ((modulePushforwardGlobalSectionsEquiv f M).symm x), ⟨_, rfl⟩, ?_⟩
    simp only [LinearEquiv.coe_coe, modulePushforwardGlobalSectionsEquiv_map,
      LinearEquiv.apply_symm_apply]

/-- Affine direct image preserves the initial short exact sequence of an actual
injective resolution of a quasicoherent module. This does not assert exactness
of direct image on all module sheaves or on all additive sheaves. -/
theorem affinePushforward_initialSequence_shortExact {Y X : Scheme.{u}}
    (f : Y ⟶ X) [IsAffineHom f] (M : Y.Modules) [M.IsQuasicoherent]
    (I : InjectiveResolution M) :
    ((CategoryTheory.InjectiveResolution.initialSequence I).map
      (Scheme.Modules.pushforward f)).ShortExact := by
  let F := Scheme.Modules.pushforward f
  let S := CategoryTheory.InjectiveResolution.initialSequence I
  have hS := CategoryTheory.InjectiveResolution.initialSequence_shortExact I
  have hmono : Mono S.f := hS.mono_f
  have he := AlgebraicGeometry.Scheme.Modules.affinePushforward_injectiveResolution_exact_succ f
    M I 0
  rw [HomologicalComplex.exactAt_iff' _ 0 1 2 (by simp) (by simp)] at he
  have hk := he.epi_kernelLift
  have hcomp : F.map S.g ≫ kernelComparison (I.cocomplex.d 1 2) F =
      kernel.lift (F.map (I.cocomplex.d 1 2)) (F.map (I.cocomplex.d 0 1))
        (by rw [← F.map_comp, I.cocomplex.d_comp_d, F.map_zero]) := by
    apply (cancel_mono (kernel.ι (F.map (I.cocomplex.d 1 2)))).mp
    simp only [S, CategoryTheory.InjectiveResolution.initialSequence, Category.assoc,
      kernelComparison_comp_ι, ← F.map_comp, kernel.lift_ι]
  have : Epi (F.map S.g) := by
    apply (epi_comp_iff_of_isIso _ (kernelComparison (I.cocomplex.d 1 2) F)).mp
    rw [hcomp]
    exact hk
  exact { exact := hS.exact.map_of_mono_of_preservesKernel F hmono inferInstance
          mono_f := by change Mono (F.map S.f); infer_instance
          epi_g := by change Epi (F.map S.g); infer_instance }

/-- The two middle terms used in the first-degree comparison are acyclic for
actual additive-sheaf cohomology; no preservation of injectives is required. -/
theorem subsingleton_moduleAddSheafH_pushforward_injective {Y X : Scheme.{u}}
    (f : Y ⟶ X) (I : Y.Modules) [Injective I] (n : ℕ) :
    Subsingleton (Sheaf.H.{u + 1}
      (moduleAddSheaf X ((Scheme.Modules.pushforward f).obj I)) (n + 1)) := by
  let : TopCat.Presheaf.IsFlasque I.presheaf :=
    AlgebraicGeometry.Scheme.Modules.injective_isFlasque Y I
  let : TopCat.Presheaf.IsFlasque
      (moduleAddSheaf X ((Scheme.Modules.pushforward f).obj I)).obj :=
    AlgebraicGeometry.Scheme.Modules.pushforward_isFlasque f I
  exact subsingleton_sheafH_of_isFlasque _ n

/-- The connecting map with its degree-zero source written as actual global sections. -/
def moduleConnectingOfSections (X : FScheme K) (S : ShortComplex X.left.Modules)
    (hS : S.ShortExact) : S.X₃.val.obj (op ⊤) →ₗ[K] moduleCohomology K X S.X₁ 1 :=
  (moduleCohomologyConnecting X S hS 0).comp (moduleH0Equiv X S.X₃).symm.toLinearMap

theorem moduleConnectingOfSections_range_eq_ker (X : FScheme K)
    (S : ShortComplex X.left.Modules) (hS : S.ShortExact) :
    LinearMap.range (moduleGlobalSectionsMap X S.g) =
      LinearMap.ker (moduleConnectingOfSections X S hS) := by
  ext z
  rw [LinearMap.mem_range, LinearMap.mem_ker]
  constructor
  · rintro ⟨y, rfl⟩
    apply (moduleCohomologyConnecting_exact_left X S hS 0 _).mpr
    refine ⟨(moduleH0Equiv X S.X₂).symm y, ?_⟩
    apply (moduleH0Equiv X S.X₃).injective
    simp only [moduleH0Equiv_map, LinearEquiv.apply_symm_apply]
    exact ((moduleH0Equiv X S.X₃).apply_symm_apply _).symm
  · intro hz
    obtain ⟨y, hy⟩ := (moduleCohomologyConnecting_exact_left X S hS 0 _).mp hz
    refine ⟨moduleH0Equiv X S.X₂ y, ?_⟩
    rw [← moduleH0Equiv_map, hy]
    exact (moduleH0Equiv X S.X₃).apply_symm_apply z

theorem moduleConnectingOfSections_surjective (X : FScheme K)
    (S : ShortComplex X.left.Modules) (hS : S.ShortExact)
    [Subsingleton (moduleCohomology K X S.X₂ 1)] :
    Function.Surjective (moduleConnectingOfSections X S hS) := by
  intro x
  obtain ⟨y, hy⟩ := (moduleCohomologyConnecting_exact_right X S hS 0 x).mp
    (Subsingleton.elim _ _)
  refine ⟨moduleH0Equiv X S.X₃ y, ?_⟩
  simpa only [moduleConnectingOfSections, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] using hy

/-- A first-degree comparison for the actual structural-field cohomology of a
short exact module sequence with an H1-acyclic middle term. The quotient map is
literally induced by the original connecting map. -/
def moduleSectionCokernelEquivH1 (X : FScheme K)
    (S : ShortComplex X.left.Modules) (hS : S.ShortExact)
    [Subsingleton (moduleCohomology K X S.X₂ 1)] :
    (S.X₃.val.obj (op ⊤) ⧸ LinearMap.range (moduleGlobalSectionsMap X S.g)) ≃ₗ[K]
      moduleCohomology K X S.X₁ 1 :=
  (Submodule.quotEquivOfEq _ _ (moduleConnectingOfSections_range_eq_ker X S hS)).trans
    ((moduleConnectingOfSections X S hS).quotKerEquivOfSurjective
      (moduleConnectingOfSections_surjective X S hS))

@[simp] theorem moduleSectionCokernelEquivH1_mk (X : FScheme K)
    (S : ShortComplex X.left.Modules) (hS : S.ShortExact)
    [Subsingleton (moduleCohomology K X S.X₂ 1)] (z : S.X₃.val.obj (op ⊤)) :
    moduleSectionCokernelEquivH1 X S hS (Submodule.Quotient.mk z) =
      moduleCohomologyConnecting X S hS 0 ((moduleH0Equiv X S.X₃).symm z) := by
  simp only [moduleSectionCokernelEquivH1, LinearEquiv.trans_apply,
    Submodule.quotEquivOfEq_mk, LinearMap.quotKerEquivOfSurjective_apply_mk]
  rfl

/-- The same cokernel comparison in degree-zero cohomology coordinates. -/
def moduleH0CokernelEquivH1 (X : FScheme K)
    (S : ShortComplex X.left.Modules) (hS : S.ShortExact)
    [Subsingleton (moduleCohomology K X S.X₂ 1)] :
    (moduleCohomology K X S.X₃ 0 ⧸ LinearMap.range (moduleCohomologyMap X S.g 0)) ≃ₗ[K]
      moduleCohomology K X S.X₁ 1 :=
  (Submodule.quotEquivOfEq _ _
    (moduleCohomologyConnecting_exact_left X S hS 0).linearMap_ker_eq.symm).trans
    ((moduleCohomologyConnecting X S hS 0).quotKerEquivOfSurjective
      (fun x ↦ (moduleCohomologyConnecting_exact_right X S hS 0 x).mp
        (Subsingleton.elim _ _)))

@[simp] theorem moduleH0CokernelEquivH1_mk (X : FScheme K)
    (S : ShortComplex X.left.Modules) (hS : S.ShortExact)
    [Subsingleton (moduleCohomology K X S.X₂ 1)]
    (z : moduleCohomology K X S.X₃ 0) :
    moduleH0CokernelEquivH1 X S hS (Submodule.Quotient.mk z) =
      moduleCohomologyConnecting X S hS 0 z := by
  simp only [moduleH0CokernelEquivH1, LinearEquiv.trans_apply,
    Submodule.quotEquivOfEq_mk, LinearMap.quotKerEquivOfSurjective_apply_mk]

/-- The reusable initial-resolution comparison, retaining the original Ext
universe and the structural K-action. -/
def moduleH1EquivResolutionSectionCokernel (X : FScheme K)
    (M : X.left.Modules) (I : InjectiveResolution M) :
    moduleCohomology K X M 1 ≃ₗ[K]
      ((CategoryTheory.InjectiveResolution.initialSequence I).X₃.val.obj (op ⊤) ⧸
        LinearMap.range (moduleGlobalSectionsMap X
          (CategoryTheory.InjectiveResolution.initialSequence I).g)) := by
  let : Subsingleton (moduleCohomology K X
      (CategoryTheory.InjectiveResolution.initialSequence I).X₂ 1) :=
    subsingleton_moduleAddSheafH_of_injective (I.cocomplex.X 0) 0
  exact (moduleSectionCokernelEquivH1 X _
    (CategoryTheory.InjectiveResolution.initialSequence_shortExact I)).symm

/-- Actual first-cohomology comparison for affine direct image of a
quasicoherent module sheaf. Both field actions are the structural actions from
`moduleCohomology`; both sides are identified through the same global-section
cokernel of the given actual injective resolution. -/
def affinePushforwardModuleH1EquivOfResolution {Y X : FScheme K}
    (f : Y ⟶ X) [IsAffineHom f.left] (M : Y.left.Modules) [M.IsQuasicoherent]
    (I : InjectiveResolution M) :
    moduleCohomology K X ((Scheme.Modules.pushforward f.left).obj M) 1 ≃ₗ[K]
      moduleCohomology K Y M 1 := by
  let S := CategoryTheory.InjectiveResolution.initialSequence I
  let F := Scheme.Modules.pushforward f.left
  let : Subsingleton (moduleCohomology K X (S.map F).X₂ 1) :=
    subsingleton_moduleAddSheafH_pushforward_injective f.left (I.cocomplex.X 0) 0
  let : Subsingleton (moduleCohomology K Y S.X₂ 1) :=
    subsingleton_moduleAddSheafH_of_injective (I.cocomplex.X 0) 0
  exact (moduleSectionCokernelEquivH1 X (S.map F)
    (affinePushforward_initialSequence_shortExact f.left M I)).symm |>.trans
    ((modulePushforwardSectionCokernelEquiv f S.g).trans
      (moduleSectionCokernelEquivH1 Y S
        (CategoryTheory.InjectiveResolution.initialSequence_shortExact I)))

/-- Resolution-free statement of the bounded affine first-cohomology comparison. -/
def affinePushforwardModuleH1Equiv {Y X : FScheme K}
    (f : Y ⟶ X) [IsAffineHom f.left] (M : Y.left.Modules) [M.IsQuasicoherent] :
    moduleCohomology K X ((Scheme.Modules.pushforward f.left).obj M) 1 ≃ₗ[K]
      moduleCohomology K Y M 1 :=
  affinePushforwardModuleH1EquivOfResolution f M (injectiveResolution M)

end AlgebraicGeometry.Scheme.Cohomology
