/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.LocallyFree.QuasiAffineCoresolution
public import Aglib.AlgebraicGeometry.Spec.SplitAdicSections
public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.AlgebraicGeometry.Noetherian

/-! # Finite original vector-bundle sections on a Hartogs open

The existing finite-free co-resolution embeds the original vector bundle in
a finite free sheaf. Evaluation preserves this monomorphism and identifies
the latter's sections with a finite power of the original scalar ring.
No normality, domain hypothesis, reflexive replacement, or cover effectivity
is used. The affine-open consumer restricts scalars along its original
`affineScalarMap`, not an independently chosen ring identification.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules.Coherent

universe u

attribute [local instance] Abelian.hasFiniteBiproducts

/-- Evaluation of the original finite free sheaf is the finite power of
the original ring of global functions. -/
def finiteFreeGlobalSectionsIso (X : Scheme.{u}) (I : Type u) [Finite I] :
    (SheafOfModules.evaluation X.ringCatSheaf (op ⊤)).obj
      (SheafOfModules.free (R := X.ringCatSheaf) I) ≅
        ModuleCat.of Γ(X, ⊤) (I → Γ(X, ⊤)) := by
  let E : X.Modules ⥤ ModuleCat.{u} Γ(X, ⊤) :=
    SheafOfModules.evaluation X.ringCatSheaf (op ⊤)
  let f : I → X.Modules := fun _ => SheafOfModules.unit X.ringCatSheaf
  let : PreservesLimitsOfShape (Discrete I) E :=
    SheafOfModules.evaluationPreservesLimitsOfShape (R := X.ringCatSheaf)
      (Discrete I) (op ⊤)
  let e : SheafOfModules.free (R := X.ringCatSheaf) I ≅ ∏ᶜ f :=
    (biproduct.isoCoproduct f).symm ≪≫ biproduct.isoProduct f
  exact E.mapIso e ≪≫ PreservesProduct.iso E f ≪≫
    ModuleCat.piIsoPi (fun _ : I => ModuleCat.of Γ(X, ⊤) Γ(X, ⊤))

/-- A vector bundle on an original quasi-affine scheme has finite global
sections when its original ring of global functions is Noetherian. -/
theorem finite_globalSections_of_quasiAffine_of_noetherian
    (X : Scheme.{u}) [X.IsQuasiAffine] [IsNoetherianRing Γ(X, ⊤)]
    (M : X.Modules) [IsFiniteLocallyFree X M] :
    Module.Finite Γ(X, ⊤) Γ(M, ⊤) := by
  obtain ⟨I, J, hI, hJ, i, d, w, _, hi, _⟩ :=
    exists_universallyExact_finiteFree_coresolution X M
  let := hI
  let := hi
  let E : X.Modules ⥤ ModuleCat.{u} Γ(X, ⊤) :=
    SheafOfModules.evaluation X.ringCatSheaf (op ⊤)
  let e := finiteFreeGlobalSectionsIso X I
  let : Mono (E.map i) := by
    change Mono ((SheafOfModules.evaluation X.ringCatSheaf (op ⊤)).map i)
    infer_instance
  let a : ModuleCat.of Γ(X, ⊤) Γ(M, ⊤) ⟶
      ModuleCat.of Γ(X, ⊤) (I → Γ(X, ⊤)) := E.map i ≫ e.hom
  have : Mono a := inferInstance
  exact Module.Finite.of_injective a.hom
    ((ModuleCat.mono_iff_injective a).mp inferInstance)

/-- Finiteness over the original source scalars. Surjectivity of the
specified scalar map suffices; no new scalar equivalence is selected. -/
theorem finite_globalSections_of_surjective_scalar
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (X : Scheme.{u}) [X.IsQuasiAffine]
    (σ : A →+* Γ(X, ⊤)) (hσ : Function.Surjective σ)
    (M : X.Modules) [IsFiniteLocallyFree X M] :
    letI : Module A Γ(M, ⊤) :=
      Module.compHom _ σ
    Module.Finite A Γ(M, ⊤) := by
  let R := Γ(X, ⊤)
  let P := Γ(M, ⊤)
  let : IsNoetherianRing R := isNoetherianRing_of_surjective A R σ hσ
  let : Algebra A R := σ.toAlgebra
  let : Module A P := Module.compHom P σ
  let : IsScalarTower A R P := .of_algebraMap_smul fun _ _ => rfl
  let : Module.Finite A R :=
    Module.Finite.of_surjective (Algebra.linearMap A R) hσ
  let : Module.Finite R P := finite_globalSections_of_quasiAffine_of_noetherian X M
  exact Module.Finite.trans R P

/-- An original Hartogs scalar identification gives finite sections for
every finite locally free module on the unchanged affine open. -/
theorem finite_globalSections_of_hartogs_open
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (U : (Spec (.of A)).Opens)
    (hU : Function.Bijective (affineScalarMap U.ι))
    (M : U.toScheme.Modules) [IsFiniteLocallyFree U.toScheme M] :
    letI : Module A Γ(M, ⊤) :=
      Module.compHom _ (affineScalarMap U.ι)
    Module.Finite A Γ(M, ⊤) := by
  let : CompactSpace U := isCompact_iff_compactSpace.mp
    (TopologicalSpace.NoetherianSpace.isCompact (U : Set (Spec (.of A))))
  let : U.toScheme.IsQuasiAffine := IsQuasiAffine.of_isImmersion U.ι
  exact finite_globalSections_of_surjective_scalar A U.toScheme
    (affineScalarMap U.ι) hU.surjective M

end AlgebraicGeometry.Scheme.Modules.Coherent
