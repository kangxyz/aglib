/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Generators.OpenFreeFunctor
public import Aglib.CategoryTheory.Abelian.Injective.ResolutionKernels
public import Aglib.AlgebraicGeometry.Modules.Epimorphisms
public import Aglib.AlgebraicGeometry.Modules.Exact
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.Topology.Sheaves.Flasque
/-!
# Flasque scheme module sheaves and dimension shifting

This module uses mathlib's actual `TopCat.Presheaf.IsFlasque` property. Injective
module sheaves are flasque. Short exact sequences with flasque kernel lift
sections over every open, and flasque quotients remain flasque. Applied to the
actual kernel sequences of an injective resolution, these results prove that
all successive kernels of a flasque module sheaf are flasque.

All statements hold on arbitrary schemes; no quasicoherence is assumed.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v w z
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

namespace AlgebraicGeometry.Scheme.Modules

/-- Injective module sheaves are flasque on every scheme. -/
instance injective_isFlasque (X : Scheme.{u}) (M : X.Modules) [Injective M] :
    TopCat.Presheaf.IsFlasque M.presheaf where
  epi {_U _V} h := (AddCommGrpCat.epi_iff_surjective _).mpr
    (injective_sections_restrict_surjective X M h.unop)

/-- The actual underlying additive sheaf, with source explicitly `X.Modules`. -/
abbrev toAdditiveSheaf (X : Scheme.{u}) :
    X.Modules ⥤ TopCat.Sheaf AddCommGrpCat.{u} X.toTopCat :=
  SheafOfModules.toSheaf.{u} X.ringCatSheaf

instance toAdditiveSheaf_additive (X : Scheme.{u}) : (toAdditiveSheaf X).Additive where
  map_add := by intros; rfl

/-- Forgetting the module structure preserves short exact sequences. -/
lemma shortExact_toSheaf {X : Scheme.{u}} {S : ShortComplex X.Modules}
    (hS : S.ShortExact) : (S.map (toAdditiveSheaf X)).ShortExact := by
  let F := SheafOfModules.toSheaf.{u} X.ringCatSheaf
  let : PreservesFiniteLimits F := inferInstanceAs
    (PreservesFiniteLimits (SheafOfModules.toSheaf.{u} X.ringCatSheaf))
  let : PreservesFiniteColimits F := ⟨fun _ => inferInstance⟩
  exact hS.map_of_exact F

/-- A sheaf short exact sequence with flasque kernel is surjective on sections
over every open; the middle and quotient sheaves are unrestricted. -/
lemma sections_surjective_of_flasque_kernel {X : Scheme.{u}} {S : ShortComplex X.Modules}
    (hS : S.ShortExact) [TopCat.Presheaf.IsFlasque S.X₁.presheaf] (U : X.Opens) :
    Function.Surjective (S.g.app U) := by
  let : TopCat.Sheaf.IsFlasque ((S.map (toAdditiveSheaf X)).X₁) :=
    inferInstanceAs (TopCat.Presheaf.IsFlasque S.X₁.presheaf)
  have h := TopCat.Sheaf.IsFlasque.epi_of_shortExact (U := U) (shortExact_toSheaf hS)
  exact (AddCommGrpCat.epi_iff_surjective _).mp h

/-- The quotient of a flasque sheaf by a flasque subsheaf is flasque. -/
lemma flasque_of_shortExact {X : Scheme.{u}} {S : ShortComplex X.Modules}
    (hS : S.ShortExact) [TopCat.Presheaf.IsFlasque S.X₁.presheaf]
    [TopCat.Presheaf.IsFlasque S.X₂.presheaf] :
    TopCat.Presheaf.IsFlasque S.X₃.presheaf := by
  let : TopCat.Sheaf.IsFlasque ((S.map (toAdditiveSheaf X)).X₁) :=
    inferInstanceAs (TopCat.Presheaf.IsFlasque S.X₁.presheaf)
  let : TopCat.Sheaf.IsFlasque ((S.map (toAdditiveSheaf X)).X₂) :=
    inferInstanceAs (TopCat.Presheaf.IsFlasque S.X₂.presheaf)
  exact TopCat.Sheaf.IsFlasque.of_shortExact_of_isFlasque₁₂ (shortExact_toSheaf hS)

/-- Successive differential kernels of an injective resolution of a flasque
module sheaf remain flasque. This is a theorem, not a resolution hypothesis. -/
lemma injectiveResolution_kernel_isFlasque {X : Scheme.{u}}
    (M : X.Modules) [TopCat.Presheaf.IsFlasque M.presheaf]
    (I : CategoryTheory.InjectiveResolution M) (n : ℕ) :
    TopCat.Presheaf.IsFlasque (kernel (I.cocomplex.d (n + 1) (n + 2))).presheaf := by
  induction n with
  | zero =>
    let : TopCat.Presheaf.IsFlasque
        (CategoryTheory.InjectiveResolution.initialSequence I).X₁.presheaf :=
      inferInstanceAs (TopCat.Presheaf.IsFlasque M.presheaf)
    let : TopCat.Presheaf.IsFlasque
        (CategoryTheory.InjectiveResolution.initialSequence I).X₂.presheaf :=
      injective_isFlasque X (I.cocomplex.X 0)
    exact flasque_of_shortExact
      (CategoryTheory.InjectiveResolution.initialSequence_shortExact I)
  | succ n ih =>
    let : TopCat.Presheaf.IsFlasque
        (CategoryTheory.InjectiveResolution.kernelSequence I (n + 1)).X₁.presheaf := ih
    let : TopCat.Presheaf.IsFlasque
        (CategoryTheory.InjectiveResolution.kernelSequence I (n + 1)).X₂.presheaf :=
      injective_isFlasque X (I.cocomplex.X (n + 1))
    exact flasque_of_shortExact
      (CategoryTheory.InjectiveResolution.kernelSequence_shortExact I (n + 1))

end AlgebraicGeometry.Scheme.Modules
