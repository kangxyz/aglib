/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Fields.FiniteEtaleTransfer.Trace
public import Aglib.AlgebraicGeometry.EtaleCohomology.SlicePullback.SourceSquare
public import Aglib.Algebra.Homology.DerivedCategory.Ext.ScalarTransfer
public import Aglib.CategoryTheory.Preadditive.CoprimeScalar

/-! # Coprime finite-field restriction on original sheaf cohomology

The actual finite-etale transfer, with its original integer-source
normalization, is combined with scalar inversion on the actual coefficient.
The source square then gives injectivity of the original scheme pullback.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry
open CategoryTheory.Sheaf.Hypercohomology
open Scheme.FiniteEtale Scheme.FiniteEtale.FieldGalois.Arbitrary

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Fields

universe u w₀ w₁

attribute [local instance] hasSheafifyLarge

variable (K E : Type u) [Field K] [Field E] [Algebra K E]
  [FiniteDimensional K E] [Algebra.IsSeparable K E]
  [HasExt.{w₀} (AbelianSheaf.{u, u + 1} (Spec (.of K)))]
  [HasExt.{w₁} (AbelianSheaf.{u, u + 1} (Spec (.of E)))]

/-- Restriction along an actual finite separable field extension of degree
coprime to an annihilator is injective on original cohomology in every degree. -/
theorem finiteField_cohomologyPullback_injective
    (A : AbelianSheaf.{u, u + 1} (Spec (.of K))) (p : ℕ)
    (hcop : (Module.finrank K E).Coprime p) (hp : p • 𝟙 A = 0) (q : ℕ) :
    Function.Injective (cohomologyPullback.{u, w₀, w₁}
      (Spec.map (CommRingCat.ofHom (algebraMap K E))) A q) := by
  let X := Spec (.of K)
  let J := Scheme.smallEtaleTopology X
  let U : X.Etale := (toEtale X).obj (finiteFieldCover K E)
  let : HasExt.{w₀} (AbelianSheaf.{u, u + 1} X) :=
    inferInstanceAs (HasExt.{w₀} (AbelianSheaf.{u, u + 1} (Spec (.of K))))
  let : HasExt.{w₁} (AbelianSheaf.{u, u + 1} U.left) :=
    inferInstanceAs (HasExt.{w₁} (AbelianSheaf.{u, u + 1} (Spec (.of E))))
  let : HasExt.{u + 2} (Sheaf (J.over U) AddCommGrpCat.{u + 1}) := HasExt.standard _
  have hi : IsIso (Module.finrank K E • 𝟙 A) :=
    Preadditive.isIso_nsmul_id_of_coprime A (Module.finrank K E) p hcop hp
  let : IsIso ((Module.finrank K E : ℤ) • 𝟙 A) := by
    simpa only [natCast_zsmul] using hi
  obtain ⟨τ, hτ⟩ := exists_finiteField_normalized_transfer K E
  have hterminal : StrictlyLocal.terminalIsTerminal K = etaleTerminalIsTerminal X :=
    Subsingleton.elim _ _
  have hτ' : τ ≫ representedIntegerAugmentation U =
      (Module.finrank K E : ℤ) • 𝟙 _ := by
    simpa only [representedIntegerAugmentation, hterminal, natCast_zsmul] using hτ
  have hinj := Ext.precomp_injective_of_scalar_transfer (A := A)
    (representedIntegerAugmentation U) τ (Module.finrank K E : ℤ) hτ' q
  exact cohomologyPullback_injective_of_represented_precomp.{u, w₀, w₁, u + 2}
    (X := X) U A q hinj

end AlgebraicGeometry.Scheme.EtaleCohomology.Fields
