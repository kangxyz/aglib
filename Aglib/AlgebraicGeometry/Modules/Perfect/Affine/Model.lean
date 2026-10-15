/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Aglib.AlgebraicGeometry.Modules.Perfect.Affine
public import Aglib.AlgebraicGeometry.Modules.Perfect.LocalModels
public import Aglib.AlgebraicGeometry.Modules.Complex.Tilde
public import Mathlib.Algebra.Homology.DerivedCategory.Plus

/-!
# Strict affine models through the original tilde/sections counit

An actual module-complex map to original affine global sections gives the
literal native tilde map followed by the original affine counit. Exactness
of tilde transports its quasi-isomorphism. A bounded finite-projective
source then gives an actual native strict-model witness. The ambient target
complex requires no term bound; the bounded-below comparison separately
retains an actual supplied native bounded-below packing of the target.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex

namespace AlgebraicGeometry.Scheme.Modules.Complex

variable (R : CommRingCat.{u}) (P : CochainComplex (ModuleCat.{u} R) ℤ)
  (K : CochainComplex (Spec R).Modules ℤ)
  (q : P ⟶ (moduleSpecΓFunctor.mapHomologicalComplex (.up ℤ)).obj K)

/-- The original native tilde of an actual module model map, followed by
the original affine tilde/global-sections adjunction counit. -/
def tildeModelMap : ((tilde.functor R).mapHomologicalComplex (.up ℤ)).obj P ⟶ K :=
  ((tilde.functor R).mapHomologicalComplex (.up ℤ)).map q ≫
    tildeGlobalSectionsCounit R (.up ℤ) K

/-- Every component retains the literal native map and original counit. -/
theorem tildeModelMap_f (j : ℤ) :
    (tildeModelMap R P K q).f j = tilde.map (q.f j) ≫ (K.X j).fromTildeΓ := by
  change (tilde.functor R).map (q.f j) ≫ (tildeGlobalSectionsCounit R (.up ℤ) K).f j = _
  rw [tildeGlobalSectionsCounit_f]
  rfl

/-- Exact native tilde preserves the actual model quasi-isomorphism;
composition with the original counit retains its actual quasi-isomorphism. -/
theorem tildeModelMap_quasiIso [QuasiIso q]
    [QuasiIso (tildeGlobalSectionsCounit R (.up ℤ) K)] :
    QuasiIso (tildeModelMap R P K q) := by
  dsimp only [tildeModelMap]
  infer_instance

local instance affineModelDerivedSheaves : HasDerivedCategory.{u + 1} (Spec R).Modules :=
  HasDerivedCategory.standard _

/-- A bounded finite-projective original module model and the original
counit give a global strict model of the actual ambient sheaf complex.
No boundedness hypothesis is imposed on that target complex. -/
theorem hasStrictModel_of_tildeModelMap (a b : ℤ)
    [P.IsStrictlyGE a] [P.IsStrictlyLE b]
    [∀ j, Module.Finite R (P.X j)] [∀ j, Module.Projective R (P.X j)]
    [QuasiIso q] [QuasiIso (tildeGlobalSectionsCounit R (.up ℤ) K)] :
    HasStrictModel K := by
  let : QuasiIso (tildeModelMap R P K q) := tildeModelMap_quasiIso R P K q
  exact ⟨⟨((tilde.functor R).mapHomologicalComplex (.up ℤ)).obj P,
      strictPerfect_tilde_of_finite_projective R P a b⟩,
    ⟨(asIso (DerivedCategory.Q.map (tildeModelMap R P K q))).symm⟩⟩

section Plus

variable (P : CochainComplex.Plus (ModuleCat.{u} R))
  (K : CochainComplex.Plus (Spec R).Modules)
  (q : P.obj ⟶ (moduleSpecΓFunctor.mapHomologicalComplex (.up ℤ)).obj K.obj)

/-- The original model/counit arrow retains the supplied actual native
bounded-below packings of source and target. -/
def tildeModelMapPlus : (tilde.functor R).mapCochainComplexPlus.obj P ⟶ K :=
  ⟨tildeModelMap R P.obj K.obj q⟩

/-- The actual original model arrow gives an isomorphism in the native
bounded-below localization. The target packing is actual input data. -/
def tildeModelDerivedIsoPlus [QuasiIso q]
    [QuasiIso (tildeGlobalSectionsCounit R (.up ℤ) K.obj)] :
    DerivedCategory.Plus.Q.obj ((tilde.functor R).mapCochainComplexPlus.obj P) ≅
      DerivedCategory.Plus.Q.obj K := by
  let : IsIso (DerivedCategory.Plus.Q.map (tildeModelMapPlus R P K q)) :=
    Localization.inverts _ (CochainComplex.Plus.quasiIso (Spec R).Modules) _
      (tildeModelMap_quasiIso R P.obj K.obj q)
  exact asIso (DerivedCategory.Plus.Q.map (tildeModelMapPlus R P K q))

/-- The native derived comparison retains the literal original model map. -/
theorem tildeModelDerivedIsoPlus_hom [QuasiIso q]
    [QuasiIso (tildeGlobalSectionsCounit R (.up ℤ) K.obj)] :
    (tildeModelDerivedIsoPlus R P K q).hom =
      DerivedCategory.Plus.Q.map (tildeModelMapPlus R P K q) := rfl

end Plus

end AlgebraicGeometry.Scheme.Modules.Complex
