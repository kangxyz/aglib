/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Godement.Stalk.TotalHomotopy
public import Aglib.AlgebraicGeometry.Modules.Stalk.Reflection

/-!
Source: `Quillen/AlgebraicGeometry/Scheme/Sheaf/GodementTotalQuasiIso.lean` at LOCAL Quillen
`189a8e779f0c68b2dfc6f8195daebb3e684a5905`. Selection: whole_general;
source ranges [[1, 66]]. Actual objects, maps and hypotheses are preserved.
-/

/-!
# The actual Godement total augmentation on original lower-bounded complexes

The original natural stalk column contractions give an actual signed total
homotopy equivalence of the original augmentation on every module stalk. The
original exact and jointly conservative module stalks then reflect homology-map
isomorphisms. Weak-arrow compatibility follows from original naturality and
two-out-of-three, with no augmentation or resolution assumed.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules.Godement

/-- The actual original total augmentation is a quasi-isomorphism for every
original lower-bounded complex of arbitrary scheme module sheaves. -/
instance godementTotalUnit_quasiIso (X : Scheme.{u}) (K : CochainComplex.Plus X.Modules) :
    QuasiIso ((godementTotalUnit X).app K.obj) :=
  godement_quasiIso_of_moduleStalks _ (fun x => godementStalkTotalUnit_quasiIso X x K)

/-- The same actual theorem with an explicit original lower bound. -/
theorem godementTotalUnit_quasiIso_of_isStrictlyGE (X : Scheme.{u})
    (K : CochainComplex X.Modules ℤ) (a : ℤ) [K.IsStrictlyGE a] :
    QuasiIso ((godementTotalUnit X).app K) :=
  godementTotalUnit_quasiIso X ⟨K, ⟨a, inferInstance⟩⟩

/-- The actual natural weak augmentation in the original lower-bounded category. -/
def godementTotalPlusUnit (X : Scheme.{u}) :
    𝟭 (CochainComplex.Plus X.Modules) ⟶ godementTotalPlus X where
  app K := ObjectProperty.homMk ((godementTotalUnit X).app K.obj)
  naturality {K L} f := by
    apply ObjectProperty.hom_ext
    exact (godementTotalUnit X).naturality f.hom

instance godementTotalPlusUnit_quasiIso (X : Scheme.{u}) (K : CochainComplex.Plus X.Modules) :
    QuasiIso ((godementTotalPlusUnit X).app K).hom := godementTotalUnit_quasiIso X K

/-- The actual totalization preserves the original weak arrows on lower-bounded
complexes, by naturality of the actual proved quasi-isomorphism unit. -/
theorem godementTotalPlus_map_quasiIso {X : Scheme.{u}}
    {K L : CochainComplex.Plus X.Modules} (f : K ⟶ L) [QuasiIso f.hom] :
    QuasiIso ((godementTotalPlus X).map f).hom := by
  change QuasiIso ((godementTotal X).map f.hom)
  have : QuasiIso ((godementTotalUnit X).app K.obj) := godementTotalUnit_quasiIso X K
  have : QuasiIso ((godementTotalUnit X).app L.obj) := godementTotalUnit_quasiIso X L
  have : QuasiIso ((godementTotalUnit X).app K.obj ≫ (godementTotal X).map f.hom) := by
    rw [← (godementTotalUnit X).naturality f.hom]
    dsimp only [CategoryTheory.Functor.id_map]
    infer_instance
  exact quasiIso_of_comp_left ((godementTotalUnit X).app K.obj) ((godementTotal X).map f.hom)

end AlgebraicGeometry.Scheme.Modules.Godement
