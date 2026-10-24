/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aglib contributors
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.KInjective.Existence.KillSmallMaps.Attachment
public import Aglib.Algebra.Homology.AcyclicColimit
public import Aglib.Algebra.Homology.MappingCone.Pushout
public import Aglib.Algebra.Homology.MappingCone.Inclusion

/-! # The actual acyclic-family attachment is a quasi-isomorphism -/

@[expose] public noncomputable section

universe w v u

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Abelian C]
  {ι : Type w} [HasColimitsOfShape (Discrete ι) C]
  [HasExactColimitsOfShape (Discrete ι) C]
  (A : ι → CochainComplex C ℤ) {K : CochainComplex C ℤ}
  (f : ∀ i, A i ⟶ K)

/-- Acyclicity of the actual coproduct follows from exactness of this colimit shape. -/
lemma killSmallMaps_coproduct_acyclic (hA : ∀ i, (A i).Acyclic) : (∐ A).Acyclic :=
  HomologicalComplex.acyclic_colimit (Discrete.functor A) (fun i => hA i.as)

set_option backward.isDefEq.respectTransparency false in
/-- The original pushout inclusion preserves homology when every attached source is acyclic. -/
lemma killSmallMapsι_quasiIso (hA : ∀ i, (A i).Acyclic) :
    QuasiIso (killSmallMapsι A f) := by
  let e := mappingCone.pushoutIdentityIso (Sigma.desc f)
  have : QuasiIso (killSmallMapsι A f ≫ e.hom) := by
    change QuasiIso (pushout.inl (Sigma.desc f) (mappingCone.inr (𝟙 (∐ A))) ≫
      (mappingCone.pushoutIdentityIso (Sigma.desc f)).hom)
    rw [mappingCone.inl_pushoutIdentityIso_hom]
    exact mappingCone.quasiIso_inr_of_acyclic _ (killSmallMaps_coproduct_acyclic A hA)
  exact quasiIso_of_comp_right (killSmallMapsι A f) e.hom

end CochainComplex
