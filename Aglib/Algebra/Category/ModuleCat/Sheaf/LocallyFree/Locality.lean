/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.Presentation
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree

/-!
# Locality of finite bases for module sheaves on a site

Relocated from `Aglib/AlgebraicGeometry/Modules/LocallyFree/Locality.lean` at Aglib
`451aeda6b8bb5b44402b574dd6cf60f912360f8c`,
SHA-256 `63707ec1099ec3f8e22aac5b09edaf5cac5cba94047bc52ea700beab11dafad2`.
The statements retain their original universes, hypotheses and actual maps.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v w w' t t'
open CategoryTheory CategoryTheory.Limits

namespace SheafOfModules

section BasisTransport
variable {C : Type w} [Category.{w'} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}}
  [∀ U, HasSheafify (J.over U) AddCommGrpCat.{u}]
  [∀ U, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Transport finite local bases along an isomorphism on an arbitrary site. -/
theorem finiteLocalBasis_of_sheafIso {M N : SheafOfModules.{u} R}
    (e : M ≅ N) (q : SheafOfModules.LocalGeneratorsData.{v} M)
    [hq : q.IsLocallyFreeData] [hf : q.IsFiniteType] :
    ∃ q' : SheafOfModules.LocalGeneratorsData.{v} N,
      q'.IsLocallyFreeData ∧ q'.IsFiniteType := by
  let q' : SheafOfModules.LocalGeneratorsData.{v} N :=
    { I := q.I
      X := q.X
      coversTop := q.coversTop
      generators i := (q.generators i).ofEpi
        ((SheafOfModules.overFunctor R (q.X i)).mapIso e).hom }
  refine ⟨q', ?_, ?_⟩
  · constructor
    intro i
    exact generatingSections_ofEpi_isIso (q.generators i)
      ((SheafOfModules.overFunctor R (q.X i)).mapIso e).hom
  · constructor
    intro i
    constructor
    exact (hf.isFiniteType i).finite

end BasisTransport

section BasisBinding
variable {C : Type w} [Category.{w'} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}}
  [∀ U, HasSheafify (J.over U) AddCommGrpCat.{u}]
  [∀ U, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ U V, HasSheafify ((J.over U).over V) AddCommGrpCat.{u}]
  [∀ U V, ((J.over U).over V).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Compose a cover with finite local bases on its slice sites. -/
theorem finiteLocalBasis_bind (M : SheafOfModules.{u} R) {ι : Type u}
    (U : ι → C) (hU : J.CoversTop U)
    (q : ∀ i, SheafOfModules.LocalGeneratorsData.{u} (M.over (U i)))
    (hq : ∀ i, (q i).IsLocallyFreeData) (hf : ∀ i, (q i).IsFiniteType) :
    ∃ q' : SheafOfModules.LocalGeneratorsData.{u} M,
      q'.IsLocallyFreeData ∧ q'.IsFiniteType := by
  let (i : ι) : (q i).IsLocallyFreeData := hq i
  let (i : ι) : (q i).IsFiniteType := hf i
  let q' := SheafOfModules.QuasicoherentData.bind M U hU (fun i => (q i).quasiCoherentData)
  refine ⟨q'.localGeneratorsData, ?_, ?_⟩
  · constructor
    intro i
    dsimp only [q', SheafOfModules.QuasicoherentData.localGeneratorsData,
      SheafOfModules.QuasicoherentData.bind]
    apply presentationOfIsIso_generators_isIso
    apply presentationMap_generators_isIso
    exact (hq i.1).isIso i.2
  · constructor
    intro i
    constructor
    change Finite ((q i.1).generators i.2).I
    exact ((hf i.1).isFiniteType i.2).finite

end BasisBinding

end SheafOfModules
