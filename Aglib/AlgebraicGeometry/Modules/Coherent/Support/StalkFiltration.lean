/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Abelian.SerreClass.ExactKernels
public import Aglib.AlgebraicGeometry.Stalk.CodimensionOne
public import Aglib.AlgebraicGeometry.Modules.Coherent.FlatPullback
public import Aglib.CategoryTheory.SmallModel.Abelian
public import Aglib.CategoryTheory.ExactCategory.Abelian
public import Aglib.AlgebraicGeometry.Morphisms.Flat.AffineStalk

/-!
# Actual coherent support strata defined by stalk pullback

Source-only extraction from `R5Lab.KTheory.Quillen.SupportFiltration` at R5Lab revision
`e6d63abca2403f50b6b413101ad7f6a7f2e0e2c7`. Existing objects, maps,
hypotheses, universes, proof bodies and mathematical namespaces are retained.
The original source correspondence remains in the supplying application module.
-/



/-!
Native migration from `R5Lab.Aglib.AlgebraicGeometry.Modules.Support.StalkFiltration` at R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`88210e5e308bc0e18ecfe104ed70547cc8d1bfd1de4c6be146a3d941db6b83a5`.
Original objects, maps, universes and explicit hypotheses are retained.
Native providers replace duplicate implementations.
-/

@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme
attribute [local instance] Abelian.hasFiniteBiproducts
namespace AlgebraicGeometry.Scheme.Modules.Coherent.Support

universe s

/-- The chosen small model of finite-type quasicoherent sheaves on `X`. -/
abbrev Coh (X : Scheme.{s}) :=
  SmallModel.{s + 1} (Scheme.Modules.QuasiCoherent.FiniteTypeSheaves X)

/-- Original coherent pullback, transferred to the actual upper small model. -/
def stalkPullback (X : Scheme.{s}) [IsLocallyNoetherian X] (x : X) :
    _root_.CategoryTheory.ExactCategory.ExactFunctor
        (_root_.CategoryTheory.ExactCategory.abelianExactStructure (Coh X))
      (_root_.CategoryTheory.ExactCategory.abelianExactStructure (Coh (Spec (X.presheaf.stalk
          x)))) :=
by
  letI : Flat (X.fromSpecStalk x) := Scheme.fromSpecStalk_flat X x
  exact _root_.CategoryTheory.SmallModel.mapAbelianExactFunctor
    (Scheme.Modules.Coherent.coherentExactPullback (X.fromSpecStalk x))

variable (X : Scheme.{s}) [IsIntegral X] [IsLocallyNoetherian X]

/-- The actual kernel of restriction to the generic stalk. -/
def positiveSupport : ObjectProperty (Coh X) :=
  (stalkPullback X (genericPoint X)).toFunctor.kernel

instance positiveSupport_serre : (positiveSupport X).IsSerreClass :=
  CategoryTheory.ObjectProperty.exactKernelSerre (stalkPullback X (genericPoint X))

/-- The full subcategory of the small coherent model whose generic-stalk pullback vanishes. -/
abbrev CohOne := (positiveSupport X).FullSubcategory

/-- Actual stalk pullback after the positive-support inclusion. -/
def positiveStalkPullback (x : X) :
    _root_.CategoryTheory.ExactCategory.ExactFunctor
        (_root_.CategoryTheory.ExactCategory.abelianExactStructure (CohOne X))
      (_root_.CategoryTheory.ExactCategory.abelianExactStructure (Coh (Spec (X.presheaf.stalk
          x)))) :=
  (_root_.CategoryTheory.ObjectProperty.exactInclusion (positiveSupport X)).comp (stalkPullback X x)

/-- Vanishing at every actual codimension-one stalk, inside positive support. -/
def secondSupport : ObjectProperty (CohOne X) :=
  fun M => ∀ x : CodimensionOnePoint X,
    (positiveStalkPullback X x.1).toFunctor.kernel M

instance secondSupport_serre : (secondSupport X).IsSerreClass := by
  let : ∀ x : CodimensionOnePoint X,
      (positiveStalkPullback X x.1).toFunctor.kernel.IsSerreClass :=
    fun x => CategoryTheory.ObjectProperty.exactKernelSerre (positiveStalkPullback X x.1)
  exact CategoryTheory.ObjectProperty.forallSerre (fun x : CodimensionOnePoint X =>
    (positiveStalkPullback X x.1).toFunctor.kernel)

end AlgebraicGeometry.Scheme.Modules.Coherent.Support
