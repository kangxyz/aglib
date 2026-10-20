/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.NoetherianPushforward
public import Aglib.AlgebraicGeometry.Modules.Invertible.FinitePresentation
public import Aglib.AlgebraicGeometry.Modules.Invertible.TensorFaithful
public import Aglib.AlgebraicGeometry.Modules.Invertible.ZeroLocus.Regular
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.PointedCover
public import Aglib.AlgebraicGeometry.Cohomology.Modules.StructureSheaf
public import Aglib.AlgebraicGeometry.Cohomology.Modules.Constants
public import Aglib.AlgebraicGeometry.Cohomology.Modules.Basic
public import Aglib.AlgebraicGeometry.Morphisms.FiniteFlat.Basic
public import Aglib.AlgebraicGeometry.Modules.BaseChange.Basic
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Rank
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Relative
public import Aglib.AlgebraicGeometry.Modules.Invertible.Basic
public import Aglib.AlgebraicGeometry.Modules.Invertible.Tensor
public import Aglib.AlgebraicGeometry.Modules.Pullback.OpenRestriction
public import Aglib.AlgebraicGeometry.Modules.Invertible.TensorAssociator
public import Aglib.AlgebraicGeometry.Modules.InternalHom
public import Aglib.AlgebraicGeometry.Modules.Invertible.Dual
public import Aglib.AlgebraicGeometry.Modules.Invertible.Pullback
public import Aglib.AlgebraicGeometry.Morphisms.Smooth.Properties
public import Aglib.AlgebraicGeometry.Properties.Normal.Basic
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Field
public import Aglib.AlgebraicGeometry.Geometrically.Integral.GlobalSections
public import Aglib.AlgebraicGeometry.Cohomology.Finiteness.ProperInputs
public import Aglib.AlgebraicGeometry.Cohomology.Functoriality.Isomorphism
public import Aglib.AlgebraicGeometry.Cohomology.Functoriality.Pullback
public import Aglib.AlgebraicGeometry.Cohomology.Finiteness.Coherent
public import Aglib.AlgebraicGeometry.Cohomology.Vanishing.Basic
public import Aglib.AlgebraicGeometry.SchemeOverField
public import Aglib.AlgebraicGeometry.Modules.Pullback.Tensor.Unit
public import Aglib.AlgebraicGeometry.Modules.Invertible.PullbackTensor.Local

/-!
Native migration from `R5Lab.Aglib.AlgebraicGeometry.Cohomology.BaseChange.LineBundleEvaluation`
at R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`7e9e77fda1918945d05471a04efebbc163b4bf79d1d9edaf86a551d5fdebd127`.
Original objects, maps, universes and explicit hypotheses are retained.
Native providers replace duplicate implementations.
-/

@[expose] public section

open _root_.AlgebraicGeometry.Scheme
  (NormalComponentsOpen  SmoothClosedPointDimension
    SmoothFieldDimension SmoothFieldNormality SmoothFieldRegularity)
open _root_.AlgebraicGeometry.Scheme.Cohomology
  (FibreCohomologyConcentrated NoetherianSheafCohomologyVanishing
    evaluation_pullback_ne_zero moduleAddSheaf moduleCohomology moduleH0Equiv relativeEvaluation)
open _root_.AlgebraicGeometry.Scheme.Modules.Invertible
  (LineBundle classOf dualEvaluationIso dualLineBundle lineBundle_isLocallyFree
    pullbackLineBundle tensorLineBundle)
open _root_.AlgebraicGeometry.Scheme.Modules (pullbackUnitIso)
open _root_.AlgebraicGeometry.Scheme.Modules
  (pullbackTensorMap pullbackTensorMap_naturality tensorSheafMap)
open _root_.AlgebraicGeometry.Scheme.OverField (FScheme)

/- Interface migration basis: 46f53465aaf3b0167049e9c8e9e2294111bb4281.
Original mathematical and construction source identities are retained. -/
/-!
# Actual relative evaluation for degree-one line bundles

The genus-one, degree-one geometric-fibre profile is proved from the general
all-genus Riemann–Roch and high-degree vanishing families, together with the
all-Noetherian-scheme Zariski cohomological dimension theorem. No genus-one
cohomology profile is retained as a background assumption.

The cohomology theorem over a locally Noetherian original base is applied to the actual module
sheaf pushforward. Its local bases produce a genuine rank-one line bundle.
The evaluation contraction is literally the tensor of the actual adjunction
counit with the identity of the actual dual bundle, followed by actual dual
evaluation. Its source has class f*P - L, the sign for the negative zero divisor.

The application uses locally Noetherian original bases, including nonreduced
bases; its canonical comparison permits every new target. The canonical
base-change square and unconditional tensor faithfulness now
prove that the contraction is regular on every integral geometric fibre.
No section, graph, or Abel inverse is asserted at this stage. All fibre curve, genus and degree
hypotheses are explicit application conditions to be discharged later.
-/
/-!
Manuscript application: K2-018 `prop:k2018-arithmetic-characters` and
`lem:k2018-geometric-exact-order`, mathematical-source revision
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`.
Frozen engineering basis: `7f86e4a1763cc4ec35e9b0a8acd659750355a0de`.
This module is a new reusable curve foundation for that application.
-/

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
open CategoryTheory Limits AlgebraicGeometry Opposite
namespace AlgebraicGeometry.Scheme.Cohomology
universe u
variable {Z S : Scheme.{u}} (f : Z ⟶ S)
variable [IsLocallyNoetherian S]
/-- The actual direct image, equipped with the rank-one local bases supplied by
the geometric cohomology profile over a locally Noetherian original base. -/
def directImageLineBundle
    [IsProper f] [LocallyOfFinitePresentation f] [Flat f] (L : LineBundle Z)
    (hL : FibreCohomologyConcentrated f L.val 1) : LineBundle S := by
  letI : SheafOfModules.IsLocallyFree.{u} L.val := lineBundle_isLocallyFree Z L
  letI : L.val.IsFinitePresentation := Scheme.Modules.Invertible.lineBundle_isFinitePresentation Z L
  refine ⟨(Scheme.Modules.pushforward f).obj L.val, ?_⟩
  obtain ⟨q, hq, hn⟩ := (Scheme.Cohomology.localFreeCohomologyBaseChange_of_isLocallyNoetherian
    f L.val 1 hL).1
  exact ⟨q, hq, fun i ↦ ⟨(hn i).some.trans (Equiv.ofUnique (Fin 1) PUnit.{u + 1})⟩⟩

@[simp] theorem directImageLineBundle_val
    [IsProper f] [LocallyOfFinitePresentation f] [Flat f] (L : LineBundle Z)
    (hL : FibreCohomologyConcentrated f L.val 1) :
    (directImageLineBundle f L hL).val = (Scheme.Modules.pushforward f).obj L.val := rfl

/-- The line bundle `L` dual tensored with the pullback of its direct image,
which is the source of the relative evaluation contraction. -/
def evaluationIdealLineBundle
    [IsProper f] [LocallyOfFinitePresentation f] [Flat f] (L : LineBundle Z)
    (hL : FibreCohomologyConcentrated f L.val 1) : LineBundle Z :=
  tensorLineBundle Z (dualLineBundle Z L)
    (pullbackLineBundle f (directImageLineBundle f L hL))

/-- The contraction obtained by tensoring the actual adjunction counit with
the identity of the dual line bundle and applying dual evaluation. -/
def evaluationContraction
    [IsProper f] [LocallyOfFinitePresentation f] [Flat f] (L : LineBundle Z)
    (hL : FibreCohomologyConcentrated f L.val 1) :
    (show Z.Modules from (evaluationIdealLineBundle f L hL).val) ⟶
      (show Z.Modules from SheafOfModules.unit Z.ringCatSheaf) :=
  tensorSheafMap Z (𝟙 (dualLineBundle Z L).val) (relativeEvaluation f L.val) ≫
    (dualEvaluationIso Z L).hom
end AlgebraicGeometry.Scheme.Cohomology

namespace AlgebraicGeometry.Scheme.Cohomology
universe u
open AlgebraicGeometry.Scheme.Modules.Invertible AlgebraicGeometry.Scheme.Hom
variable {Z S : Scheme.{u}} (f : Z ⟶ S)
variable [IsLocallyNoetherian S]
variable [IsProper f] [LocallyOfFinitePresentation f] [Flat f]
variable (L : LineBundle Z) (hL : FibreCohomologyConcentrated f L.val 1)
theorem evaluationContraction_pullback_ne_zero
    (K : Type u) [Field K] [IsAlgClosed K] (t : Spec (.of K) ⟶ S) :
    (Scheme.Modules.pullback (pullback.fst f t)).map (evaluationContraction f L hL) ≠ 0 := by
  letI : SheafOfModules.IsLocallyFree.{u} L.val := lineBundle_isLocallyFree Z L
  letI : L.val.IsFinitePresentation := Scheme.Modules.Invertible.lineBundle_isFinitePresentation Z L
  let g := pullback.fst f t
  let N : (pullback f t).Modules := (Scheme.Modules.pullback g).obj L.val
  haveI : IsIso (Scheme.Modules.moduleBaseChangeMap f t L.val) :=
    (Scheme.Cohomology.localFreeCohomologyBaseChange_of_isLocallyNoetherian
      f L.val 1 hL).2 _ t
  haveI : Nontrivial (moduleCohomology K (Over.mk (pullback.snd f t)) N 0) :=
    Module.nontrivial_of_finrank_eq_succ (hL K t).1
  haveI : Nontrivial Γ(N,⊤) :=
    (moduleH0Equiv (Over.mk (pullback.snd f t)) N).toEquiv.symm.nontrivial
  have hn := evaluation_pullback_ne_zero f t L.val
  intro h
  have hzero : (Scheme.Modules.pullback g).map
      (tensorSheafMap Z (𝟙 (dualLineBundle Z L).val) (relativeEvaluation f L.val)) = 0 := by
    apply (cancel_mono ((Scheme.Modules.pullback g).map (dualEvaluationIso Z L).hom)).mp
    rw [zero_comp, ← Functor.map_comp]
    exact h
  have he := pullbackTensorMap_naturality g (𝟙 (dualLineBundle Z L).val) (relativeEvaluation f
      L.val)
  erw [CategoryTheory.Functor.map_id] at he
  haveI :=
      Scheme.Modules.Invertible.PullbackTensor.Local.pullbackTensorMap_isIso g (dualLineBundle
          Z L).val
    ((Scheme.Modules.pullback f).obj ((Scheme.Modules.pushforward f).obj L.val))
    (dualLineBundle Z L).property
  have ht : tensorSheafMap (pullback f t)
      (𝟙 ((Scheme.Modules.pullback g).obj (dualLineBundle Z L).val))
      ((Scheme.Modules.pullback g).map (relativeEvaluation f L.val)) = 0 := by
    apply (cancel_epi (pullbackTensorMap g (dualLineBundle Z L).val
      ((Scheme.Modules.pullback f).obj ((Scheme.Modules.pushforward f).obj L.val)))).mp
    simpa only [CategoryTheory.Functor.map_id, hzero, zero_comp, comp_zero] using he.symm
  exact hn (tensorSheafMap_lineBundle_detects_zero (pullback f t)
    (pullbackLineBundle g (dualLineBundle Z L)) _ ht)

end AlgebraicGeometry.Scheme.Cohomology
