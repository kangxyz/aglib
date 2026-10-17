/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Descent.Modules.ZariskiStack

/-! Focused consumer of the module-sheaf descent layer. The pseudofunctor is Mathlib's
`Scheme.Modules.pseudofunctor.comp Adj.forget₁`, with the actual pullback functors
`Scheme.Modules.pullback f`; the topology is Mathlib's `Scheme.zariskiTopology`; the stack
classes are Mathlib's `Pseudofunctor.IsPrestack` and `Pseudofunctor.IsStack`. Universes are
`Scheme.{u}` and `Cat.{u, u + 1}`. The guards below include `projectionSurjective` and the three
Zariski `IsStack` instances of `Descent/ZariskiStack.lean`. -/

@[expose] public section

noncomputable section

open CategoryTheory Opposite Bicategory Pseudofunctor AlgebraicGeometry Scheme.Modules

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

example : pullbackPseudofunctor.{u} = Scheme.Modules.pseudofunctor.comp Adj.forget₁ := rfl

example : pullbackPseudofunctor.obj (.mk (op X)) = Cat.of X.Modules := rfl

example : (pullbackPseudofunctor.map f.op.toLoc).toFunctor = Scheme.Modules.pullback f := rfl

example (M : quasicoherentPseudofunctor.obj (.mk (op X))) : M.obj.IsQuasicoherent := M.property

example (L : lineBundlePseudofunctor.obj (.mk (op X))) :
    Scheme.Modules.Invertible.IsLocallyRankOne X L.obj :=
  L.property

example : pullbackPseudofunctor.{u}.IsPrestack Scheme.zariskiTopology := inferInstance

example : quasicoherentPseudofunctor.{u}.IsPrestack Scheme.zariskiTopology := inferInstance

example : lineBundlePseudofunctor.{u}.IsPrestack Scheme.zariskiTopology := inferInstance

example (h : ∀ (S : Scheme.{u}) (ι : Type (u + 1)) (U : ι → S.Opens), iSup U = ⊤ →
      (pullbackPseudofunctor.{u}.toDescentData (fun i ↦ (U i).ι)).EssSurj) :
    pullbackPseudofunctor.{u}.IsStack Scheme.zariskiTopology :=
  isStack_zariskiTopology_of_essSurj h

example [pullbackPseudofunctor.{u}.IsStack Scheme.zariskiTopology] :
    quasicoherentPseudofunctor.{u}.IsStack Scheme.zariskiTopology :=
  isStack_quasicoherentPseudofunctor_of_isStack

example [pullbackPseudofunctor.{u}.IsStack Scheme.zariskiTopology] :
    lineBundlePseudofunctor.{u}.IsStack Scheme.zariskiTopology :=
  isStack_lineBundlePseudofunctor_of_isStack

example {ι : Type*} {Z : ι → Scheme.{u}} (g : ∀ i, Z i ⟶ Y) [∀ i, IsOpenImmersion (g i)]
    (hg : ∀ y : Y, ∃ (i : ι) (z : Z i), g i z = y) :
    (pullbackPseudofunctor.{u}.toDescentData g).FullyFaithful :=
  fullyFaithfulToDescentDataOfOpenImmersion g hg

/--
info: 'AlgebraicGeometry.Scheme.Modules.isPrestack_zariskiTopology' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms isPrestack_zariskiTopology

/--
info: 'AlgebraicGeometry.Scheme.Modules.isStack_zariskiTopology_of_essSurj' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms isStack_zariskiTopology_of_essSurj

/--
info: 'AlgebraicGeometry.Scheme.Modules.isStack_quasicoherentPseudofunctor_of_isStack' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms isStack_quasicoherentPseudofunctor_of_isStack

/--
info: 'AlgebraicGeometry.Scheme.Modules.isStack_lineBundlePseudofunctor_of_isStack' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms isStack_lineBundlePseudofunctor_of_isStack

/--
info: 'AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback_comp_hom_app' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms restrictFunctorIsoPullback_comp_hom_app

/--
info: 'CategoryTheory.Pseudofunctor.ObjectProperty.isStack_fullsubcategory' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ObjectProperty.isStack_fullsubcategory

/--
info: 'AlgebraicGeometry.Scheme.Modules.pullbackPseudofunctor_mapComp'_hom_app' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms pullbackPseudofunctor_mapComp'_hom_app

/--
info: 'AlgebraicGeometry.Scheme.Modules.fullyFaithfulToDescentDataOfOpenImmersion' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms fullyFaithfulToDescentDataOfOpenImmersion

/--
info: 'AlgebraicGeometry.Scheme.Modules.isQuasicoherent_of_mem_zariskiTopology' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms isQuasicoherent_of_mem_zariskiTopology

/--
info: 'AlgebraicGeometry.Scheme.Modules.isLocallyRankOne_of_mem_zariskiTopology' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms isLocallyRankOne_of_mem_zariskiTopology

/--
info: 'AlgebraicGeometry.Scheme.Modules.isStack_zariskiTopology_of_opens' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms isStack_zariskiTopology_of_opens

/--
info: 'AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback_congr_hom_app' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms restrictFunctorIsoPullback_congr_hom_app

/--
info: 'CategoryTheory.Pseudofunctor.ObjectProperty.isEquivalence_toDescentData_fullsubcategory' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ObjectProperty.isEquivalence_toDescentData_fullsubcategory

/--
info: 'AlgebraicGeometry.Scheme.Modules.isPrestack_quasicoherentPseudofunctor_zariskiTopology' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms isPrestack_quasicoherentPseudofunctor_zariskiTopology

/--
info: 'AlgebraicGeometry.Scheme.Modules.isPrestack_lineBundlePseudofunctor_zariskiTopology' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms isPrestack_lineBundlePseudofunctor_zariskiTopology

/--
info: 'AlgebraicGeometry.Scheme.Modules.pullbackPseudofunctor_pullHom_restrict' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms pullbackPseudofunctor_pullHom_restrict

/--
info: 'AlgebraicGeometry.Scheme.Modules.OpenCoverGluing.gluedPresheaf_isSheaf' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms OpenCoverGluing.gluedPresheaf_isSheaf

/--
info: 'AlgebraicGeometry.Scheme.Modules.OpenCoverGluing.projection_app_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms OpenCoverGluing.projection_app_injective

/--
info: 'AlgebraicGeometry.Scheme.Modules.OpenCoverGluing.toObj_comm' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms OpenCoverGluing.toObj_comm

/--
info: 'AlgebraicGeometry.Scheme.Modules.OpenCoverGluing.phi_comm_aux' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms OpenCoverGluing.phi_comm_aux

/--
info: 'AlgebraicGeometry.Scheme.Modules.OpenCoverGluing.hom_eq_transition' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms OpenCoverGluing.hom_eq_transition

/--
info: 'AlgebraicGeometry.Scheme.Modules.OpenCoverGluing.descentData_comm_of' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms OpenCoverGluing.descentData_comm_of

/--
info: 'AlgebraicGeometry.Scheme.Modules.OpenCoverGluing.isIso_toObj' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms OpenCoverGluing.isIso_toObj

/--
info: 'AlgebraicGeometry.Scheme.Modules.OpenCoverGluing.essSurj_toDescentData' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms OpenCoverGluing.essSurj_toDescentData

/--
info: 'AlgebraicGeometry.Scheme.Modules.OpenCoverGluing.isStackFor_ofArrows' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms OpenCoverGluing.isStackFor_ofArrows

/--
info: 'AlgebraicGeometry.Scheme.Modules.isStack_zariskiTopology_of_projectionSurjective' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms isStack_zariskiTopology_of_projectionSurjective

/--
info: 'AlgebraicGeometry.Scheme.Modules.isStack_quasicoherentPseudofunctor_of_projectionSurjective' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms isStack_quasicoherentPseudofunctor_of_projectionSurjective

/--
info: 'AlgebraicGeometry.Scheme.Modules.isStack_lineBundlePseudofunctor_of_projectionSurjective' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms isStack_lineBundlePseudofunctor_of_projectionSurjective

/--
info: 'CategoryTheory.Pseudofunctor.DescentData.comm_of_overlap' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms DescentData.comm_of_overlap

example {S : Scheme.{u}} {ι : Type u} {Y : ι → Scheme.{u}} (f : ∀ i, Y i ⟶ S)
    [∀ i, IsOpenImmersion (f i)] (D : pullbackPseudofunctor.{u}.DescentData f) :
    (OpenCoverGluing.glued f D).val = OpenCoverGluing.gluedPresheaf f D :=
  rfl

example {S : Scheme.{u}} {ι : Type u} {Y : ι → Scheme.{u}} (f : ∀ i, Y i ⟶ S)
    [∀ i, IsOpenImmersion (f i)] (D : pullbackPseudofunctor.{u}.DescentData f) :
    (pullbackPseudofunctor.toDescentData f).obj (OpenCoverGluing.glued f D) ⟶ D :=
  OpenCoverGluing.comparison f D

example (h : ProjectionSurjective.{u}) :
    pullbackPseudofunctor.{u}.IsStack Scheme.zariskiTopology :=
  isStack_zariskiTopology_of_projectionSurjective h

/--
info: 'AlgebraicGeometry.Scheme.Modules.OpenCoverGluing.cocycle_app' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms OpenCoverGluing.cocycle_app

/--
info: 'AlgebraicGeometry.Scheme.Modules.OpenCoverGluing.comp_first_restrict_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms OpenCoverGluing.comp_first_restrict_eq

/--
info: 'AlgebraicGeometry.Scheme.Modules.projectionSurjective' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms projectionSurjective

/--
info: 'AlgebraicGeometry.Scheme.Modules.isStack_pullbackPseudofunctor_zariskiTopology' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms isStack_pullbackPseudofunctor_zariskiTopology

/--
info: 'AlgebraicGeometry.Scheme.Modules.isStack_quasicoherentPseudofunctor_zariskiTopology' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms isStack_quasicoherentPseudofunctor_zariskiTopology

/--
info: 'AlgebraicGeometry.Scheme.Modules.isStack_lineBundlePseudofunctor_zariskiTopology' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms isStack_lineBundlePseudofunctor_zariskiTopology

-- The three Zariski stack instances are found by instance search.
example : pullbackPseudofunctor.{u}.IsStack Scheme.zariskiTopology := inferInstance

example : quasicoherentPseudofunctor.{u}.IsStack Scheme.zariskiTopology := inferInstance

example : lineBundlePseudofunctor.{u}.IsStack Scheme.zariskiTopology := inferInstance

example : ProjectionSurjective.{u} := projectionSurjective
