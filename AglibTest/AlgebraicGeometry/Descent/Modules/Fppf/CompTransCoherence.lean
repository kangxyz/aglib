/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Descent.Modules.Fppf.CompTransCoherence

/-! Focused consumer of the coherence of the comparison transformation over `Spec`: the generic
reductions of `CompTransAlong.nat_comp` to the ambient and to the `pullbackCongr`/`pullbackComp`
forms, the leaf-wise rearrangements, the transport lemma, the Mod-level bridges, the
transformation `specCompTransAlong` and the unconditional affine stack theorem, with axiom
guards. -/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry Scheme.Modules CommRingCat

universe u

example {X Y : CommRingCat.{u}ᵒᵖ} (g : Y ⟶ X)
    (N : moduleCatExtendScalarsPseudofunctorOpOp.{u}.obj (.mk (Opposite.op X))) :
    ((specTransNat g).hom.app N).hom = (tildePullbackIso g.unop).inv.app N :=
  specTransNat_hom_app_hom g N

/--
info: 'CategoryTheory.Pseudofunctor.natComp_of_natCompAmbient' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Pseudofunctor.natComp_of_natCompAmbient

/--
info: 'CategoryTheory.Pseudofunctor.natCompAmbient_of_natCompPullback' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Pseudofunctor.natCompAmbient_of_natCompPullback

/--
info: 'CategoryTheory.comp_eq_of_leaves' depends on axioms: [Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.comp_eq_of_leaves

/--
info: 'AlgebraicGeometry.Scheme.Modules.moduleCat_mapComp'_hom_app_op'' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Modules.moduleCat_mapComp'_hom_app_op'

/-- The affine stack theorem, consumed at its stated generality. -/
example {A B : CommRingCat.{u}} (f : A ⟶ B) (hf : f.hom.FaithfullyFlat) :
    quasicoherentPseudofunctor.{u}.IsStackFor (Presieve.singleton (Spec.map f)) :=
  isStackFor_quasicoherentPseudofunctor_singleton_specMap f hf

/-- The components of `specCompTransAlong` are `specTransApp`. -/
example (X : CommRingCat.{u}ᵒᵖ) : specCompTransAlong.{u}.toCompTrans.app X = specTransApp X :=
  rfl

/--
info: 'AlgebraicGeometry.Scheme.Modules.isStackFor_quasicoherentPseudofunctor_singleton_specMap' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms isStackFor_quasicoherentPseudofunctor_singleton_specMap

/--
info: 'AlgebraicGeometry.Scheme.Modules.specCompTransAlong' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Modules.specCompTransAlong

/--
info: 'AlgebraicGeometry.Scheme.Modules.specNatCompAlong' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Modules.specNatCompAlong

/--
info: 'CategoryTheory.Pseudofunctor.natCompAlong_of_transport' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Pseudofunctor.natCompAlong_of_transport

/--
info: 'CategoryTheory.Pseudofunctor.natCompAlong_of_natCompPullback' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Pseudofunctor.natCompAlong_of_natCompPullback

/--
info: 'CategoryTheory.comp_eq_of_leaves_heq' depends on axioms: [Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.comp_eq_of_leaves_heq
