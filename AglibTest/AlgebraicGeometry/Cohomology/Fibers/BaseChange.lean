/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Cohomology.Fibers.BaseChange

/-! Focused consumer of point-fibre cohomology under base change of the family: the fibre
identification along `κ(b t') ⟶ κ(t')`, coefficient transport, and invariance of the point-fibre
dimensions and Euler characteristics for qcqs morphisms and quasicoherent coefficients, with
axiom guards. -/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme.Cohomology

universe u

variable {X S T T' : Scheme.{u}} (p : X ⟶ S) (s : T ⟶ S) (s' : T' ⟶ S) (b : T' ⟶ T)
  (hb : b ≫ s = s')

/-- The fibre of `X ×_S T'` at `t'` is the base change of the fibre of `X ×_S T` at `b t'`. -/
example (t' : T') :
    IsPullback (fiberBaseChange p s s' b hb t') (pullback.snd p (T'.fromSpecResidueField t' ≫ s'))
      (pullback.snd p (T.fromSpecResidueField (b t') ≫ s)) (Spec.map (b.residueFieldMap t')) :=
  isPullback_fiberBaseChange p s s' b hb t'

/-- The fibre maps to `X ×_S T` are compatible, so coefficients transport naturally. -/
example (t' : T') (M : (pullback p s).Modules) :
    (Scheme.Modules.pullback (residueFieldBaseChange p s' t')).obj
        ((Scheme.Modules.pullback (familyBaseChange p s s' b hb)).obj M) ≅
      (Scheme.Modules.pullback (fiberBaseChange p s s' b hb t')).obj
        ((Scheme.Modules.pullback (residueFieldBaseChange p s (b t'))).obj M) :=
  (familyBaseChangeFiberNatIso p s s' b hb t').app M

/-- **Invariance of point-fibre cohomology under base change of the family.** -/
example [QuasiCompact p] [QuasiSeparated p] (M : (pullback p s).Modules) [M.IsQuasicoherent]
    (q : ℕ) (t' : T') :
    modulePointFiberCohomologyDimension (pullback.snd p s')
        ((Scheme.Modules.pullback (familyBaseChange p s s' b hb)).obj M) q t' =
      modulePointFiberCohomologyDimension (pullback.snd p s) M q (b t') ∧
    modulePointFiberEulerChar (pullback.snd p s')
        ((Scheme.Modules.pullback (familyBaseChange p s s' b hb)).obj M) t' =
      modulePointFiberEulerChar (pullback.snd p s) M (b t') :=
  ⟨modulePointFiberCohomologyDimension_familyBaseChange p s s' b hb M q t',
    modulePointFiberEulerChar_familyBaseChange p s s' b hb M t'⟩

/-- **Invariance of point-fibre vanishing under base change of the family.** -/
example [QuasiCompact p] [QuasiSeparated p] (M : (pullback p s).Modules) [M.IsQuasicoherent]
    (q : ℕ) (t' : T') :
    Subsingleton (modulePointFiberCohomology (pullback.snd p s')
        ((Scheme.Modules.pullback (familyBaseChange p s s' b hb)).obj M) q t') ↔
      Subsingleton (modulePointFiberCohomology (pullback.snd p s) M q (b t')) :=
  subsingleton_modulePointFiberCohomology_familyBaseChange_iff p s s' b hb M q t'

/-- Point fibres are residue-field base changes. -/
example (M : (pullback p s).Modules) (q : ℕ) (t : T) :
    modulePointFiberCohomologyDimension (pullback.snd p s) M q t =
      moduleCohomologyDimension (K := T.residueField t)
        (pullback.snd p (T.fromSpecResidueField t ≫ s))
        ((Scheme.Modules.pullback (residueFieldBaseChange p s t)).obj M) q :=
  modulePointFiberCohomologyDimension_eq_pullbackMap p s M q t

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.modulePointFiberCohomologyDimension_familyBaseChange' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms modulePointFiberCohomologyDimension_familyBaseChange

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.isPullback_fiberBaseChange' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms isPullback_fiberBaseChange

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.subsingleton_modulePointFiberCohomology_familyBaseChange_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms subsingleton_modulePointFiberCohomology_familyBaseChange_iff
