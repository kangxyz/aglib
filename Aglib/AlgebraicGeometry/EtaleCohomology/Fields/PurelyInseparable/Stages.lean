/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Descent.GlobalFinitePureDescent
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Descent.FiniteFieldCoverGlobal

/-! # Actual finite stages of purely inseparable base change -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.FiniteEtale.PurelyInseparable

universe u

variable (K L : Type u) [Field K] [Field L] [Algebra K L]
  [IsPurelyInseparable K L]

/-- Finite purely inseparable invariance for the literal map of field spectra. -/
theorem finiteSpecBaseChange_isEquivalence [Module.Finite K L] :
    (baseChange (Spec.algebraMap K L)).IsEquivalence := by
  let p := 𝟙 (Spec (.of K))
  let f := Spec.algebraMap K L
  let := Global.finitePureBaseChange_isEquivalence K L p
  exact Global.baseChange_isEquivalence_of_isoSquare
    (asIso (pullback.snd p f)) (Iso.refl _) f (pullback.fst p f)
    (by simpa [p] using (pullback.condition (f := p) (g := f)).symm)

/-- Each actual finite field stage has the original finite-etale pullback equivalence. -/
theorem stageBaseChange_isEquivalence {X : Scheme.{u}}
    (p : X ⟶ Spec (.of K)) (s : (Finset L)ᵒᵖ) :
    (baseChange ((FieldLimit.schemeDiagram K L p).obj s).hom).IsEquivalence := by
  let F := FieldLimit.finiteField K L s.unop
  let f := Spec.algebraMap K F
  let := Global.finitePureBaseChange_isEquivalence K F p
  change (baseChange (pullback.snd f p)).IsEquivalence
  exact Global.baseChange_isEquivalence_of_isoSquare
    (pullbackSymmetry p f) (Iso.refl _) (pullback.snd f p) (pullback.fst p f)
    (by simp)

/-- Actual cover objects descend across arbitrary purely inseparable extensions.
Only the source scheme is assumed quasi-compact and quasi-separated. -/
theorem projectionBaseChange_essSurj {X : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X] (p : X ⟶ Spec (.of K)) :
    (baseChange (pullback.fst p (Spec.algebraMap K L))).EssSurj where
  mem_essImage Y := by
    obtain ⟨s, Z, ⟨e⟩⟩ := FieldCoverDescent.exists_qcqs_cover K L p Y
    let g := ((FieldLimit.schemeDiagram K L p).obj (op s)).hom
    let q := FieldLimit.fieldProjection K L p (op s)
    let : (baseChange g).IsEquivalence := stageBaseChange_isEquivalence K L p (op s)
    let W := (baseChange g).objPreimage Z
    refine ⟨W, ⟨?_
      ≪≫ (baseChange q).mapIso ((baseChange g).objObjPreimageIso Z) ≪≫ e⟩⟩
    exact (eqToIso (congrArg (fun f ↦ (baseChange f).obj W)
      (FieldLimit.fieldProjection_base K L p (op s)).symm)) ≪≫
      (baseChangeComp g q).app W

end AlgebraicGeometry.Scheme.FiniteEtale.PurelyInseparable
