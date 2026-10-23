/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Fields.PurelyInseparable.Fullness

/-! # Finite-etale invariance for arbitrary purely inseparable field extensions -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.FiniteEtale.PurelyInseparable

universe u

variable (K L : Type u) [Field K] [Field L] [Algebra K L]
  [IsPurelyInseparable K L]

/-- The literal finite-etale pullback functor is an equivalence, including
infinite-degree purely inseparable extensions and imperfect base fields. -/
theorem specBaseChange_isEquivalence :
    (baseChange (Spec.algebraMap K L)).IsEquivalence := by
  let p := 𝟙 (Spec (.of K))
  let f := Spec.algebraMap K L
  let e := asIso (pullback.snd p f)
  let : (baseChange (pullback.fst p f)).EssSurj := projectionBaseChange_essSurj K L p
  let : (baseChange (Iso.refl (Spec (.of K))).hom).EssSurj :=
    (Global.baseChangeIsoEquivalence (Iso.refl (Spec (.of K)))).essSurj_functor
  let : (baseChange e.inv).EssSurj :=
    (Global.baseChangeIsoEquivalence e.symm).essSurj_functor
  let : (baseChange (Iso.refl (Spec (.of K))).hom ⋙
      baseChange (pullback.fst p f) ⋙ baseChange e.inv).EssSurj :=
    Functor.essSurj_comp _ _
  let : (baseChange f).EssSurj := Functor.essSurj_of_iso
    (Global.baseChangeIsoSquare e (Iso.refl _) f (pullback.fst p f)
      (by simpa [p, e] using (pullback.condition (f := p) (g := f)).symm)).symm
  let := specBaseChange_full K L
  let : (baseChange f).Faithful := Global.baseChange_faithful_of_flat_surjective f
  exact { }

end AlgebraicGeometry.Scheme.FiniteEtale.PurelyInseparable
