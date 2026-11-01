/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.FormallyUnramified.SectionDescent
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.BaseChange
public import Aglib.AlgebraicGeometry.Geometrically.Connected.FieldExtension

/-! # Full faithfulness under flat geometrically connected base change

Actual scheme-map descent supplies the inverse of the original finite-etale
base-change map on Hom sets. This constructs full faithfulness, not essential
surjectivity or an equivalence of finite-etale categories.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.FiniteEtale

variable {X Y : Scheme.{u}} (q : Y ⟶ X) [GeometricallyConnected q]

section Descent

variable (hE : ∀ U : FiniteEtale X, EffectiveEpi (pullback.fst U.obj.hom q))

include hE

/-- The original base-change map on finite-etale Hom sets is bijective.
The inverse is supplied by actual separated-unramified section descent. -/
theorem baseChange_map_bijective_of_geometricallyConnected (U V : FiniteEtale X) :
    Function.Bijective ((baseChange q).map : (U ⟶ V) →
      ((baseChange q).obj U ⟶ (baseChange q).obj V)) := by
  let := hE U
  have hb := Scheme.Hom.bijective_overPullback_map q U.obj V.obj
  constructor
  · intro a b hab
    apply ObjectProperty.hom_ext
    apply hb.injective
    exact congrArg (fun k => k.hom) hab
  · intro b
    obtain ⟨a, ha⟩ := hb.surjective b.hom
    refine ⟨ObjectProperty.homMk a, ?_⟩
    apply ObjectProperty.hom_ext
    exact ha

/-- Full faithfulness of the actual functor, constructed using only the
proved bijectivity of its original maps. -/
def fullyFaithfulBaseChangeOfGeometricallyConnected : (baseChange q).FullyFaithful := by
  let : (baseChange q).Full := {
    map_surjective := fun {U V} =>
      (baseChange_map_bijective_of_geometricallyConnected q hE U V).surjective }
  let : (baseChange q).Faithful := {
    map_injective := fun {U V} =>
      (baseChange_map_bijective_of_geometricallyConnected q hE U V).injective }
  exact Functor.FullyFaithful.ofFullyFaithful (baseChange q)

end Descent

/-- Flat quasi-compact geometrically connected morphisms supply the effective
epimorphism on every finite-etale test. -/
def fullyFaithfulBaseChangeOfFlatQuasiCompact
    [Flat q] [QuasiCompact q] : (baseChange q).FullyFaithful :=
  fullyFaithfulBaseChangeOfGeometricallyConnected q (fun _ => inferInstance)

/-- Flat locally finitely presented geometrically connected morphisms supply
full faithfulness without a quasi-compactness hypothesis. -/
def fullyFaithfulBaseChangeOfFlatLfp
    [Flat q] [LocallyOfFinitePresentation q] : (baseChange q).FullyFaithful :=
  fullyFaithfulBaseChangeOfGeometricallyConnected q (fun _ => inferInstance)

/-- Arbitrary extension of an algebraically closed field gives full
faithfulness on the actual finite-etale base-change functor of every scheme. -/
def fullyFaithfulBaseChangeFieldExtension
    (k K : Type u) [Field k] [IsAlgClosed k] [Field K] [Algebra k K]
    {Z : Scheme.{u}} (p : Z ⟶ Spec (.of k)) :
    (baseChange (pullback.fst p
      (Spec.map (CommRingCat.ofHom (algebraMap k K))))).FullyFaithful := by
  let := Scheme.Geometrically.fieldSpec_geometricallyConnected k K
  exact fullyFaithfulBaseChangeOfFlatQuasiCompact
    (pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap k K))))

end AlgebraicGeometry.Scheme.FiniteEtale
