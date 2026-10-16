/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.CochainComplex.BoundedAbove.Basic
public import Aglib.CategoryTheory.Localization.Approximation


/-!
# The actual bounded-above derived localization

Good truncation preserves all original quasi-isomorphisms. Its actual counits
are invertible on each pair of bounded complexes once the truncation degree is
large enough. The approximation criterion proves full faithfulness of the
bounded-complex localization into the ambient derived category. Actual bounded
representatives give essential surjectivity, hence a genuine equivalence with
`DerivedCategory.Minus`. No projective/injective existence assumption is required.
-/
/-!
Source: frozen dirty Quillen `6db56ddd3fdb898ef5de29d5fe51a0c61f9ba116`.
`Quillen/Algebra/Homology/BoundedDerivedLocalization.lean`.
SHA-256: `30f1094c68cb51d2b35d33584702adf68cc4b0d5f8521a978e8ee79d715c866f`.
Selected source lines: 1–162.
Actual source objects, maps, hypotheses and independent universes are preserved.
-/

@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v w
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace CochainComplex

variable (C : Type u) [Category.{v} C] [Abelian C]

/-- Actual good truncation, regarded as a genuinely bounded-above complex. -/
def truncationToBounded (n : ℤ) : CochainComplex C ℤ ⥤ BoundedAboveComplex C where
  obj K := ⟨K.truncLE n, n, inferInstance⟩
  map f := ObjectProperty.homMk (CochainComplex.truncLEMap f n)
  map_id K := by apply ObjectProperty.hom_ext; apply HomologicalComplex.truncLEMap_id
  map_comp f g := by apply ObjectProperty.hom_ext; apply HomologicalComplex.truncLEMap_comp

/-- The good-truncation counit uses the original chain map. -/
def truncationToBoundedCounit (n : ℤ) :
    truncationToBounded C n ⋙ (boundedAbove C).ι ⟶ 𝟭 (CochainComplex C ℤ) where
  app K := K.ιTruncLE n
  naturality {_K _L} f := CochainComplex.ιTruncLE_naturality f n

/-- Good truncation preserves all original quasi-isomorphisms. -/
theorem truncationToBounded_quasiIso (n : ℤ) :
    HomologicalComplex.quasiIso C (.up ℤ) ≤
      ((HomologicalComplex.quasiIso C (.up ℤ)).inverseImage (boundedAbove C).ι).inverseImage
        (truncationToBounded C n) := by
  intro K L f hf
  let : QuasiIso f := hf
  change QuasiIso (CochainComplex.truncLEMap f n)
  rw [CochainComplex.quasiIso_truncLEMap_iff]
  intros
  infer_instance

/-- Every pair of genuinely bounded inputs eventually has invertible good-truncation counits. -/
theorem truncationToBounded_eventually (K L : BoundedAboveComplex C) :
    ∃ n, (HomologicalComplex.quasiIso C (.up ℤ))
      ((truncationToBoundedCounit C n).app K.obj) ∧
      (HomologicalComplex.quasiIso C (.up ℤ)) ((truncationToBoundedCounit C n).app L.obj) := by
  let n := max (chosenUpperBound K) (chosenUpperBound L)
  have : K.obj.IsStrictlyLE n := K.obj.isStrictlyLE_of_le (chosenUpperBound K) n (le_max_left _ _)
  have : L.obj.IsStrictlyLE n := L.obj.isStrictlyLE_of_le (chosenUpperBound L) n (le_max_right _ _)
  exact ⟨n, inferInstanceAs (QuasiIso (K.obj.ιTruncLE n)),
    inferInstanceAs (QuasiIso (L.obj.ιTruncLE n))⟩

/-- Quasi-isomorphisms in the full category of bounded-above cochain complexes, detected by the
inclusion into all cochain complexes. -/
abbrev boundedAboveQuasiIso : MorphismProperty (BoundedAboveComplex C) :=
  (HomologicalComplex.quasiIso C (.up ℤ)).inverseImage (boundedAbove C).ι

/-- The actual inclusion of bounded-complex localizations is fully faithful. -/
def boundedAboveLocalizationFullyFaithful :
    (Localization.Restriction.inclusion (boundedAbove C).ι
      (HomologicalComplex.quasiIso C (.up ℤ))).FullyFaithful :=
  Localization.Restriction.fullyFaithful _ _ (truncationToBounded C)
    (truncationToBoundedCounit C) (truncationToBounded_quasiIso C) (truncationToBounded_eventually
      C)

variable [HasDerivedCategory.{w} C]

/-- The canonical inclusion into the actual ambient derived category. -/
def boundedAboveLocalizationToDerived : (boundedAboveQuasiIso C).Localization ⥤ DerivedCategory C :=
  Localization.Restriction.inclusion (boundedAbove C).ι (HomologicalComplex.quasiIso C (.up ℤ)) ⋙
    (Localization.equivalenceFromModel DerivedCategory.Q (HomologicalComplex.quasiIso C (.up
      ℤ))).functor

/-- The inclusion agrees with the original derived localization on every original complex. -/
def boundedAboveLocalizationToDerivedFactors :
    (boundedAboveQuasiIso C).Q ⋙ boundedAboveLocalizationToDerived C ≅
      (boundedAbove C).ι ⋙ DerivedCategory.Q :=
  NatIso.ofComponents
    (fun K => (Localization.qCompEquivalenceFromModelFunctorIso DerivedCategory.Q
      (HomologicalComplex.quasiIso C (.up ℤ))).app K.obj)
    (fun f => by
      dsimp [boundedAboveLocalizationToDerived]
      rw [Localization.Restriction.inclusion_map_Q]
      exact (Localization.qCompEquivalenceFromModelFunctorIso DerivedCategory.Q
        (HomologicalComplex.quasiIso C (.up ℤ))).hom.naturality f.hom)

/-- Ambient full faithfulness transports along the actual chosen localization equivalence. -/
def boundedAboveLocalizationToDerivedFullyFaithful :
    (boundedAboveLocalizationToDerived C).FullyFaithful :=
  (boundedAboveLocalizationFullyFaithful C).comp
    (Localization.equivalenceFromModel DerivedCategory.Q
      (HomologicalComplex.quasiIso C (.up ℤ))).fullyFaithfulFunctor

/-- The canonical localized inclusion lands in exactly the ambient bounded-above subcategory. -/
def boundedAboveLocalizationToMinus :
    (boundedAboveQuasiIso C).Localization ⥤ DerivedCategory.Minus C :=
  (DerivedCategory.TStructure.t.minus).lift (boundedAboveLocalizationToDerived C) (fun A => by
    obtain ⟨K, rfl⟩ := (Localization.Construction.objEquiv (boundedAboveQuasiIso C)).surjective A
    have : (DerivedCategory.Q.obj K.obj).IsLE (chosenUpperBound K) := inferInstance
    let e : (boundedAboveLocalizationToDerived C).obj ((boundedAboveQuasiIso C).Q.obj K) ≅
        DerivedCategory.Q.obj K.obj := (boundedAboveLocalizationToDerivedFactors C).app K
    exact ⟨chosenUpperBound K, DerivedCategory.TStructure.t.isLE_of_iso e.symm (chosenUpperBound
      K)⟩)

/-- Full faithfulness of the functor from the quasi-isomorphism localization of bounded-above
cochain complexes to `DerivedCategory.Minus C`, obtained by factoring the fully faithful
ambient derived comparison through its full subcategory. -/
def boundedAboveLocalizationToMinusFullyFaithful :
    (boundedAboveLocalizationToMinus C).FullyFaithful :=
  Functor.FullyFaithful.ofCompFaithful (F := boundedAboveLocalizationToMinus C)
    (G := DerivedCategory.Minus.ι) (boundedAboveLocalizationToDerivedFullyFaithful C)

instance boundedAboveLocalizationToMinus_essSurj :
    (boundedAboveLocalizationToMinus C).EssSurj where
  mem_essImage X := by
    obtain ⟨K, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage (boundedAboveQMinus C) X
    refine ⟨(boundedAboveQuasiIso C).Q.obj K, ⟨ObjectProperty.isoMk _ ?_⟩⟩
    exact (boundedAboveLocalizationToDerivedFactors C).app K ≪≫
      (DerivedCategory.Minus.ι).mapIso e

/-- The localization of actual bounded-above complexes is genuinely equivalent to
mathlib's bounded-above full subcategory of the ambient derived category. -/
def boundedAboveDerivedEquivalence :
    (boundedAboveQuasiIso C).Localization ≌ DerivedCategory.Minus C := by
  let := (boundedAboveLocalizationToMinusFullyFaithful C).full
  let := (boundedAboveLocalizationToMinusFullyFaithful C).faithful
  let : (boundedAboveLocalizationToMinus C).IsEquivalence := { }
  exact (boundedAboveLocalizationToMinus C).asEquivalence

/-- The bounded-complex localization agrees with the original ambient derived functor. -/
def boundedAboveLocalizationToMinusFactors :
    (boundedAboveQuasiIso C).Q ⋙ boundedAboveLocalizationToMinus C ≅ boundedAboveQMinus C :=
  NatIso.ofComponents
    (fun K => ObjectProperty.isoMk _ ((boundedAboveLocalizationToDerivedFactors C).app K))
    (fun f => ObjectProperty.hom_ext _ ((boundedAboveLocalizationToDerivedFactors C).hom.naturality
      f))

/-- The original bounded-complex functor really is a localization at the original
  quasi-isomorphisms. -/
instance boundedAboveQMinus_isLocalization :
    (boundedAboveQMinus C).IsLocalization (boundedAboveQuasiIso C) :=
  Functor.IsLocalization.of_equivalence_target (boundedAboveQuasiIso C).Q
    (boundedAboveQuasiIso C) (boundedAboveQMinus C) (boundedAboveDerivedEquivalence C)
    (boundedAboveLocalizationToMinusFactors C)

end CochainComplex
