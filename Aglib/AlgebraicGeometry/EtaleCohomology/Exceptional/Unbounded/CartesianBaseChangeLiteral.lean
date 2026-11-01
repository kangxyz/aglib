/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.CartesianBaseChange
public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.CartesianBaseChangeGeometry
public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.CartesianBaseChangeLiteralAlgebra
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.SourceIsoIdentity
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.StructuralCoherence

/-! # The given-Cartesian-square exchange specializes to the original literal-pullback exchange -/

@[expose] public noncomputable section
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients

private theorem eqToIso_congr_symm
    {A C : Type*} [Category* C] (F : A → C) {a b : A} (h : a = b) :
    eqToIso (congrArg F h.symm) = (eqToIso (congrArg F h)).symm := by
  cases h
  rfl

universe u wX wS wL wT wM wN wR
variable {X S T : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f]
  [Nonempty (Hom.DenseCompactification f)] (g : T ⟶ S)
  (Λ : Type (u + 1)) [Ring Λ]
  [hX : HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
  [hL : HasDerivedCategory.{wL} (ModuleSheaf (pullback g f) Λ)]
  [hT : HasDerivedCategory.{wT} (ModuleSheaf T Λ)]
  [sourceModels : ∀ C : Hom.DenseCompactification f,
    HasDerivedCategory.{wM} (ModuleSheaf C.Xbar Λ)]
  [literalModels : ∀ C : Hom.DenseCompactification (pullback.fst g f),
    HasDerivedCategory.{wN} (ModuleSheaf C.Xbar Λ)]
  [rawModels : ∀ C : Hom.DenseCompactification f,
    HasDerivedCategory.{wR} (ModuleSheaf (pullback g C.p) Λ)]

local instance unboundedLiteralCartesianNonempty :
    Nonempty (Hom.DenseCompactification (pullback.fst g f)) :=
  ⟨Hom.DenseCompactification.baseChangeObj g (moduleExceptionalSuppliedCompactification f)⟩

omit [QuasiCompact f] [Nonempty (Hom.DenseCompactification f)]
  [HasDerivedCategory.{wS} (ModuleSheaf S Λ)] hT sourceModels literalModels rawModels in
/-- After the actual universal source isomorphism is identified, the remaining
native source compositor is the inverse original source-identity normalizer. -/
theorem moduleUnboundedCartesianBaseChangeSourceUnit :
    eqToIso (congrArg
        (fun z : pullback g f ⟶ X => moduleUnboundedDerivedInverseImage Λ z)
        (Category.id_comp (pullback.snd g f)).symm) ≪≫
      moduleUnboundedDerivedInverseImageCompIso Λ (pullback.snd g f) (𝟙 (pullback g f)) =
      (Functor.rightUnitor (moduleUnboundedDerivedInverseImage Λ (pullback.snd g f))).symm ≪≫
        Functor.isoWhiskerLeft (moduleUnboundedDerivedInverseImage Λ (pullback.snd g f))
          (moduleUnboundedDerivedInverseImageIdIso Λ (pullback g f)).symm := by
  have h := cartesianSourceCompositor_of_unit
    (eqToIso (congrArg
      (fun z : pullback g f ⟶ X => moduleUnboundedDerivedInverseImage Λ z)
      (Category.id_comp (pullback.snd g f))))
    (moduleUnboundedDerivedInverseImageCompIso Λ (pullback.snd g f) (𝟙 (pullback g f)))
    (Functor.isoWhiskerLeft (moduleUnboundedDerivedInverseImage Λ (pullback.snd g f))
        (moduleUnboundedDerivedInverseImageIdIso Λ (pullback g f)) ≪≫
      Functor.rightUnitor (moduleUnboundedDerivedInverseImage Λ (pullback.snd g f)))
    (moduleUnboundedDerivedInverseImageCompIso_comp_id Λ (pullback.snd g f))
  exact (congrArg
    (fun z => z ≪≫ moduleUnboundedDerivedInverseImageCompIso Λ
      (pullback.snd g f) (𝟙 (pullback g f)))
    (eqToIso_congr_symm
      (fun z : pullback g f ⟶ X => moduleUnboundedDerivedInverseImage Λ z)
      (Category.id_comp (pullback.snd g f)))).trans h

variable (N : ℕ) (hN : 0 < N) (hΛ : N • (1 : Λ) = 0)

private theorem cartesianLiteral_from_source_identity
    (e : pullback g f ≅ pullback g f) (he : e = Iso.refl (pullback g f))
    (hf : e.hom ≫ pullback.fst g f = pullback.fst g f)
    (ha : e.hom ≫ pullback.snd g f = pullback.snd g f) :
    cartesianSourceExchange
      (moduleExceptionalDirectImageUnboundedBaseChangeIsoOfNonempty f g Λ N hN hΛ)
        (moduleExceptionalDirectImageUnboundedSourceIsoOfNonempty
          (pullback.fst g f) (pullback.fst g f) e hf Λ N hN hΛ)
        (eqToIso (congrArg (fun z => moduleUnboundedDerivedInverseImage Λ z) ha.symm) ≪≫
          moduleUnboundedDerivedInverseImageCompIso Λ (pullback.snd g f) e.hom) =
      moduleExceptionalDirectImageUnboundedBaseChangeIsoOfNonempty f g Λ N hN hΛ := by
  subst e
  exact (congrArg₂
    (fun ψ c => cartesianSourceExchange
      (moduleExceptionalDirectImageUnboundedBaseChangeIsoOfNonempty f g Λ N hN hΛ) ψ c)
    (moduleExceptionalDirectImageUnboundedSourceIsoOfNonempty_refl_self
      (pullback.fst g f) Λ hL hT literalModels N hN hΛ)
    (moduleUnboundedCartesianBaseChangeSourceUnit f g Λ)).trans
      (cartesianSourceExchange_identity _ _)

/-- With the same literal target model family, the given-square API is the
unchanged original literal-pullback base-change isomorphism. -/
theorem moduleExceptionalDirectImageUnboundedCartesianBaseChangeIsoOfNonempty_literal :
    moduleExceptionalDirectImageUnboundedCartesianBaseChangeIsoOfNonempty
        f (pullback.fst g f) g (pullback.snd g f) (IsPullback.of_hasPullback g f).flip Λ N hN hΛ =
      moduleExceptionalDirectImageUnboundedBaseChangeIsoOfNonempty f g Λ N hN hΛ :=
  cartesianLiteral_from_source_identity f g Λ N hN hΛ
    (IsPullback.of_hasPullback g f).flip.flip.isoPullback
    (moduleCartesianBaseChange_literalSourceIso f g)
    (IsPullback.of_hasPullback g f).flip.flip.isoPullback_hom_fst
    (IsPullback.of_hasPullback g f).flip.flip.isoPullback_hom_snd

end AlgebraicGeometry.Scheme.EtaleCohomology
