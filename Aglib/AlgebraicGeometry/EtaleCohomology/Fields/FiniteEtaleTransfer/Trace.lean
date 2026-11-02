/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Fields.FiniteEtaleTransfer.Gluing
public import Aglib.CategoryTheory.Sites.Free.FiniteSumTransfer
public import Aglib.AlgebraicGeometry.FundamentalGroup.Field.ArbitraryGalois
public import Aglib.AlgebraicGeometry.EtaleCohomology.StrictlyLocal.Site

/-! # The normalized transfer for actual finite-etale representables

The map is obtained by gluing the finite sums of original generators. Its
augmentation is the actual finite-flat rank. For finite separable fields this
rank is the original `Module.finrank`, and the source is normalized by the
existing constant-integer/free-terminal isomorphism.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open CategoryTheory.Sheaf.Hypercohomology

namespace AlgebraicGeometry.Scheme.FiniteEtale

universe u

attribute [local instance] Fintype.ofFinite

variable {X : Scheme.{u}} (Y : Scheme.FiniteEtale X)
    [HasSheafify (Scheme.smallEtaleTopology X) AddCommGrpCat.{u + 1}]

/-- Glued finite-etale sums split the actual represented augmentation up to
its constant finite-flat rank. -/
theorem exists_freeRepresentable_transfer (n : ℕ) (hn : ∀ x : X, Y.obj.hom.finrank x = n) :
    ∃ τ : freeAbelianSheaf.{u + 1} (Scheme.smallEtaleTopology X) (Scheme.Etale.mk (𝟙 X)) ⟶
      freeAbelianSheaf.{u + 1} (Scheme.smallEtaleTopology X) ((toEtale X).obj Y),
      τ ≫ (freeAbelianSheafFunctor.{u + 1} (Scheme.smallEtaleTopology X)).map
        ((MorphismProperty.Over.mkIdTerminal (@Etale : MorphismProperty Scheme.{u}) X).from
          ((toEtale X).obj Y)) = n • 𝟙 _ := by
  classical
  let J := Scheme.smallEtaleTopology X
  let T : X.Etale := Scheme.Etale.mk (𝟙 X)
  let hT : IsTerminal T :=
    MorphismProperty.Over.mkIdTerminal (@Etale : MorphismProperty Scheme.{u}) X
  choose V A e v hv using exists_labelled_chart Y
  let p (x : X) : V x ⟶ T := hT.from (V x)
  have hp : Sieve.ofArrows V p ∈ J T :=
    SheafDescent.etaleFamily_covering V p (fun x => by
      refine ⟨x, v x, ?_⟩
      have hw := MorphismProperty.Over.w (p x)
      change (p x).left ≫ 𝟙 X = (V x).hom at hw
      have hw' : (p x).left = (V x).hom := (Category.comp_id (p x).left).symm.trans hw
      exact (congrArg (fun k : (V x).left ⟶ X => k (v x)) hw').trans (hv x))
  obtain ⟨τ, _hlocal, hτ⟩ := exists_freeRepresentable_transfer_of_cover.{u + 1} J hT
    V p hp (fun x => A x) (fun x => chartSiteSection Y (e x))
    (fun i j W f g _ => chartSum_matching Y V A e i j W f g)
    n (fun x => (chartSplitting_card Y (e x) (v x)).trans (hn _))
  exact ⟨τ, hτ⟩

/-- The same transfer with the exact original constant-integer source and
represented augmentation used by field restriction. -/
theorem exists_normalized_transfer (n : ℕ) (hn : ∀ x : X, Y.obj.hom.finrank x = n) :
    ∃ τ : (constantSheaf (Scheme.smallEtaleTopology X) AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of (ULift.{u + 1} ℤ)) ⟶
      freeAbelianSheaf.{u + 1} (Scheme.smallEtaleTopology X) ((toEtale X).obj Y),
      τ ≫ ((freeAbelianSheafFunctor.{u + 1} (Scheme.smallEtaleTopology X)).map
        ((MorphismProperty.Over.mkIdTerminal (@Etale : MorphismProperty Scheme.{u}) X).from
          ((toEtale X).obj Y)) ≫
        (constantIntegerFreeTerminalIso (Scheme.smallEtaleTopology X)
          (MorphismProperty.Over.mkIdTerminal (@Etale : MorphismProperty Scheme.{u}) X)).inv) =
        n • 𝟙 _ := by
  exact exists_normalized_transfer_of_freeRepresentable.{u + 1}
    (Scheme.smallEtaleTopology X)
    (MorphismProperty.Over.mkIdTerminal (@Etale : MorphismProperty Scheme.{u}) X)
    n (exists_freeRepresentable_transfer Y n hn)

end AlgebraicGeometry.Scheme.FiniteEtale

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Fields

open Scheme.FiniteEtale Scheme.FiniteEtale.FieldGalois.Arbitrary

universe u

attribute [local instance] Fintype.ofFinite

variable (K E : Type u) [Field K] [Field E] [Algebra K E]
    [FiniteDimensional K E] [Algebra.IsSeparable K E]
    [HasSheafify (Scheme.smallEtaleTopology (Spec (.of K))) AddCommGrpCat.{u + 1}]

/-- Finite separable field transfer with the exact normalized source and the
actual field degree, not a label-cardinality hypothesis. -/
theorem exists_finiteField_normalized_transfer :
    ∃ τ : (constantSheaf (Scheme.smallEtaleTopology (Spec (.of K))) AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of (ULift.{u + 1} ℤ)) ⟶
      freeAbelianSheaf.{u + 1} (Scheme.smallEtaleTopology (Spec (.of K)))
        ((toEtale _).obj (finiteFieldCover K E)),
      τ ≫ ((freeAbelianSheafFunctor.{u + 1} (Scheme.smallEtaleTopology (Spec (.of K)))).map
        ((StrictlyLocal.terminalIsTerminal K).from ((toEtale _).obj (finiteFieldCover K E))) ≫
        (constantIntegerFreeTerminalIso (Scheme.smallEtaleTopology (Spec (.of K)))
          (StrictlyLocal.terminalIsTerminal K)).inv) = Module.finrank K E • 𝟙 _ := by
  have hr (x : Spec (.of K)) : (finiteFieldCover K E).obj.hom.finrank x =
      Module.finrank K E := by
    change (Spec.map (CommRingCat.ofHom (algebraMap K E))).finrank x = _
    simp only [Scheme.Hom.finrank_SpecMap_algebraMap, Module.rankAtStalk_eq_finrank_of_free]
    rfl
  have h := exists_normalized_transfer (finiteFieldCover K E) (Module.finrank K E) hr
  have ht : StrictlyLocal.terminalIsTerminal K =
      MorphismProperty.Over.mkIdTerminal (@Etale : MorphismProperty Scheme.{u}) (Spec (.of K)) :=
    Subsingleton.elim _ _
  simpa only [ht] using h

end AlgebraicGeometry.Scheme.EtaleCohomology.Fields
