/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.CoverLimits
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-! The actual scheme underlying a finite cover coproduct is its scheme
coproduct. This supplies the finite constant-cover representation producer. -/

@[expose] public section

noncomputable section
set_option autoImplicit false

open _root_.CategoryTheory _root_.CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.FiniteEtale
open _root_.AlgebraicGeometry.Scheme.FiniteEtale (forgetToScheme)

universe u
variable {X : Scheme.{u}}

/-- The initial structure on the scheme underlying the empty finite étale cover. -/
def emptyCoverSchemeIsInitial (X : Scheme.{u}) :
    IsInitial ((forgetToScheme X).obj
      (Scheme.FiniteEtale.Connectedness.emptyCover X)) :=
  emptyIsInitial

instance instPreservesInitialCoverToScheme (X : Scheme.{u}) :
    PreservesColimit (_root_.CategoryTheory.Functor.empty.{0} (Scheme.FiniteEtale X))
      (forgetToScheme X) :=
  preservesColimit_of_preserves_colimit_cocone (emptyCoverIsInitial X)
    ((isColimitMapCoconeEmptyCoconeEquiv (forgetToScheme X) _).symm
      (emptyCoverSchemeIsInitial X))

instance instPreservesEmptyColimitsCoverToScheme (X : Scheme.{u}) :
    PreservesColimitsOfShape (Discrete PEmpty.{1}) (forgetToScheme X) :=
  preservesColimitsOfShape_pempty_of_preservesInitial (forgetToScheme X)

/-- The coproduct colimit structure on the schemes underlying the binary coproduct of covers. -/
def binaryCoproductSchemeIsColimit (Y Z : Scheme.FiniteEtale X) :
    IsColimit (BinaryCofan.mk ((forgetToScheme X).map (binaryCoproductInl Y Z))
      ((forgetToScheme X).map (binaryCoproductInr Y Z))) := by
  change IsColimit (BinaryCofan.mk (coprod.inl : Y.obj.left ⟶ Y.obj.left ⨿ Z.obj.left)
    coprod.inr)
  exact coprodIsCoprod _ _

instance instPreservesBinaryCoproductCoverToScheme (Y Z : Scheme.FiniteEtale X) :
    PreservesColimit (pair Y Z) (forgetToScheme X) :=
  preservesColimit_of_preserves_colimit_cocone (binaryCoproductIsColimit Y Z)
    ((isColimitMapCoconeBinaryCofanEquiv (forgetToScheme X)
      (binaryCoproductInl Y Z) (binaryCoproductInr Y Z)).symm
        (binaryCoproductSchemeIsColimit Y Z))

instance instPreservesBinaryCoproductsCoverToScheme (X : Scheme.{u}) :
    PreservesColimitsOfShape (Discrete WalkingPair) (forgetToScheme X) where
  preservesColimit {K} :=
    preservesColimit_of_iso_diagram (forgetToScheme X) (diagramIsoPair K).symm

instance instPreservesFiniteCoproductsCoverToScheme (X : Scheme.{u}) :
    PreservesFiniteCoproducts (forgetToScheme X) where
  preserves n :=
    PreservesFiniteCoproducts.of_preserves_binary_and_initial (forgetToScheme X) (Fin n)

/-- The trivial finite étale cover of `X` formed as an `A`-indexed coproduct of terminal covers. -/
def trivialCover (X : Scheme.{u}) (A : Type u) [Finite A] : Scheme.FiniteEtale X :=
  ∐ fun _ : A => terminalCover X

/-- The comparison from the scheme underlying the trivial cover to the coproduct of copies of
`X`. -/
def trivialCoverSigmaIso (X : Scheme.{u}) (A : Type u) [Finite A] :
    (trivialCover X A).obj.left ≅ ∐ fun _ : A => X :=
  PreservesCoproduct.iso (forgetToScheme X) (fun _ : A => terminalCover X)

theorem trivialCoverSigmaIso_ι (X : Scheme.{u}) (A : Type u) [Finite A] (a : A) :
    (Sigma.ι (fun _ : A => terminalCover X) a).hom.left ≫
      (trivialCoverSigmaIso X A).hom = Sigma.ι (fun _ : A => X) a := by
  have h := map_ι_comp_inv_sigmaComparison (forgetToScheme X)
    (fun _ : A => terminalCover X) a
  change (forgetToScheme X).map (Sigma.ι (fun _ : A => terminalCover X) a) ≫
    (PreservesCoproduct.iso (forgetToScheme X) (fun _ : A => terminalCover X)).hom =
      Sigma.ι (fun _ : A => (forgetToScheme X).obj (terminalCover X)) a
  simpa only [← PreservesCoproduct.inv_hom, IsIso.Iso.inv_inv] using h

end AlgebraicGeometry.Scheme.FiniteEtale

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 fa57486c71d917b2b3e170f6662d5d82b95d7a40b38295a2fdb3277376dcd3cf.
Definitions, hypotheses and universes are retained modulo native names. -/
