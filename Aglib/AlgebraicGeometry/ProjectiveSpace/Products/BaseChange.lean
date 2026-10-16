/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.Structure
public import Aglib.AlgebraicGeometry.Limits.FiniteProducts.BaseChange

/-!
# Original base change of finite projective products

The existing native finite over-product comparison is viewed through the
original pullback symmetry. This identifies the fibre product whose first
projection is the displayed base map with the same finite product of the
original component pullbacks. Both the base projection and all component
projections are retained. No second product object is defined.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.ProjectiveSpace

variable (R : Type u) [CommRing R] {S : Scheme.{u}}
  (f : S ⟶ Spec (.of R)) {m : ℕ} (ι : Fin m → Type u)

/-- The same native finite product after the original base change, with the
base-first pullback convention used by the actual graph-product pair. -/
def productBaseChangeIso :
    pullback f (Scheme.finiteProductOver (fun i => Over.mk (toSpec R (ι i)))).hom ≅
      (Scheme.finiteProductOver (fun i =>
        (Over.pullback f).obj (Over.mk (toSpec R (ι i))))).left :=
  pullbackSymmetry f _ ≪≫ (Over.forget S).mapIso
    (Scheme.finiteProductOverPullbackIso f (fun i => Over.mk (toSpec R (ι i))))

@[reassoc (attr := simp)]
theorem productBaseChangeIso_hom_base :
    (productBaseChangeIso R f ι).hom ≫
        (Scheme.finiteProductOver (fun i =>
          (Over.pullback f).obj (Over.mk (toSpec R (ι i))))).hom =
      pullback.fst f (Scheme.finiteProductOver (fun i => Over.mk (toSpec R (ι i)))).hom := by
  simp [productBaseChangeIso, Category.assoc]

/-- Every component is the original projective projection of the original fibre product. -/
@[reassoc (attr := simp)]
theorem productBaseChangeIso_hom_π_fst (i : Fin m) :
    (productBaseChangeIso R f ι).hom ≫
        (Scheme.finiteProductOverπ (fun j =>
          (Over.pullback f).obj (Over.mk (toSpec R (ι j)))) i).left ≫
          pullback.fst (toSpec R (ι i)) f =
      pullback.snd f (Scheme.finiteProductOver (fun j => Over.mk (toSpec R (ι j)))).hom ≫
        (Scheme.finiteProductOverπ (fun j => Over.mk (toSpec R (ι j))) i).left := by
  let P : Fin m → Over (Spec (.of R)) := fun j => Over.mk (toSpec R (ι j))
  have H : (Scheme.finiteProductOverPullbackIso f P).hom.left ≫
        (Scheme.finiteProductOverπ (fun j => (Over.pullback f).obj (P j)) i).left ≫
          pullback.fst (toSpec R (ι i)) f =
      pullback.fst (Scheme.finiteProductOver P).hom f ≫
        (Scheme.finiteProductOverπ P i).left :=
    Scheme.finiteProductOverPullbackIso_hom_π_fst f P i
  change ((pullbackSymmetry f (Scheme.finiteProductOver P).hom).hom ≫
    (Scheme.finiteProductOverPullbackIso f P).hom.left) ≫ _ ≫ _ = _
  rw [Category.assoc, H, pullbackSymmetry_hom_comp_fst_assoc]

/-- The empty-family comparison is exactly the original first pullback projection. -/
theorem productBaseChangeIso_zero_hom (ι : Fin 0 → Type u) :
    (productBaseChangeIso R f ι).hom = pullback.fst f (𝟙 (Spec (.of R))) := by
  simpa [Scheme.finiteProductOver] using productBaseChangeIso_hom_base R f ι

/-- The actual first projection of a finite projective product is proper. -/
theorem isProper_productProjection [∀ i, Finite (ι i)] :
    IsProper (pullback.fst f
      (Scheme.finiteProductOver (fun i => Over.mk (toSpec R (ι i)))).hom) := by
  let : ∀ i, IsProper (Over.mk (toSpec R (ι i))).hom := fun i => by
    change IsProper (toSpec R (ι i))
    infer_instance
  let : IsProper (Scheme.finiteProductOver (fun i => Over.mk (toSpec R (ι i)))).hom :=
    Scheme.isProper_finiteProductOver _
  infer_instance

/-- The original product pullback over a locally Noetherian base is locally Noetherian.
No Noetherian hypothesis on the original presentation ring is needed. -/
theorem isLocallyNoetherian_productPullback [IsLocallyNoetherian S] [∀ i, Finite (ι i)] :
    IsLocallyNoetherian
      (pullback f (Scheme.finiteProductOver (fun i => Over.mk (toSpec R (ι i)))).hom) := by
  let : IsProper (pullback.fst f
      (Scheme.finiteProductOver (fun i => Over.mk (toSpec R (ι i)))).hom) :=
    isProper_productProjection R f ι
  exact LocallyOfFiniteType.isLocallyNoetherian
    (pullback.fst f (Scheme.finiteProductOver (fun i => Over.mk (toSpec R (ι i)))).hom)

end AlgebraicGeometry.ProjectiveSpace
