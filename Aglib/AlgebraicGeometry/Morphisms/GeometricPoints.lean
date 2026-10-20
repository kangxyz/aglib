/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.RationalPoint.ExtensionSource
public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-!
# Morphism equality detected by a specified algebraically closed extension

Source: `R5Lab.AlgebraicGeometry.EllipticCurve.Tate.MapFaithfulness`,
revision `f8a3314ddecffcada2ec721d26d56a937bed9690`, original lines 101–144.
Only the stated generic slice is admitted; its actual objects, maps and hypotheses are retained.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.OverField
universe u
/-- Equality on all points over a specified algebraically closed extension
implies equality of the original-field morphisms. Closed-point density is used
on the actual scalar extension, then field-extension faithful flatness descends
its equality. No point-faithfulness premise is supplied. -/
theorem hom_eq_of_extension_points {F K : Type u} [Field F] [Field K] [IsAlgClosed K]
    (f : F →+* K) {C D : FScheme F}
    [GeometricallyReduced C.hom] [LocallyOfFiniteType C.hom]
    [IsSeparated D.hom] [LocallyOfFiniteType D.hom]
    (m n : C ⟶ D)
    (h : ∀ x : extensionPointSource f ⟶ C, x ≫ m = x ≫ n) : m = n := by
  let s := Spec.map (CommRingCat.ofHom f)
  let P := Over.pullback s
  let C' := P.obj C
  let D' := P.obj D
  let : Surjective s := ⟨fun x => ⟨IsLocalRing.closedPoint K, Subsingleton.elim _ _⟩⟩
  let : IsReduced C'.left := by dsimp [C', P]; infer_instance
  let : LocallyOfFiniteType C'.hom := by dsimp [C', P]; infer_instance
  let : IsSeparated D'.hom := by dsimp [D', P]; infer_instance
  let : LocallyOfFiniteType D'.hom := by dsimp [D', P]; infer_instance
  let : LocallyOfFiniteType ((P.map m).left ≫ D'.hom) := by
    change LocallyOfFiniteType ((P.map m).left ≫ (P.obj D).hom)
    rw [(P.map m).w]
    dsimp [P]
    infer_instance
  apply P.map_injective
  apply Over.OverMorphism.ext
  apply ext_of_apply_eq D'.hom Set.univ isOpen_univ.isLocallyClosed dense_univ
  · intro x _ hx
    let z := pointOfClosedPoint C'.hom x hx
    have hz : z ≫ C'.hom = 𝟙 _ := pointOfClosedPoint_comp C'.hom x hx
    change z ≫ pullback.snd C.hom s = 𝟙 _ at hz
    let y : extensionPointSource f ⟶ C :=
      Over.homMk (z ≫ pullback.fst C.hom s) (by
        rw [Category.assoc, pullback.condition, ← Category.assoc, hz]
        exact Category.id_comp s)
    have he := congrArg (fun t : extensionPointSource f ⟶ D => t.left) (h y)
    have he' : z ≫ (P.map m).left = z ≫ (P.map n).left := by
      apply pullback.hom_ext
      · simpa [P, y, Category.assoc] using he
      · simp [P]
    have hp := congrArg (fun t : Spec (.of K) ⟶ D'.left => t (IsLocalRing.closedPoint K)) he'
    simpa [z] using hp
  · exact (P.map m).w.trans (P.map n).w.symm

end AlgebraicGeometry.Scheme.OverField
