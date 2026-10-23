/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Category.CommAlgCat.FiniteType
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.RingTheory.Etale.Basic
public import Aglib.RingTheory.Unramified.Equalizer

/-!
# A small filtered category of geometric etale neighborhoods

Objects are native finite-type algebra presentations that are etale, equipped
with a point in a fixed field over the base. Morphisms are actual algebra maps preserving the
point. Tensor products give common successors, and one-element localizations
coequalize parallel morphisms. No henselianity, separable closedness, or approximation is assumed.

Unlike rational-residue neighborhoods, the chosen field need not be the residue
field of the base. Thus this index retains geometric residue extensions needed
for strict henselization. This leaf constructs the filtered index only, not its
colimit or a strict Henselianity instance.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open scoped TensorProduct

universe u v

/-- A small presentation of an etale algebra with a point in a fixed field over the base. -/
structure GeometricEtaleNeighborhood (R : Type u) [CommRing R]
    (Ω : Type u) [Field Ω] [Algebra R Ω] : Type u where
  /-- A native small finite-type algebra presentation. -/
  presentation : FGAlgCatSkeleton R
  /-- The presented algebra is etale. -/
  isEtale : Algebra.Etale R presentation.eval.obj
  /-- The chosen field-valued point over the base. -/
  point : presentation.eval.obj →ₐ[R] Ω

namespace GeometricEtaleNeighborhood

variable {R : Type u} [CommRing R] {Ω : Type u} [Field Ω] [Algebra R Ω]

/-- The actual commutative algebra underlying a pointed neighborhood. -/
abbrev algebra (X : GeometricEtaleNeighborhood R Ω) : CommAlgCat.{u} R :=
  X.presentation.eval.obj

instance (X : GeometricEtaleNeighborhood R Ω) : Algebra.Etale R X.algebra := X.isEtale

/-- Morphisms are algebra homomorphisms preserving the chosen field-valued point. -/
abbrev Hom (X Y : GeometricEtaleNeighborhood R Ω) :=
  { f : X.algebra →ₐ[R] Y.algebra // Y.point.comp f = X.point }

instance : SmallCategory (GeometricEtaleNeighborhood R Ω) where
  Hom := Hom
  id X := ⟨AlgHom.id R X.algebra, by simp⟩
  comp f g := ⟨g.val.comp f.val, by
    rw [← AlgHom.comp_assoc, g.property, f.property]⟩
  id_comp := by intros; apply Subtype.ext; rfl
  comp_id := by intros; apply Subtype.ext; rfl
  assoc := by intros; apply Subtype.ext; rfl

variable (R Ω) in
/-- The diagram of actual commutative algebras underlying the neighborhoods. -/
def diagram : GeometricEtaleNeighborhood R Ω ⥤ CommAlgCat.{u} R where
  obj X := X.algebra
  map f := CommAlgCat.ofHom f.val

/-- Every pointed etale algebra admits a small native presentation, even when
its carrier lies in a different universe from the base. -/
theorem exists_equiv (A : Type v) [CommRing A] [Algebra R A] [Algebra.Etale R A]
    (p : A →ₐ[R] Ω) :
    ∃ (X : GeometricEtaleNeighborhood R Ω) (e : A ≃ₐ[R] X.algebra),
      X.point.comp e.toAlgHom = p := by
  obtain ⟨P, ⟨e⟩⟩ := Algebra.FiniteType.exists_fgAlgCatSkeleton R A
  let X : GeometricEtaleNeighborhood R Ω :=
    ⟨P, Algebra.Etale.of_equiv e, p.comp e.symm.toAlgHom⟩
  refine ⟨X, e, ?_⟩
  apply AlgHom.ext
  intro a
  change p (e.symm (e a)) = p a
  rw [e.symm_apply_apply]

instance : Nonempty (GeometricEtaleNeighborhood R Ω) := by
  obtain ⟨X, _, _⟩ := exists_equiv R (Algebra.ofId R (Ω))
  exact ⟨X⟩

/-- Tensoring the actual algebras gives a common successor with the literal
left and right tensor inclusions, transported through a small presentation. -/
theorem exists_tensor_cocone (X Y : GeometricEtaleNeighborhood R Ω) :
    ∃ (Z : GeometricEtaleNeighborhood R Ω) (e : X.algebra ⊗[R] Y.algebra ≃ₐ[R] Z.algebra)
      (f : X ⟶ Z) (g : Y ⟶ Z),
      f.val = e.toAlgHom.comp Algebra.TensorProduct.includeLeft ∧
      g.val = e.toAlgHom.comp Algebra.TensorProduct.includeRight := by
  let : Algebra.Etale R (X.algebra ⊗[R] Y.algebra) :=
    Algebra.Etale.comp R X.algebra _
  let p : X.algebra ⊗[R] Y.algebra →ₐ[R] Ω :=
    Algebra.TensorProduct.lift X.point Y.point (fun _ _ => .all _ _)
  obtain ⟨Z, e, he⟩ := exists_equiv (X.algebra ⊗[R] Y.algebra) p
  have hleft : Z.point.comp (e.toAlgHom.comp Algebra.TensorProduct.includeLeft) =
      X.point := by
    rw [← AlgHom.comp_assoc, he]
    exact Algebra.TensorProduct.lift_comp_includeLeft _ _ _
  have hright : Z.point.comp (e.toAlgHom.comp Algebra.TensorProduct.includeRight) =
      Y.point := by
    rw [← AlgHom.comp_assoc, he]
    exact Algebra.TensorProduct.lift_comp_includeRight' _ _ _
  exact ⟨Z, e, ⟨_, hleft⟩, ⟨_, hright⟩, rfl, rfl⟩

/-- Parallel pointed maps are coequalized by the actual localization map at
an element whose chosen field value is one, followed by a small presentation. -/
theorem exists_localization_coequalizer {X Y : GeometricEtaleNeighborhood R Ω}
    (f g : X ⟶ Y) :
    ∃ s : Y.algebra, Y.point s = 1 ∧
      ∃ (Z : GeometricEtaleNeighborhood R Ω) (e : Localization.Away s ≃ₐ[R] Z.algebra)
        (h : Y ⟶ Z),
        h.val = e.toAlgHom.comp (IsScalarTower.toAlgHom R Y.algebra (Localization.Away s)) ∧
          f ≫ h = g ≫ h := by
  have hp : Y.point.toRingHom.comp f.val.toRingHom =
      Y.point.toRingHom.comp g.val.toRingHom := by
    exact congrArg AlgHom.toRingHom (f.property.trans g.property.symm)
  obtain ⟨s, hs, hfg, q, hq⟩ :=
    Algebra.FormallyUnramified.exists_pointed_localization_coequalizer
      f.val g.val Y.point.toRingHom hp
  let qA : Localization.Away s →ₐ[R] Ω :=
    { q with
      commutes' r := by
        rw [IsScalarTower.algebraMap_apply R Y.algebra (Localization.Away s)]
        exact (RingHom.congr_fun hq (algebraMap R Y.algebra r)).trans (Y.point.commutes r) }
  have hqA : qA.comp (IsScalarTower.toAlgHom R Y.algebra (Localization.Away s)) =
      Y.point := by
    apply AlgHom.ext
    intro a
    exact RingHom.congr_fun hq a
  obtain ⟨Z, e, he⟩ := exists_equiv (Localization.Away s) qA
  let h : Y ⟶ Z :=
    ⟨e.toAlgHom.comp (IsScalarTower.toAlgHom R Y.algebra (Localization.Away s)), by
      rw [← AlgHom.comp_assoc, he, hqA]⟩
  refine ⟨s, hs, Z, e, h, rfl, ?_⟩
  apply Subtype.ext
  change (e.toAlgHom.comp (IsScalarTower.toAlgHom R Y.algebra (Localization.Away s))).comp
      f.val =
    (e.toAlgHom.comp (IsScalarTower.toAlgHom R Y.algebra (Localization.Away s))).comp
      g.val
  rw [AlgHom.comp_assoc, AlgHom.comp_assoc, hfg]

instance : IsFiltered (GeometricEtaleNeighborhood R Ω) where
  cocone_objs X Y := by
    obtain ⟨Z, _, f, g, _, _⟩ := exists_tensor_cocone X Y
    exact ⟨Z, f, g, trivial⟩
  cocone_maps := by
    intro X Y f g
    obtain ⟨_, _, Z, _, h, _, hh⟩ := exists_localization_coequalizer f g
    exact ⟨Z, h, hh⟩

end GeometricEtaleNeighborhood
