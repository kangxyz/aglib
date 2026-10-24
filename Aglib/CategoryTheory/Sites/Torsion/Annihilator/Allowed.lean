/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.Torsion.Annihilator
public import Aglib.CategoryTheory.Sites.Torsion.Points
public import Mathlib.Algebra.Group.Submonoid.Basic

/-! # Annihilator diagrams with multiplicatively allowed positive orders

Positive members of a multiplicative set, ordered by divisibility, index the
existing native annihilator kernels. The local condition is detected by the
original point fibres of a small conservative family.
-/

@[expose] public noncomputable section

open CategoryTheory.Limits Opposite

namespace CategoryTheory

/-- Positive allowed annihilators, with divisibility rather than numerical order. -/
structure AllowedAnnihilatorIndex (M : Submonoid ℕ) where
  /-- The underlying positive allowed annihilator. -/
  val : ℕ
  positive : 0 < val
  mem : val ∈ M

namespace AllowedAnnihilatorIndex

variable (M : Submonoid ℕ)

instance : Preorder (AllowedAnnihilatorIndex M) where
  le n m := n.val ∣ m.val
  le_refl n := dvd_refl n.val
  le_trans _ _ _ := dvd_trans

instance : Nonempty (AllowedAnnihilatorIndex M) := ⟨⟨1, by decide, M.one_mem⟩⟩

/-- Multiplication supplies a common upper bound without introducing forbidden orders. -/
instance : IsFiltered (AllowedAnnihilatorIndex M) where
  cocone_objs n m :=
    ⟨⟨n.val * m.val, Nat.mul_pos n.positive m.positive, M.mul_mem n.mem m.mem⟩,
      homOfLE ⟨m.val, rfl⟩, homOfLE ⟨n.val, Nat.mul_comm _ _⟩, trivial⟩
  cocone_maps {_ _} f g := ⟨_, 𝟙 _, by subsingleton⟩

end AllowedAnnihilatorIndex

namespace Presheaf

universe u v w

variable {C : Type u} [Category.{v} C]

/-- The sieve of restrictions killed by a positive member of the allowed multiplicative set. -/
def allowedTorsionSieve (M : Submonoid ℕ) (F : Cᵒᵖ ⥤ AddCommGrpCat.{w})
    {U : C} (s : F.obj (op U)) : Sieve U where
  arrows V f := ∃ n : ℕ, 0 < n ∧ n ∈ M ∧ n • F.map f.op s = 0
  downward_closed := by
    intro V W f hf g
    obtain ⟨n, hn, hm, hs⟩ := hf
    refine ⟨n, hn, hm, ?_⟩
    simpa only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply,
      map_nsmul, map_zero] using congrArg (F.map g.op) hs

/-- Local torsion with all annihilators belonging to the specified multiplicative set. -/
def IsLocallyAllowedTorsion (M : Submonoid ℕ) (J : GrothendieckTopology C)
    (F : Cᵒᵖ ⥤ AddCommGrpCat.{w}) : Prop :=
  ∀ (U : C) (s : F.obj (op U)), allowedTorsionSieve M F s ∈ J U

/-- Allowed positive annihilators imply the existing internal torsion condition. -/
theorem IsLocallyAllowedTorsion.isLocallyTorsion {M : Submonoid ℕ}
    {J : GrothendieckTopology C} {F : Cᵒᵖ ⥤ AddCommGrpCat.{w}}
    (hF : IsLocallyAllowedTorsion M J F) : IsLocallyTorsion J F := by
  intro U s
  apply J.superset_covering ?_ (hF U s)
  rintro V f ⟨n, hn, _, hs⟩
  exact ⟨n, hn, hs⟩

/-- Every original point-fibre element has a positive allowed annihilator. -/
theorem IsLocallyAllowedTorsion.fiber [LocallySmall.{w} C]
    {M : Submonoid ℕ} {J : GrothendieckTopology C}
    {F : Cᵒᵖ ⥤ AddCommGrpCat.{w}} (hF : IsLocallyAllowedTorsion M J F)
    (Φ : GrothendieckTopology.Point.{w} J)
    (z : (Φ.presheafFiber (A := AddCommGrpCat.{w})).obj F) :
    ∃ n : ℕ, 0 < n ∧ n ∈ M ∧ n • z = 0 := by
  obtain ⟨U, x, s, rfl⟩ := Φ.toPresheafFiber_jointly_surjective z
  obtain ⟨V, f, ⟨n, hn, hm, hs⟩, y, hy⟩ := Φ.jointly_surjective _ (hF U s) x
  refine ⟨n, hn, hm, ?_⟩
  rw [← hy, ← Φ.toPresheafFiber_w_apply f y F s, ← map_nsmul, hs, map_zero]

/-- The original fibres of a small conservative family detect allowed local annihilators. -/
theorem isLocallyAllowedTorsion_of_fibers [LocallySmall.{w} C]
    {M : Submonoid ℕ} {J : GrothendieckTopology C}
    {F : Cᵒᵖ ⥤ AddCommGrpCat.{w}}
    [HasSheafify J (Type w)] [J.WEqualsLocallyBijective (Type w)]
    (P : ObjectProperty (GrothendieckTopology.Point.{w} J))
    [ObjectProperty.Small.{w} P] (hP : P.IsConservativeFamilyOfPoints)
    (hF : ∀ (Φ : P.FullSubcategory)
      (z : (Φ.obj.presheafFiber (A := AddCommGrpCat.{w})).obj F),
      ∃ n : ℕ, 0 < n ∧ n ∈ M ∧ n • z = 0) :
    IsLocallyAllowedTorsion M J F := by
  intro U s
  let R := allowedTorsionSieve M F s
  change R ∈ J U
  rw [← Sieve.ofArrows_category R, hP.jointly_reflect_ofArrows_mem_of_small]
  intro Φ x
  obtain ⟨n, hn, hm, hs⟩ := hF Φ (Φ.obj.toPresheafFiber U x F s)
  have heq : Φ.obj.toPresheafFiber U x F (n • s) =
      Φ.obj.toPresheafFiber U x F 0 := by
    simpa only [map_nsmul, map_zero] using hs
  obtain ⟨V, f, y, hy, hf⟩ :=
    (Φ.obj.toPresheafFiber_eq_iff' U x (n • s) 0).mp heq
  have hr : R f := ⟨n, hn, hm, by simpa only [map_nsmul, map_zero] using hf⟩
  exact ⟨⟨Over.mk f, hr⟩, y, hy⟩

end Presheaf

namespace Sheaf

universe u v w

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{w}] (M : Submonoid ℕ)

/-- The existing kernel sheaves, indexed only by positive allowed annihilators. -/
def allowedAnnihilatorDiagram (F : Sheaf J AddCommGrpCat.{w}) :
    AllowedAnnihilatorIndex M ⥤ Sheaf J AddCommGrpCat.{w} where
  obj n := annihilator F n.val
  map h := annihilatorMap F (leOfHom h)
  map_id n := annihilatorMap_refl F n.val
  map_comp h h' := (annihilatorMap_comp F (leOfHom h) (leOfHom h')).symm

/-- The divisibility transitions preserve the original kernel inclusions. -/
@[simp, reassoc]
theorem allowedAnnihilatorDiagram_map_ι (F : Sheaf J AddCommGrpCat.{w})
    {n m : AllowedAnnihilatorIndex M} (h : n ⟶ m) :
    (allowedAnnihilatorDiagram M F).map h ≫ annihilatorι F m.val =
      annihilatorι F n.val := annihilatorMap_ι F (leOfHom h)

/-- The actual annihilator inclusions are the specified cocone legs. -/
def allowedAnnihilatorCocone (F : Sheaf J AddCommGrpCat.{w}) :
    Cocone (allowedAnnihilatorDiagram M F) where
  pt := F
  ι :=
    { app n := annihilatorι F n.val
      naturality := by
        intro n m h
        change (allowedAnnihilatorDiagram M F).map h ≫ annihilatorι F m.val =
          annihilatorι F n.val ≫ 𝟙 F
        rw [allowedAnnihilatorDiagram_map_ι, Category.comp_id] }

/-- The stage is killed by its actual positive allowed index. -/
theorem allowedAnnihilatorDiagram_annihilated (F : Sheaf J AddCommGrpCat.{w})
    (n : AllowedAnnihilatorIndex M) :
    n.val • 𝟙 ((allowedAnnihilatorDiagram M F).obj n) = 0 :=
  nsmul_id_annihilator F n.val

/-- Original coefficient maps act on the original annihilator kernels. -/
def allowedAnnihilatorCoefficientMap {F G : Sheaf J AddCommGrpCat.{w}} (q : F ⟶ G) :
    allowedAnnihilatorDiagram M F ⟶ allowedAnnihilatorDiagram M G where
  app n := annihilatorCoefficientMap q n.val
  naturality := by
    intro n m h
    exact annihilatorMap_coefficient_naturality q (leOfHom h)

/-- The coefficient-induced diagram map preserves the original cocone. -/
@[reassoc]
theorem allowedAnnihilatorCoefficientMap_ι {F G : Sheaf J AddCommGrpCat.{w}}
    (q : F ⟶ G) (n : AllowedAnnihilatorIndex M) :
    (allowedAnnihilatorCoefficientMap M q).app n ≫
        (allowedAnnihilatorCocone M G).ι.app n =
      (allowedAnnihilatorCocone M F).ι.app n ≫ q :=
  annihilatorCoefficientMap_ι q n.val

/-- Each allowed stage has allowed local torsion with its original uniform annihilator. -/
theorem allowedAnnihilatorDiagram_isLocallyAllowedTorsion
    (F : Sheaf J AddCommGrpCat.{w}) (n : AllowedAnnihilatorIndex M) :
    Presheaf.IsLocallyAllowedTorsion M J
      ((allowedAnnihilatorDiagram M F).obj n).obj := by
  intro U s
  apply J.superset_covering ?_ (J.top_mem U)
  intro V f _
  refine ⟨n.val, n.positive, n.mem, ?_⟩
  exact congrArg
    (fun q : (allowedAnnihilatorDiagram M F).obj n ⟶
      (allowedAnnihilatorDiagram M F).obj n =>
        q.hom.app (op V) (((allowedAnnihilatorDiagram M F).obj n).obj.map f.op s))
    (allowedAnnihilatorDiagram_annihilated M F n)

end Sheaf

end CategoryTheory
