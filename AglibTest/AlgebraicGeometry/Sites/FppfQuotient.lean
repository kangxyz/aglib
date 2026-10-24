/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Sites.FppfQuotient
public import Aglib.AlgebraicGeometry.Sites.OverRepresentability

/-!
# Consumer checks for representability by an fppf quotient

The public statements of `Sites/FppfQuotient` (Kleiman, *The Picard scheme*,
arXiv:math/0504020v1, Lemma 4.9, fppf form on locally Noetherian test schemes) are exercised on
their own hypotheses, and on the functor of points of a locally Noetherian scheme `Q` over `S`,
an fppf sheaf because the fppf topology is subcanonical: with `Z = Q`, `q = 𝟙` and `z = 𝟙`, all
hypotheses hold, the descended section is `𝟙`, and the bijection is `f ↦ f`.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits Opposite AlgebraicGeometry

universe v u

namespace AglibTest.FppfQuotient

open Scheme

variable {S : Scheme.{u}}

/-- A single flat surjective morphism locally of finite presentation is an fppf covering. -/
example {T U : Over S} (k : U ⟶ T) [Flat k.left] [Surjective k.left]
    [LocallyOfFinitePresentation k.left] :
    Sieve.ofArrows (fun _ : PUnit.{1} => U) (fun _ => k) ∈ (Scheme.fppfTopology.over S) T :=
  ofArrows_mem_fppfTopology_over _ _ (fun _ => inferInstance) (fun _ => inferInstance)
    fun t => ⟨PUnit.unit, k.left.surjective t⟩

section Hypotheses

variable {F : (Over S)ᵒᵖ ⥤ Type v} (hF : Presieve.IsSheaf (Scheme.fppfTopology.over S) F)
  (G : Subfunctor ((locallyNoetherianOverInclusion S).op ⋙ F)) {Z Q : LocallyNoetherianOver S}
  (q : Z ⟶ Q) [Flat q.hom.left] [Surjective q.hom.left] [LocallyOfFinitePresentation q.hom.left]
  (z : F.obj (op Z.obj)) (hz : z ∈ G.obj (op Z))
  (hG : ∀ ξ : F.obj (op Q.obj), F.map q.hom.op ξ ∈ G.obj (op Z) → ξ ∈ G.obj (op Q))
  (h₁ : ∀ ⦃T : LocallyNoetherianOver S⦄ (a b : T ⟶ Z), F.map a.hom.op z = F.map b.hom.op z →
    a ≫ q = b ≫ q)
  (h₂ : ∀ ⦃T : LocallyNoetherianOver S⦄ (a b : T ⟶ Z), a ≫ q = b ≫ q →
    F.map a.hom.op z = F.map b.hom.op z)
  (h₃ : ∀ ⦃T : LocallyNoetherianOver S⦄ (ξ : F.obj (op T.obj)), ξ ∈ G.obj (op T) →
    ∀ t : T.obj.left, ∃ (U : LocallyNoetherianOver S) (k : U ⟶ T) (a : U ⟶ Z),
      Flat k.hom.left ∧ LocallyOfFinitePresentation k.hom.left ∧ t ∈ Set.range k.hom.left ∧
        F.map a.hom.op z = F.map k.hom.op ξ)

/-- (h₂) in its universal form: from a cartesian square `R ⇉ Z ⟶ Q` along which `z` has equal
pullbacks. -/
example {R : Over S} (p₁ p₂ : R ⟶ Z.obj) (hR : IsPullback p₁.left p₂.left q.hom.left q.hom.left)
    (hp : F.map p₁.op z = F.map p₂.op z) :
    ∀ ⦃T : LocallyNoetherianOver S⦄ (a b : T ⟶ Z), a ≫ q = b ≫ q →
      F.map a.hom.op z = F.map b.hom.op z :=
  map_eq_map_of_comp_eq_of_isPullback q z p₁ p₂ hR hp

include hF h₂ in
/-- The descended section `λ` is the unique section pulling back to `z`. -/
example : ∃! l : F.obj (op Q.obj), F.map q.hom.op l = z :=
  ⟨fppfQuotientSection hF q z h₂, map_fppfQuotientSection hF q z h₂,
    fun _ hl => eq_fppfQuotientSection_of_map_eq hF q z h₂ hl⟩

include hF hz hG h₁ h₂ h₃ in
/-- `Q` represents `G` on locally Noetherian test schemes, through `f ↦ f^* λ`. -/
example {T : LocallyNoetherianOver S} (f : T ⟶ Q) :
    ((representableByOfFppfQuotient hF G q z hz hG h₁ h₂ h₃).homEquiv f).1 =
      F.map f.hom.op (fppfQuotientSection hF q z h₂) :=
  representableByOfFppfQuotient_homEquiv_coe hF G q z hz hG h₁ h₂ h₃ f

include hF hz hG h₁ h₂ h₃ in
/-- Every section of `G` over a locally Noetherian `T` is `f^* λ` for exactly one `f : T ⟶ Q`. -/
example {T : LocallyNoetherianOver S} (ξ : F.obj (op T.obj)) (hξ : ξ ∈ G.obj (op T)) :
    ∃! f : T ⟶ Q, F.map f.hom.op (fppfQuotientSection hF q z h₂) = ξ := by
  obtain ⟨f, hf⟩ := exists_map_eq_of_fppfQuotient hF G q z h₁ h₃
    (map_fppfQuotientSection hF q z h₂) ξ hξ
  exact ⟨f, hf, fun f' hf' => hom_ext_of_fppfQuotient q z h₁
    (map_fppfQuotientSection hF q z h₂) (hf'.trans hf.symm)⟩

end Hypotheses

section OverSubfunctor

open Scheme.LocalRepresentability

variable {F : (Over S)ᵒᵖ ⥤ Type v} (hF : Presieve.IsSheaf (Scheme.fppfTopology.over S) F)
  (G : Subfunctor F) {Z Q : LocallyNoetherianOver S} (q : Z ⟶ Q) [Flat q.hom.left]
  [Surjective q.hom.left] [LocallyOfFinitePresentation q.hom.left] (z : F.obj (op Z.obj))
  (hz : z ∈ G.obj (op Z.obj))
  (hG : ∀ ξ : F.obj (op Q.obj), F.map q.hom.op ξ ∈ G.obj (op Z.obj) → ξ ∈ G.obj (op Q.obj))
  (h₁ : ∀ ⦃T : LocallyNoetherianOver S⦄ (a b : T ⟶ Z), F.map a.hom.op z = F.map b.hom.op z →
    a ≫ q = b ≫ q)
  (h₂ : ∀ ⦃T : LocallyNoetherianOver S⦄ (a b : T ⟶ Z), a ≫ q = b ≫ q →
    F.map a.hom.op z = F.map b.hom.op z)
  (h₃ : ∀ ⦃T : LocallyNoetherianOver S⦄ (ξ : F.obj (op T.obj)), ξ ∈ G.obj (op T.obj) →
    ∀ t : T.obj.left, ∃ (U : LocallyNoetherianOver S) (k : U ⟶ T) (a : U ⟶ Z),
      Flat k.hom.left ∧ LocallyOfFinitePresentation k.hom.left ∧ t ∈ Set.range k.hom.left ∧
        F.map a.hom.op z = F.map k.hom.op ξ)

include hF hz hG h₁ h₂ h₃ in
/-- For a subfunctor `G` of `F` on all of `Over S`, the lemma applies to its restriction to
locally Noetherian test schemes; this is the functor `(ι.op ⋙ G.toFunctor)` of the blueprint's
Lean shape. -/
example : ((locallyNoetherianOverInclusion S).op ⋙ G.toFunctor).RepresentableBy Q :=
  representableByOfFppfQuotient hF (restrictSubfunctor (locallyNoetherianOver S) G) q z hz hG h₁ h₂
    h₃

end OverSubfunctor

section Points

variable (Q : LocallyNoetherianOver S)

/-- The functor of points of `Q` over `S` is an fppf sheaf. -/
theorem isSheaf_yoneda_obj : Presieve.IsSheaf (Scheme.fppfTopology.over S) (yoneda.obj Q.obj) :=
  GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _

instance : Flat (𝟙 Q : Q ⟶ Q).hom.left := inferInstanceAs (Flat (𝟙 Q.obj.left))

instance : Surjective (𝟙 Q : Q ⟶ Q).hom.left := inferInstanceAs (Surjective (𝟙 Q.obj.left))

instance : LocallyOfFinitePresentation (𝟙 Q : Q ⟶ Q).hom.left :=
  inferInstanceAs (LocallyOfFinitePresentation (𝟙 Q.obj.left))

theorem h₁_points ⦃T : LocallyNoetherianOver S⦄ (a b : T ⟶ Q) :
    (yoneda.obj Q.obj).map a.hom.op (𝟙 Q.obj) = (yoneda.obj Q.obj).map b.hom.op (𝟙 Q.obj) →
      a ≫ 𝟙 Q = b ≫ 𝟙 Q := by
  intro h
  rw [Category.comp_id, Category.comp_id]
  exact ObjectProperty.hom_ext _ (by simpa using h)

theorem h₂_points ⦃T : LocallyNoetherianOver S⦄ (a b : T ⟶ Q) :
    a ≫ 𝟙 Q = b ≫ 𝟙 Q →
      (yoneda.obj Q.obj).map a.hom.op (𝟙 Q.obj) = (yoneda.obj Q.obj).map b.hom.op (𝟙 Q.obj) := by
  intro h
  simp only [Category.comp_id] at h
  simp [h]

theorem h₃_points ⦃T : LocallyNoetherianOver S⦄ (ξ : (yoneda.obj Q.obj).obj (op T.obj))
    (_ : ξ ∈ (⊤ : Subfunctor ((locallyNoetherianOverInclusion S).op ⋙ yoneda.obj Q.obj)).obj
      (op T)) (t : T.obj.left) :
    ∃ (U : LocallyNoetherianOver S) (k : U ⟶ T) (a : U ⟶ Q),
      Flat k.hom.left ∧ LocallyOfFinitePresentation k.hom.left ∧ t ∈ Set.range k.hom.left ∧
        (yoneda.obj Q.obj).map a.hom.op (𝟙 Q.obj) = (yoneda.obj Q.obj).map k.hom.op ξ :=
  ⟨T, 𝟙 T, ObjectProperty.homMk ξ, inferInstanceAs (Flat (𝟙 T.obj.left)),
    inferInstanceAs (LocallyOfFinitePresentation (𝟙 T.obj.left)), ⟨t, rfl⟩, by simp⟩

/-- The functor of points of `Q`, as the quotient of `Q` by the identity. -/
def pointsRepresentableBy :
    (⊤ : Subfunctor ((locallyNoetherianOverInclusion S).op ⋙
      yoneda.obj Q.obj)).toFunctor.RepresentableBy Q :=
  representableByOfFppfQuotient (isSheaf_yoneda_obj Q) ⊤ (𝟙 Q) (𝟙 Q.obj) trivial
    (fun _ _ => trivial) (h₁_points Q) (h₂_points Q) (h₃_points Q)

/-- The descended section of the identity is the identity. -/
example : fppfQuotientSection (isSheaf_yoneda_obj Q) (𝟙 Q) (𝟙 Q.obj) (h₂_points Q) = 𝟙 Q.obj :=
  (eq_fppfQuotientSection_of_map_eq (isSheaf_yoneda_obj Q) (𝟙 Q) (𝟙 Q.obj) (h₂_points Q)
    (by simp)).symm

end Points

/--
info: 'AlgebraicGeometry.Scheme.representableByOfFppfQuotient' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms representableByOfFppfQuotient

/--
info: 'AlgebraicGeometry.Scheme.exists_map_eq_of_fppfQuotient' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms exists_map_eq_of_fppfQuotient

/--
info: 'AlgebraicGeometry.Scheme.hom_ext_of_fppfQuotient' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms hom_ext_of_fppfQuotient

/--
info: 'AlgebraicGeometry.Scheme.existsUnique_map_eq_of_fppfQuotient' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms existsUnique_map_eq_of_fppfQuotient

end AglibTest.FppfQuotient
