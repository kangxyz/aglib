/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Descent.FinitePresentation.Modules.Affine
public import Aglib.AlgebraicGeometry.Modules.InternalHom.Gluing
public import Aglib.AlgebraicGeometry.Modules.BaseChange.Affine.Mate
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.HigherDirectImage.Nonflat.HomLocality

/-!
# Actual finite-presentation module maps over cofiltered scheme limits

The comparisons use the original cone and native pullback composition. Both
module sheaves are already given at a stage; no object-descent family is an
input to these constructions.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- The native comparison for the original cone equation at an actual
transition into a prescribed stage. -/
def pullbackConeCompIso {I : Type u} [Category.{u} I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) {i j : I} (q : j ⟶ i) :
    pullback (c.π.app i) ≅ pullback (D.map q) ⋙ pullback (c.π.app j) :=
  pullbackCongr (c.w q).symm ≪≫ (pullbackComp (c.π.app j) (D.map q)).symm

/-- Naturally isomorphic functors detect the same equalities of actual arrows. -/
theorem map_eq_iff_natIso
    {A B : Type*} [Category A] [Category B] {F G : A ⥤ B}
    (e : F ≅ G) {M N : A} (f g : M ⟶ N) : F.map f = F.map g ↔ G.map f = G.map g := by
  constructor
  · intro h
    apply (cancel_epi (e.hom.app M)).mp
    rw [← e.hom.naturality f, ← e.hom.naturality g, h]
  · intro h
    apply (cancel_mono (e.hom.app N)).mp
    rw [e.hom.naturality f, e.hom.naturality g, h]

/-- Equality after a composite pullback is equality after the two actual pullbacks. -/
theorem pullback_map_eq_comp_iff {X Y Z : Scheme.{u}}
    (a : X ⟶ Y) (b : Y ⟶ Z) {M N : Z.Modules} (f g : M ⟶ N) :
    (pullback (a ≫ b)).map f = (pullback (a ≫ b)).map g ↔
      (pullback a).map ((pullback b).map f) = (pullback a).map ((pullback b).map g) :=
  map_eq_iff_natIso (pullbackComp a b).symm f g

/-- Transport an actual pullback equality along equality of the base morphisms. -/
theorem pullback_map_eq_of_eq {X Y : Scheme.{u}} {a b : X ⟶ Y}
    (h : a = b) {M N : Y.Modules} {f g : M ⟶ N}
    (e : (pullback a).map f = (pullback a).map g) :
    (pullback b).map f = (pullback b).map g :=
  (map_eq_iff_natIso (pullbackCongr h) f g).mp e

/-- An actual pullback equality persists after a further pullback. -/
theorem pullback_map_eq_of_comp {X Y Z : Scheme.{u}}
    (a : X ⟶ Y) (b : Y ⟶ Z) {M N : Z.Modules} {f g : M ⟶ N}
    (h : (pullback b).map f = (pullback b).map g) :
    (pullback (a ≫ b)).map f = (pullback (a ≫ b)).map g :=
  (pullback_map_eq_comp_iff a b f g).mpr (congrArg (fun k => (pullback a).map k) h)

private theorem pullback_map_injective_of_isIso {X Y : Scheme.{u}}
    (a : X ⟶ Y) [IsIso a] {M N : Y.Modules} {f g : M ⟶ N}
    (h : (pullback a).map f = (pullback a).map g) : f = g := by
  have h' := pullback_map_eq_of_comp (inv a) a h
  have h'' := pullback_map_eq_of_eq (IsIso.inv_hom_id a) h'
  exact (map_eq_iff_natIso (pullbackId Y) f g).mp h''

/-- Equality of two actual stage arrows is detected at a later stage of a
cofiltered diagram of affine schemes. The scheme-to-spectrum comparisons
use the original global-section maps and require no flatness. -/
theorem exists_affine_hom_equality_above_of_isLimit
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) [∀ i, IsAffine (D.obj i)]
    (c : Cone D) (hc : IsLimit c) (i : I)
    (M N : (D.obj i).Modules) [M.IsFinitePresentation] [N.IsFinitePresentation]
    (f g : M ⟶ N)
    (h : (pullback (c.π.app i)).map f = (pullback (c.π.app i)).map g) :
    ∃ (j : I) (q : j ⟶ i),
      (pullback (D.map q)).map f = (pullback (D.map q)).map g := by
  have : IsAffine c.pt := Scheme.isAffine_of_isLimit c hc
  have {j k : I} (q : j ⟶ k) : IsAffineHom (D.map q) := inferInstance
  have (j : I) : CompactSpace (D.obj j) := inferInstance
  have (j : I) : QuasiSeparatedSpace (D.obj j) := inferInstance
  let F := D.op ⋙ Scheme.Γ
  let cΓ := Scheme.Γ.mapCocone c.op
  have hcΓ : IsColimit cΓ := (nonempty_isColimit_Γ_mapCocone D c hc).some
  let A := pullback (D.obj i).isoSpec.inv
  let M' := A.obj M
  let N' := A.obj N
  let f' := A.map f
  let g' := A.map g
  have h' : (pullback (Spec.map (cΓ.ι.app (.op i)))).map f' =
      (pullback (Spec.map (cΓ.ι.app (.op i)))).map g' := by
    apply (pullback_map_eq_comp_iff _ _ f g).mp
    apply pullback_map_eq_of_eq
      (Scheme.isoSpec_inv_naturality (X := c.pt) (Y := D.obj i) (c.π.app i)).symm
    exact pullback_map_eq_of_comp c.pt.isoSpec.inv (c.π.app i) h
  obtain ⟨j, q, hq⟩ := exists_spec_hom_equality_above_of_isColimit F cΓ hcΓ
    (.op i) M' N' f' g' h'
  refine ⟨j.unop, q.unop, ?_⟩
  apply pullback_map_injective_of_isIso (D.obj j.unop).isoSpec.inv
  apply (pullback_map_eq_comp_iff _ _ f g).mp
  apply pullback_map_eq_of_eq (Scheme.isoSpec_inv_naturality (D.map q.unop))
  exact (pullback_map_eq_comp_iff _ _ f g).mpr hq

/-- Equality after the limit pullback is detected on an actual later
base change of any affine chart of the given stage. -/
theorem exists_hom_equality_on_affine_baseChanges
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u})
    [∀ {j k} (q : j ⟶ k), IsAffineHom (D.map q)]
    (c : Cone D) (hc : IsLimit c) (i : I)
    (M N : (D.obj i).Modules) [M.IsFinitePresentation] [N.IsFinitePresentation]
    (f g : M ⟶ N)
    (h : (pullback (c.π.app i)).map f = (pullback (c.π.app i)).map g)
    {U : Scheme.{u}} [IsAffine U] (a : U ⟶ D.obj i) :
    ∃ (j : I) (q : j ⟶ i),
      (pullback (Limits.pullback.fst (D.map q) a ≫ D.map q)).map f =
        (pullback (Limits.pullback.fst (D.map q) a ≫ D.map q)).map g := by
  let D' := Scheme.baseChangeDiagram D i a
  let c' := Scheme.baseChangeCone D c i a
  have hc' : IsLimit c' := Scheme.isLimitBaseChangeCone D c hc i a
  have (j : Over i) : IsAffine (D'.obj j) := by
    change IsAffine (Limits.pullback (D.map j.hom) a)
    exact isAffine_of_isAffineHom (Limits.pullback.snd (D.map j.hom) a)
  let o : Over i := Over.mk (𝟙 i)
  let p : D'.obj o ⟶ D.obj i := Limits.pullback.fst (D.map o.hom) a
  have hp : c'.π.app o ≫ p = Limits.pullback.fst (c.π.app i) a ≫ c.π.app i := by
    simp [c', p, o, Scheme.baseChangeCone, Scheme.baseChangeDiagram,
      Functor.comp_map, Over.forget_map, Over.pullback_map_left]
  have h' : (pullback (c'.π.app o)).map ((pullback p).map f) =
      (pullback (c'.π.app o)).map ((pullback p).map g) := by
    apply (pullback_map_eq_comp_iff _ _ f g).mp
    apply pullback_map_eq_of_eq hp.symm
    exact pullback_map_eq_of_comp (Limits.pullback.fst (c.π.app i) a) (c.π.app i) h
  obtain ⟨j, q, hq⟩ := exists_affine_hom_equality_above_of_isLimit D' c' hc' o
    ((pullback p).obj M) ((pullback p).obj N) ((pullback p).map f) ((pullback p).map g) h'
  have hleft : q.left = j.hom := by simpa [o] using Over.w q
  have hp' : D'.map q ≫ p = Limits.pullback.fst (D.map j.hom) a ≫ D.map j.hom := by
    simp [D', p, o, Scheme.baseChangeDiagram, Functor.comp_map,
      Over.forget_map, Over.pullback_map_left, hleft]
  exact ⟨j.left, j.hom, pullback_map_eq_of_eq hp'
    ((pullback_map_eq_comp_iff _ _ f g).mpr hq)⟩

/-- Equality of two actual finitely presented stage-module arrows descends
from the limit to one later stage of a quasi-compact scheme system with
affine transition maps. No quasi-separatedness is needed for this equality
statement. -/
theorem exists_hom_equality_above_of_isLimit
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u})
    [∀ {j k} (q : j ⟶ k), IsAffineHom (D.map q)]
    [∀ j, CompactSpace (D.obj j)]
    (c : Cone D) (hc : IsLimit c) (i : I)
    (M N : (D.obj i).Modules) [M.IsFinitePresentation] [N.IsFinitePresentation]
    (f g : M ⟶ N)
    (h : (pullback (c.π.app i)).map f = (pullback (c.π.app i)).map g) :
    ∃ (j : I) (q : j ⟶ i),
      (pullback (D.map q)).map f = (pullback (D.map q)).map g := by
  classical
  let 𝒰 := (D.obj i).affineCover.finiteSubcover
  have (a : 𝒰.I₀) : IsAffine (𝒰.X a) := inferInstanceAs
    (IsAffine ((D.obj i).affineCover.X ((D.obj i).affineCover.idx a.1)))
  choose j q hq using fun a : 𝒰.I₀ =>
    exists_hom_equality_on_affine_baseChanges D c hc i M N f g h (𝒰.f a)
  obtain ⟨k, q₀, v, hv⟩ := IsCofiltered.wideCospan q
  refine ⟨k, q₀, ?_⟩
  let 𝒱 : Scheme.OpenCover (D.obj k) := 𝒰.pullback₁ (D.map q₀)
  apply Nonflat.hom_ext_of_restrict_jointlySurjective 𝒱.X 𝒱.f (Scheme.Cover.exists_eq 𝒱)
  intro a
  apply (map_eq_iff_natIso (restrictFunctorIsoPullback (𝒱.f a)) _ _).mpr
  apply (pullback_map_eq_comp_iff _ _ f g).mp
  let r : Limits.pullback (D.map q₀) (𝒰.f a) ⟶
      Limits.pullback (D.map (q a)) (𝒰.f a) :=
    Limits.pullback.map _ _ _ _ (D.map (v a)) (𝟙 _) (𝟙 _)
      (by rw [Category.comp_id, ← D.map_comp, hv a]) (by simp)
  have hr : r ≫ (Limits.pullback.fst (D.map (q a)) (𝒰.f a) ≫ D.map (q a)) =
      Limits.pullback.fst (D.map q₀) (𝒰.f a) ≫ D.map q₀ := by
    dsimp only [r, Limits.pullback.map]
    rw [Limits.pullback.lift_fst_assoc, Category.assoc, ← D.map_comp, hv a]
  exact pullback_map_eq_of_eq hr
    (pullback_map_eq_of_comp r _ (hq a))

/-- Native composition through an actual commuting triangle. -/
def pullbackTriangleIso {X Y S : Scheme.{u}}
    (a : X ⟶ Y) (b : Y ⟶ S) (d : X ⟶ S) (h : a ≫ b = d) :
    pullback b ⋙ pullback a ≅ pullback d :=
  pullbackComp a b ≪≫ pullbackCongr h

private theorem pullbackConeCompIso_eq_triangle {I : Type u} [Category.{u} I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) {i j : I} (q : j ⟶ i) :
    pullbackConeCompIso D c q =
      (pullbackTriangleIso (c.π.app j) (D.map q) (c.π.app i) (c.w q)).symm := by
  rfl

/-- Pull an original map to a specified composite base morphism, using the
native triangle isomorphism on its source and target. -/
def pullbackHomOfTriangle {X Y S : Scheme.{u}}
    (a : X ⟶ Y) (b : Y ⟶ S) (d : X ⟶ S) (h : a ≫ b = d)
    {M N : S.Modules} (f : (pullback b).obj M ⟶ (pullback b).obj N) :
    (pullback d).obj M ⟶ (pullback d).obj N :=
  (pullbackTriangleIso a b d h).inv.app M ≫ (pullback a).map f ≫
    (pullbackTriangleIso a b d h).hom.app N

private theorem pullbackComp_assoc_hom
    {W X Y S : Scheme.{u}} (a : W ⟶ X) (b : X ⟶ Y) (d : Y ⟶ S)
    (M : S.Modules) :
    (pullback a).map ((pullbackComp b d).hom.app M) ≫
        (pullbackComp a (b ≫ d)).hom.app M =
      (pullbackComp a b).hom.app ((pullback d).obj M) ≫
        (pullbackComp (a ≫ b) d).hom.app M ≫
          (pullbackCongr (Category.assoc a b d)).hom.app M := by
  have H := congrArg (fun t => t.app M) (pseudofunctor_associativity a b d)
  change (pullbackComp a (b ≫ d)).inv.app M ≫
      (pullback a).map ((pullbackComp b d).inv.app M) ≫
      (pullbackComp a b).hom.app ((pullback d).obj M) ≫
      (pullbackComp (a ≫ b) d).hom.app M =
        (pullbackCongr (Category.assoc a b d)).inv.app M at H
  have H' := congrArg (fun t =>
    (pullback a).map ((pullbackComp b d).hom.app M) ≫
      (pullbackComp a (b ≫ d)).hom.app M ≫ t) H
  have H'' :
      (pullbackComp a b).hom.app ((pullback d).obj M) ≫
          (pullbackComp (a ≫ b) d).hom.app M =
        (pullback a).map ((pullbackComp b d).hom.app M) ≫
          (pullbackComp a (b ≫ d)).hom.app M ≫
            (pullbackCongr (Category.assoc a b d)).inv.app M := by
    simp only [Iso.hom_inv_id_app_assoc,
      ← Functor.map_comp_assoc, Iso.hom_inv_id_app] at H'
    simpa only [CategoryTheory.Functor.map_id, Category.id_comp] using H'
  apply (cancel_mono ((pullbackCongr (Category.assoc a b d)).inv.app M)).mp
  simpa only [Category.assoc, Iso.hom_inv_id_app, Category.comp_id] using H''.symm

/-- The actual triangle comparisons compose through native pullback associativity. -/
theorem pullbackTriangleIso_assoc_hom
    {W X Y S : Scheme.{u}} (a : X ⟶ Y) (b : W ⟶ X) (d : Y ⟶ S)
    (r : X ⟶ S) (hr : a ≫ d = r) (s : W ⟶ S) (hs : b ≫ r = s)
    (M : S.Modules) :
    (pullback b).map ((pullbackTriangleIso a d r hr).hom.app M) ≫
        (pullbackTriangleIso b r s hs).hom.app M =
      (pullbackComp b a).hom.app ((pullback d).obj M) ≫
        (pullbackTriangleIso (b ≫ a) d s
          (by rw [Category.assoc, hr, hs])).hom.app M := by
  subst r
  subst s
  simpa only [pullbackTriangleIso, Iso.trans_hom, NatTrans.comp_app,
    pullbackCongr, eqToIso_refl, Iso.refl_hom, NatTrans.id_app, Category.comp_id]
    using pullbackComp_assoc_hom b a d M

/-- Transporting an original arrow through two actual pullback triangles
agrees with transport through their composite triangle. -/
theorem pullbackHomOfTriangle_comp
    {W X Y S : Scheme.{u}} (a : X ⟶ Y) (b : W ⟶ X) (d : Y ⟶ S)
    (r : X ⟶ S) (hr : a ≫ d = r) (s : W ⟶ S) (hs : b ≫ r = s)
    {M N : S.Modules} (f : (pullback d).obj M ⟶ (pullback d).obj N) :
    pullbackHomOfTriangle b r s hs (pullbackHomOfTriangle a d r hr f) =
      pullbackHomOfTriangle (b ≫ a) d s (by rw [Category.assoc, hr, hs]) f := by
  let e := pullbackTriangleIso a d r hr
  let e' := pullbackTriangleIso b r s hs
  let e'' := pullbackTriangleIso (b ≫ a) d s (by rw [Category.assoc, hr, hs])
  let C := pullbackComp b a
  have hm : (pullback b).map (e.hom.app M) ≫ e'.hom.app M =
      C.hom.app ((pullback d).obj M) ≫ e''.hom.app M :=
    pullbackTriangleIso_assoc_hom a b d r hr s hs M
  have hn : (pullback b).map (e.hom.app N) ≫ e'.hom.app N =
      C.hom.app ((pullback d).obj N) ≫ e''.hom.app N :=
    pullbackTriangleIso_assoc_hom a b d r hr s hs N
  apply (cancel_epi ((pullback b).map (e.hom.app M) ≫ e'.hom.app M)).mp
  apply (cancel_mono (e''.inv.app N)).mp
  change (((pullback b).map (e.hom.app M) ≫ e'.hom.app M) ≫
      (e'.inv.app M ≫ (pullback b).map (e.inv.app M ≫ (pullback a).map f ≫ e.hom.app N) ≫
        e'.hom.app N)) ≫ e''.inv.app N =
    (((pullback b).map (e.hom.app M) ≫ e'.hom.app M) ≫
      (e''.inv.app M ≫ (pullback (b ≫ a)).map f ≫ e''.hom.app N)) ≫ e''.inv.app N
  simp only [Functor.map_comp, Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [← Functor.map_comp_assoc, e.hom_inv_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp]
  rw [← Category.assoc ((pullback b).map (e.hom.app N)), hn]
  rw [← Category.assoc ((pullback b).map (e.hom.app M)), hm]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc, Iso.hom_inv_id_app]
  exact C.hom.naturality f


private theorem pullbackTriangleIso_congr_left
    {X Y S : Scheme.{u}} {a b : X ⟶ Y} (h : a = b)
    (d : Y ⟶ S) (r : X ⟶ S) (ha : a ≫ d = r) (hb : b ≫ d = r)
    (M : S.Modules) :
    (pullbackCongr h).hom.app ((pullback d).obj M) ≫
        (pullbackTriangleIso b d r hb).hom.app M =
      (pullbackTriangleIso a d r ha).hom.app M := by
  subst b
  exact Category.id_comp _

/-- A commuting triangle of stage maps preserves the original coefficient
pullback comparison, component by component. -/
theorem pullbackTriangleIso_cone_hom
    {S X Y Z : Scheme.{u}} (a : X ⟶ Y) (b : Y ⟶ S) (u : Z ⟶ X)
    (v : Z ⟶ Y) (hu : u ≫ a = v) (t : X ⟶ S) (ha : a ≫ b = t)
    (l : Z ⟶ S) (hl : u ≫ t = l) (hv : v ≫ b = l) (M : S.Modules) :
    (pullbackTriangleIso u a v hu).inv.app ((pullback b).obj M) ≫
        (pullback u).map ((pullbackTriangleIso a b t ha).hom.app M) =
      (pullbackTriangleIso v b l hv).hom.app M ≫
        (pullbackTriangleIso u t l hl).inv.app M := by
  have H := pullbackTriangleIso_assoc_hom a u b t ha l hl M
  rw [← pullbackTriangleIso_congr_left hu b l (by rw [Category.assoc, ha, hl]) hv M] at H
  apply (cancel_mono ((pullbackTriangleIso u t l hl).hom.app M)).mp
  rw [Category.assoc, H]
  simp only [pullbackTriangleIso, Iso.trans_inv, Iso.trans_hom, NatTrans.comp_app,
    Category.assoc, Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app, Category.comp_id]

/-- Transport an actual lifted arrow through specified source, target and
limit isomorphisms, retaining its original recovery square. -/
theorem lift_conjugate_recovery
    {C D E : Type*} [Category C] [Category D] [Category E]
    (F₀ : C ⥤ E) (F₁ : C ⥤ D) (G : D ⥤ E) (U : F₀ ≅ F₁ ⋙ G)
    {P Q : C} {X Y : E} {P' Q' : D}
    (eP : F₀.obj P ≅ X) (eQ : F₀.obj Q ≅ Y)
    (sP : F₁.obj P ≅ P') (sQ : F₁.obj Q ≅ Q')
    (lP : G.obj P' ≅ X) (lQ : G.obj Q' ≅ Y)
    (hP : U.hom.app P ≫ G.map sP.hom = eP.hom ≫ lP.inv)
    (hQ : U.hom.app Q ≫ G.map sQ.hom = eQ.hom ≫ lQ.inv)
    (f : X ⟶ Y) (g : F₁.obj P ⟶ F₁.obj Q)
    (hg : U.hom.app P ≫ G.map g = (eP.hom ≫ f ≫ eQ.inv) ≫ U.hom.app Q) :
    lP.inv ≫ G.map (sP.inv ≫ g ≫ sQ.hom) = f ≫ lQ.inv := by
  have hc : G.map sP.hom ≫ G.map sP.inv = 𝟙 _ := by
    rw [← G.map_comp, sP.hom_inv_id]
    exact G.map_id _
  apply (cancel_epi eP.hom).mp
  rw [Functor.map_comp, Functor.map_comp]
  calc
    eP.hom ≫ (lP.inv ≫ (G.map sP.inv ≫ (G.map g ≫ G.map sQ.hom))) =
        (U.hom.app P ≫ G.map sP.hom) ≫ G.map sP.inv ≫ G.map g ≫ G.map sQ.hom := by
      rw [hP]
      simp only [Category.assoc]
    _ = (U.hom.app P ≫ G.map g) ≫ G.map sQ.hom := by
      simp only [Category.assoc, reassoc_of% hc]
    _ = (eP.hom ≫ f ≫ eQ.inv) ≫ (U.hom.app Q ≫ G.map sQ.hom) := by
      rw [hg]
      simp only [Category.assoc]
    _ = eP.hom ≫ (f ≫ lQ.inv) := by
      rw [hQ]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]

/-- Three actual commuting squares preserve the two original cone-triangle comparisons. -/
theorem pullbackSquareIso_cone_hom
    {X₀ X₁ X₂ S₀ S₁ S₂ : Scheme.{u}}
    (p : X₁ ⟶ X₀) (q : X₂ ⟶ X₁) (r : X₂ ⟶ X₀) (hr : q ≫ p = r)
    (φ : S₁ ⟶ S₀) (ψ : S₂ ⟶ S₁) (ρ : S₂ ⟶ S₀) (hρ : ψ ≫ φ = ρ)
    (a₀ : S₀ ⟶ X₀) (a₁ : S₁ ⟶ X₁) (a₂ : S₂ ⟶ X₂)
    (w₁ : φ ≫ a₀ = a₁ ≫ p) (w₂ : ψ ≫ a₁ = a₂ ≫ q) (w₀ : ρ ≫ a₀ = a₂ ≫ r)
    (M : X₀.Modules) :
    (pullbackTriangleIso ψ φ ρ hρ).inv.app ((pullback a₀).obj M) ≫
        (pullback ψ).map ((pullbackSquareIso a₁ φ p a₀ w₁.symm).hom.app M) ≫
        (pullbackSquareIso a₂ ψ q a₁ w₂.symm).hom.app ((pullback p).obj M) =
      (pullbackSquareIso a₂ ρ r a₀ w₀.symm).hom.app M ≫
        (pullback a₂).map ((pullbackTriangleIso q p r hr).inv.app M) := by
  subst r
  subst ρ
  let R := a₂ ≫ (q ≫ p)
  have hA : ψ ≫ (a₁ ≫ p) = R := by rw [← Category.assoc, w₂, Category.assoc]
  have hB : (ψ ≫ a₁) ≫ p = R := by rw [w₂, Category.assoc]
  let e₀ := pullbackTriangleIso (ψ ≫ φ) a₀ R w₀
  let e₁ := pullbackTriangleIso φ a₀ (a₁ ≫ p) w₁
  let e₂ := pullbackTriangleIso ψ a₁ (a₂ ≫ q) w₂
  let E₀ := pullbackComp a₂ (q ≫ p)
  let E₁ := pullbackComp a₁ p
  let E₂ := pullbackComp a₂ q
  let eA := pullbackTriangleIso ψ (a₁ ≫ p) R hA
  let eB := pullbackTriangleIso (a₂ ≫ q) p R (Category.assoc a₂ q p)
  have h₁ : (pullback ψ).map (e₁.hom.app M) ≫ eA.hom.app M =
      (pullbackComp ψ φ).hom.app ((pullback a₀).obj M) ≫ e₀.hom.app M :=
    pullbackTriangleIso_assoc_hom φ ψ a₀ (a₁ ≫ p) w₁ R hA M
  have h₂ : (pullback ψ).map (E₁.hom.app M) ≫ eA.hom.app M =
      e₂.hom.app ((pullback p).obj M) ≫ eB.hom.app M := by
    have H := pullbackTriangleIso_assoc_hom a₁ ψ p (a₁ ≫ p) rfl R hA M
    change (pullback ψ).map (E₁.hom.app M) ≫ eA.hom.app M =
      (pullbackComp ψ a₁).hom.app ((pullback p).obj M) ≫
        (pullbackTriangleIso (ψ ≫ a₁) p R hB).hom.app M at H
    rw [← pullbackTriangleIso_congr_left w₂ p R hB (Category.assoc a₂ q p) M] at H
    exact H
  have h₃ : (pullback a₂).map ((pullbackComp q p).hom.app M) ≫ E₀.hom.app M =
      E₂.hom.app ((pullback p).obj M) ≫ eB.hom.app M :=
    pullbackComp_assoc_hom a₂ q p M
  apply (cancel_epi ((pullbackComp ψ φ).hom.app ((pullback a₀).obj M))).mp
  apply (cancel_mono ((pullback a₂).map ((pullbackComp q p).hom.app M) ≫ E₀.hom.app M)).mp
  change ((pullbackComp ψ φ).hom.app ((pullback a₀).obj M) ≫
      ((pullbackComp ψ φ).inv.app ((pullback a₀).obj M) ≫
        (pullback ψ).map (e₁.hom.app M ≫ E₁.inv.app M) ≫
        (e₂.hom.app ((pullback p).obj M) ≫ E₂.inv.app ((pullback p).obj M)))) ≫
      ((pullback a₂).map ((pullbackComp q p).hom.app M) ≫ E₀.hom.app M) =
    ((pullbackComp ψ φ).hom.app ((pullback a₀).obj M) ≫
      (e₀.hom.app M ≫ E₀.inv.app M ≫
        (pullback a₂).map ((pullbackComp q p).inv.app M))) ≫
      ((pullback a₂).map ((pullbackComp q p).hom.app M) ≫ E₀.hom.app M)
  have hcancel : (pullback a₂).map ((pullbackComp q p).inv.app M) ≫
      (pullback a₂).map ((pullbackComp q p).hom.app M) = 𝟙 _ := by
    rw [← Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id]
  simp only [Functor.map_comp, Category.assoc, Iso.hom_inv_id_app_assoc, reassoc_of% hcancel,
    Iso.inv_hom_id_app]
  rw [h₃]
  simp only [Iso.inv_hom_id_app_assoc]
  rw [← h₂]
  have he₁ : (pullback ψ).map (E₁.inv.app M) ≫ (pullback ψ).map (E₁.hom.app M) = 𝟙 _ := by
    rw [← Functor.map_comp, E₁.inv_hom_id_app]
    exact (pullback ψ).map_id _
  simp only [reassoc_of% he₁]
  exact h₁

private theorem pullback_faithful_of_isIso {X Y : Scheme.{u}}
    (a : X ⟶ Y) [IsIso a] : (pullback a).Faithful where
  map_injective := pullback_map_injective_of_isIso a

private theorem pullback_full_of_isIso {X Y : Scheme.{u}}
    (a : X ⟶ Y) [IsIso a] : (pullback a).Full := by
  let : (pullback (inv a)).Faithful := pullback_faithful_of_isIso (inv a)
  let e : pullback a ⋙ pullback (inv a) ≅ 𝟭 Y.Modules :=
    pullbackComp (inv a) a ≪≫ pullbackCongr (IsIso.inv_hom_id a) ≪≫ pullbackId Y
  exact Functor.Full.of_comp_faithful_iso e

private theorem lift_from_comparison
    {C₀ C₁ C₂ D₀ D₁ D₂ : Type*}
    [Category C₀] [Category C₁] [Category C₂]
    [Category D₀] [Category D₁] [Category D₂]
    (A₀ : C₀ ⥤ D₀) (A₁ : C₁ ⥤ D₁) (A₂ : C₂ ⥤ D₂) [A₂.Faithful]
    (F₀ : C₀ ⥤ C₂) (F₁ : C₀ ⥤ C₁) (G : C₁ ⥤ C₂)
    (H₀ : D₀ ⥤ D₂) (H₁ : D₀ ⥤ D₁) (K : D₁ ⥤ D₂)
    (u : F₀ ≅ F₁ ⋙ G) (U : H₀ ≅ H₁ ⋙ K)
    (β₀ : A₀ ⋙ H₀ ≅ F₀ ⋙ A₂) (β₁ : A₀ ⋙ H₁ ≅ F₁ ⋙ A₁)
    (β₂ : A₁ ⋙ K ≅ G ⋙ A₂)
    (hcoh : ∀ P, U.hom.app (A₀.obj P) ≫ K.map (β₁.hom.app P) ≫
      β₂.hom.app (F₁.obj P) = β₀.hom.app P ≫ A₂.map (u.hom.app P))
    (P Q : C₀) (f : F₀.obj P ⟶ F₀.obj Q)
    (gS : H₁.obj (A₀.obj P) ⟶ H₁.obj (A₀.obj Q))
    (hgS : U.hom.app (A₀.obj P) ≫ K.map gS =
      (β₀.hom.app P ≫ A₂.map f ≫ β₀.inv.app Q) ≫ U.hom.app (A₀.obj Q))
    (g : F₁.obj P ⟶ F₁.obj Q)
    (hg : A₁.map g = β₁.inv.app P ≫ gS ≫ β₁.hom.app Q) :
    u.hom.app P ≫ G.map g = f ≫ u.hom.app Q := by
  apply A₂.map_injective
  rw [Functor.map_comp, Functor.map_comp]
  apply (cancel_epi (β₀.hom.app P)).mp
  have hn : K.map (A₁.map g) ≫ β₂.hom.app (F₁.obj Q) =
      β₂.hom.app (F₁.obj P) ≫ A₂.map (G.map g) := β₂.hom.naturality g
  have hcancel : K.map (β₁.hom.app P) ≫ K.map (β₁.inv.app P) = 𝟙 _ := by
    rw [← K.map_comp, β₁.hom_inv_id_app]
    exact K.map_id _
  calc
    β₀.hom.app P ≫ (A₂.map (u.hom.app P) ≫ A₂.map (G.map g)) =
        (U.hom.app (A₀.obj P) ≫ K.map (β₁.hom.app P) ≫
          β₂.hom.app (F₁.obj P)) ≫ A₂.map (G.map g) := by
      rw [hcoh]
      simp only [Category.assoc]
    _ = U.hom.app (A₀.obj P) ≫ K.map (β₁.hom.app P) ≫
        K.map (A₁.map g) ≫ β₂.hom.app (F₁.obj Q) := by
      rw [Category.assoc, Category.assoc, ← hn]
    _ = U.hom.app (A₀.obj P) ≫ K.map gS ≫
        K.map (β₁.hom.app Q) ≫ β₂.hom.app (F₁.obj Q) := by
      rw [hg, Functor.map_comp, Functor.map_comp]
      simp only [Category.assoc, reassoc_of% hcancel]
    _ = (β₀.hom.app P ≫ A₂.map f ≫ β₀.inv.app Q) ≫
        (U.hom.app (A₀.obj Q) ≫ K.map (β₁.hom.app Q) ≫ β₂.hom.app (F₁.obj Q)) := by
      rw [← Category.assoc (U.hom.app (A₀.obj P)), hgS]
      simp only [Category.assoc]
    _ = β₀.hom.app P ≫ (A₂.map f ≫ A₂.map (u.hom.app Q)) := by
      rw [hcoh]
      simp only [Category.assoc, Iso.inv_hom_id_app_assoc]

private theorem exists_lift_from_comparison
    {C₀ C₁ C₂ D₀ D₁ D₂ : Type*}
    [Category C₀] [Category C₁] [Category C₂]
    [Category D₀] [Category D₁] [Category D₂]
    (A₀ : C₀ ⥤ D₀) (A₁ : C₁ ⥤ D₁) (A₂ : C₂ ⥤ D₂)
    (hfull : A₁.Full) (hfaithful : A₂.Faithful)
    (F₀ : C₀ ⥤ C₂) (F₁ : C₀ ⥤ C₁) (G : C₁ ⥤ C₂)
    (H₀ : D₀ ⥤ D₂) (H₁ : D₀ ⥤ D₁) (K : D₁ ⥤ D₂)
    (u : F₀ ≅ F₁ ⋙ G) (U : H₀ ≅ H₁ ⋙ K)
    (β₀ : A₀ ⋙ H₀ ≅ F₀ ⋙ A₂) (β₁ : A₀ ⋙ H₁ ≅ F₁ ⋙ A₁)
    (β₂ : A₁ ⋙ K ≅ G ⋙ A₂)
    (hcoh : ∀ P, U.hom.app (A₀.obj P) ≫ K.map (β₁.hom.app P) ≫
      β₂.hom.app (F₁.obj P) = β₀.hom.app P ≫ A₂.map (u.hom.app P))
    (P Q : C₀) (f : F₀.obj P ⟶ F₀.obj Q)
    (gS : H₁.obj (A₀.obj P) ⟶ H₁.obj (A₀.obj Q))
    (hgS : U.hom.app (A₀.obj P) ≫ K.map gS =
      (β₀.hom.app P ≫ A₂.map f ≫ β₀.inv.app Q) ≫ U.hom.app (A₀.obj Q)) :
    ∃ g : F₁.obj P ⟶ F₁.obj Q,
      u.hom.app P ≫ G.map g = f ≫ u.hom.app Q := by
  let : A₁.Full := hfull
  let : A₂.Faithful := hfaithful
  obtain ⟨g, hg⟩ := A₁.map_surjective (β₁.inv.app P ≫ gS ≫ β₁.hom.app Q)
  exact ⟨g, lift_from_comparison A₀ A₁ A₂ F₀ F₁ G H₀ H₁ K u U β₀ β₁ β₂ hcoh
    P Q f gS hgS g hg⟩

private theorem specPullbackCompOfEq_eq_triangle
    {R S T : CommRingCat.{u}} (φ : R ⟶ S) (ψ : S ⟶ T) (ρ : R ⟶ T)
    (h : φ ≫ ψ = ρ) :
    specPullbackCompOfEq φ ψ ρ h =
      (pullbackTriangleIso (Spec.map ψ) (Spec.map φ) (Spec.map ρ)
        (by rw [← Spec.map_comp, h])).symm := by
  subst ρ
  apply Iso.ext
  simp only [specPullbackCompOfEq, pullbackTriangleIso, Iso.trans_hom,
    Iso.symm_hom, Iso.trans_inv, eqToIso_refl, Iso.refl_hom, Category.id_comp]
  rfl

private def homInSpectralCoordinates
    {X Y : Scheme.{u}} {R S : CommRingCat.{u}}
    (r : X ⟶ Y) (ρ : R ⟶ S) (a₀ : Spec R ⟶ Y) (a₁ : Spec S ⟶ X)
    (w : Spec.map ρ ≫ a₀ = a₁ ≫ r) {M N : Y.Modules}
    (f : (pullback r).obj M ⟶ (pullback r).obj N) :
    (pullback (Spec.map ρ)).obj ((pullback a₀).obj M) ⟶
      (pullback (Spec.map ρ)).obj ((pullback a₀).obj N) :=
  (pullbackSquareIso a₁ (Spec.map ρ) r a₀ w.symm).hom.app M ≫ (pullback a₁).map f ≫
    (pullbackSquareIso a₁ (Spec.map ρ) r a₀ w.symm).inv.app N

private theorem pullbackSquareIso_spec_cone_hom
    {X₀ X₁ X₂ : Scheme.{u}} {R₀ R₁ R₂ : CommRingCat.{u}}
    (p : X₁ ⟶ X₀) (q : X₂ ⟶ X₁) (r : X₂ ⟶ X₀) (hr : q ≫ p = r)
    (φ : R₀ ⟶ R₁) (ψ : R₁ ⟶ R₂) (ρ : R₀ ⟶ R₂) (hρ : φ ≫ ψ = ρ)
    (a₀ : Spec R₀ ⟶ X₀) (a₁ : Spec R₁ ⟶ X₁) (a₂ : Spec R₂ ⟶ X₂)
    (w₁ : Spec.map φ ≫ a₀ = a₁ ≫ p) (w₂ : Spec.map ψ ≫ a₁ = a₂ ≫ q)
    (w₀ : Spec.map ρ ≫ a₀ = a₂ ≫ r) (M : X₀.Modules) :
    (specPullbackCompOfEq φ ψ ρ hρ).hom.app ((pullback a₀).obj M) ≫
        (pullback (Spec.map ψ)).map ((pullbackSquareIso a₁ (Spec.map φ) p a₀ w₁.symm).hom.app M) ≫
        (pullbackSquareIso a₂ (Spec.map ψ) q a₁ w₂.symm).hom.app ((pullback p).obj M) =
      (pullbackSquareIso a₂ (Spec.map ρ) r a₀ w₀.symm).hom.app M ≫
        (pullback a₂).map ((pullbackTriangleIso q p r hr).inv.app M) := by
  rw [specPullbackCompOfEq_eq_triangle]
  exact pullbackSquareIso_cone_hom p q r hr (Spec.map φ) (Spec.map ψ) (Spec.map ρ)
    (by rw [← Spec.map_comp, hρ]) a₀ a₁ a₂ w₁ w₂ w₀ M

private theorem hom_lift_from_spectral_coordinates
    {X₀ X₁ X₂ : Scheme.{u}} {R₀ R₁ R₂ : CommRingCat.{u}}
    (p : X₁ ⟶ X₀) (q : X₂ ⟶ X₁) (r : X₂ ⟶ X₀) (hr : q ≫ p = r)
    (φ : R₀ ⟶ R₁) (ψ : R₁ ⟶ R₂) (ρ : R₀ ⟶ R₂) (hρ : φ ≫ ψ = ρ)
    (a₀ : Spec R₀ ⟶ X₀) (a₁ : Spec R₁ ⟶ X₁) (a₂ : Spec R₂ ⟶ X₂)
    [IsIso a₁] [IsIso a₂]
    (w₁ : Spec.map φ ≫ a₀ = a₁ ≫ p) (w₂ : Spec.map ψ ≫ a₁ = a₂ ≫ q)
    (w₀ : Spec.map ρ ≫ a₀ = a₂ ≫ r)
    (M N : X₀.Modules) (f : (pullback r).obj M ⟶ (pullback r).obj N)
    (gS : (pullback (Spec.map φ)).obj ((pullback a₀).obj M) ⟶
      (pullback (Spec.map φ)).obj ((pullback a₀).obj N))
    (hgS : (specPullbackCompOfEq φ ψ ρ hρ).hom.app ((pullback a₀).obj M) ≫
          (pullback (Spec.map ψ)).map gS =
        homInSpectralCoordinates r ρ a₀ a₂ w₀ f ≫
          (specPullbackCompOfEq φ ψ ρ hρ).hom.app ((pullback a₀).obj N)) :
    ∃ g : (pullback p).obj M ⟶ (pullback p).obj N,
      (pullbackTriangleIso q p r hr).inv.app M ≫ (pullback q).map g =
        f ≫ (pullbackTriangleIso q p r hr).inv.app N := by
  exact exists_lift_from_comparison (pullback a₀) (pullback a₁) (pullback a₂)
    (pullback_full_of_isIso a₁) (pullback_faithful_of_isIso a₂)
    (pullback r) (pullback p) (pullback q)
    (pullback (Spec.map ρ)) (pullback (Spec.map φ)) (pullback (Spec.map ψ))
    (pullbackTriangleIso q p r hr).symm (specPullbackCompOfEq φ ψ ρ hρ)
    (pullbackSquareIso a₂ (Spec.map ρ) r a₀ w₀.symm)
    (pullbackSquareIso a₁ (Spec.map φ) p a₀ w₁.symm)
    (pullbackSquareIso a₂ (Spec.map ψ) q a₁ w₂.symm)
    (pullbackSquareIso_spec_cone_hom p q r hr φ ψ ρ hρ a₀ a₁ a₂ w₁ w₂ w₀)
    M N f gS hgS

private theorem exists_hom_in_spectral_coordinates
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (i : I)
    (F : Iᵒᵖ ⥤ CommRingCat.{u}) (cF : Cocone F) (hcF : IsColimit cF)
    (a : ∀ j, Spec (F.obj (.op j)) ≅ D.obj j) (aLimit : Spec cF.pt ≅ c.pt)
    (hD : ∀ {j k} (q : j ⟶ k),
      Spec.map (F.map q.op) ≫ (a k).hom = (a j).hom ≫ D.map q)
    (hC : ∀ j, Spec.map (cF.ι.app (.op j)) ≫ (a j).hom = aLimit.hom ≫ c.π.app j)
    (M N : (D.obj i).Modules) [M.IsFinitePresentation] [N.IsFinitePresentation]
    (f : (pullback (c.π.app i)).obj M ⟶ (pullback (c.π.app i)).obj N) :
    ∃ (j : I) (q : j ⟶ i)
      (g : (pullback (D.map q)).obj M ⟶ (pullback (D.map q)).obj N),
      (pullbackConeCompIso D c q).hom.app M ≫ (pullback (c.π.app j)).map g =
        f ≫ (pullbackConeCompIso D c q).hom.app N := by
  let fS := homInSpectralCoordinates (c.π.app i) (cF.ι.app (.op i))
    (a i).hom aLimit.hom (hC i) f
  obtain ⟨j, q, gS, hgS⟩ := exists_spec_hom_above_of_isColimit F cF hcF (.op i)
    ((pullback (a i).hom).obj M) ((pullback (a i).hom).obj N) fS
  obtain ⟨g, hg⟩ := hom_lift_from_spectral_coordinates
    (X₀ := D.obj i) (X₁ := D.obj j.unop) (X₂ := c.pt)
    (D.map q.unop) (c.π.app j.unop) (c.π.app i) (c.w q.unop)
    (F.map q) (cF.ι.app j) (cF.ι.app (.op i)) (cF.w q)
    (a i).hom (a j.unop).hom aLimit.hom (hD q.unop) (hC j.unop) (hC i) M N f gS hgS
  refine ⟨j.unop, q.unop, g, ?_⟩
  simpa only [pullbackConeCompIso_eq_triangle, Iso.symm_hom] using hg

private theorem exists_affine_limit_coordinates
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) [∀ i, IsAffine (D.obj i)]
    (c : Cone D) (hc : IsLimit c) :
    ∃ (F : Iᵒᵖ ⥤ CommRingCat.{u}) (cF : Cocone F) (_ : IsColimit cF)
      (a : ∀ j, Spec (F.obj (.op j)) ≅ D.obj j) (aLimit : Spec cF.pt ≅ c.pt),
      (∀ {j k} (q : j ⟶ k),
        Spec.map (F.map q.op) ≫ (a k).hom = (a j).hom ≫ D.map q) ∧
      ∀ j, Spec.map (cF.ι.app (.op j)) ≫ (a j).hom = aLimit.hom ≫ c.π.app j := by
  have : IsAffine c.pt := Scheme.isAffine_of_isLimit c hc
  have {j k : I} (q : j ⟶ k) : IsAffineHom (D.map q) := inferInstance
  have (j : I) : CompactSpace (D.obj j) := inferInstance
  have (j : I) : QuasiSeparatedSpace (D.obj j) := inferInstance
  refine ⟨D.op ⋙ Scheme.Γ, Scheme.Γ.mapCocone c.op,
    (nonempty_isColimit_Γ_mapCocone D c hc).some,
    fun j => (D.obj j).isoSpec.symm, c.pt.isoSpec.symm, ?_, ?_⟩
  · intro j k q
    exact Scheme.isoSpec_inv_naturality (X := D.obj j) (Y := D.obj k) (D.map q)
  · intro j
    exact Scheme.isoSpec_inv_naturality (X := c.pt) (Y := D.obj j) (c.π.app j)

/-- An actual map between limit pullbacks of two given finitely presented
module sheaves on an affine stage descends to a later affine stage. The
recovery equation uses the original cone and its native comparison. -/
theorem exists_affine_hom_above_of_isLimit
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) [∀ i, IsAffine (D.obj i)]
    (c : Cone D) (hc : IsLimit c) (i : I)
    (M N : (D.obj i).Modules) [M.IsFinitePresentation] [N.IsFinitePresentation]
    (f : (pullback (c.π.app i)).obj M ⟶ (pullback (c.π.app i)).obj N) :
    ∃ (j : I) (q : j ⟶ i)
      (g : (pullback (D.map q)).obj M ⟶ (pullback (D.map q)).obj N),
      (pullbackConeCompIso D c q).hom.app M ≫ (pullback (c.π.app j)).map g =
        f ≫ (pullbackConeCompIso D c q).hom.app N := by
  obtain ⟨F, cF, hcF, a, aLimit, hD, hC⟩ := exists_affine_limit_coordinates D c hc
  exact exists_hom_in_spectral_coordinates D c i F cF hcF a aLimit hD hC M N f

private theorem pullbackHomOfTriangle_eq_iff
    {X Y S : Scheme.{u}} (a : X ⟶ Y) (b : Y ⟶ S) (d : X ⟶ S) (h : a ≫ b = d)
    {M N : S.Modules} (g : (pullback b).obj M ⟶ (pullback b).obj N)
    (f : (pullback d).obj M ⟶ (pullback d).obj N) :
    pullbackHomOfTriangle a b d h g = f ↔
      (pullbackTriangleIso a b d h).inv.app M ≫ (pullback a).map g =
        f ≫ (pullbackTriangleIso a b d h).inv.app N := by
  constructor
  · intro H
    apply (cancel_mono ((pullbackTriangleIso a b d h).hom.app N)).mp
    simpa only [pullbackHomOfTriangle, Category.assoc, Iso.inv_hom_id_app, Category.comp_id] using H
  · intro H
    dsimp only [pullbackHomOfTriangle]
    rw [← Category.assoc, H]
    simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]

/-- Affine Hom descent with two original fp coefficient sheaves on one
fixed base. The output arrows live over the actual structural maps, and
recover through the original limit triangles. -/
theorem exists_relative_affine_hom_above_of_isLimit
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) [∀ i, IsAffine (D.obj i)]
    (c : Cone D) (hc : IsLimit c) {S : Scheme.{u}}
    (t : D ⟶ (Functor.const I).obj S) (l : c.pt ⟶ S)
    (hl : ∀ i, c.π.app i ≫ t.app i = l) (i : I)
    (M N : S.Modules) [M.IsFinitePresentation] [N.IsFinitePresentation]
    (f : (pullback l).obj M ⟶ (pullback l).obj N) :
    ∃ (j : I) (_ : j ⟶ i)
      (g : (pullback (t.app j)).obj M ⟶ (pullback (t.app j)).obj N),
      pullbackHomOfTriangle (c.π.app j) (t.app j) l (hl j) g = f := by
  let eᵢ := pullbackTriangleIso (c.π.app i) (t.app i) l (hl i)
  let fᵢ := eᵢ.hom.app M ≫ f ≫ eᵢ.inv.app N
  obtain ⟨j, q, g₀, hg₀⟩ := exists_affine_hom_above_of_isLimit D c hc i
    ((pullback (t.app i)).obj M) ((pullback (t.app i)).obj N) fᵢ
  have hq : D.map q ≫ t.app i = t.app j :=
    (t.naturality q).trans (Category.comp_id _)
  let eⱼ := pullbackTriangleIso (D.map q) (t.app i) (t.app j) hq
  let eₗ := pullbackTriangleIso (c.π.app j) (t.app j) l (hl j)
  let g := eⱼ.inv.app M ≫ g₀ ≫ eⱼ.hom.app N
  refine ⟨j, q, g, (pullbackHomOfTriangle_eq_iff _ _ _ _ _ _).mpr ?_⟩
  let U := pullbackConeCompIso D c q
  have hcoh (P : S.Modules) :
      U.hom.app ((pullback (t.app i)).obj P) ≫
          (pullback (c.π.app j)).map (eⱼ.hom.app P) =
        eᵢ.hom.app P ≫ eₗ.inv.app P :=
    pullbackTriangleIso_cone_hom (D.map q) (t.app i) (c.π.app j)
      (c.π.app i) (c.w q) (t.app j) hq l (hl j) (hl i) P
  exact lift_conjugate_recovery (pullback (c.π.app i)) (pullback (D.map q))
    (pullback (c.π.app j)) U (eᵢ.app M) (eᵢ.app N) (eⱼ.app M) (eⱼ.app N)
    (eₗ.app M) (eₗ.app N) (hcoh M) (hcoh N) f g₀ hg₀

private def chartStructure {I : Type u} [Category.{u} I]
    (D : I ⥤ Scheme.{u}) (i : I) {X : Scheme.{u}} (f : X ⟶ D.obj i) :
    Scheme.baseChangeDiagram D i f ⟶ (Functor.const (Over i)).obj (D.obj i) where
  app j := Limits.pullback.snd (D.map j.hom) f ≫ f
  naturality {j k} q := by
    simp [Scheme.baseChangeDiagram, Functor.comp_map, Over.forget_map,
      Over.pullback_map_left]

private def chartLimitStructure {I : Type u} [Category.{u} I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (i : I) {X : Scheme.{u}} (f : X ⟶ D.obj i) :
    (Scheme.baseChangeCone D c i f).pt ⟶ D.obj i :=
  Limits.pullback.snd (c.π.app i) f ≫ f

private theorem chartLimitStructure_w {I : Type u} [Category.{u} I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (i : I) {X : Scheme.{u}} (f : X ⟶ D.obj i)
    (j : Over i) :
    (Scheme.baseChangeCone D c i f).π.app j ≫ (chartStructure D i f).app j =
      chartLimitStructure D c i f := by
  simp [chartStructure, chartLimitStructure, Scheme.baseChangeCone, Scheme.baseChangeDiagram,
    Functor.comp_map, Over.forget_map, Over.pullback_map_left]

private theorem chartStructure_w {I : Type u} [Category.{u} I]
    (D : I ⥤ Scheme.{u}) (i : I) {X : Scheme.{u}} (f : X ⟶ D.obj i)
    {j k : Over i} (q : j ⟶ k) :
    (Scheme.baseChangeDiagram D i f).map q ≫ (chartStructure D i f).app k =
      (chartStructure D i f).app j := by
  exact ((chartStructure D i f).naturality q).trans (Category.comp_id _)

private def chartLimitHom {I : Type u} [Category.{u} I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (i : I)
    {M N : (D.obj i).Modules}
    (a : (pullback (c.π.app i)).obj M ⟶ (pullback (c.π.app i)).obj N)
    {X : Scheme.{u}} (f : X ⟶ D.obj i) :
    (pullback (chartLimitStructure D c i f)).obj M ⟶
      (pullback (chartLimitStructure D c i f)).obj N :=
  pullbackHomOfTriangle (Limits.pullback.fst (c.π.app i) f) (c.π.app i)
    (chartLimitStructure D c i f) Limits.pullback.condition a

/-- A finite family of actual affine-chart restrictions of one original
limit arrow has actual lifts at one common stage of the original diagram.
Every lift retains its original limit recovery equation. -/
private theorem exists_common_affine_chart_homs
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u})
    [∀ {j k} (q : j ⟶ k), IsAffineHom (D.map q)]
    (c : Cone D) (hc : IsLimit c) (i : I)
    {A : Type u} [Finite A] (X : A → Scheme.{u}) [∀ a, IsAffine (X a)]
    (f : ∀ a, X a ⟶ D.obj i)
    (M N : (D.obj i).Modules) [M.IsFinitePresentation] [N.IsFinitePresentation]
    (a : (pullback (c.π.app i)).obj M ⟶ (pullback (c.π.app i)).obj N) :
    ∃ (j : Over i) (g : ∀ x : A,
      (pullback ((chartStructure D i (f x)).app j)).obj M ⟶
        (pullback ((chartStructure D i (f x)).app j)).obj N),
      ∀ x, pullbackHomOfTriangle ((Scheme.baseChangeCone D c i (f x)).π.app j)
          ((chartStructure D i (f x)).app j) (chartLimitStructure D c i (f x))
          (chartLimitStructure_w D c i (f x) j) (g x) = chartLimitHom D c i a (f x) := by
  classical
  let : Fintype A := Fintype.ofFinite A
  have (x : A) (j : Over i) : IsAffine ((Scheme.baseChangeDiagram D i (f x)).obj j) := by
    change IsAffine (Limits.pullback (D.map j.hom) (f x))
    exact isAffine_of_isAffineHom (Limits.pullback.snd (D.map j.hom) (f x))
  choose j q g hg using fun x : A => exists_relative_affine_hom_above_of_isLimit
    (Scheme.baseChangeDiagram D i (f x)) (Scheme.baseChangeCone D c i (f x))
    (Scheme.isLimitBaseChangeCone D c hc i (f x))
    (chartStructure D i (f x)) (chartLimitStructure D c i (f x))
    (chartLimitStructure_w D c i (f x)) (Over.mk (𝟙 i)) M N (chartLimitHom D c i a (f x))
  obtain ⟨k, hk⟩ := IsCofiltered.inf_objs_exists (Finset.univ.image j)
  let v (x : A) : k ⟶ j x := (hk (Finset.mem_image.mpr ⟨x, by simp, rfl⟩)).some
  refine ⟨k, fun x => pullbackHomOfTriangle
    ((Scheme.baseChangeDiagram D i (f x)).map (v x))
    ((chartStructure D i (f x)).app (j x)) ((chartStructure D i (f x)).app k)
    (chartStructure_w D i (f x) (v x)) (g x), fun x => ?_⟩
  rw [pullbackHomOfTriangle_comp]
  simpa only [(Scheme.baseChangeCone D c i (f x)).w (v x)] using hg x

private def chartMap {S T X Y : Scheme.{u}}
    (t : T ⟶ S) (f : X ⟶ S) (g : Y ⟶ S) (a : X ⟶ Y) (ha : a ≫ g = f) :
    Limits.pullback t f ⟶ Limits.pullback t g :=
  Limits.pullback.map t f t g (𝟙 _) a (𝟙 _) (by simp) (by simpa using ha.symm)

private theorem chartMap_fst {S T X Y : Scheme.{u}}
    (t : T ⟶ S) (f : X ⟶ S) (g : Y ⟶ S) (a : X ⟶ Y) (ha : a ≫ g = f) :
    chartMap t f g a ha ≫ Limits.pullback.fst t g = Limits.pullback.fst t f := by
  simp [chartMap]

private theorem chartMap_snd {S T X Y : Scheme.{u}}
    (t : T ⟶ S) (f : X ⟶ S) (g : Y ⟶ S) (a : X ⟶ Y) (ha : a ≫ g = f) :
    chartMap t f g a ha ≫ Limits.pullback.snd t g = Limits.pullback.snd t f ≫ a := by
  simp [chartMap]

private theorem chartMap_structure {I : Type u} [Category.{u} I]
    (D : I ⥤ Scheme.{u}) (i : I) {X Y : Scheme.{u}}
    (f : X ⟶ D.obj i) (g : Y ⟶ D.obj i) (a : X ⟶ Y) (ha : a ≫ g = f)
    (j : Over i) :
    chartMap (D.map j.hom) f g a ha ≫ (chartStructure D i g).app j =
      (chartStructure D i f).app j := by
  simp [chartMap, chartStructure, Category.assoc, ha]

private theorem chartMap_limit_structure {I : Type u} [Category.{u} I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (i : I) {X Y : Scheme.{u}}
    (f : X ⟶ D.obj i) (g : Y ⟶ D.obj i) (a : X ⟶ Y) (ha : a ≫ g = f) :
    chartMap (c.π.app i) f g a ha ≫ chartLimitStructure D c i g =
      chartLimitStructure D c i f := by
  simp [chartMap, chartLimitStructure, Category.assoc, ha]

private theorem chartMap_cone {I : Type u} [Category.{u} I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (i : I) {X Y : Scheme.{u}}
    (f : X ⟶ D.obj i) (g : Y ⟶ D.obj i) (a : X ⟶ Y) (ha : a ≫ g = f)
    (j : Over i) :
    (Scheme.baseChangeCone D c i f).π.app j ≫ chartMap (D.map j.hom) f g a ha =
      chartMap (c.π.app i) f g a ha ≫ (Scheme.baseChangeCone D c i g).π.app j := by
  apply Limits.pullback.hom_ext <;>
    simp [chartMap, Scheme.baseChangeCone, Scheme.baseChangeDiagram,
      Functor.comp_map, Over.forget_map, Over.pullback_map_left, Category.assoc]

private theorem chartMap_transition {I : Type u} [Category.{u} I]
    (D : I ⥤ Scheme.{u}) (i : I) {X Y : Scheme.{u}}
    (f : X ⟶ D.obj i) (g : Y ⟶ D.obj i) (a : X ⟶ Y) (ha : a ≫ g = f)
    {j k : Over i} (q : j ⟶ k) :
    (Scheme.baseChangeDiagram D i f).map q ≫ chartMap (D.map k.hom) f g a ha =
      chartMap (D.map j.hom) f g a ha ≫ (Scheme.baseChangeDiagram D i g).map q := by
  apply Limits.pullback.hom_ext <;>
    simp [chartMap, Scheme.baseChangeDiagram, Functor.comp_map,
      Over.forget_map, Over.pullback_map_left, Category.assoc]

private theorem pullbackHomOfTriangle_map_inj_iff
    {X Y S : Scheme.{u}} (a : X ⟶ Y) (b : Y ⟶ S) (d : X ⟶ S) (h : a ≫ b = d)
    {M N : S.Modules} (f g : (pullback b).obj M ⟶ (pullback b).obj N) :
    pullbackHomOfTriangle a b d h f = pullbackHomOfTriangle a b d h g ↔
      (pullback a).map f = (pullback a).map g := by
  simp only [pullbackHomOfTriangle, ← Category.assoc, cancel_mono, cancel_epi]

private theorem chartHom_recovery_of_map
    {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u}) (c : Cone D) (i : I)
    {M N : (D.obj i).Modules}
    (F : (pullback (c.π.app i)).obj M ⟶ (pullback (c.π.app i)).obj N)
    {X Y : Scheme.{u}} (f : X ⟶ D.obj i) (g : Y ⟶ D.obj i)
    (a : X ⟶ Y) (ha : a ≫ g = f) (j : Over i)
    (G : (pullback ((chartStructure D i g).app j)).obj M ⟶
      (pullback ((chartStructure D i g).app j)).obj N)
    (hG : pullbackHomOfTriangle ((Scheme.baseChangeCone D c i g).π.app j)
        ((chartStructure D i g).app j) (chartLimitStructure D c i g)
        (chartLimitStructure_w D c i g j) G = chartLimitHom D c i F g) :
    pullbackHomOfTriangle ((Scheme.baseChangeCone D c i f).π.app j)
        ((chartStructure D i f).app j) (chartLimitStructure D c i f)
        (chartLimitStructure_w D c i f j)
        (pullbackHomOfTriangle (chartMap (D.map j.hom) f g a ha)
          ((chartStructure D i g).app j) ((chartStructure D i f).app j)
          (chartMap_structure D i f g a ha j) G) = chartLimitHom D c i F f := by
  rw [pullbackHomOfTriangle_comp]
  simp only [chartMap_cone]
  rw [← pullbackHomOfTriangle_comp ((Scheme.baseChangeCone D c i g).π.app j)
    (chartMap (c.π.app i) f g a ha) ((chartStructure D i g).app j)
    (chartLimitStructure D c i g) (chartLimitStructure_w D c i g j)
    (chartLimitStructure D c i f) (chartMap_limit_structure D c i f g a ha)]
  rw [hG]
  dsimp only [chartLimitHom]
  simp only [pullbackHomOfTriangle_comp, chartMap_fst]

private theorem chartHom_map_transition
    {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u}) (i : I)
    {M N : (D.obj i).Modules} {X Y : Scheme.{u}}
    (f : X ⟶ D.obj i) (g : Y ⟶ D.obj i) (a : X ⟶ Y) (ha : a ≫ g = f)
    {j k : Over i} (q : j ⟶ k)
    (G : (pullback ((chartStructure D i g).app k)).obj M ⟶
      (pullback ((chartStructure D i g).app k)).obj N) :
    pullbackHomOfTriangle ((Scheme.baseChangeDiagram D i f).map q)
      ((chartStructure D i f).app k) ((chartStructure D i f).app j)
      (chartStructure_w D i f q)
      (pullbackHomOfTriangle (chartMap (D.map k.hom) f g a ha)
        ((chartStructure D i g).app k) ((chartStructure D i f).app k)
        (chartMap_structure D i f g a ha k) G) =
    pullbackHomOfTriangle (chartMap (D.map j.hom) f g a ha)
      ((chartStructure D i g).app j) ((chartStructure D i f).app j)
      (chartMap_structure D i f g a ha j)
      (pullbackHomOfTriangle ((Scheme.baseChangeDiagram D i g).map q)
        ((chartStructure D i g).app k) ((chartStructure D i g).app j)
        (chartStructure_w D i g q) G) := by
  simp only [pullbackHomOfTriangle_comp, chartMap_transition]


private theorem exists_compatible_chart_homs
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u})
    [∀ {j k} (q : j ⟶ k), IsAffineHom (D.map q)]
    [∀ j, CompactSpace (D.obj j)]
    (c : Cone D) (hc : IsLimit c) (i : I) [QuasiSeparatedSpace (D.obj i)]
    {A : Type u} [Finite A] (X : A → Scheme.{u}) [∀ a, IsAffine (X a)]
    (f : ∀ a, X a ⟶ D.obj i)
    (M N : (D.obj i).Modules) [M.IsFinitePresentation] [N.IsFinitePresentation]
    (F : (pullback (c.π.app i)).obj M ⟶ (pullback (c.π.app i)).obj N) :
    ∃ (j : Over i) (g : ∀ x : A,
      (pullback ((chartStructure D i (f x)).app j)).obj M ⟶
        (pullback ((chartStructure D i (f x)).app j)).obj N),
      (∀ x, pullbackHomOfTriangle ((Scheme.baseChangeCone D c i (f x)).π.app j)
          ((chartStructure D i (f x)).app j) (chartLimitStructure D c i (f x))
          (chartLimitStructure_w D c i (f x) j) (g x) = chartLimitHom D c i F (f x)) ∧
      ∀ a b, let w := Limits.pullback.fst (f a) (f b) ≫ f a
        pullbackHomOfTriangle
          (chartMap (D.map j.hom) w (f a) (Limits.pullback.fst (f a) (f b)) rfl)
          ((chartStructure D i (f a)).app j) ((chartStructure D i w).app j)
          (chartMap_structure D i w (f a) (Limits.pullback.fst (f a) (f b)) rfl j) (g a) =
        pullbackHomOfTriangle
          (chartMap (D.map j.hom) w (f b) (Limits.pullback.snd (f a) (f b))
            Limits.pullback.condition.symm)
          ((chartStructure D i (f b)).app j) ((chartStructure D i w).app j)
          (chartMap_structure D i w (f b) (Limits.pullback.snd (f a) (f b))
            Limits.pullback.condition.symm j) (g b) := by
  classical
  obtain ⟨j, g, hg⟩ := exists_common_affine_chart_homs D c hc i X f M N F
  have (a : A) : QuasiCompact (f a) := inferInstance
  let w (ab : A × A) := Limits.pullback.fst (f ab.1) (f ab.2) ≫ f ab.1
  have (ab : A × A) : QuasiCompact (w ab) := inferInstance
  let L (ab : A × A) := pullbackHomOfTriangle
    (chartMap (D.map j.hom) (w ab) (f ab.1) (Limits.pullback.fst (f ab.1) (f ab.2)) rfl)
    ((chartStructure D i (f ab.1)).app j) ((chartStructure D i (w ab)).app j)
    (chartMap_structure D i (w ab) (f ab.1) (Limits.pullback.fst (f ab.1) (f ab.2)) rfl j)
    (g ab.1)
  let R (ab : A × A) := pullbackHomOfTriangle
    (chartMap (D.map j.hom) (w ab) (f ab.2) (Limits.pullback.snd (f ab.1) (f ab.2))
      Limits.pullback.condition.symm)
    ((chartStructure D i (f ab.2)).app j) ((chartStructure D i (w ab)).app j)
    (chartMap_structure D i (w ab) (f ab.2) (Limits.pullback.snd (f ab.1) (f ab.2))
      Limits.pullback.condition.symm j) (g ab.2)
  have hlimit (ab : A × A) :
      (pullback ((Scheme.baseChangeCone D c i (w ab)).π.app j)).map (L ab) =
        (pullback ((Scheme.baseChangeCone D c i (w ab)).π.app j)).map (R ab) := by
    apply (pullbackHomOfTriangle_map_inj_iff _ _ _
      (chartLimitStructure_w D c i (w ab) j) (L ab) (R ab)).mp
    exact (chartHom_recovery_of_map D c i F (w ab) (f ab.1)
      (Limits.pullback.fst (f ab.1) (f ab.2)) rfl j (g ab.1) (hg ab.1)).trans
      (chartHom_recovery_of_map D c i F (w ab) (f ab.2)
        (Limits.pullback.snd (f ab.1) (f ab.2)) Limits.pullback.condition.symm
        j (g ab.2) (hg ab.2)).symm
  choose k q hq using fun ab : A × A => exists_hom_equality_above_of_isLimit
    (Scheme.baseChangeDiagram D i (w ab)) (Scheme.baseChangeCone D c i (w ab))
    (Scheme.isLimitBaseChangeCone D c hc i (w ab)) j
    ((pullback ((chartStructure D i (w ab)).app j)).obj M)
    ((pullback ((chartStructure D i (w ab)).app j)).obj N) (L ab) (R ab) (hlimit ab)
  obtain ⟨l, q₀, v, hv⟩ := IsCofiltered.wideCospan q
  let g' (a : A) := pullbackHomOfTriangle ((Scheme.baseChangeDiagram D i (f a)).map q₀)
    ((chartStructure D i (f a)).app j) ((chartStructure D i (f a)).app l)
    (chartStructure_w D i (f a) q₀) (g a)
  refine ⟨l, g', ?_, ?_⟩
  · intro a
    dsimp only [g']
    rw [pullbackHomOfTriangle_comp]
    simpa only [(Scheme.baseChangeCone D c i (f a)).w q₀] using hg a
  · intro a b
    let ab : A × A := (a, b)
    have H := congrArg (fun h =>
      (pullback ((Scheme.baseChangeDiagram D i (w ab)).map (v ab))).map h) (hq ab)
    have H' := (pullback_map_eq_comp_iff
      ((Scheme.baseChangeDiagram D i (w ab)).map (v ab))
      ((Scheme.baseChangeDiagram D i (w ab)).map (q ab)) (L ab) (R ab)).mpr H
    have hmap : (Scheme.baseChangeDiagram D i (w ab)).map (v ab) ≫
        (Scheme.baseChangeDiagram D i (w ab)).map (q ab) =
          (Scheme.baseChangeDiagram D i (w ab)).map q₀ := by
      rw [← Functor.map_comp, hv ab]
    have H'' := pullback_map_eq_of_eq hmap H'
    have H''' := (pullbackHomOfTriangle_map_inj_iff
      ((Scheme.baseChangeDiagram D i (w ab)).map q₀)
      ((chartStructure D i (w ab)).app j) ((chartStructure D i (w ab)).app l)
      (chartStructure_w D i (w ab) q₀) (L ab) (R ab)).mpr H''
    simpa only [L, R, chartHom_map_transition, g', w, ab] using H'''


/-- Actual arrows between the pullbacks of two original sheaves glue on a
jointly surjective open family, with the native pullback-overlap equation. -/
theorem exists_hom_of_pullback_openCover
    {S : Scheme.{u}} {A : Type u} (X : A → Scheme.{u}) (a : ∀ i, X i ⟶ S)
    [∀ i, IsOpenImmersion (a i)]
    (hcover : ∀ x : S, ∃ i y, a i y = x) (M N : S.Modules)
    (f : ∀ i, (pullback (a i)).obj M ⟶ (pullback (a i)).obj N)
    (hcomp : ∀ i k,
      (pullback (Limits.pullback.fst (a i) (a k))).map (f i) ≫
          (pullbackSquareIso (Limits.pullback.snd (a i) (a k))
            (Limits.pullback.fst (a i) (a k)) (a k) (a i)
            Limits.pullback.condition.symm).hom.app N =
        (pullbackSquareIso (Limits.pullback.snd (a i) (a k))
          (Limits.pullback.fst (a i) (a k)) (a k) (a i) Limits.pullback.condition.symm).hom.app M ≫
          (pullback (Limits.pullback.snd (a i) (a k))).map (f k)) :
    ∃ F : M ⟶ N, ∀ i, (pullback (a i)).map F = f i := by
  let f' i := (restrictFunctorIsoPullback (a i)).hom.app M ≫ f i ≫
    (restrictFunctorIsoPullback (a i)).inv.app N
  have hcomp' : InternalHom.RestrictionHomCompatible a M N f' := by
    intro i k
    let p₁ := Limits.pullback.fst (a i) (a k)
    let p₂ := Limits.pullback.snd (a i) (a k)
    have H := hcomp i k
    dsimp only [pullbackSquareIso, pullbackTriangleIso, Iso.trans_hom,
      Iso.symm_hom, NatTrans.comp_app] at H
    have n₁ := restrictRestrictIso_hom_naturality p₁ (a i) (M := M) (N := N) (f i)
    have n₂ := restrictRestrictIso_hom_naturality p₂ (a k) (M := M) (N := N) (f k)
    have o₁ := overlapRestrictIso_hom_app_restrictRestrictIso_hom (a i) (a k) M
    have o₂ := overlapRestrictIso_hom_app_restrictRestrictIso_hom (a i) (a k) N
    rw [← cancel_mono (restrictRestrictIso p₂ (a k) N).hom, Category.assoc, o₂]
    change (restrictFunctor p₁).map ((restrictFunctorIsoPullback (a i)).hom.app M ≫ f i ≫
        (restrictFunctorIsoPullback (a i)).inv.app N) ≫ _ =
      (_ ≫ (restrictFunctor p₂).map ((restrictFunctorIsoPullback (a k)).hom.app M ≫ f k ≫
        (restrictFunctorIsoPullback (a k)).inv.app N)) ≫ _
    rw [reassoc_of% n₁, Category.assoc, n₂, reassoc_of% o₁]
    simpa only [Category.assoc] using congrArg
      (fun z => (restrictRestrictIso p₁ (a i) M).hom ≫ z) H
  obtain ⟨F, hF, _⟩ := InternalHom.existsUnique_restrictionHom X a hcover M N f' hcomp'
  refine ⟨F, fun i => ?_⟩
  apply (cancel_epi ((restrictFunctorIsoPullback (a i)).hom.app M)).mp
  rw [← (restrictFunctorIsoPullback (a i)).hom.naturality F, hF i]
  simp only [f', Category.assoc, Iso.inv_hom_id_app, Category.comp_id]


private theorem pullbackHomOfTriangle_change_coeff
    {S Y X V : Scheme.{u}} (b : Y ⟶ S) (a : X ⟶ Y) (t : X ⟶ S) (ha : a ≫ b = t)
    (k : V ⟶ X) (q : V ⟶ Y) (hq : k ≫ a = q)
    {M N : S.Modules} (g : (pullback t).obj M ⟶ (pullback t).obj N) :
    (pullbackComp q b).inv.app M ≫
        pullbackHomOfTriangle k a q hq
          ((pullbackTriangleIso a b t ha).hom.app M ≫ g ≫
            (pullbackTriangleIso a b t ha).inv.app N) ≫
        (pullbackComp q b).hom.app N =
      pullbackHomOfTriangle k t (q ≫ b) (by rw [← ha, ← Category.assoc, hq]) g := by
  have ht : k ≫ t = q ≫ b := by rw [← ha, ← Category.assoc, hq]
  let Ea := pullbackTriangleIso a b t ha
  let Eq := pullbackTriangleIso k a q hq
  let Er := pullbackComp q b
  let Et := pullbackTriangleIso k t (q ≫ b) ht
  have H (P : S.Modules) : (pullback k).map (Ea.hom.app P) ≫ Et.hom.app P =
      Eq.hom.app ((pullback b).obj P) ≫ Er.hom.app P := by
    have H := pullbackTriangleIso_assoc_hom a k b t ha (q ≫ b) ht P
    rw [← pullbackTriangleIso_congr_left hq b (q ≫ b)
      (by rw [Category.assoc, ha, ht]) rfl P] at H
    exact H
  have hcN : (pullback k).map (Ea.inv.app N) ≫ (pullback k).map (Ea.hom.app N) = 𝟙 _ := by
    rw [← Functor.map_comp, Ea.inv_hom_id_app, CategoryTheory.Functor.map_id]
  apply (cancel_epi ((pullback k).map (Ea.hom.app M) ≫ Et.hom.app M)).mp
  apply (cancel_mono (Et.inv.app N)).mp
  have HL :
      (((pullback k).map (Ea.hom.app M) ≫ Et.hom.app M) ≫
        (Er.inv.app M ≫ (Eq.inv.app ((pullback b).obj M) ≫
          (pullback k).map (Ea.hom.app M ≫ g ≫ Ea.inv.app N) ≫
          Eq.hom.app ((pullback b).obj N)) ≫ Er.hom.app N)) ≫ Et.inv.app N =
        (pullback k).map (Ea.hom.app M) ≫ (pullback k).map g := by
    rw [H M]
    simp only [Functor.map_comp, Category.assoc, Iso.hom_inv_id_app_assoc]
    rw [← Category.assoc (Eq.hom.app ((pullback b).obj N)), ← H N]
    simp only [Category.assoc, reassoc_of% hcN, Iso.hom_inv_id_app]
    simp only [Functor.comp_obj, Category.comp_id]
  have HR :
      (((pullback k).map (Ea.hom.app M) ≫ Et.hom.app M) ≫
        (Et.inv.app M ≫ (pullback k).map g ≫ Et.hom.app N)) ≫ Et.inv.app N =
        (pullback k).map (Ea.hom.app M) ≫ (pullback k).map g := by
    simp only [Category.assoc, Iso.hom_inv_id_app_assoc, Iso.hom_inv_id_app]
    simp only [Functor.comp_obj, Category.comp_id]
  exact HL.trans HR.symm

private theorem relative_pullback_cover_gluing
    {S Y : Scheme.{u}} (b : Y ⟶ S) {A : Type u} (X : A → Scheme.{u})
    (a : ∀ i, X i ⟶ Y) [∀ i, IsOpenImmersion (a i)]
    (hcover : ∀ y : Y, ∃ i x, a i x = y)
    (t : ∀ i, X i ⟶ S) (ht : ∀ i, a i ≫ b = t i)
    (M N : S.Modules) (g : ∀ i, (pullback (t i)).obj M ⟶ (pullback (t i)).obj N)
    (hcomp : ∀ i j, let q := Limits.pullback.fst (a i) (a j) ≫ a i
      pullbackHomOfTriangle (Limits.pullback.fst (a i) (a j)) (t i) (q ≫ b)
          (by rw [← ht i, ← Category.assoc]) (g i) =
        pullbackHomOfTriangle (Limits.pullback.snd (a i) (a j)) (t j) (q ≫ b)
          (by rw [← ht j, ← Category.assoc]
              exact congrArg (· ≫ b) Limits.pullback.condition.symm) (g j)) :
    ∃ G : (pullback b).obj M ⟶ (pullback b).obj N,
      ∀ i, pullbackHomOfTriangle (a i) b (t i) (ht i) G = g i := by
  let e i := pullbackTriangleIso (a i) b (t i) (ht i)
  let f i := (e i).hom.app M ≫ g i ≫ (e i).inv.app N
  have hf : ∀ i j,
      (pullback (Limits.pullback.fst (a i) (a j))).map (f i) ≫
          (pullbackSquareIso (Limits.pullback.snd (a i) (a j))
            (Limits.pullback.fst (a i) (a j)) (a j) (a i) Limits.pullback.condition.symm).hom.app
              ((pullback b).obj N) =
        (pullbackSquareIso (Limits.pullback.snd (a i) (a j))
          (Limits.pullback.fst (a i) (a j)) (a j) (a i) Limits.pullback.condition.symm).hom.app
            ((pullback b).obj M) ≫
          (pullback (Limits.pullback.snd (a i) (a j))).map (f j) := by
    intro i j
    let p₁ := Limits.pullback.fst (a i) (a j)
    let p₂ := Limits.pullback.snd (a i) (a j)
    let q := p₁ ≫ a i
    let E₁ := pullbackTriangleIso p₁ (a i) q rfl
    let E₂ := pullbackTriangleIso p₂ (a j) q Limits.pullback.condition.symm
    have H : pullbackHomOfTriangle p₁ (a i) q rfl (f i) =
        pullbackHomOfTriangle p₂ (a j) q Limits.pullback.condition.symm (f j) := by
      apply (cancel_epi ((pullbackComp q b).inv.app M)).mp
      apply (cancel_mono ((pullbackComp q b).hom.app N)).mp
      have hi := pullbackHomOfTriangle_change_coeff b (a i) (t i) (ht i) p₁ q rfl (g i)
      have hj := pullbackHomOfTriangle_change_coeff b (a j) (t j) (ht j) p₂ q
        Limits.pullback.condition.symm (g j)
      simpa only [f, e, Category.assoc] using hi.trans ((hcomp i j).trans hj.symm)
    apply (cancel_epi (E₁.inv.app ((pullback b).obj M))).mp
    apply (cancel_mono (E₂.hom.app ((pullback b).obj N))).mp
    change (E₁.inv.app ((pullback b).obj M) ≫
        ((pullback p₁).map (f i) ≫ E₁.hom.app ((pullback b).obj N) ≫
          E₂.inv.app ((pullback b).obj N))) ≫ E₂.hom.app ((pullback b).obj N) =
      (E₁.inv.app ((pullback b).obj M) ≫
        (E₁.hom.app ((pullback b).obj M) ≫ E₂.inv.app ((pullback b).obj M) ≫
          (pullback p₂).map (f j))) ≫ E₂.hom.app ((pullback b).obj N)
    simpa only [pullbackHomOfTriangle, E₁, E₂, Category.assoc,
      Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app,
      Category.comp_id] using H
  obtain ⟨G, hG⟩ := exists_hom_of_pullback_openCover X a hcover
    ((pullback b).obj M) ((pullback b).obj N) f hf
  refine ⟨G, fun i => ?_⟩
  dsimp only [pullbackHomOfTriangle]
  rw [hG i]
  simp only [f, e, Category.assoc, Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app, Category.comp_id]


private theorem chartMap_structure_base {S T X Y : Scheme.{u}}
    (b : T ⟶ S) (f : X ⟶ S) (g : Y ⟶ S) (a : X ⟶ Y) (ha : a ≫ g = f) :
    chartMap b f g a ha ≫ (Limits.pullback.snd b g ≫ g) = Limits.pullback.snd b f ≫ f := by
  simp [chartMap, Category.assoc, ha]

private theorem pullbackHomOfTriangle_eq_of_factor
    {S X Y W V : Scheme.{u}} (a : W ⟶ X) (b : W ⟶ Y)
    (x : X ⟶ S) (y : Y ⟶ S) (w : W ⟶ S) (ha : a ≫ x = w) (hb : b ≫ y = w)
    (z : V ⟶ W) (v : V ⟶ S) (hz : z ≫ w = v)
    (p : V ⟶ X) (q : V ⟶ Y) (hp : z ≫ a = p) (hq : z ≫ b = q)
    {M N : S.Modules} (f : (pullback x).obj M ⟶ (pullback x).obj N)
    (g : (pullback y).obj M ⟶ (pullback y).obj N)
    (h : pullbackHomOfTriangle a x w ha f = pullbackHomOfTriangle b y w hb g) :
    pullbackHomOfTriangle p x v (by rw [← hp, Category.assoc, ha, hz]) f =
      pullbackHomOfTriangle q y v (by rw [← hq, Category.assoc, hb, hz]) g := by
  have H := congrArg (fun k => pullbackHomOfTriangle z w v hz k) h
  simpa only [pullbackHomOfTriangle_comp, hp, hq] using H

private theorem exists_pullback_overlap_map
    {S T X Y : Scheme.{u}} (b : T ⟶ S) (u : X ⟶ S) (v : Y ⟶ S) :
    let p₁ := Limits.pullback.fst (Limits.pullback.fst b u) (Limits.pullback.fst b v)
    let p₂ := Limits.pullback.snd (Limits.pullback.fst b u) (Limits.pullback.fst b v)
    let q := p₁ ≫ Limits.pullback.fst b u
    let w := Limits.pullback.fst u v ≫ u
    ∃ z : Limits.pullback (Limits.pullback.fst b u) (Limits.pullback.fst b v) ⟶
        Limits.pullback b w,
      z ≫ chartMap b w u (Limits.pullback.fst u v) rfl = p₁ ∧
      z ≫ chartMap b w v (Limits.pullback.snd u v) Limits.pullback.condition.symm = p₂ ∧
      z ≫ (Limits.pullback.snd b w ≫ w) = q ≫ b := by
  let p₁ := Limits.pullback.fst (Limits.pullback.fst b u) (Limits.pullback.fst b v)
  let p₂ := Limits.pullback.snd (Limits.pullback.fst b u) (Limits.pullback.fst b v)
  let q := p₁ ≫ Limits.pullback.fst b u
  let w := Limits.pullback.fst u v ≫ u
  have hw : (p₁ ≫ Limits.pullback.snd b u) ≫ u = (p₂ ≫ Limits.pullback.snd b v) ≫ v := by
    calc
      (p₁ ≫ Limits.pullback.snd b u) ≫ u = (p₁ ≫ Limits.pullback.fst b u) ≫ b := by
        rw [Category.assoc, Category.assoc, Limits.pullback.condition (f := b) (g := u)]
      _ = (p₂ ≫ Limits.pullback.fst b v) ≫ b :=
        congrArg (· ≫ b) (Limits.pullback.condition
          (f := Limits.pullback.fst b u) (g := Limits.pullback.fst b v))
      _ = (p₂ ≫ Limits.pullback.snd b v) ≫ v := by
        rw [Category.assoc, Category.assoc, Limits.pullback.condition (f := b) (g := v)]
  let z₀ := Limits.pullback.lift (p₁ ≫ Limits.pullback.snd b u)
    (p₂ ≫ Limits.pullback.snd b v) hw
  let z : Limits.pullback (Limits.pullback.fst b u) (Limits.pullback.fst b v) ⟶
      Limits.pullback b w := Limits.pullback.lift q z₀ (by
    change (p₁ ≫ Limits.pullback.fst b u) ≫ b = z₀ ≫ (Limits.pullback.fst u v ≫ u)
    rw [← Category.assoc, Limits.pullback.lift_fst]
    rw [Category.assoc, Category.assoc, Limits.pullback.condition (f := b) (g := u)])
  have hzf : z ≫ Limits.pullback.fst b w = q := Limits.pullback.lift_fst _ _ _
  have hzs : z ≫ Limits.pullback.snd b w = z₀ := Limits.pullback.lift_snd _ _ _
  have hz₀f : z₀ ≫ Limits.pullback.fst u v = p₁ ≫ Limits.pullback.snd b u :=
    Limits.pullback.lift_fst _ _ _
  have hz₀s : z₀ ≫ Limits.pullback.snd u v = p₂ ≫ Limits.pullback.snd b v :=
    Limits.pullback.lift_snd _ _ _
  refine ⟨z, ?_, ?_, ?_⟩
  · apply Limits.pullback.hom_ext (f := b) (g := u)
    · rw [Category.assoc, chartMap_fst, hzf]
    · rw [Category.assoc, chartMap_snd, ← Category.assoc, hzs, hz₀f]
  · apply Limits.pullback.hom_ext (f := b) (g := v)
    · rw [Category.assoc, chartMap_fst, hzf]
      exact Limits.pullback.condition
    · rw [Category.assoc, chartMap_snd, ← Category.assoc, hzs, hz₀s]
  · rw [← Limits.pullback.condition (f := b) (g := w), ← Category.assoc, hzf]

private theorem pullback_overlap_hom_compat
    {S T X Y : Scheme.{u}} (b : T ⟶ S) (u : X ⟶ S) (v : Y ⟶ S)
    (M N : S.Modules)
    (f : (pullback (Limits.pullback.snd b u ≫ u)).obj M ⟶
      (pullback (Limits.pullback.snd b u ≫ u)).obj N)
    (g : (pullback (Limits.pullback.snd b v ≫ v)).obj M ⟶
      (pullback (Limits.pullback.snd b v ≫ v)).obj N)
    (hcomp : let w := Limits.pullback.fst u v ≫ u
      pullbackHomOfTriangle (chartMap b w u (Limits.pullback.fst u v) rfl)
          (Limits.pullback.snd b u ≫ u) (Limits.pullback.snd b w ≫ w)
          (chartMap_structure_base b w u (Limits.pullback.fst u v) rfl) f =
        pullbackHomOfTriangle
          (chartMap b w v (Limits.pullback.snd u v) Limits.pullback.condition.symm)
          (Limits.pullback.snd b v ≫ v) (Limits.pullback.snd b w ≫ w)
          (chartMap_structure_base b w v (Limits.pullback.snd u v)
            Limits.pullback.condition.symm) g) :
    let p₁ := Limits.pullback.fst (Limits.pullback.fst b u) (Limits.pullback.fst b v)
    let p₂ := Limits.pullback.snd (Limits.pullback.fst b u) (Limits.pullback.fst b v)
    let q := p₁ ≫ Limits.pullback.fst b u
    pullbackHomOfTriangle p₁ (Limits.pullback.snd b u ≫ u) (q ≫ b)
        (by rw [← Limits.pullback.condition, ← Category.assoc]) f =
      pullbackHomOfTriangle p₂ (Limits.pullback.snd b v ≫ v) (q ≫ b)
        (by rw [← Limits.pullback.condition, ← Category.assoc]
            exact congrArg (· ≫ b) Limits.pullback.condition.symm) g := by
  let p₁ := Limits.pullback.fst (Limits.pullback.fst b u) (Limits.pullback.fst b v)
  let p₂ := Limits.pullback.snd (Limits.pullback.fst b u) (Limits.pullback.fst b v)
  let q := p₁ ≫ Limits.pullback.fst b u
  let w := Limits.pullback.fst u v ≫ u
  obtain ⟨z, hz₁, hz₂, hz⟩ := exists_pullback_overlap_map b u v
  exact pullbackHomOfTriangle_eq_of_factor
    (chartMap b w u (Limits.pullback.fst u v) rfl)
    (chartMap b w v (Limits.pullback.snd u v) Limits.pullback.condition.symm)
    (Limits.pullback.snd b u ≫ u) (Limits.pullback.snd b v ≫ v)
    (Limits.pullback.snd b w ≫ w)
    (chartMap_structure_base b w u (Limits.pullback.fst u v) rfl)
    (chartMap_structure_base b w v (Limits.pullback.snd u v) Limits.pullback.condition.symm)
    z (q ≫ b) hz p₁ p₂ hz₁ hz₂ f g hcomp

/-- An actual map between the limit pullbacks of two given finitely presented
module sheaves on a qcqs stage descends to a later stage. The recovery square
uses the original cone and its native pullback-composition isomorphism. -/
theorem exists_hom_above_of_isLimit
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u})
    [∀ {j k} (q : j ⟶ k), IsAffineHom (D.map q)]
    [∀ j, CompactSpace (D.obj j)] [∀ j, QuasiSeparatedSpace (D.obj j)]
    (c : Cone D) (hc : IsLimit c) (i : I)
    (M N : (D.obj i).Modules) [M.IsFinitePresentation] [N.IsFinitePresentation]
    (F : (pullback (c.π.app i)).obj M ⟶ (pullback (c.π.app i)).obj N) :
    ∃ (j : I) (q : j ⟶ i)
      (G : (pullback (D.map q)).obj M ⟶ (pullback (D.map q)).obj N),
      (pullbackConeCompIso D c q).hom.app M ≫ (pullback (c.π.app j)).map G =
        F ≫ (pullbackConeCompIso D c q).hom.app N := by
  classical
  let 𝒰 := (D.obj i).affineCover.finiteSubcover
  have (a : 𝒰.I₀) : IsAffine (𝒰.X a) := inferInstanceAs
    (IsAffine ((D.obj i).affineCover.X ((D.obj i).affineCover.idx a.1)))
  obtain ⟨j, g, hg, hcomp⟩ := exists_compatible_chart_homs D c hc i 𝒰.X 𝒰.f M N F
  let b := D.map j.hom
  let 𝒱 : Scheme.OpenCover (D.obj j.left) :=
    { I₀ := 𝒰.I₀
      X a := Limits.pullback b (𝒰.f a)
      f a := Limits.pullback.fst b (𝒰.f a)
      mem₀ := (𝒰.pullback₁ b).mem₀ }
  let t (a : 𝒰.I₀) := (chartStructure D i (𝒰.f a)).app j
  have ht (a : 𝒰.I₀) : 𝒱.f a ≫ b = t a := Limits.pullback.condition
  have hcompat (a a' : 𝒰.I₀) :
      let q := Limits.pullback.fst (𝒱.f a) (𝒱.f a') ≫ 𝒱.f a
      pullbackHomOfTriangle (Limits.pullback.fst (𝒱.f a) (𝒱.f a')) (t a) (q ≫ b)
          (by rw [← ht a, ← Category.assoc]) (g a) =
        pullbackHomOfTriangle (Limits.pullback.snd (𝒱.f a) (𝒱.f a')) (t a') (q ≫ b)
          (by rw [← ht a', ← Category.assoc]
              exact congrArg (· ≫ b) Limits.pullback.condition.symm) (g a') := by
    exact pullback_overlap_hom_compat b (𝒰.f a) (𝒰.f a') M N (g a) (g a') (hcomp a a')
  obtain ⟨G, hG⟩ := relative_pullback_cover_gluing b 𝒱.X 𝒱.f
    (Scheme.Cover.exists_eq 𝒱) t ht M N g hcompat
  let H := pullbackHomOfTriangle (c.π.app j.left) b (c.π.app i) (c.w j.hom) G
  have hHF : H = F := by
    let 𝒲 : Scheme.OpenCover c.pt :=
      { I₀ := 𝒰.I₀
        X a := Limits.pullback (c.π.app j.left) (𝒱.f a)
        f a := Limits.pullback.fst (c.π.app j.left) (𝒱.f a)
        mem₀ := (𝒱.pullback₁ (c.π.app j.left)).mem₀ }
    apply Nonflat.hom_ext_of_restrict_jointlySurjective 𝒲.X 𝒲.f (Scheme.Cover.exists_eq 𝒲)
    intro a
    apply (map_eq_iff_natIso (restrictFunctorIsoPullback (𝒲.f a)) H F).mpr
    let p := Limits.pullback.fst (c.π.app j.left) (𝒱.f a)
    let r := Limits.pullback.snd (c.π.app j.left) (𝒱.f a)
    let l := p ≫ c.π.app i
    have hr : r ≫ t a = l := by
      rw [← ht a, ← Category.assoc, ← Limits.pullback.condition, Category.assoc, c.w j.hom]
    let z : Limits.pullback (c.π.app j.left) (𝒱.f a) ⟶
        Limits.pullback (c.π.app i) (𝒰.f a) :=
      Limits.pullback.lift p (r ≫ Limits.pullback.snd b (𝒰.f a)) (by
        change l = (r ≫ Limits.pullback.snd b (𝒰.f a)) ≫ 𝒰.f a
        exact hr.symm.trans (Category.assoc _ _ _).symm)
    have hzfst : z ≫ Limits.pullback.fst (c.π.app i) (𝒰.f a) = p := by simp [z]
    have hcfst : (Scheme.baseChangeCone D c i (𝒰.f a)).π.app j ≫
        Limits.pullback.fst b (𝒰.f a) =
          Limits.pullback.fst (c.π.app i) (𝒰.f a) ≫ c.π.app j.left := by
      simp [b, Scheme.baseChangeCone, Scheme.baseChangeDiagram, Functor.comp_map,
        Over.forget_map, Over.pullback_map_left]
    have hcsnd : (Scheme.baseChangeCone D c i (𝒰.f a)).π.app j ≫
        Limits.pullback.snd b (𝒰.f a) = Limits.pullback.snd (c.π.app i) (𝒰.f a) := by
      simp [b, Scheme.baseChangeCone, Scheme.baseChangeDiagram, Functor.comp_map,
        Over.forget_map, Over.pullback_map_left]
    have hzcone : z ≫ (Scheme.baseChangeCone D c i (𝒰.f a)).π.app j = r := by
      apply Limits.pullback.hom_ext (f := b) (g := 𝒰.f a)
      · rw [Category.assoc, hcfst, ← Category.assoc, hzfst]
        exact Limits.pullback.condition
      · rw [Category.assoc, hcsnd]
        simp [z]
    have hz : z ≫ chartLimitStructure D c i (𝒰.f a) = l := by
      change z ≫ (Limits.pullback.snd (c.π.app i) (𝒰.f a) ≫ 𝒰.f a) = l
      rw [← Limits.pullback.condition, ← Category.assoc, hzfst]
    apply (pullbackHomOfTriangle_map_inj_iff p (c.π.app i) l rfl H F).mp
    have hp : p ≫ c.π.app j.left = r ≫ 𝒱.f a := Limits.pullback.condition
    calc
      pullbackHomOfTriangle p (c.π.app i) l rfl H =
          pullbackHomOfTriangle r (t a) l hr
            (pullbackHomOfTriangle (𝒱.f a) b (t a) (ht a) G) := by
        dsimp only [H]
        simp only [pullbackHomOfTriangle_comp, hp]
      _ = pullbackHomOfTriangle r (t a) l hr (g a) := by rw [hG a]
      _ = pullbackHomOfTriangle z (chartLimitStructure D c i (𝒰.f a)) l hz
          (pullbackHomOfTriangle ((Scheme.baseChangeCone D c i (𝒰.f a)).π.app j)
            (t a) (chartLimitStructure D c i (𝒰.f a))
            (chartLimitStructure_w D c i (𝒰.f a) j) (g a)) := by
        simp only [pullbackHomOfTriangle_comp, hzcone]
      _ = pullbackHomOfTriangle z (chartLimitStructure D c i (𝒰.f a)) l hz
          (chartLimitHom D c i F (𝒰.f a)) := by rw [hg a]
      _ = pullbackHomOfTriangle p (c.π.app i) l rfl F := by
        dsimp only [chartLimitHom]
        simp only [pullbackHomOfTriangle_comp, hzfst]
  refine ⟨j.left, j.hom, G, ?_⟩
  exact (pullbackHomOfTriangle_eq_iff (c.π.app j.left) b (c.π.app i)
    (c.w j.hom) G F).mp hHF


/-- Global fixed-base Hom descent for original finitely presented coefficients.
The actual structural maps and every original limit recovery equation are retained. -/
theorem exists_relative_hom_above_of_isLimit
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u})
    [∀ {j k} (q : j ⟶ k), IsAffineHom (D.map q)]
    [∀ j, CompactSpace (D.obj j)] [∀ j, QuasiSeparatedSpace (D.obj j)]
    (c : Cone D) (hc : IsLimit c) {S : Scheme.{u}}
    (t : D ⟶ (Functor.const I).obj S) (l : c.pt ⟶ S)
    (hl : ∀ i, c.π.app i ≫ t.app i = l) (i : I)
    (M N : S.Modules) [M.IsFinitePresentation] [N.IsFinitePresentation]
    (f : (pullback l).obj M ⟶ (pullback l).obj N) :
    ∃ (j : I) (_ : j ⟶ i)
      (g : (pullback (t.app j)).obj M ⟶ (pullback (t.app j)).obj N),
      pullbackHomOfTriangle (c.π.app j) (t.app j) l (hl j) g = f := by
  let eᵢ := pullbackTriangleIso (c.π.app i) (t.app i) l (hl i)
  let fᵢ := eᵢ.hom.app M ≫ f ≫ eᵢ.inv.app N
  obtain ⟨j, q, g₀, hg₀⟩ := exists_hom_above_of_isLimit D c hc i
    ((pullback (t.app i)).obj M) ((pullback (t.app i)).obj N) fᵢ
  have hq : D.map q ≫ t.app i = t.app j :=
    (t.naturality q).trans (Category.comp_id _)
  let eⱼ := pullbackTriangleIso (D.map q) (t.app i) (t.app j) hq
  let eₗ := pullbackTriangleIso (c.π.app j) (t.app j) l (hl j)
  let g := eⱼ.inv.app M ≫ g₀ ≫ eⱼ.hom.app N
  refine ⟨j, q, g, (pullbackHomOfTriangle_eq_iff _ _ _ _ _ _).mpr ?_⟩
  let U := pullbackConeCompIso D c q
  have hcoh (P : S.Modules) :
      U.hom.app ((pullback (t.app i)).obj P) ≫
          (pullback (c.π.app j)).map (eⱼ.hom.app P) =
        eᵢ.hom.app P ≫ eₗ.inv.app P :=
    pullbackTriangleIso_cone_hom (D.map q) (t.app i) (c.π.app j)
      (c.π.app i) (c.w q) (t.app j) hq l (hl j) (hl i) P
  exact lift_conjugate_recovery (pullback (c.π.app i)) (pullback (D.map q))
    (pullback (c.π.app j)) U (eᵢ.app M) (eᵢ.app N) (eⱼ.app M) (eⱼ.app N)
    (eₗ.app M) (eₗ.app N) (hcoh M) (hcoh N) f g₀ hg₀

end AlgebraicGeometry.Scheme.Modules
