/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Group.CartierDuality.Functor
public import Aglib.RingTheory.Bialgebra.FiniteDualEquiv

/-!
# The original finite group and its actual double dual

The coordinate comparison for the dual group is the native fully faithful
preimage of its original affine group isomorphism. Transposing that comparison
and using the original native bidual evaluation gives the group bidual
isomorphism. No second coordinate algebra or bidual choice is introduced.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite Module
open scoped Module.Dual.FiniteDual

namespace AlgebraicGeometry.Scheme.Group.CartierDuality

universe u

open AlgebraicGeometry.Scheme.OverField (FScheme)

variable {k : Type u} [Field k]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The native fully faithful preimage of an actual Spec group isomorphism. -/
def specGroupPullbackIso {A B : CommHopfAlgCat.{u} k} (e : specGroup A ≅ specGroup B) :
    B ≅ A :=
  ((AlgebraicGeometry.hopfSpec.fullyFaithful (R := CommRingCat.of k)).preimageIso e).unop

@[simp]
theorem specGroupPullbackIso_hom {A B : CommHopfAlgCat.{u} k}
    (e : specGroup A ≅ specGroup B) :
    (specGroupPullbackIso e).hom = specGroupPullback e.hom := rfl

@[simp]
theorem specGroupPullbackIso_inv {A B : CommHopfAlgCat.{u} k}
    (e : specGroup A ≅ specGroup B) :
    (specGroupPullbackIso e).inv = specGroupPullback e.inv := rfl

/-- The native Spec image of the original comparison map. -/
theorem hopfSpec_specGroupPullbackIso_hom {A B : CommHopfAlgCat.{u} k}
    (e : specGroup A ≅ specGroup B) :
    (AlgebraicGeometry.hopfSpec (CommRingCat.of k)).map (specGroupPullbackIso e).hom.op =
      e.hom := by
  exact hopfSpec_specGroupPullback e.hom

/-- The original transpose of a Hopf equivalence, sent through native Spec. -/
def specGroupDualIso {A B : CommHopfAlgCat.{u} k}
    [Coalgebra.IsCocomm k A] [FiniteDimensional k A]
    [Coalgebra.IsCocomm k B] [FiniteDimensional k B] (e : A ≅ B) :
    specGroup (CommHopfAlgCat.of k (Dual k A)) ≅
      specGroup (CommHopfAlgCat.of k (Dual k B)) :=
  (AlgebraicGeometry.hopfSpec (CommRingCat.of k)).mapIso
    (CommHopfAlgCat.isoMk (CommHopfAlgCat.ofIso e).dual).op

/-- The same dual-isomorphism map is native Spec of the original transposed hom. -/
theorem hopfSpec_specGroupDualIso_hom {A B : CommHopfAlgCat.{u} k}
    [Coalgebra.IsCocomm k A] [FiniteDimensional k A]
    [Coalgebra.IsCocomm k B] [FiniteDimensional k B] (e : A ≅ B) :
    (AlgebraicGeometry.hopfSpec (CommRingCat.of k)).map
        (CommHopfAlgCat.ofHom e.hom.hom.dual).op = (specGroupDualIso e).hom := rfl

/-- The original bidual evaluation as an isomorphism between native Hopf objects. -/
def hopfBidualIso (A : CommHopfAlgCat.{u} k)
    [Coalgebra.IsCocomm k A] [FiniteDimensional k A] :
    A ≅ CommHopfAlgCat.of k (Dual k (Dual k A)) :=
  (CommHopfAlgCat.ofIsoSelf A).symm ≪≫
    CommHopfAlgCat.isoMk (Module.Dual.evalBialgEquiv k A)

@[simp]
theorem hopfBidualIso_hom_hom (A : CommHopfAlgCat.{u} k)
    [Coalgebra.IsCocomm k A] [FiniteDimensional k A] :
    (hopfBidualIso A).hom.hom = (Module.Dual.evalBialgEquiv k A).toBialgHom := by
  ext a f
  rfl

@[simp]
theorem hopfBidualIso_inv_hom (A : CommHopfAlgCat.{u} k)
    [Coalgebra.IsCocomm k A] [FiniteDimensional k A] :
    (hopfBidualIso A).inv.hom = (Module.Dual.evalBialgEquiv k A).symm.toBialgHom := by
  ext f
  rfl

/-- Naturality of the same native Hopf bidual evaluation. -/
theorem hopfBidualIso_naturality {A B : CommHopfAlgCat.{u} k}
    [Coalgebra.IsCocomm k A] [FiniteDimensional k A]
    [Coalgebra.IsCocomm k B] [FiniteDimensional k B] (f : A ⟶ B) :
    f ≫ (hopfBidualIso B).hom =
      (hopfBidualIso A).hom ≫ CommHopfAlgCat.ofHom f.hom.dual.dual := by
  apply CommHopfAlgCat.hom_ext
  simp only [CommHopfAlgCat.hom_comp, hopfBidualIso_hom_hom, CommHopfAlgCat.hom_ofHom]
  exact (Module.Dual.evalBialgEquiv_natural f.hom).symm

/-- Naturality of the original inverse of bidual evaluation. -/
theorem hopfBidualIso_inv_naturality {A B : CommHopfAlgCat.{u} k}
    [Coalgebra.IsCocomm k A] [FiniteDimensional k A]
    [Coalgebra.IsCocomm k B] [FiniteDimensional k B] (f : A ⟶ B) :
    (hopfBidualIso A).inv ≫ f =
      CommHopfAlgCat.ofHom f.hom.dual.dual ≫ (hopfBidualIso B).inv := by
  apply (cancel_epi (hopfBidualIso A).hom).mp
  have h := congrArg (fun t => t ≫ (hopfBidualIso B).inv) (hopfBidualIso_naturality f)
  simpa [Category.assoc] using h

/-- The original inverse bidual evaluation transposes to evaluation on the dual. -/
theorem dual_hopfBidualIso_inv (A : CommHopfAlgCat.{u} k)
    [Coalgebra.IsCocomm k A] [FiniteDimensional k A] :
    CommHopfAlgCat.ofHom (hopfBidualIso A).inv.hom.dual =
      (hopfBidualIso (CommHopfAlgCat.of k (Dual k A))).hom := by
  apply CommHopfAlgCat.hom_ext
  rw [CommHopfAlgCat.hom_ofHom, hopfBidualIso_inv_hom, hopfBidualIso_hom_hom]
  ext f g
  exact Module.apply_evalEquiv_symm_apply k A f g

/-- Transposing the whole original inverse-evaluation composite recovers the original Hopf map. -/
theorem hopfBidualIso_dual_composite {A B : CommHopfAlgCat.{u} k}
    [Coalgebra.IsCocomm k A] [FiniteDimensional k A]
    [Coalgebra.IsCocomm k B] [FiniteDimensional k B]
    (q : CommHopfAlgCat.of k (Dual k A) ⟶ B) :
    CommHopfAlgCat.ofHom ((hopfBidualIso A).inv.hom.comp q.hom.dual).dual ≫
      (hopfBidualIso B).inv = q := by
  apply CommHopfAlgCat.hom_ext
  simp only [CommHopfAlgCat.hom_comp, CommHopfAlgCat.hom_ofHom, hopfBidualIso_inv_hom]
  exact BialgHom.dual_eval_symm_comp q.hom

/-- Native bidual evaluation, with its original inverse, on the actual Spec groups. -/
def specGroupBidualIso (A : CommHopfAlgCat.{u} k)
    [Coalgebra.IsCocomm k A] [FiniteDimensional k A] :
    specGroup A ≅ specGroup (CommHopfAlgCat.of k (Dual k (Dual k A))) :=
  ((AlgebraicGeometry.hopfSpec (CommRingCat.of k)).mapIso
    (hopfBidualIso A).op).symm

/-- The same Spec bidual comparison is the native image of inverse evaluation. -/
theorem hopfSpec_hopfBidualIso_inv (A : CommHopfAlgCat.{u} k)
    [Coalgebra.IsCocomm k A] [FiniteDimensional k A] :
    (AlgebraicGeometry.hopfSpec (CommRingCat.of k)).map (hopfBidualIso A).inv.op =
      (specGroupBidualIso A).hom := rfl

variable (G : Grp (FScheme k)) [IsFinite G.X.hom] [IsCommMonObj G.X]

/-- Compare the dual group's actual Gamma coordinates with the original linear dual. -/
def dualCoordinateIso :
    CommHopfAlgCat.of k (Dual k (coordinateHopf G)) ≅ coordinateHopf (dualGroup G) :=
  specGroupPullbackIso (A := coordinateHopf (dualGroup G))
    (B := CommHopfAlgCat.of k (Dual k (coordinateHopf G))) (coordinateSpecIso (dualGroup G))

/-- The comparison on the dual coordinate is the original affine group isomorphism. -/
theorem hopfSpec_dualCoordinateIso_hom :
    (AlgebraicGeometry.hopfSpec (CommRingCat.of k)).map (dualCoordinateIso G).hom.op =
      (coordinateSpecIso (dualGroup G)).hom := by
  exact hopfSpec_specGroupPullbackIso_hom (coordinateSpecIso (dualGroup G))

/-- The original finite commutative group is isomorphic to its actual double Cartier dual. -/
def bidualIso : G ≅ dualGroup (dualGroup G) :=
  (coordinateSpecIso G).symm ≪≫ specGroupBidualIso (coordinateHopf G) ≪≫
    specGroupDualIso (A := CommHopfAlgCat.of k (Dual k (coordinateHopf G)))
      (B := coordinateHopf (dualGroup G)) (dualCoordinateIso G)

/-- Coordinate pullback of the original bidual map is inverse evaluation after
the dual comparison. -/
theorem dualCoordinateIso_bidualIso_hom :
    (dualCoordinateIso (dualGroup G)).hom ≫ coordinateMap (bidualIso G).hom =
      CommHopfAlgCat.ofHom (dualCoordinateIso G).hom.hom.dual ≫
        (hopfBidualIso (coordinateHopf G)).inv := by
  have h : ((coordinateSpecIso G).hom ≫ (bidualIso G).hom ≫
      (coordinateSpecIso (dualGroup (dualGroup G))).inv) ≫
      (coordinateSpecIso (dualGroup (dualGroup G))).hom =
      (specGroupBidualIso (coordinateHopf G)).hom ≫
        (specGroupDualIso (A := CommHopfAlgCat.of k (Dual k (coordinateHopf G)))
          (B := coordinateHopf (dualGroup G)) (dualCoordinateIso G)).hom := by
    simp [bidualIso, Category.assoc]
    rfl
  apply Quiver.Hom.op_inj
  apply (AlgebraicGeometry.hopfSpec.fullyFaithful (R := CommRingCat.of k)).map_injective
  rw [op_comp, op_comp, CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
    hopfSpec_coordinateMap, hopfSpec_dualCoordinateIso_hom, hopfSpec_hopfBidualIso_inv,
    hopfSpec_specGroupDualIso_hom (dualCoordinateIso G)]
  exact h

variable {G} {H : Grp (FScheme k)} [IsFinite H.X.hom] [IsCommMonObj H.X]

/-- Coordinate pullback of a dual morphism preserves the same original Gamma comparison. -/
theorem dualCoordinateIso_naturality (f : G ⟶ H) :
    (dualCoordinateIso G).hom ≫ coordinateMap (dualMap f) =
      CommHopfAlgCat.ofHom (coordinateMap f).hom.dual ≫ (dualCoordinateIso H).hom := by
  have h : ((coordinateSpecIso (dualGroup H)).hom ≫ dualMap f ≫
      (coordinateSpecIso (dualGroup G)).inv) ≫ (coordinateSpecIso (dualGroup G)).hom =
      (coordinateSpecIso (dualGroup H)).hom ≫ dualMap f := by
    simp [Category.assoc]
  apply Quiver.Hom.op_inj
  apply (AlgebraicGeometry.hopfSpec.fullyFaithful (R := CommRingCat.of k)).map_injective
  rw [op_comp, op_comp, CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
    hopfSpec_coordinateMap, hopfSpec_dualCoordinateIso_hom, hopfSpec_dualCoordinateIso_hom]
  exact h

/-- Naturality of the original group bidual isomorphism. -/
theorem bidualIso_naturality (f : G ⟶ H) :
    f ≫ (bidualIso H).hom = (bidualIso G).hom ≫ dualMap (dualMap f) := by
  let c := coordinateMap f
  let cd := coordinateMap (dualMap f)
  let dcd := CommHopfAlgCat.ofHom cd.hom.dual
  let ddc := CommHopfAlgCat.ofHom c.hom.dual.dual
  let dqG := CommHopfAlgCat.ofHom (dualCoordinateIso G).hom.hom.dual
  let dqH := CommHopfAlgCat.ofHom (dualCoordinateIso H).hom.hom.dual
  let kG := coordinateMap (bidualIso G).hom
  let kH := coordinateMap (bidualIso H).hom
  let vG := (hopfBidualIso (coordinateHopf G)).inv
  let vH := (hopfBidualIso (coordinateHopf H)).inv
  have hd := congrArg
    (fun t : CommHopfAlgCat.of k (Dual k (coordinateHopf G)) ⟶
        coordinateHopf (dualGroup H) => CommHopfAlgCat.ofHom t.hom.dual)
    (dualCoordinateIso_naturality f)
  simp only [CommHopfAlgCat.hom_comp, CommHopfAlgCat.hom_ofHom,
    BialgHom.dual_comp, CommHopfAlgCat.ofHom_comp] at hd
  apply coordinateMap_injective (G := G) (H := dualGroup (dualGroup H))
  rw [coordinateMap_comp, coordinateMap_comp]
  apply (cancel_epi (dualCoordinateIso (dualGroup H)).hom).mp
  calc
    (dualCoordinateIso (dualGroup H)).hom ≫ (kH ≫ c) = dqH ≫ vH ≫ c := by
      simpa only [Category.assoc] using
        congrArg (fun t => t ≫ c) (dualCoordinateIso_bidualIso_hom H)
    _ = dqH ≫ ddc ≫ vG :=
      congrArg (fun t => dqH ≫ t) (hopfBidualIso_inv_naturality c)
    _ = dcd ≫ dqG ≫ vG := by
      simpa only [Category.assoc] using congrArg (fun t => t ≫ vG) hd.symm
    _ = dcd ≫ (dualCoordinateIso (dualGroup G)).hom ≫ kG :=
      congrArg (fun t => dcd ≫ t) (dualCoordinateIso_bidualIso_hom G).symm
    _ = (dualCoordinateIso (dualGroup H)).hom ≫
        coordinateMap (dualMap (dualMap f)) ≫ kG := by
      simpa only [Category.assoc] using
        congrArg (fun t => t ≫ kG) (dualCoordinateIso_naturality (dualMap f)).symm

variable (G)

/-- The original group bidual map satisfies the actual triple-dual triangle. -/
theorem bidualIso_hom_comp_dualMap :
    (bidualIso (dualGroup G)).hom ≫ dualMap (bidualIso G).hom = 𝟙 (dualGroup G) := by
  let kG := coordinateMap (bidualIso G).hom
  let kDG := coordinateMap (bidualIso (dualGroup G)).hom
  let dkG := CommHopfAlgCat.ofHom kG.hom.dual
  let dqDG := CommHopfAlgCat.ofHom (dualCoordinateIso (dualGroup G)).hom.hom.dual
  let vDG := (hopfBidualIso (coordinateHopf (dualGroup G))).inv
  have hd := congrArg
    (fun t : CommHopfAlgCat.of k (Dual k (coordinateHopf (dualGroup G))) ⟶
        coordinateHopf G => CommHopfAlgCat.ofHom t.hom.dual)
    (dualCoordinateIso_bidualIso_hom G)
  rw [CommHopfAlgCat.hom_comp, CommHopfAlgCat.hom_comp, CommHopfAlgCat.hom_ofHom,
    BialgHom.dual_comp, CommHopfAlgCat.ofHom_comp] at hd
  apply coordinateMap_injective (G := dualGroup G) (H := dualGroup G)
  rw [coordinateMap_comp, coordinateMap_id]
  apply (cancel_epi (dualCoordinateIso G).hom).mp
  rw [Category.comp_id]
  calc
    (dualCoordinateIso G).hom ≫ (coordinateMap (dualMap (bidualIso G).hom) ≫ kDG) =
        dkG ≫ (dualCoordinateIso (dualGroup (dualGroup G))).hom ≫ kDG := by
      simpa only [Category.assoc] using
        congrArg (fun t => t ≫ kDG) (dualCoordinateIso_naturality (bidualIso G).hom)
    _ = dkG ≫ dqDG ≫ vDG :=
      congrArg (fun t => dkG ≫ t) (dualCoordinateIso_bidualIso_hom (dualGroup G))
    _ = (dualCoordinateIso G).hom := by
      have h := congrArg (fun t => t ≫ vDG) hd
      have hclose := hopfBidualIso_dual_composite
        (A := coordinateHopf G) (B := coordinateHopf (dualGroup G)) (dualCoordinateIso G).hom
      have hfinal := h.trans hclose
      simpa only [Category.assoc] using hfinal

/-- Transposing the original bidual map gives the original inverse bidual map of the dual. -/
theorem dualMap_bidualIso_hom :
    dualMap (bidualIso G).hom = (bidualIso (dualGroup G)).inv := by
  apply (cancel_epi (bidualIso (dualGroup G)).hom).mp
  rw [bidualIso_hom_comp_dualMap G, Iso.hom_inv_id]

end AlgebraicGeometry.Scheme.Group.CartierDuality
