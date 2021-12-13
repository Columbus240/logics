Inductive ForallT {A : Type} (P : A -> Type) : list A -> Type :=
| ForallT_nil : ForallT P nil
| ForallT_cons a l :
  P a -> ForallT P l ->
  ForallT P (cons a l).

(* A non-empty rose-tree. If empty rose-trees are necessary, use
   [option] of this type, or add a nil constructor. (These two
   approaches yield different results.) *)
Inductive RTree (A : Type) : Type :=
| RTree_cons : A -> list (RTree A) -> RTree A.

Arguments RTree_cons {_} _ _.

Require Import List.
Import ListNotations.

Inductive RTForallT {A : Type} (P : A -> Type) : RTree A -> Type :=
| RTF_nil a :
  P a -> RTForallT P (RTree_cons a [])
| RTF_cons a l b :
  RTForallT P b ->
  RTForallT P (RTree_cons a l) ->
  RTForallT P (RTree_cons a (b :: l)).

Lemma RTForallT_inv_root A P a l :
  @RTForallT A P (RTree_cons a l) ->
  P a.
Proof.
  intros.
  induction l.
  { inversion X; subst; clear X.
    assumption.
  }
  inversion X; subst; clear X.
  auto.
Qed.

Lemma RTForallT_inv_list A P a l :
  @RTForallT A P (RTree_cons a l) ->
  ForallT (RTForallT P) l.
Proof.
  intros.
  induction l.
  { constructor. }
  constructor.
  { inversion X; subst; clear X.
    assumption.
  }
  inversion X; subst; clear X.
  auto.
Qed.

Inductive RTForallT0 {A : Type} (P : A -> Type) : RTree A -> Type :=
| RTF0_cons (a : A) (l : list (RTree A)) :
  P a -> ForallT (RTForallT0 P) l ->
  RTForallT0 P (RTree_cons a l).

Lemma RTForallT0_complete {A : Type} (P : A -> Type) t :
  RTForallT P t -> RTForallT0 P t.
Proof.
  intros.
  induction X.
  { constructor; try assumption.
    constructor.
  }
  inversion IHX2; subst; clear IHX2.
  constructor; try assumption.
  constructor; try assumption.
Qed.

Section RTree_rect.
  Context {A : Type}.
  Variable (P : RTree A -> Type).
  Variable (Q : A -> Type).

  Hypothesis Hcons :
    forall (a : A) (l : list (RTree A)),
      Q a -> ForallT P l ->
      P (RTree_cons a l).

  Fixpoint RTree_rect1 (t : RTree A) (H : RTForallT0 Q t) : P t.
  Proof.
    intros.
    induction H.
    apply Hcons; try assumption.
    induction f; constructor.
    { now apply RTree_rect1. }
    assumption.
  Defined.

  Corollary RTree_rect0 (t : RTree A) (H : RTForallT Q t) : P t.
  Proof.
    apply RTree_rect1.
    apply RTForallT0_complete.
    assumption.
  Defined.
End RTree_rect.
