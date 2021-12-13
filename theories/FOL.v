Require Import EquivDec.
Require Import SetoidClass.

Set Primitive Projections.
Set Universe Polymorphism.

Axiom well_order : Type.
Axiom well_order_zero : well_order.
Axiom well_order_one : well_order.
Axiom well_order_succ : well_order -> well_order.
Axiom well_order_arbitrary_sum :
  forall (I : Type) (F : I -> well_order), well_order.

(** Propositional Languages *)
(* Def. 2.59 in “PT for Fuzzy L.” *)
  (* corresponds to the signature of an algebra (in the context of univ. algebra). *)
  Record PropType :=
    { connective : Type;
      connective_arity : connective -> Type; (* each connective has an arity *)
    }.
  (* Using the trick of Andrej Bauer
     https://gist.github.com/andrejbauer/3cc438ab38646516e5e9278fdb22022c
     of defining arity not via [nat] but via the amount of elements in a type.
  *)

  (* NOTE: The def. of [PropFormula] is identical to the definition of
  the term algebra in the context of univ. algebra. *)
Section PropositionalLanguage.
  Variables (L : PropType) (var : Type).

  (* The type [var] indexes the variables. *)
  Inductive PropFormula : Type :=
  | PF_var : var -> PropFormula
  | PF_connective (c : L.(connective)) (f : L.(connective_arity) c -> PropFormula) : PropFormula.

  Inductive PropFormula_eq : PropFormula -> PropFormula -> Prop :=
  | PF_eq_var v :
    PropFormula_eq (PF_var v) (PF_var v)
  | PF_eq_connective c f0 f1 :
    (forall i, PropFormula_eq (f0 i) (f1 i)) ->
    PropFormula_eq (PF_connective c f0) (PF_connective c f1).

  (* [A] is a subformula of [B] iff [subformula A B] *)
  Inductive subformula : PropFormula -> PropFormula -> Prop :=
  | subformula_refl A : subformula A A
  | subformula_compat A c (f : L.(connective_arity) c -> PropFormula) i :
    subformula A (f i) ->
    subformula A (PF_connective c f).

  (* Assigns each [PropFormula] a well-order, i.e. an ordinal. *)
  Fixpoint complexity (A : PropFormula) : well_order :=
    match A with
    | PF_var _ => well_order_one
    | PF_connective c f =>
        well_order_succ (well_order_arbitrary_sum
                           _ (fun i => complexity (f i)))
    end.

  Instance PropFormula_eq_Equivalence : Equivalence PropFormula_eq.
  Admitted.

  (* [EqDec_A] encapsulates that we "can do recursion" on
     [L.(connective_arity) c] for each [c]. But currently the
     statement is too strong. *)
  Lemma PropFormula_eqdec_unusable (EqDec_C : EqDec L.(connective) eq)
        (EqDec_A : forall c (f0 f1 : L.(connective_arity) c -> PropFormula),
            { forall i, f0 i === f1 i } + { ~ forall i, f0 i === f1 i })
        (EqDec_V : EqDec var eq)
    : EqDec PropFormula PropFormula_eq.
  Proof.
    red.
    induction x.
    - (* x = PF_var _ *)
      induction y.
      2: {
        right. intros ?.
        inversion H; subst; clear H.
      }
      specialize (EqDec_V v v0) as [|].
      + left. red in e. subst. constructor.
      + right. intros ?.
        inversion H; subst; clear H.
        red in c. congruence.
    - (* x = PF_connective _ _ *)
      induction y.
      { right. intros ?.
        inversion H; subst; clear H.
      }
      destruct (EqDec_C c c0) as [|].
      2: {
        right. intros ?.
        inversion H; subst; clear H.
        apply c1.
        reflexivity.
      }
      red in e. subst.
      specialize (EqDec_A c0 f f0) as [|].
      { left. constructor. assumption. }
      right. intros ?.
      red in H.
      apply n. intros.
      inversion H; subst; clear H.
      apply Eqdep_dec.inj_pair2_eq_dec in H2, H3; try assumption.
      subst.
      apply H1.
  Defined.
End PropositionalLanguage.

(* Claim: If for a [PropType] all connectives have an arity on which
one can do recursion (i.e. in "practice" at most countable) and [var]
has decidable equality (and some decidability or recursion on the type
[connective] of the signature), then [subformula] is
decidable. Equality is then probably also decidable. We can probably
show the converse as well. *)

Section SequentCalculus.
  (* A sequent calculus is determined by its language and its rules.
     It shall be possible to compare sequent calculi over the same language. *)
  (* How to best abstract what a rule is? *)
End SequentCalculus.

(*Section Classical_Propositional_Logic.*)
  (* This def. is too specific. Lift it to the more general system.
Inductive Formula : Set :=
| var (n : nat)
| not : Formula -> Formula
| and : Formula -> Formula -> Formula
| or : Formula -> Formula -> Formula
| impl : Formula -> Formula -> Formula.

*)
