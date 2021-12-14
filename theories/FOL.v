Require Import EquivDec.
Require Import SetoidClass.

Require Import Calculi.

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

Definition Equinumerous (A B : Type) :=
  { p : (A -> B) * (B -> A) |
    (forall x, (fst p) (snd p x) = x) /\
      (forall x, (snd p) (fst p x) = x) }.

(* [P0] is extended by [P1] *)
Record PropTypeExtension (P0 P1 : PropType) :=
  {
    PTE_connective : P0.(connective) -> P1.(connective);
    PTE_connective_inj : forall x y,
      PTE_connective x = PTE_connective y -> x = y;
    PTE_connective_arity :
    forall x, Equinumerous (P0.(connective_arity) x)
                           (P1.(connective_arity) (PTE_connective x));
  }.

  (* NOTE: The def. of [PropFormula] is identical to the definition of
  the term algebra in the context of univ. algebra. *)
Section PropositionalLanguage.
  Variables (L : PropType) (var : Type).
  (* Necessary for making [PropFormula_eq] (provably) transitive,
     without having to assume proof-irrelevance or somesuch. *)
  Context `{Lc_dec : EqDec L.(connective) eq}.

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

  Instance PropFormula_eq_Refl : Reflexive PropFormula_eq.
  Proof.
    red; intros.
    induction x; constructor; assumption.
  Qed.

  Instance PropFormula_eq_Sym : Symmetric PropFormula_eq.
  Proof.
    red; intros.
    induction H; constructor; assumption.
  Qed.

  Instance PropFormula_eq_Equivalence : Equivalence PropFormula_eq.
  Proof.
    split; try typeclasses eauto.
    red; intros.
    revert z H0.
    induction H; intros z Hz; inversion Hz; subst; clear Hz.
    { constructor. }
    apply Eqdep_dec.inj_pair2_eq_dec in H3.
    2: { assumption. }
    subst.
    constructor.
    auto.
  Qed.

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

  Definition PropHilbertCalculus
             {rules : Type} (rules_inferences : rules -> _) : Calculus :=
    {|
      structures := PropFormula;
      rules := rules;
      rules_inferences := rules_inferences;
    |}.
End PropositionalLanguage.

Variant impl_neg :=
| impl | neg.

Definition impl_neg_Sig :=
  {| connective := impl_neg;
    connective_arity :=
    fun p =>
      match p with
      | impl => unit + unit
      | neg => unit
      end%type;
  |}.

Definition INS_neg {var} (A : PropFormula impl_neg_Sig var) :
  PropFormula impl_neg_Sig var :=
  PF_connective
    impl_neg_Sig var neg
    (fun _ => A).

Definition INS_impl {var} (A B : PropFormula impl_neg_Sig var) :
  PropFormula impl_neg_Sig var :=
  PF_connective
    impl_neg_Sig var impl
    (fun p =>
       match p with
       | inl _ => A
       | inr _ => B
       end).

Definition HCPC_CL1 {var} (A B : PropFormula impl_neg_Sig var)
  : PropFormula impl_neg_Sig var :=
  INS_impl A (INS_impl B A).

Definition HCPC_CL2 {var} (A B C : PropFormula impl_neg_Sig var)
  : PropFormula impl_neg_Sig var :=
  INS_impl (INS_impl A (INS_impl B C))
           (INS_impl (INS_impl A B) (INS_impl A C)).

Definition HCPC_CL3 {var} (A B : PropFormula impl_neg_Sig var)
  : PropFormula impl_neg_Sig var :=
  INS_impl
    (INS_impl (INS_neg A)
              (INS_neg B))
    (INS_impl B A).

Require Import List.
Import ListNotations.

Definition INS_MP {var} A B :
  Inference (PropFormula impl_neg_Sig var) :=
  {|
    premises := [A; INS_impl A B];
    conclusion := B
  |}.

Definition Inference_Axiom {S} (A : S) : Inference S :=
  {|
    premises := [];
    conclusion := A;
  |}.

Variant HCPC_rules :=
  HCPCr_CL1 | HCPCr_CL2 | HCPCr_CL3 | HCPCr_MP.

Definition HCPC : Calculus :=
  PropHilbertCalculus
    impl_neg_Sig
    nat
    (fun r : HCPC_rules =>
       match r with
       | HCPCr_MP =>
           (fun p => exists A B, p = INS_MP A B)
       | HCPCr_CL1 =>
           (fun p => exists A B, p = Inference_Axiom (HCPC_CL1 A B))
       | HCPCr_CL3 =>
           (fun p => exists A B, p = Inference_Axiom (HCPC_CL3 A B))
       | HCPCr_CL2 => (fun p => exists A B C, p = Inference_Axiom (HCPC_CL2 A B C))
       end).

Require Import Ensembles.

Fact HCPC_impl_refl A :
  @Derivable HCPC (Empty_set _) (INS_impl A A).
Proof.
  unshelve eexists.
  - constructor.
    { split.
      2: apply (Some HCPCr_MP).
      apply (INS_impl A A).
    }
    refine [_; _].
    + constructor.
      2: apply nil.
      split.
      2: apply (Some HCPCr_CL1).
      apply (INS_impl A (INS_impl A A)).
    + constructor.
      { split.
        { apply (INS_impl
                   (INS_impl A (INS_impl A A))
                   (INS_impl A A)).
        }
        apply (Some HCPCr_MP).
      }
      refine [_;_].
      * constructor.
        2: apply nil.
        split.
        2: apply (Some HCPCr_CL1).
        apply (INS_impl
                 A
                 (INS_impl
                    (INS_impl A A)
                    A)).
      * constructor.
        2: apply nil.
        split.
        2: apply (Some HCPCr_CL2).
        apply (INS_impl
                 (INS_impl
                    A
                    (INS_impl
                       (INS_impl A A)
                       A))
                 (INS_impl
                    (INS_impl A (INS_impl A A))
                    (INS_impl A A))).
  - split.
    2: reflexivity.
    repeat constructor; red; simpl.
    + eexists _, _.
      reflexivity.
    + eexists _, _.
      reflexivity.
    + eexists _, _, _. reflexivity.
    + eexists _, _. reflexivity.
    + eexists _, _. reflexivity.
Qed.

Section PropositionalHilbertCalculus.
End PropositionalHilbertCalculus.
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
