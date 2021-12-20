Require Import EquivDec.
Require Import SetoidClass.
Require Import RelationClasses.

Require Import Calculi.

Set Primitive Projections.
Set Universe Polymorphism.
Set Default Goal Selector "!".

Axiom well_order : Type.
Axiom well_order_zero : well_order.
Axiom well_order_one : well_order.
Axiom well_order_succ : well_order -> well_order.
Axiom well_order_arbitrary_sum :
  forall (I : Type) (F : I -> well_order), well_order.

Require Import Category.Instance.Algebra.

(** Propositional Languages *)
(* Def. 2.59 in “PT for Fuzzy L.” *)
  (* corresponds to the signature of an algebra (in the context of univ. algebra). *)
Definition PropType := Signature.
  (* Using the trick of Andrej Bauer
     https://gist.github.com/andrejbauer/3cc438ab38646516e5e9278fdb22022c
     of defining arity not via [nat] but via the amount of elements in a type.
  *)

Definition Equinumerous (A B : Type) :=
  { p : (A -> B) * (B -> A) |
    (forall x, (fst p) (snd p x) = x) /\
      (forall x, (snd p) (fst p x) = x) }.

Require Import Category.Theory.Isomorphism.
Import Category.Instance.Coq.

(* [P0] is extended by [P1] *)
Record PropTypeExtension (P0 P1 : PropType) :=
  {
    PTE_connective : P0.(operations) -> P1.(operations);
    PTE_connective_inj : forall x y,
      PTE_connective x = PTE_connective y -> x = y;
    PTE_connective_arity :
    forall x, (op_arity x) ≅[Coq] (op_arity (PTE_connective x));
  }.

Arguments term_atom {_} {_} _.
Arguments term_op {_} {_} _ _.

  (* NOTE: The def. of [PropFormula] is identical to the definition of
  the term algebra in the context of univ. algebra. *)
Section PropositionalLanguage.
  Variables (L : PropType) (var : Type).
  (* Necessary for making [PropFormula_eq] (provably) transitive,
     without having to assume proof-irrelevance or somesuch. *)
  Context `{Lc_dec : EqDec L.(operations) eq}.

  (* The type [var] indexes the variables. *)
  Definition PropFormula := @Terms L var.

  (* [A] is a subformula of [B] iff [subformula A B] *)
  Inductive subformula : PropFormula -> PropFormula -> Prop :=
  | subformula_refl A : subformula A A
  | subformula_compat A c (f : op_arity c -> PropFormula) i :
    subformula A (f i) ->
    subformula A (term_op c f).

  (* Assigns each [PropFormula] a well-order, i.e. an ordinal. *)
  Fixpoint complexity (A : PropFormula) : well_order :=
    match A with
    | term_atom _ => well_order_one
    | term_op c f =>
        well_order_succ (well_order_arbitrary_sum
                           _ (fun i => complexity (f i)))
    end.

  Import Category.Lib.Setoid.
  Existing Instance Algebra.Terms_Setoid.

  (* Add well-founded recursion on the complexity to complete this.
     And a sufficient condition on each [op_arity o]. *)
  Fixpoint Terms_equiv_EqDec
        (EqDec_C : EqDec L.(operations) eq)
        (EqDec_V : EqDec var eq)
    (x y : Terms var) :
    (x ≈ y) + ( x ≈ y -> Empty_set ).
  Proof.
    refine (
    match x, y with
    | term_atom v0, term_atom v1 =>
        if EqDec_V v0 v1 then
          inl _
        else
          inr _
    | term_op c0 f0, term_op c1 f1 =>
        if EqDec_C c0 c1 then
          _
        else
          inr _
    | term_atom _, term_op _ _ => inr _
    | term_op _ _, term_atom _ => inr _
    end).
    - red in e. subst.
      constructor.
    - intros.
      red in c.
      inversion X; subst; clear X.
      unshelve epose proof (c _). { reflexivity. }
      contradiction.
    - intros.
      inversion X; subst; clear X.
    - intros.
      inversion X; subst; clear X.
    - inversion e; subst; clear e.
      assert ((forall i, f0 i ≈ f1 i) + ((forall i, f0 i ≈ f1 i) -> Empty_set)).
      { (* TODO: Add a recursion here. somehow. *)
        admit.
      }
      destruct X; [left|right].
      + constructor. assumption.
      + intros.
        inversion X; subst; clear X.
        apply Eqdep_dec.inj_pair2_eq_dec in H, H1; try assumption.
        subst. auto.
    - intros.
      inversion X; subst; clear X.
      apply Eqdep_dec.inj_pair2_eq_dec in H1, H3; try assumption.
      subst.
      unshelve epose proof (c _). { reflexivity. }
      contradiction.
  Admitted.

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

(* MAYBE: There are multiple ways to do sequent calculus: using lists
   or using multisets or using sets. We could formalize all of these
   and provide "bridge" theorems between them. I.e. a sequent calculus
   using sets has contraction as a multiset calculus and a multiset
   calculus has exchange as a list calculus.
*)

(* MAYBE: Define boolean algebras and use this to give a semantics to
   classical logic *)

(*Section Classical_Propositional_Logic.*)
  (* This def. is too specific. Lift it to the more general system.
Inductive Formula : Set :=
| var (n : nat)
| not : Formula -> Formula
| and : Formula -> Formula -> Formula
| or : Formula -> Formula -> Formula
| impl : Formula -> Formula -> Formula.

*)

Variant BA_Connectives :=
| BA_and | BA_or | BA_neg | BA_bot | BA_top.

Let Empty := Datatypes.Empty_set.

Definition BooleanAlgebraSig : PropType :=
  {|
    connective := BA_Connectives;
    connective_arity :=
    fun c =>
      match c with
      | BA_and => unit + unit
      | BA_or => unit + unit
      | BA_neg => unit
      | BA_bot => Empty
      | BA_top => Empty
      end%type;
|}.

Record FOLanguage :=
  { FOL_predicate : Type;
    FOL_predicate_arity : FOL_predicate -> Type;
    FOL_function : Type;
    FOL_function_arity : FOL_function -> Type;
    FOL_connective : Type;
    FOL_connective_arity : FOL_connective -> Type;
  }.

Section FirstOrderLanguage.
  Variables (L : FOLanguage) (var : Type).
  Context `{Lf_dec : EqDec L.(FOL_function) eq}.
  Context `{Lp_dec : EqDec L.(FOL_predicate) eq}.
  Context `{Lc_dec : EqDec L.(FOL_connective) eq}.

  Inductive FOLTerm : Type :=
  | FOL_Tvar : var -> FOLTerm
  | FOL_Tfun (f : L.(FOL_function)) (a : L.(FOL_function_arity) f -> FOLTerm) : FOLTerm.

  Inductive FOLTerm_eq : FOLTerm -> FOLTerm -> Prop :=
  | FOLT_eq_var v :
    FOLTerm_eq (FOL_Tvar v) (FOL_Tvar v)
  | FOLT_eq_fun f a0 a1 :
    (forall i, FOLTerm_eq (a0 i) (a1 i)) ->
    FOLTerm_eq (FOL_Tfun f a0) (FOL_Tfun f a1).

  Instance FOLTerm_eq_Refl : Reflexive FOLTerm_eq.
  Proof.
    red; intros.
    induction x; constructor; assumption.
  Qed.

  Instance FOLTerm_eq_Sym : Symmetric FOLTerm_eq.
  Proof.
    red; intros.
    induction H; constructor; assumption.
  Qed.

  Instance FOLTerm_eq_Equivalence : Equivalence FOLTerm_eq.
  Proof.
    split; try typeclasses eauto.
    red; intros.
    revert z H0.
    induction H; intros z Hz; inversion Hz; subst; clear Hz.
    { constructor. }
    apply Eqdep_dec.inj_pair2_eq_dec in H3.
    2: assumption.
    subst. constructor. auto.
  Qed.

  (* First-order language with equality. *)
  Inductive FOLFormula : Type :=
  | FOL_eq : FOLTerm -> FOLTerm -> FOLFormula
  | FOL_pred (p : L.(FOL_predicate)) (t : L.(FOL_predicate_arity) p -> FOLTerm) : FOLFormula
  | FOL_conn (c : L.(FOL_connective)) (f : L.(FOL_connective_arity) c -> FOLFormula) : FOLFormula
  | FOL_all : var -> FOLFormula -> FOLFormula
  | FOL_ex : var -> FOLFormula -> FOLFormula.

  Inductive FOLFormula_eq : FOLFormula -> FOLFormula -> Prop :=
  | FOL_eq_eq t00 t01 t10 t11 :
    FOLTerm_eq t00 t10 ->
    FOLTerm_eq t01 t11 ->
    FOLFormula_eq (FOL_eq t00 t01) (FOL_eq t10 t11)
  | FOL_eq_pred p t0 t1 :
    (forall i, FOLTerm_eq (t0 i) (t1 i)) ->
    FOLFormula_eq (FOL_pred p t0) (FOL_pred p t1)
  | FOL_eq_conn c f0 f1 :
    (forall i, FOLFormula_eq (f0 i) (f1 i)) ->
    FOLFormula_eq (FOL_conn c f0) (FOL_conn c f1)
  | FOL_eq_all v f0 f1 :
    FOLFormula_eq f0 f1 ->
    FOLFormula_eq (FOL_all v f0) (FOL_all v f1)
  | FOL_eq_ex v f0 f1 :
    FOLFormula_eq f0 f1 ->
    FOLFormula_eq (FOL_ex v f0) (FOL_ex v f1).

  Instance FOLFormula_eq_Refl : Reflexive FOLFormula_eq.
  Proof using.
    red; intros.
    induction x; constructor; try assumption; reflexivity.
  Qed.

  Instance FOLFormula_eq_Symm : Symmetric FOLFormula_eq.
  Proof using.
    red; intros.
    induction H; constructor; try assumption;
      intros; symmetry; auto.
  Qed.

  Instance FOLFormula_eq_Equivalence : Equivalence FOLFormula_eq.
  Proof using Lc_dec Lf_dec Lp_dec.
    split; try typeclasses eauto.
    red; intros.
    revert z H0.
    induction H; intros z Hz; inversion Hz; subst; clear Hz;
      constructor; auto.
    - (* FOL_eq *)
      transitivity t10; assumption.
    - (* FOL_eq *)
      transitivity t11; assumption.
    - (* FOL_pred *)
      apply Eqdep_dec.inj_pair2_eq_dec in H2.
      2: assumption.
      subst. intros.
      transitivity (t1 i); auto.
    - (* FOL_conn *)
      apply Eqdep_dec.inj_pair2_eq_dec in H3.
      2: assumption.
      subst. intros. apply H0.
      auto.
  Qed.
End FirstOrderLanguage.
