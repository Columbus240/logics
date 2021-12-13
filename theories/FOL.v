(* Possible TODO: Split this file into the following files:
   - Theory of Rose Trees
   - General theory of calculi
   - Definition of a propositional/algebraic language

   Maybe fix the algorithm that checks validity of a derivation.
 *)

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

(** Section: Inferences. *)
Record Inference (S : Type) :=
  { premises : list S;
    conclusion : S
  }.

Arguments premises {_} _.
Arguments conclusion {_} _.

Require Import Ensembles.

Record Calculus :=
  { structures : Type;
    rules : Type;
    rules_inferences : rules -> Ensemble (Inference structures);
  }.

Require Import Logics.Utils.

Definition DerivationTree (C : Calculus) : Type :=
  RTree (C.(structures) * option C.(rules)).

Require Import List.
Import Ensembles.

Definition RTree_root {A : Type} (t : RTree A) : A :=
  match t with
  | RTree_cons e _ => e
  end.

Import ListNotations.

Require Import Program.Basics.

Definition DerivTree_root {C} : @DerivationTree C -> _ := compose fst RTree_root.

Inductive Derivation {C : Calculus} (T : Ensemble C.(structures)) : DerivationTree C -> Type :=
| Deriv_ax e : In _ T e -> Derivation T (RTree_cons (e, None) [])
| Deriv_rule (e : C.(structures)) (prem : list (DerivationTree C)) r :
  ForallT (Derivation T) prem ->
  In _ (C.(rules_inferences) r) {| premises := map DerivTree_root prem;
           conclusion := e
         |} ->
  Derivation T (RTree_cons (e, Some r) prem).

Definition Derivable {C : Calculus} (T : Ensemble C.(structures)) (e : C.(structures)) : Prop :=
  exists (D : DerivationTree C), inhabited (Derivation T D) /\ DerivTree_root D = e.

Fixpoint RTForallT_True {A : Type} t :
  RTForallT (fun _ : A => True) t.
Proof.
  induction t.
  induction l.
  { constructor.
    constructor.
  }
  constructor.
  { apply RTForallT_True. }
  assumption.
Defined.

Lemma RTForallT_forall {A : Type} (P : A -> Type) :
  (forall a : A, P a) ->
  forall t, RTForallT P t.
Proof.
  intros.
  apply RTree_rect0 with (Q := (fun _ => True)).
  2: {
    apply RTForallT_True.
  }
  intros.
  induction X0; constructor; auto.
Qed.

Lemma ForallT_dec {A : Type} (P : A -> Type) :
  (forall a : A, P a + (P a -> False)) ->
  forall l, ForallT P l + (ForallT P l -> False).
Proof.
Admitted.

Lemma ForallT_dec_lift {A : Type} (P : A -> Type) l :
  ForallT (fun D => (P D) + (P D -> False))%type l ->
  ForallT P l + (ForallT P l -> False).
Proof.
  intros.
  induction X.
  { left. constructor. }
  destruct p.
  2: {
    right.
    intros.
    inversion X0; subst; clear X0.
    contradiction.
  }
  destruct IHX.
  - left. constructor; assumption.
  - right. intros.
    inversion X0; subst; clear X0.
    contradiction.
Qed.

(*
(* If the set of axioms [T] and the set of rules are decidable, then
   we can decide whether a given tree is a [Derivation T] or not. *)
Lemma Derivation_dec {C : Calculus} (T : Ensemble C.(structures)) (D : DerivationTree C)
      (T_dec : forall e, { In _ T e } + { ~ In _ T e })
      (R_dec : forall e l, { r | In _ C.(rules) r /\
                                   In _ r {| premises := map RTree_root l;
                                            conclusion := e |} } +
                             { forall r, In _ C.(rules) r ->
                                         ~ In _ r {| premises := map RTree_root l;
                                                    conclusion := e |} }) :
  Derivation T D + ( Derivation T D -> False ).
Proof.
  apply (RTree_rect0 (fun D => Derivation T D + ( Derivation T D -> False ))%type
                     (fun _ => True)).
  2: {
    apply RTForallT_True.
  }
  intros.
  clear H.
  assert (ForallT (Derivation T) l + (ForallT (Derivation T) l -> False)).
  { apply ForallT_dec_lift.
    induction X.
    { constructor. }
    constructor; try assumption.
  }
  clear X.
  destruct X0.
  2: {
    right.
    intros ?.
    inversion X; subst; clear X.
    { apply f.
      constructor.
    }
    auto.
  }
  pose proof (R_dec a l) as [|].
  { left. destruct s as [r []].
    apply Deriv_rule with (r0 := r);
      assumption.
  }
  destruct l.
  2: {
    right.
    intros ?.
    inversion X; subst; clear X.
    eapply n; eauto.
  }
  destruct (T_dec a).
  - left.
    constructor.
    assumption.
  - right.
    intros ?.
    inversion X; subst; clear X; try contradiction.
    eapply n; eauto.
Defined.
*)

(* Prop. 3.7a in “PT for FL” *)
Fixpoint Derivable_monotonous {C} {T0 T1 : Ensemble C.(structures)}
  (H : Included _ T0 T1) D (HD : Derivation T0 D) : Derivation T1 D.
Proof.
  induction HD.
  { constructor.
    apply H.
    assumption.
  }
  constructor; auto.
  clear i.
  induction f.
  { constructor. }
  constructor.
  { eapply Derivable_monotonous;
      eauto.
  }
  assumption.
Defined.

Fixpoint ForallT_map {A : Type} {P : A -> Type} {Q : A -> Type} (f : forall a, P a -> Q a)
      (l : list A) (H : ForallT P l) :
  list { a & { b : P a & Q a } } :=
  match H with
  | ForallT_nil _ => []
  | ForallT_cons _ a l Ha Hl => (existT _ a (existT _ Ha (f a Ha))) :: (ForallT_map f l Hl)
  end.

Lemma ForallT_impl {A : Type} {P Q : A -> Type} :
  (forall a, P a -> Q a) ->
  forall l,
    ForallT P l ->
    ForallT Q l.
Proof.
  intros.
  induction X0; constructor; auto.
Defined.

Fixpoint Derivable_compactness_list {C} (D : DerivationTree C) : list C.(structures) :=
  match D with
  | RTree_cons (a, None) _ => [a]
  | RTree_cons (_, Some _) l =>
      concat (map Derivable_compactness_list l)
  end.

Fixpoint Derivable_compactness_list_correct_0 {C T} D (HD : @Derivation C T D) :
  Forall (In _ T) (Derivable_compactness_list D).
Proof.
  induction HD.
  - simpl.
    repeat constructor.
    assumption.
  - simpl.
    rewrite Forall_concat.
    rewrite Forall_map.
    clear i.
    induction f.
    { constructor. }
    constructor.
    2: { assumption. }
    apply Derivable_compactness_list_correct_0.
    assumption.
Defined.

Fixpoint Derivable_compactness_list_correct_1 {C T} D (HD : @Derivation C T D) :
  Derivation (fun p => List.In p (Derivable_compactness_list D)) D.
Proof.
  induction HD.
  { simpl.
    repeat constructor.
  }
  constructor; try assumption.
  clear i.
  induction f.
  { constructor. }
  constructor.
  - apply (Derivable_compactness_list_correct_1 _ _ a) in p.
    eapply Derivable_monotonous; try eassumption.
    intros ? ?.
    red. simpl.
    rewrite in_app_iff.
    left. assumption.
  - eapply ForallT_impl.
    2: { apply IHf. }
    apply Derivable_monotonous.
    intros ? ?.
    red. simpl.
    rewrite in_app_iff.
    right. assumption.
Defined.

Definition RuleDerivable (C : Calculus) (r : Ensemble (Inference C.(structures))) :=
  forall i,
   In _ r i ->
   @Derivable C (fun p => List.In p i.(premises)) i.(conclusion).

Definition RuleAdmissible (C : Calculus) (r : Ensemble (Inference C.(structures))) :=
  forall i,
    In _ r i ->
    ForallT (@Derivable C (Empty_set _)) i.(premises) ->
    Derivable (Empty_set _) i.(conclusion).

Definition RuleInvertible (C : Calculus) (r : Ensemble (Inference C.(structures))) :=
  forall i,
    In _ r i ->
    Derivable (Empty_set _) i.(conclusion) ->
    ForallT (@Derivable C (Empty_set _)) i.(premises).

Require Import Image.

(* [C0] is extended by [C1]. Injectivity is stated here, because it
   seems the natural way to model set inclusion in texts.

   The compatibility rule is stated with [Included] instead of
   [Same_set], because when the language is extended, then new
   instances of rules shall be able to appear.
*)
Record CalculusExtension (C0 C1 : Calculus) :=
  { CE_structure : C0.(structures) -> C1.(structures);
    CE_structure_inj :
    forall x y, CE_structure x = CE_structure y -> x = y;
    CE_rules : C0.(rules) -> C1.(rules);
    CE_rules_inj :
    forall x y, CE_rules x = CE_rules y -> x = y;
    CE_rules_compat :
    forall x, Included _
                       (Im _ _ (C0.(rules_inferences) x)
                           (fun r => {| premises := map CE_structure r.(premises);
                                       conclusion := CE_structure r.(conclusion);
                                     |}))
                       (C1.(rules_inferences) (CE_rules x));
  }.

Arguments CE_structure {_} {_} _.
Arguments CE_rules {_} {_} _.

Lemma ForallT_map0 {A B : Type} (f : A -> B) (P : B -> Type) (l : list A) :
  ForallT (fun x : A => P (f x)) l ->
  ForallT P (map f l).
Proof.
  intros.
  induction X.
  { constructor. }
  simpl.
  constructor; assumption.
Qed.

Section CalculusExtension.
  (* The extension of a calculus preserves derivations. *)
  Context {C0 C1 : Calculus}.
  Variable (CE : CalculusExtension C0 C1).

  Fixpoint CE_DerivationTree (D : DerivationTree C0) : DerivationTree C1 :=
    match D with
    | RTree_cons (a, o) l =>
        RTree_cons (CE.(CE_structure) a, option_map CE.(CE_rules) o)
                   (map CE_DerivationTree l)
    end.

  Lemma CE_DerivationTree_DerivTree_root D :
    DerivTree_root (CE_DerivationTree D) = CE.(CE_structure) (DerivTree_root D).
  Proof.
    unfold DerivTree_root.
    unfold RTree_root.
    unfold CE_DerivationTree.
    unfold compose.
    induction D.
    destruct a.
    simpl.
    reflexivity.
  Qed.

  Fixpoint CE_Derivation T D (HD : Derivation T D) :
    Derivation
      (Im _ _ T CE.(CE_structure))
      (CE_DerivationTree D).
  Proof.
    induction HD.
    { constructor.
      exists e; auto.
    }
    constructor.
    2: {
      apply CE_rules_compat.
      rewrite map_map.
      eexists; try eassumption.
      simpl.
      clear i f r.
      induction prem.
      { simpl. reflexivity. }
      simpl.
      inversion IHprem; subst; clear IHprem.
      rewrite H0.
      rewrite CE_DerivationTree_DerivTree_root.
      reflexivity.
    }
    clear r i.
    apply ForallT_map0.
    induction f.
    { constructor. }
    constructor.
    2: assumption.
    clear IHf.
    apply CE_Derivation.
    assumption.
  Defined.
End CalculusExtension.

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
