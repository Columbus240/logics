(* MAYBE: Define a separate type for schematic rules to simplify using
   them? *)
(* MAYBE: Find an easy to use notation for rose trees. Maybe some one has
already written a library for these kinds of trees which I can use? Maybe for
another programming language? *)

Set Primitive Projections.
Set Universe Polymorphism.

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

Import ListNotations.

Require Import Program.Basics.

Definition DerivTree_root {C} : @DerivationTree C -> _ := compose fst RTree_root.

(* [Derivation] lives in [Prop], because once we have a derivation, it
   shouldn’t really matter "how" it was proven correct.
   The only things that appear here are [In] propositions, which
   should always (in this case) be (able to be) proof-irrelevant.
*)
Inductive Derivation {C : Calculus} (T : Ensemble C.(structures)) : DerivationTree C -> Prop :=
| Deriv_ax e : In _ T e -> Derivation T (RTree_cons (e, None) [])
| Deriv_rule (e : C.(structures)) (prem : list (DerivationTree C)) r :
  ForallT (Derivation T) prem ->
  In _ (C.(rules_inferences) r) {| premises := map DerivTree_root prem;
           conclusion := e
         |} ->
  Derivation T (RTree_cons (e, Some r) prem).

Definition Derivable {C : Calculus} (T : Ensemble C.(structures)) (e : C.(structures)) : Type :=
  { D : DerivationTree C | Derivation T D /\ DerivTree_root D = e }.

Definition CalculusDecidableTautologies (C : Calculus) :=
  forall s : C.(structures),
    Derivable (Empty_set _) s + (Derivable (Empty_set _) s -> False).

Definition CalculusDecidable (C : Calculus) :=
  forall
    (T : Ensemble C.(structures))
    (Tdec : forall x, {In _ T x} + {~ In _ T x})
    (s : C.(structures)),
    Derivable T s + (Derivable T s -> False).

Fact CalculusDecidable_impl_DecidableTautologies (C : Calculus) :
  CalculusDecidable C -> CalculusDecidableTautologies C.
Proof.
  intros.
  red; red in X.
  apply X.
  intros.
  right.
  intros ?.
  destruct H.
Defined.

(* If the set of axioms [T] and the set of rules are decidable, then
   we can decide whether a given tree is a [Derivation T] or not. *)
Lemma Derivation_dec {C : Calculus} (T : Ensemble C.(structures)) (D : DerivationTree C)
      (T_dec : forall e, { In _ T e } + { ~ In _ T e })
      (R_dec : forall e l r, { In _ (C.(rules_inferences) r) {| premises := map DerivTree_root l;
                                                             conclusion := e |} } +
                             { ~ In _ (C.(rules_inferences) r) {| premises := map DerivTree_root l;
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
    inversion H; subst; clear H.
    { apply f.
      constructor.
    }
    auto.
  }
  destruct a as [a [|]].
  - (* Rule *)
    pose proof (R_dec a l) as [|].
    { left. apply Deriv_rule with (r0 := r);
        eassumption.
    }
    right.
    intros ?.
    inversion H; subst; clear H.
    contradiction.
  - (* Axiom *)
    destruct l.
    2: {
      right.
      intros ?.
      inversion H; subst; clear H.
    }
    destruct (T_dec a).
    + left.
      constructor.
      assumption.
    + right.
      intros ?.
      inversion H; subst; clear H; try contradiction.
Defined.

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
  clear H0.
  induction X.
  { constructor. }
  constructor.
  { eapply Derivable_monotonous;
      eauto.
  }
  assumption.
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
    clear H.
    induction X.
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
  clear H.
  induction X.
  { constructor. }
  constructor.
  - apply (Derivable_compactness_list_correct_1 _ _ a) in p.
    eapply Derivable_monotonous; try eassumption.
    intros ? ?.
    red. simpl.
    rewrite in_app_iff.
    left. assumption.
  - eapply ForallT_impl.
    2: { apply IHX. }
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

(* Extend a given calculus [C] with an additional set of rules. *)
Definition CE_RuleExtension (C : Calculus)
           {r : Type} (r_inf : r -> _)
  : Calculus :=
  {|
    structures := C.(structures);
    rules := C.(rules) + r;
    rules_inferences :=
    fun r0 =>
      match r0 with
      | inl r0 => C.(rules_inferences) r0
      | inr r0 => r_inf r0
      end;
  |}.

Lemma map_id {A : Type} (l : list A) :
  map id l = l.
Proof.
  induction l.
  - reflexivity.
  - simpl.
    unfold id at 1.
    congruence.
Qed.

Program Definition CE_RuleExtension_Extension (C : Calculus) {r} (r_inf : r -> _) :
  CalculusExtension C (CE_RuleExtension C r_inf) :=
  {|
    CE_structure := id;
    CE_rules := inl;
  |}.
Next Obligation.
  intros ? ?.
  inversion H; subst; clear H.
  rewrite map_id.
  unfold id.
  assumption.
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
      clear H X r.
      induction prem.
      { simpl. reflexivity. }
      simpl.
      inversion IHprem; subst; clear IHprem.
      rewrite H0.
      rewrite CE_DerivationTree_DerivTree_root.
      reflexivity.
    }
    clear r H.
    apply ForallT_map0.
    induction X.
    { constructor. }
    constructor.
    2: assumption.
    clear IHX.
    apply CE_Derivation.
    assumption.
  Defined.
End CalculusExtension.
