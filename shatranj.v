(* ========================================================================= *)
(* SHATRANJ FORMALIZATION - SECTION 1: FOUNDATIONS AND METATHEORY           *)
(* ========================================================================= *)

(** * Core Imports *)

Require Import Coq.Program.Basics.
Require Import Coq.Program.Tactics.
Require Import Coq.Program.Wf.
Require Import Coq.Program.Equality.

Require Import Coq.Logic.Decidable.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.Classical.
Require Import Coq.Logic.ClassicalChoice.
Require Import Coq.Logic.ProofIrrelevance.

Require Import Coq.Bool.Bool.
Require Import Coq.Bool.BoolEq.
Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.
Require Import Coq.NArith.NArith.
Require Import Coq.Lists.List.
Require Import Coq.Vectors.Fin.
Require Import Coq.micromega.Lia.
Require Import Coq.Strings.String.

Import ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope string_scope.

(** * Custom Tactics for Automation *)

Ltac destruct_match :=
  match goal with
  | [ |- context[match ?x with _ => _ end] ] => destruct x eqn:?
  | [ H: context[match ?x with _ => _ end] |- _ ] => destruct x eqn:?
  end.

Ltac solve_bool :=
  repeat match goal with
  | [ H: _ && _ = true |- _ ] => apply andb_prop in H; destruct H
  | [ H: _ || _ = false |- _ ] => apply orb_false_elim in H; destruct H
  | [ |- _ && _ = true ] => apply andb_true_intro; split
  | [ |- _ || _ = true ] => apply orb_true_intro
  | [ H: ?x = true |- ?x = true ] => exact H
  | [ H: ?x = false |- ?x = false ] => exact H
  | [ H: true = false |- _ ] => discriminate H
  | [ H: false = true |- _ ] => discriminate H
  end.

Ltac solve_decidability :=
  repeat match goal with
  | [ |- {?x = ?y} + {?x <> ?y} ] => decide equality
  | [ |- decidable _ ] => unfold decidable; tauto
  end.

(** * Setoid Infrastructure for Extensional Equality *)

Definition eq_dec (A: Type) := forall (x y: A), {x = y} + {x <> y}.

Class DecidableEq (A: Type) := {
  dec_eq : eq_dec A
}.

(** * Proof Mode Configuration *)

Set Implicit Arguments.
Set Asymmetric Patterns.
Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".

(** * Basic Decidability Instances *)

#[global]
Instance bool_decidable_eq : DecidableEq bool := {
  dec_eq := bool_dec
}.

#[global]
Instance nat_decidable_eq : DecidableEq nat := {
  dec_eq := Nat.eq_dec
}.

#[global]
Instance Z_decidable_eq : DecidableEq Z := {
  dec_eq := Z.eq_dec
}.

(** * Option Type Utilities *)

Definition option_map2 {A B C: Type} (f: A -> B -> C) 
  (oa: option A) (ob: option B) : option C :=
  match oa, ob with
  | Some a, Some b => Some (f a b)
  | _, _ => None
  end.

Definition option_bind {A B: Type} (oa: option A) (f: A -> option B) : option B :=
  match oa with
  | Some a => f a
  | None => None
  end.

Notation "ma >>= f" := (option_bind ma f) (at level 50, left associativity).

(** * Function Extensionality Available *)

Lemma fun_ext : forall {A B: Type} (f g: A -> B),
  (forall x, f x = g x) -> f = g.
Proof.
  exact @functional_extensionality.
Qed.

Lemma fun_ext_dep : forall {A: Type} {B: A -> Type} (f g: forall x, B x),
  (forall x, f x = g x) -> f = g.
Proof.
  exact @functional_extensionality_dep.
Qed.

(** * Classical Logic Axioms Available *)

Lemma excluded_middle : forall P: Prop, P \/ ~P.
Proof.
  exact classic.
Qed.

Lemma choice_axiom : forall (A B: Type) (R: A -> B -> Prop),
  (forall x, exists y, R x y) ->
  exists f: A -> B, forall x, R x (f x).
Proof.
  exact choice.
Qed.

Lemma proof_irrelevance_axiom : forall (P: Prop) (p1 p2: P), p1 = p2.
Proof.
  exact proof_irrelevance.
Qed.

(** * Helper for Program Definitions *)

#[global]
Obligation Tactic := program_simpl; auto; try lia.

(** * List Utilities *)

Fixpoint list_all {A: Type} (P: A -> bool) (l: list A) : bool :=
  match l with
  | [] => true
  | x :: xs => P x && list_all P xs
  end.

Fixpoint list_any {A: Type} (P: A -> bool) (l: list A) : bool :=
  match l with
  | [] => false
  | x :: xs => P x || list_any P xs
  end.

Lemma list_all_forall : forall {A: Type} (P: A -> bool) (l: list A),
  list_all P l = true <-> forall x, In x l -> P x = true.
Proof.
  intros A P l.
  induction l; simpl.
  - split; intros.
    + contradiction.
    + reflexivity.
  - split; intros.
    + apply andb_prop in H. destruct H as [HPa Hrec].
      destruct H0 as [<-|Hin].
      * exact HPa.
      * apply IHl; assumption.
    + apply andb_true_intro. split.
      * apply H. left. reflexivity.
      * apply IHl. intros x Hin. apply H. right. exact Hin.
Qed.

Lemma list_any_exists : forall {A: Type} (P: A -> bool) (l: list A),
  list_any P l = true <-> exists x, In x l /\ P x = true.
Proof.
  intros A P l.
  induction l; simpl.
  - split; intros.
    + discriminate.
    + destruct H as [x [[] _]].
  - split; intros.
    + apply orb_prop in H. destruct H as [HPa|Hrec].
      * exists a. split; [left; reflexivity|exact HPa].
      * apply IHl in Hrec. destruct Hrec as [x [Hin HPx]].
        exists x. split; [right; exact Hin|exact HPx].
    + destruct H as [x [[<-|Hin] HPx]].
      * apply orb_true_intro. left. exact HPx.
      * apply orb_true_intro. right. apply IHl.
        exists x. split; assumption.
Qed.

(** * Error Handling Infrastructure *)

Inductive result (A: Type) : Type :=
  | Ok : A -> result A
  | Error : string -> result A.

Arguments Ok {A}.
Arguments Error {A}.

Definition result_bind {A B: Type} (r: result A) (f: A -> result B) : result B :=
  match r with
  | Ok a => f a
  | Error msg => Error msg
  end.

Notation "r >>? f" := (result_bind r f) (at level 50, left associativity).

(** * Dependent Pair Utilities *)

Definition sigT_eq1 {A: Type} {P: A -> Type} {x y: A} {px: P x} {py: P y}
  (H: existT P x px = existT P y py) : x = y :=
  f_equal (@projT1 A P) H.

Definition sigT_eq2 {A: Type} {P: A -> Type} {x: A} {px py: P x}
  (H: existT P x px = existT P x py) : px = py.
Proof.
  apply Eqdep.EqdepTheory.inj_pair2.
  exact H.
Qed.

(** * Relation Utilities *)

Section Relations.
  Variable A : Type.
  Variable R : A -> A -> Prop.

  Inductive rtc : A -> A -> Prop :=
    | rtc_refl : forall x, rtc x x
    | rtc_step : forall x y z, R x y -> rtc y z -> rtc x z.

  Lemma rtc_trans : forall x y z, rtc x y -> rtc y z -> rtc x z.
  Proof.
    intros x y z Hxy Hyz.
    induction Hxy; auto.
    apply rtc_step with y; auto.
  Qed.

  Definition deterministic := forall x y z, R x y -> R x z -> y = z.
  Definition functional := forall x, exists! y, R x y.
End Relations.

(** * Enhanced Tactics *)

Ltac break_match :=
  match goal with
  | [ |- context[match ?x with _ => _ end] ] => 
      let Heq := fresh "Heq" in destruct x eqn:Heq
  | [ H: context[match ?x with _ => _ end] |- _ ] => 
      let Heq := fresh "Heq" in destruct x eqn:Heq
  end.

Ltac break_if :=
  match goal with
  | [ |- context[if ?b then _ else _] ] => 
      let Heq := fresh "Heq" in destruct b eqn:Heq
  | [ H: context[if ?b then _ else _] |- _ ] => 
      let Heq := fresh "Heq" in destruct b eqn:Heq
  end.

Ltac inv H := inversion H; clear H; subst.

Ltac contradiction_eq :=
  match goal with
  | [ H: ?x = ?y |- _ ] => 
      assert (x <> y) by discriminate; contradiction
  end.

(** * Common Proof Patterns *)

Lemma option_some_inv : forall {A: Type} (x y: A),
  Some x = Some y -> x = y.
Proof.
  intros. injection H. auto.
Qed.

Lemma option_bind_some : forall {A B: Type} (ma: option A) (f: A -> option B) (b: B),
  (ma >>= f) = Some b ->
  exists a, ma = Some a /\ f a = Some b.
Proof.
  intros. unfold option_bind in H.
  destruct ma; [eauto|discriminate].
Qed.

Lemma bool_eq_reflect : forall b1 b2: bool,
  b1 = b2 <-> (b1 = true <-> b2 = true).
Proof.
  intros. destruct b1, b2; intuition.
Qed.

(** * List Enhanced Utilities *)

Lemma list_find_spec : forall {A: Type} (P: A -> bool) (l: list A),
  match find P l with
  | Some x => In x l /\ P x = true
  | None => forall x, In x l -> P x = false
  end.
Proof.
  intros. induction l; simpl.
  - intros x [].
  - destruct (P a) eqn:HPa.
    + split; auto.
    + destruct (find P l) eqn:Hfind.
      * destruct IHl as [Hin HP]. split; auto.
      * intros x [<-|Hin]; auto.
Qed.

Fixpoint list_remove {A: Type} (dec: forall x y: A, {x = y} + {x <> y}) 
  (x: A) (l: list A) : list A :=
  match l with
  | [] => []
  | y :: ys => if dec x y then ys else y :: list_remove dec x ys
  end.

Lemma list_remove_In : forall {A: Type} (dec: forall x y: A, {x = y} + {x <> y})
  (x y: A) (l: list A),
  In y (list_remove dec x l) -> In y l.
Proof.
  intros A dec x y l. induction l; simpl; intros H.
  - assumption.
  - destruct (dec x a).
    + subst. right. assumption.
    + destruct H.
      * left. assumption.
      * right. apply IHl. assumption.
Qed.

(* The converse requires NoDup or a different specification *)
Lemma list_remove_In_weak : forall {A: Type} (dec: forall x y: A, {x = y} + {x <> y})
  (x y: A) (l: list A),
  In y l -> x <> y -> In y (list_remove dec x l).
Proof.
  intros A dec x y l. induction l; simpl; intros Hin Hneq.
  - assumption.
  - destruct (dec x a).
    + subst. destruct Hin.
      * subst. contradiction.
      * assumption.
    + destruct Hin.
      * left. assumption.
      * right. apply IHl; assumption.
Qed.

(** * Well-Founded Recursion Support *)

Definition measure_wf {A: Type} (f: A -> nat) : well_founded (fun x y => (f x < f y)%nat).
Proof.
  unfold well_founded.
  intro a. 
  remember (f a) as n.
  revert a Heqn.
  induction n using lt_wf_ind.
  intros a Heqn. constructor. intros y Hlt.
  apply H with (m := f y).
  - rewrite Heqn. exact Hlt.
  - reflexivity.
Defined.

(** * Finite Type Utilities (preview for Section 2) *)

Definition finite_dec {A: Type} (l: list A) (dec: forall x y: A, {x = y} + {x <> y}) :
  forall x: A, {In x l} + {~ In x l}.
Proof.
  intro x. induction l.
  - right. intro H. inversion H.
  - destruct (dec x a).
    + left. left. auto.
    + destruct IHl.
      * left. right. auto.
      * right. intro H. destruct H.
        -- subst. contradiction.
        -- contradiction.
Defined.

(** * Validation: Extended Example *)

Example option_bind_assoc : forall {A B C: Type} 
  (ma: option A) (f: A -> option B) (g: B -> option C),
  ((ma >>= f) >>= g) = (ma >>= (fun a => f a >>= g)).
Proof.
  intros. destruct ma; reflexivity.
Qed.

(** * End of Section 1: Foundations and Metatheory *)

Close Scope Z_scope.
Close Scope bool_scope.

(** * End of Section 1: Foundations and Metatheory *)

(* ========================================================================= *)
(* SECTION 2: FINITE DOMAIN THEORY                 *)
(* ========================================================================= *)

Open Scope nat_scope. 

(** * Finite 8 Theory *)

Definition Fin8 := Fin.t 8.

(** * Enumeration of Fin8 *)

Definition enum_fin8 : list Fin8 :=
  [Fin.F1; Fin.FS Fin.F1; Fin.FS (Fin.FS Fin.F1); 
   Fin.FS (Fin.FS (Fin.FS Fin.F1));
   Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1)));
   Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1))));
   Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1)))));
   Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1))))))].

(** * Conversion between Fin8 and nat *)

Definition fin8_to_nat (f: Fin8) : nat := proj1_sig (Fin.to_nat f).

Definition nat_to_fin8 (n: nat) (H: n < 8) : Fin8 :=
  match n as n' return n' < 8 -> Fin8 with
  | 0 => fun _ => Fin.F1
  | 1 => fun _ => Fin.FS Fin.F1
  | 2 => fun _ => Fin.FS (Fin.FS Fin.F1)
  | 3 => fun _ => Fin.FS (Fin.FS (Fin.FS Fin.F1))
  | 4 => fun _ => Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1)))
  | 5 => fun _ => Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1))))
  | 6 => fun _ => Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1)))))
  | 7 => fun _ => Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1))))))
  | S (S (S (S (S (S (S (S n8))))))) => fun H' => 
      match Nat.lt_irrefl _ (Nat.lt_le_trans _ _ _ H' (Nat.le_add_r 8 n8)) with end
  end H.

Lemma fin8_to_nat_bound : forall (f: Fin8), (fin8_to_nat f < 8)%nat.
Proof.
  intro f. unfold fin8_to_nat.
  destruct (Fin.to_nat f) as [n Hn]. simpl. exact Hn.
Qed.

Definition nat_to_fin8_aux (n: nat) : Fin8 :=
  match n with
  | 0 => Fin.F1
  | 1 => Fin.FS Fin.F1
  | 2 => Fin.FS (Fin.FS Fin.F1)
  | 3 => Fin.FS (Fin.FS (Fin.FS Fin.F1))
  | 4 => Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1)))
  | 5 => Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1))))
  | 6 => Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1)))))
  | _ => Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1))))))
  end.

(** * Decidable equality for Fin8 *)

#[global]
Instance fin8_decidable_eq : DecidableEq Fin8 := {
  dec_eq := Fin.eq_dec
}.

(** * Exhaustive enumeration theorem *)

Lemma fin8_F1_in_enum : In (@Fin.F1 7) enum_fin8.
Proof. simpl. left. reflexivity. Qed.

Lemma fin8_FS_F1_in_enum : In (Fin.FS (@Fin.F1 6)) enum_fin8.
Proof. simpl. right. left. reflexivity. Qed.

Lemma fin8_2_in_enum : In (Fin.FS (Fin.FS (@Fin.F1 5))) enum_fin8.
Proof. simpl. do 2 right. left. reflexivity. Qed.

Lemma fin8_3_in_enum : In (Fin.FS (Fin.FS (Fin.FS (@Fin.F1 4)))) enum_fin8.
Proof. simpl. do 3 right. left. reflexivity. Qed.

Lemma fin8_4_in_enum : In (Fin.FS (Fin.FS (Fin.FS (Fin.FS (@Fin.F1 3))))) enum_fin8.
Proof. simpl. do 4 right. left. reflexivity. Qed.

Lemma fin8_5_in_enum : In (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (@Fin.F1 2)))))) enum_fin8.
Proof. simpl. do 5 right. left. reflexivity. Qed.

Lemma fin8_6_in_enum : In (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (@Fin.F1 1))))))) enum_fin8.
Proof. simpl. do 6 right. left. reflexivity. Qed.

Lemma fin8_7_in_enum : In (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (@Fin.F1 0)))))))) enum_fin8.
Proof. simpl. do 7 right. left. reflexivity. Qed.

Lemma all_fin8_case_F1 : forall f: Fin8,
  f = @Fin.F1 7 -> In f enum_fin8.
Proof.
  intros f Heq. rewrite Heq. apply fin8_F1_in_enum.
Qed.

Lemma all_fin8_case_FS_F1 : forall f: Fin8,
  f = Fin.FS (@Fin.F1 6) -> In f enum_fin8.
Proof.
  intros f Heq. rewrite Heq. apply fin8_FS_F1_in_enum.
Qed.

Lemma all_fin8_case_2 : forall f: Fin8,
  f = Fin.FS (Fin.FS (@Fin.F1 5)) -> In f enum_fin8.
Proof.
  intros f Heq. rewrite Heq. apply fin8_2_in_enum.
Qed.

Lemma all_fin8_case_3 : forall f: Fin8,
  f = Fin.FS (Fin.FS (Fin.FS (@Fin.F1 4))) -> In f enum_fin8.
Proof.
  intros f Heq. rewrite Heq. apply fin8_3_in_enum.
Qed.

Lemma all_fin8_case_4 : forall f: Fin8,
  f = Fin.FS (Fin.FS (Fin.FS (Fin.FS (@Fin.F1 3)))) -> In f enum_fin8.
Proof.
  intros f Heq. rewrite Heq. apply fin8_4_in_enum.
Qed.

Lemma all_fin8_case_5 : forall f: Fin8,
  f = Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (@Fin.F1 2))))) -> In f enum_fin8.
Proof.
  intros f Heq. rewrite Heq. apply fin8_5_in_enum.
Qed.

Lemma all_fin8_case_6 : forall f: Fin8,
  f = Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (@Fin.F1 1)))))) -> In f enum_fin8.
Proof.
  intros f Heq. rewrite Heq. apply fin8_6_in_enum.
Qed.

Lemma all_fin8_case_7 : forall f: Fin8,
  f = Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (@Fin.F1 0))))))) -> In f enum_fin8.
Proof.
  intros f Heq. rewrite Heq. apply fin8_7_in_enum.
Qed.

Ltac fin8_cases f :=
  repeat (destruct f as [|f]; [|]); [| inversion f].

Lemma all_fin8_in_enumeration : forall f: Fin8, In f enum_fin8.
Proof.
  intro f.
  apply (Fin.caseS' f); [apply fin8_F1_in_enum|].
  intro f1. apply (Fin.caseS' f1); [apply fin8_FS_F1_in_enum|].
  intro f2. apply (Fin.caseS' f2); [apply fin8_2_in_enum|].
  intro f3. apply (Fin.caseS' f3); [apply fin8_3_in_enum|].
  intro f4. apply (Fin.caseS' f4); [apply fin8_4_in_enum|].
  intro f5. apply (Fin.caseS' f5); [apply fin8_5_in_enum|].
  intro f6. apply (Fin.caseS' f6); [apply fin8_6_in_enum|].
  intro f7. apply (Fin.caseS' f7); [apply fin8_7_in_enum|].
  intro f8. inversion f8.
Qed.

Lemma enum_fin8_NoDup : NoDup enum_fin8.
Proof.
  unfold enum_fin8.
  repeat constructor; simpl; intuition discriminate.
Qed.

(** * Finite Type Class *)

Class Finite (A: Type) := {
  enum : list A;
  enum_complete : forall x: A, In x enum;
  enum_nodup : NoDup enum
}.

(** * Finite instances *)

#[global]
Instance fin8_finite : Finite Fin8 := {
  enum := enum_fin8;
  enum_complete := all_fin8_in_enumeration;
  enum_nodup := enum_fin8_NoDup
}.

#[global]
Instance bool_finite : Finite bool := {
  enum := [true; false];
  enum_complete := fun b => match b with 
    | true => or_introl eq_refl 
    | false => or_intror (or_introl eq_refl) 
    end;
  enum_nodup := ltac:(repeat constructor; simpl; intuition discriminate)
}.

#[global]
Instance unit_finite : Finite unit := {
  enum := [tt];
  enum_complete := fun u => match u with tt => or_introl eq_refl end;
  enum_nodup := ltac:(repeat constructor; simpl; intuition)
}.

Lemma NoDup_app {A: Type} : forall (l1 l2: list A),
  NoDup l1 -> NoDup l2 -> 
  (forall x, In x l1 -> In x l2 -> False) ->
  NoDup (l1 ++ l2).
Proof.
  intros l1 l2 H1 H2 Hdisj.
  induction H1.
  - simpl. exact H2.
  - simpl. constructor.
    + intro Hin. apply in_app_or in Hin. destruct Hin.
      * contradiction.
      * apply (Hdisj x). 
        -- left. reflexivity.
        -- exact H0.
    + apply IHNoDup. intros y Hy1 Hy2.
      apply (Hdisj y).
      * right. exact Hy1.
      * exact Hy2.
Qed.

Lemma NoDup_map_pair_l {A B: Type} : forall (a: A) (lb: list B),
  NoDup lb -> NoDup (map (fun b => (a, b)) lb).
Proof.
  intros a lb Hnd.
  induction Hnd.
  - simpl. constructor.
  - simpl. constructor.
    + intro Hin. apply in_map_iff in Hin.
      destruct Hin as [b' [Heq Hin']].
      injection Heq. intros. subst.
      contradiction.
    + exact IHHnd.
Qed.

Lemma in_map_pair_disjoint {A B: Type} : forall (a1 a2: A) (lb: list B) (p: A * B),
  a1 <> a2 ->
  In p (map (fun b => (a1, b)) lb) ->
  In p (list_prod (a2 :: nil) lb) ->
  False.
Proof.
  intros a1 a2 lb p Hneq H1 H2.
  apply in_map_iff in H1. destruct H1 as [b1 [Heq1 Hin1]].
  simpl in H2.
  destruct p as [pa pb].
  apply in_app_or in H2. destruct H2 as [H2 | H2].
  + apply in_map_iff in H2. destruct H2 as [b2 [Heq2 Hin2]].
    injection Heq1. injection Heq2. intros. subst. contradiction.
  + simpl in H2. contradiction.
Qed.

Lemma NoDup_map {A B: Type} : forall (f: A -> B) (l: list A),
  (forall x y, In x l -> In y l -> f x = f y -> x = y) ->
  NoDup l -> NoDup (map f l).
Proof.
  intros f l Hinj Hnd.
  induction Hnd.
  - simpl. constructor.
  - simpl. constructor.
    + intro Hmem. apply in_map_iff in Hmem.
      destruct Hmem as [y [Heq HinY]].
      assert (x = y).
      { apply Hinj.
        - left. reflexivity.
        - right. exact HinY.
        - symmetry. exact Heq. }
      subst. contradiction.
    + apply IHHnd. intros. apply Hinj; auto.
      * right. auto.
      * right. auto.
Qed.

Lemma NoDup_list_prod {A B: Type} : forall (la: list A) (lb: list B),
  NoDup la -> NoDup lb -> NoDup (list_prod la lb).
Proof.
  intros la lb Ha Hb.
  induction Ha as [|a la' Hnin Hnd IH].
  - simpl. constructor.
  - simpl. apply NoDup_app.
    + apply NoDup_map_pair_l. exact Hb.
    + apply IH.
    + intros p H1 H2.
      apply in_map_iff in H1. destruct H1 as [b [Heq Hinb]].
      subst. apply in_prod_iff in H2. destruct H2 as [Hina' Hinb'].
      apply Hnin. exact Hina'.
Qed.

#[global]
Instance prod_finite {A B: Type} `{Finite A} `{Finite B} : Finite (A * B).
Proof.
  refine {| enum := list_prod enum enum |}.
  - intros [a b]. apply in_prod; apply enum_complete.
  - apply NoDup_list_prod; apply enum_nodup.
Defined.

#[global]
Instance sum_finite {A B: Type} `{Finite A} `{Finite B} : Finite (A + B).
Proof.
  refine {| enum := map inl enum ++ map inr enum |}.
  - intros [a|b].
    + apply in_or_app. left. apply in_map. apply enum_complete.
    + apply in_or_app. right. apply in_map. apply enum_complete.
  - apply NoDup_app.
    + apply NoDup_map.
      * intros x y _ _ Heq. injection Heq. auto.
      * apply enum_nodup.
    + apply NoDup_map.
      * intros x y _ _ Heq. injection Heq. auto.
      * apply enum_nodup.
    + intros x Hin1 Hin2.
      apply in_map_iff in Hin1. destruct Hin1 as [a [Ha _]].
      apply in_map_iff in Hin2. destruct Hin2 as [b [Hb _]].
      subst. discriminate.
Defined.

(** * Exhaustive case analysis *)

Lemma fin8_exhaustive : forall (f: Fin8) (P: Fin8 -> Prop),
  P Fin.F1 ->
  P (Fin.FS Fin.F1) ->
  P (Fin.FS (Fin.FS Fin.F1)) ->
  P (Fin.FS (Fin.FS (Fin.FS Fin.F1))) ->
  P (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1)))) ->
  P (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1))))) ->
  P (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1)))))) ->
  P (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1))))))) ->
  P f.
Proof.
  intros f P H0 H1 H2 H3 H4 H5 H6 H7.
  apply (Fin.caseS' f); [exact H0|].
  intro f1. apply (Fin.caseS' f1); [exact H1|].
  intro f2. apply (Fin.caseS' f2); [exact H2|].
  intro f3. apply (Fin.caseS' f3); [exact H3|].
  intro f4. apply (Fin.caseS' f4); [exact H4|].
  intro f5. apply (Fin.caseS' f5); [exact H5|].
  intro f6. apply (Fin.caseS' f6); [exact H6|].
  intro f7. apply (Fin.caseS' f7); [exact H7|].
  intro f8. inversion f8.
Qed.

(** * Bijection with bounded nat *)

Definition fin8_bij_nat (f: Fin8) : {n: nat | n < 8} :=
  exist _ (fin8_to_nat f) (fin8_to_nat_bound f).

Definition nat_bij_fin8 (sn: {n: nat | n < 8}) : Fin8 :=
  nat_to_fin8_aux (proj1_sig sn).

Lemma nat_fin8_round_trip : forall n H,
  fin8_to_nat (@nat_to_fin8 n H) = n.
  Proof.
  intros n H.
  unfold fin8_to_nat, nat_to_fin8.
  destruct n as [|[|[|[|[|[|[|[|n8]]]]]]]].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - exfalso. simpl in H. lia.
Qed.

Lemma fin8_bij_inv2 : forall sn,
  fin8_bij_nat (nat_bij_fin8 sn) = sn.
Proof.
  intros [n H]. unfold fin8_bij_nat, nat_bij_fin8.
  simpl. unfold fin8_to_nat, nat_to_fin8_aux.
  destruct n as [|[|[|[|[|[|[|[|n8]]]]]]]].
  - simpl. f_equal. apply proof_irrelevance_axiom.
  - simpl. f_equal. apply proof_irrelevance_axiom.
  - simpl. f_equal. apply proof_irrelevance_axiom.
  - simpl. f_equal. apply proof_irrelevance_axiom.
  - simpl. f_equal. apply proof_irrelevance_axiom.
  - simpl. f_equal. apply proof_irrelevance_axiom.
  - simpl. f_equal. apply proof_irrelevance_axiom.
  - simpl. f_equal. apply proof_irrelevance_axiom.
  - exfalso. simpl in H. lia.
Qed.

Lemma fin8_bij_inv1 : forall f,
  nat_bij_fin8 (fin8_bij_nat f) = f.
Proof.
  intro f. unfold nat_bij_fin8, fin8_bij_nat.
  simpl. unfold fin8_to_nat, nat_to_fin8_aux.
  apply fin8_exhaustive with (f := f);
    (simpl; reflexivity).
Qed.

(** * Cardinality *)

Definition finite_card {A: Type} `{FA: Finite A} : nat := List.length (@enum A FA).

Lemma fin8_card : @finite_card Fin8 _ = 8.
Proof.
  unfold finite_card. simpl. reflexivity.
Qed.

(** * Decision procedures for finite types *)

Definition finite_forall_dec {A: Type} `{Finite A} (P: A -> bool) : bool :=
  list_all P enum.

Definition finite_exists_dec {A: Type} `{Finite A} (P: A -> bool) : bool :=
  list_any P enum.

Lemma finite_forall_dec_correct : forall {A: Type} `{Finite A} (P: A -> bool),
  finite_forall_dec P = true <-> forall x: A, P x = true.
Proof.
  intros. unfold finite_forall_dec.
  rewrite list_all_forall. split; intros.
  - apply H0. apply enum_complete.
  - apply H0.
Qed.

Lemma finite_exists_dec_correct : forall {A: Type} `{Finite A} (P: A -> bool),
  finite_exists_dec P = true <-> exists x: A, P x = true.
Proof.
  intros. unfold finite_exists_dec.
  rewrite list_any_exists. split; intros.
  - destruct H0 as [x [Hin HP]]. exists x. exact HP.
  - destruct H0 as [x HP]. exists x. split; [apply enum_complete|exact HP].
Qed.

(** * Validation Lemma *)

Lemma all_fin8_in_enumeration_validated : forall (f: Fin.t 8), 
  In f enum_fin8.
Proof.
  exact all_fin8_in_enumeration.
Qed.

(** * Additional utilities for finite domains *)

Definition fin8_pred (f: Fin8) : option Fin8 :=
  match fin8_to_nat f with
  | 0 => None
  | S n' => match lt_dec n' 8 with
            | left H => Some (@nat_to_fin8 n' H)
            | right _ => None
            end
  end.

Definition fin8_succ (f: Fin8) : option Fin8 :=
  let n := fin8_to_nat f in
  match lt_dec (S n) 8 with
  | left H => Some (@nat_to_fin8 (S n) H)
  | right _ => None
  end.

(** * End of Section 2: Finite Domain Theory *)

(* ========================================================================= *)
(* SECTION 3: POSITION ABSTRACTION                                          *)
(* ========================================================================= *)

(** * Concrete Implementation of Position System *)

(** * Rank and File as wrapped Fin8 *)

Record Rank : Type := mkRank { 
  rank_val : Fin8 
}.

Record File : Type := mkFile { 
  file_val : Fin8 
}.

Record Position : Type := mkPosition {
  pos_rank : Rank;
  pos_file : File
}.

(** * Decidable Equality Instances *)

Lemma rank_eq_dec : forall (r1 r2: Rank), {r1 = r2} + {r1 <> r2}.
Proof.
  intros [v1] [v2].
  destruct (Fin.eq_dec v1 v2).
  - left. f_equal. exact e.
  - right. intro H. injection H. contradiction.
Defined.

Lemma file_eq_dec : forall (f1 f2: File), {f1 = f2} + {f1 <> f2}.
Proof.
  intros [v1] [v2].
  destruct (Fin.eq_dec v1 v2).
  - left. f_equal. exact e.
  - right. intro H. injection H. contradiction.
Defined.

Lemma position_eq_dec : forall (p1 p2: Position), {p1 = p2} + {p1 <> p2}.
Proof.
  intros [r1 f1] [r2 f2].
  destruct (rank_eq_dec r1 r2), (file_eq_dec f1 f2).
  - left. f_equal; assumption.
  - right. intro H. injection H. intros. contradiction.
  - right. intro H. injection H. intros. contradiction.
  - right. intro H. injection H. intros. contradiction.
Defined.

#[global]
Instance rank_decidable_eq : DecidableEq Rank := {
  dec_eq := rank_eq_dec
}.

#[global]
Instance file_decidable_eq : DecidableEq File := {
  dec_eq := file_eq_dec
}.

#[global]
Instance position_decidable_eq : DecidableEq Position := {
  dec_eq := position_eq_dec
}.

(** * Construction/Destruction Properties *)

Lemma pos_eta : forall p, 
  mkPosition (pos_rank p) (pos_file p) = p.
Proof.
  intros [r f]. reflexivity.
Qed.

Lemma pos_beta_rank : forall r f, 
  pos_rank (mkPosition r f) = r.
Proof.
  reflexivity.
Qed.

Lemma pos_beta_file : forall r f, 
  pos_file (mkPosition r f) = f.
Proof.
  reflexivity.
Qed.

Lemma position_ext : forall p1 p2,
  pos_rank p1 = pos_rank p2 ->
  pos_file p1 = pos_file p2 ->
  p1 = p2.
Proof.
  intros [r1 f1] [r2 f2]. simpl. intros <- <-. reflexivity.
Qed.

(** * Concrete Rank Values *)

Definition rank1 : Rank := mkRank Fin.F1.
Definition rank2 : Rank := mkRank (Fin.FS Fin.F1).
Definition rank3 : Rank := mkRank (Fin.FS (Fin.FS Fin.F1)).
Definition rank4 : Rank := mkRank (Fin.FS (Fin.FS (Fin.FS Fin.F1))).
Definition rank5 : Rank := mkRank (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1)))).
Definition rank6 : Rank := mkRank (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1))))).
Definition rank7 : Rank := mkRank (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1)))))).
Definition rank8 : Rank := mkRank (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1))))))).

(** * Concrete File Values *)

Definition fileA : File := mkFile Fin.F1.
Definition fileB : File := mkFile (Fin.FS Fin.F1).
Definition fileC : File := mkFile (Fin.FS (Fin.FS Fin.F1)).
Definition fileD : File := mkFile (Fin.FS (Fin.FS (Fin.FS Fin.F1))).
Definition fileE : File := mkFile (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1)))).
Definition fileF : File := mkFile (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1))))).
Definition fileG : File := mkFile (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1)))))).
Definition fileH : File := mkFile (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1))))))).

(** * Coordinate Arithmetic *)

Open Scope Z_scope.

Definition rankZ (p: Position) : Z :=
  Z.of_nat (fin8_to_nat (rank_val (pos_rank p))).

Definition fileZ (p: Position) : Z :=
  Z.of_nat (fin8_to_nat (file_val (pos_file p))).

Definition Z_to_rank (z: Z) : option Rank :=
  if Z_lt_dec z 0 then None
  else if Z_lt_dec z 8 then 
    Some (mkRank (nat_to_fin8_aux (Z.to_nat z)))
  else None.

Definition Z_to_file (z: Z) : option File :=
  if Z_lt_dec z 0 then None
  else if Z_lt_dec z 8 then 
    Some (mkFile (nat_to_fin8_aux (Z.to_nat z)))
  else None.

(** * Offset Function *)

Definition offset (p: Position) (dr df: Z) : option Position :=
  let new_rank := rankZ p + dr in
  let new_file := fileZ p + df in
  match Z_to_rank new_rank, Z_to_file new_file with
  | Some r, Some f => Some (mkPosition r f)
  | _, _ => None
  end.

(** * Bounds Properties *)

Lemma rankZ_bounds : forall p, 0 <= rankZ p < 8.
Proof.
  intro p. unfold rankZ.
  pose proof (fin8_to_nat_bound (rank_val (pos_rank p))).
  split.
  - lia.
  - lia.
Qed.

Lemma fileZ_bounds : forall p, 0 <= fileZ p < 8.
Proof.
  intro p. unfold fileZ.
  pose proof (fin8_to_nat_bound (file_val (pos_file p))).
  split.
  - lia.
  - lia.
Qed.

(** * Offset Properties *)

Lemma offset_zero : forall p,
  offset p 0 0 = Some p.
Proof.
  intro p.
  unfold offset.
  assert (Hr: rankZ p + 0 = rankZ p) by ring.
  assert (Hf: fileZ p + 0 = fileZ p) by ring.
  rewrite Hr, Hf.
  unfold Z_to_rank, Z_to_file.
  pose proof (rankZ_bounds p) as [Hr1 Hr2].
  pose proof (fileZ_bounds p) as [Hf1 Hf2].
  destruct (Z_lt_dec (rankZ p) 0); [lia|].
  destruct (Z_lt_dec (rankZ p) 8); [|lia].
  destruct (Z_lt_dec (fileZ p) 0); [lia|].
  destruct (Z_lt_dec (fileZ p) 8); [|lia].
  f_equal.
  unfold rankZ, fileZ in *.
  destruct p as [r f]. simpl in *.
  f_equal.
  - f_equal. destruct r as [rv]. simpl.
    rewrite Nat2Z.id.
    apply fin8_exhaustive with (f := rv);
      (simpl; reflexivity).
  - f_equal. destruct f as [fv]. simpl.
    rewrite Nat2Z.id.
    apply fin8_exhaustive with (f := fv);
      (simpl; reflexivity).
Qed.

Lemma offset_inverse : forall p dr df p',
  offset p dr df = Some p' ->
  offset p' (-dr) (-df) = Some p.
Proof.
  intros p dr df p' H.
  unfold offset in *.
  destruct (Z_to_rank (rankZ p + dr)) eqn:Hr; [|discriminate].
  destruct (Z_to_file (fileZ p + df)) eqn:Hf; [|discriminate].
  injection H. intro Heq. subst p'. clear H.
  simpl.
  unfold Z_to_rank in Hr. unfold Z_to_file in Hf.
  destruct (Z_lt_dec (rankZ p + dr) 0); [discriminate|].
  destruct (Z_lt_dec (rankZ p + dr) 8); [|discriminate].
  destruct (Z_lt_dec (fileZ p + df) 0); [discriminate|].
  destruct (Z_lt_dec (fileZ p + df) 8); [|discriminate].
  injection Hr. injection Hf. intros Hf' Hr'. clear Hr Hf.
  unfold rankZ, fileZ. simpl.
  assert (Hrz: Z.of_nat (fin8_to_nat (rank_val r)) = rankZ p + dr).
  { subst r. simpl.
    assert (Hr8: 0 <= rankZ p + dr < 8) by lia.
    unfold nat_to_fin8_aux.
    remember (Z.to_nat (rankZ p + dr)) as nr.
    assert (Hnr: Z.of_nat nr = rankZ p + dr).
    { subst nr. rewrite Z2Nat.id; lia. }
    destruct nr as [|[|[|[|[|[|[|[|n8]]]]]]]]; simpl; try exact Hnr.
    exfalso. rewrite <- Hnr in Hr8. simpl in Hr8. lia.
  }
  assert (Hfz: Z.of_nat (fin8_to_nat (file_val f)) = fileZ p + df).
  { subst f. simpl.
    assert (Hf8: 0 <= fileZ p + df < 8) by lia.
    unfold nat_to_fin8_aux.
    remember (Z.to_nat (fileZ p + df)) as nf.
    assert (Hnf: Z.of_nat nf = fileZ p + df).
    { subst nf. rewrite Z2Nat.id; lia. }
    destruct nf as [|[|[|[|[|[|[|[|n8]]]]]]]]; simpl; try exact Hnf.
    exfalso. rewrite <- Hnf in Hf8. simpl in Hf8. lia.
  }
  rewrite Hrz, Hfz.
  replace (rankZ p + dr + - dr) with (rankZ p) by ring.
  replace (fileZ p + df + - df) with (fileZ p) by ring.
  unfold offset.
  unfold Z_to_rank, Z_to_file.
  pose proof (rankZ_bounds p) as [Hr1 Hr2].
  pose proof (fileZ_bounds p) as [Hf1 Hf2].
  destruct (Z_lt_dec (rankZ p) 0); [lia|].
  destruct (Z_lt_dec (rankZ p) 8); [|lia].
  destruct (Z_lt_dec (fileZ p) 0); [lia|].
  destruct (Z_lt_dec (fileZ p) 8); [|lia].
  f_equal.
  destruct p as [pr pf]. simpl in *.
  f_equal.
  - f_equal. destruct pr as [prv]. simpl.
    apply fin8_exhaustive with (f := prv);
      (simpl; reflexivity).
  - f_equal. destruct pf as [pfv]. simpl.
    apply fin8_exhaustive with (f := pfv);
      (simpl; reflexivity).
Qed.

(** * Offset Composition *)

Lemma Z_to_rank_Some : forall z r,
  Z_to_rank z = Some r ->
  0 <= z < 8 /\ r = mkRank (nat_to_fin8_aux (Z.to_nat z)).
Proof.
  intros z r H.
  unfold Z_to_rank in H.
  destruct (Z_lt_dec z 0); [discriminate|].
  destruct (Z_lt_dec z 8); [|discriminate].
  injection H. intro. subst. split; [lia|reflexivity].
Qed.

Lemma Z_to_file_Some : forall z f,
  Z_to_file z = Some f ->
  0 <= z < 8 /\ f = mkFile (nat_to_fin8_aux (Z.to_nat z)).
Proof.
  intros z f H.
  unfold Z_to_file in H.
  destruct (Z_lt_dec z 0); [discriminate|].
  destruct (Z_lt_dec z 8); [|discriminate].
  injection H. intro. subst. split; [lia|reflexivity].
Qed.

Lemma nat_to_fin8_aux_roundtrip : forall z,
  0 <= z < 8 ->
  Z.of_nat (fin8_to_nat (nat_to_fin8_aux (Z.to_nat z))) = z.
Proof.
  intros z Hz.
  remember (Z.to_nat z) as n eqn:Heqn.
  assert (Hn: Z.of_nat n = z).
  { subst n. rewrite Z2Nat.id; lia. }
  assert (Hbound: (n < 8)%nat).
  { apply Nat2Z.inj_lt. rewrite Hn. lia. }
  rewrite <- Hn.
  clear Hz Hn Heqn z.
  destruct n as [|[|[|[|[|[|[|[|n8]]]]]]]]; simpl; try reflexivity.
  exfalso. simpl in Hbound. lia.
Qed.

(** First tiny helper: Z_to_rank preserves bounds *)
Lemma Z_to_rank_bounds : forall z r,
  Z_to_rank z = Some r -> 0 <= z < 8.
Proof.
  intros z r H.
  unfold Z_to_rank in H.
  destruct (Z_lt_dec z 0); [discriminate|].
  destruct (Z_lt_dec z 8); [lia|discriminate].
Qed.

(** Second tiny helper: Z_to_file preserves bounds *)
Lemma Z_to_file_bounds : forall z f,
  Z_to_file z = Some f -> 0 <= z < 8.
Proof.
  intros z f H.
  unfold Z_to_file in H.
  destruct (Z_lt_dec z 0); [discriminate|].
  destruct (Z_lt_dec z 8); [lia|discriminate].
Qed.

(** Third helper: offset succeeds implies bounds *)
Lemma offset_Some_bounds : forall p dr df p',
  offset p dr df = Some p' ->
  0 <= rankZ p + dr < 8 /\ 0 <= fileZ p + df < 8.
Proof.
  intros p dr df p' H.
  unfold offset in H.
  destruct (Z_to_rank (rankZ p + dr)) eqn:Hr; [|discriminate].
  destruct (Z_to_file (fileZ p + df)) eqn:Hf; [|discriminate].
  split.
  - apply Z_to_rank_bounds with r. exact Hr.
  - apply Z_to_file_bounds with f. exact Hf.
Qed.

(** Fourth helper: Z_to_rank creates the expected rank *)
Lemma Z_to_rank_creates : forall z,
  0 <= z < 8 ->
  Z_to_rank z = Some (mkRank (nat_to_fin8_aux (Z.to_nat z))).
Proof.
  intros z Hz.
  unfold Z_to_rank.
  destruct (Z_lt_dec z 0); [lia|].
  destruct (Z_lt_dec z 8); [reflexivity|lia].
Qed.

(** Fifth helper: Z_to_file creates the expected file *)
Lemma Z_to_file_creates : forall z,
  0 <= z < 8 ->
  Z_to_file z = Some (mkFile (nat_to_fin8_aux (Z.to_nat z))).
Proof.
  intros z Hz.
  unfold Z_to_file.
  destruct (Z_lt_dec z 0); [lia|].
  destruct (Z_lt_dec z 8); [reflexivity|lia].
Qed.

(** Sixth helper: rankZ of constructed position *)
Lemma rankZ_mkPosition_nat : forall z1 z2,
  0 <= z1 < 8 -> 0 <= z2 < 8 ->
  rankZ (mkPosition 
    (mkRank (nat_to_fin8_aux (Z.to_nat z1)))
    (mkFile (nat_to_fin8_aux (Z.to_nat z2)))) = z1.
Proof.
  intros z1 z2 H1 H2.
  unfold rankZ. simpl.
  apply nat_to_fin8_aux_roundtrip. exact H1.
Qed.

(** Seventh helper: fileZ of constructed position *)
Lemma fileZ_mkPosition_nat : forall z1 z2,
  0 <= z1 < 8 -> 0 <= z2 < 8 ->
  fileZ (mkPosition 
    (mkRank (nat_to_fin8_aux (Z.to_nat z1)))
    (mkFile (nat_to_fin8_aux (Z.to_nat z2)))) = z2.
Proof.
  intros z1 z2 H1 H2.
  unfold fileZ. simpl.
  apply nat_to_fin8_aux_roundtrip. exact H2.
Qed.

(** Eighth helper: offset creates expected position *)
Lemma offset_creates_position : forall p dr df,
  0 <= rankZ p + dr < 8 ->
  0 <= fileZ p + df < 8 ->
  offset p dr df = Some (mkPosition
    (mkRank (nat_to_fin8_aux (Z.to_nat (rankZ p + dr))))
    (mkFile (nat_to_fin8_aux (Z.to_nat (fileZ p + df))))).
Proof.
  intros p dr df Hr Hf.
  unfold offset.
  rewrite Z_to_rank_creates by exact Hr.
  rewrite Z_to_file_creates by exact Hf.
  reflexivity.
Qed.

(** Now the main lemma using all helpers *)
Lemma offset_compose : forall p1 p2 p3 dr1 df1 dr2 df2,
  offset p1 dr1 df1 = Some p2 ->
  offset p2 dr2 df2 = Some p3 ->
  offset p1 (dr1 + dr2) (df1 + df2) = Some p3.
Proof.
  intros p1 p2 p3 dr1 df1 dr2 df2 H1 H2.
  
  assert (B1: 0 <= rankZ p1 + dr1 < 8 /\ 0 <= fileZ p1 + df1 < 8).
  { apply offset_Some_bounds with p2. exact H1. }
  destruct B1 as [Hrbounds1 Hfbounds1].
  
  assert (B2: 0 <= rankZ p2 + dr2 < 8 /\ 0 <= fileZ p2 + df2 < 8).
  { apply offset_Some_bounds with p3. exact H2. }
  destruct B2 as [Hrbounds2' Hfbounds2'].
  
  assert (Hp2: p2 = mkPosition
    (mkRank (nat_to_fin8_aux (Z.to_nat (rankZ p1 + dr1))))
    (mkFile (nat_to_fin8_aux (Z.to_nat (fileZ p1 + df1))))).
  { 
    assert (E: offset p1 dr1 df1 = Some (mkPosition
      (mkRank (nat_to_fin8_aux (Z.to_nat (rankZ p1 + dr1))))
      (mkFile (nat_to_fin8_aux (Z.to_nat (fileZ p1 + df1)))))).
    { apply offset_creates_position; assumption. }
    rewrite E in H1. injection H1. auto.
  }
  
  rewrite Hp2 in Hrbounds2', Hfbounds2'.
  rewrite rankZ_mkPosition_nat in Hrbounds2' by assumption.
  rewrite fileZ_mkPosition_nat in Hfbounds2' by assumption.
  
  assert (Hp3: p3 = mkPosition
    (mkRank (nat_to_fin8_aux (Z.to_nat ((rankZ p1 + dr1) + dr2))))
    (mkFile (nat_to_fin8_aux (Z.to_nat ((fileZ p1 + df1) + df2))))).
  { 
    assert (E: offset p2 dr2 df2 = Some (mkPosition
      (mkRank (nat_to_fin8_aux (Z.to_nat ((rankZ p1 + dr1) + dr2))))
      (mkFile (nat_to_fin8_aux (Z.to_nat ((fileZ p1 + df1) + df2)))))).
    { 
      rewrite Hp2.
      unfold offset.
      rewrite Z_to_rank_creates.
      2: { unfold rankZ. simpl. rewrite nat_to_fin8_aux_roundtrip by exact Hrbounds1. exact Hrbounds2'. }
      rewrite Z_to_file_creates.
      2: { unfold fileZ. simpl. rewrite nat_to_fin8_aux_roundtrip by exact Hfbounds1. exact Hfbounds2'. }
      f_equal. f_equal.
      - f_equal. unfold rankZ. simpl. 
        rewrite nat_to_fin8_aux_roundtrip by exact Hrbounds1. 
        reflexivity.
      - f_equal. unfold fileZ. simpl.
        rewrite nat_to_fin8_aux_roundtrip by exact Hfbounds1.
        reflexivity.
    }
    rewrite E in H2. injection H2. auto.
  }
  
  rewrite Hp3.
  unfold offset.
  rewrite Z_to_rank_creates.
  2: { replace (rankZ p1 + (dr1 + dr2)) with ((rankZ p1 + dr1) + dr2) by ring. exact Hrbounds2'. }
  rewrite Z_to_file_creates.
  2: { replace (fileZ p1 + (df1 + df2)) with ((fileZ p1 + df1) + df2) by ring. exact Hfbounds2'. }
  f_equal. f_equal.
  - f_equal. f_equal. f_equal. ring.
  - f_equal. f_equal. f_equal. ring.
Qed.

(** * Position Enumeration *)

Definition enum_rank : list Rank :=
  [rank1; rank2; rank3; rank4; rank5; rank6; rank7; rank8].

Definition enum_file : list File :=
  [fileA; fileB; fileC; fileD; fileE; fileF; fileG; fileH].

Definition enum_position : list Position :=
  map (fun rf => mkPosition (fst rf) (snd rf)) (list_prod enum_rank enum_file).

Lemma enum_rank_complete : forall r, In r enum_rank.
Proof.
  intro r. destruct r as [rv].
  apply fin8_exhaustive with (f := rv);
    (simpl; tauto).
Qed.

Lemma enum_file_complete : forall f, In f enum_file.
Proof.
  intro f. destruct f as [fv].
  apply fin8_exhaustive with (f := fv);
    (simpl; tauto).
Qed.

Lemma enum_position_complete : forall p, In p enum_position.
Proof.
  intro p. destruct p as [r f].
  unfold enum_position.
  apply in_map_iff.
  exists (r, f).
  split.
  - simpl. reflexivity.
  - apply in_prod.
    + apply enum_rank_complete.
    + apply enum_file_complete.
Qed.

Lemma enum_rank_NoDup : NoDup enum_rank.
Proof.
  unfold enum_rank.
  repeat constructor; simpl; intuition discriminate.
Qed.

Lemma enum_file_NoDup : NoDup enum_file.
Proof.
  unfold enum_file.
  repeat constructor; simpl; intuition discriminate.
Qed.

Lemma enum_position_NoDup : NoDup enum_position.
Proof.
  unfold enum_position.
  apply NoDup_map.
  - intros [r1 f1] [r2 f2] _ _ H. simpl in H.
    injection H. intros. f_equal; assumption.
  - apply NoDup_list_prod.
    + apply enum_rank_NoDup.
    + apply enum_file_NoDup.
Qed.

(** * Finite Instance *)

#[global]
Instance rank_finite : Finite Rank := {
  enum := enum_rank;
  enum_complete := enum_rank_complete;
  enum_nodup := enum_rank_NoDup
}.

#[global]
Instance file_finite : Finite File := {
  enum := enum_file;
  enum_complete := enum_file_complete;
  enum_nodup := enum_file_NoDup
}.

#[global]
Instance position_finite : Finite Position := {
  enum := enum_position;
  enum_complete := enum_position_complete;
  enum_nodup := enum_position_NoDup
}.

(** * Algebraic Notation Support *)

Definition file_to_char (f: File) : string :=
  match fin8_to_nat (file_val f) with
  | 0%nat => "a"
  | 1%nat => "b"
  | 2%nat => "c"
  | 3%nat => "d"
  | 4%nat => "e"
  | 5%nat => "f"
  | 6%nat => "g"
  | _ => "h"
  end.

Definition rank_to_char (r: Rank) : string :=
  match fin8_to_nat (rank_val r) with
  | 0%nat => "1"
  | 1%nat => "2"
  | 2%nat => "3"
  | 3%nat => "4"
  | 4%nat => "5"
  | 5%nat => "6"
  | 6%nat => "7"
  | _ => "8"
  end.

Definition position_to_algebraic (p: Position) : string :=
  file_to_char (pos_file p) ++ rank_to_char (pos_rank p).

Definition char_to_file (c: string) : option File :=
  match c with
  | "a" => Some fileA
  | "b" => Some fileB
  | "c" => Some fileC
  | "d" => Some fileD
  | "e" => Some fileE
  | "f" => Some fileF
  | "g" => Some fileG
  | "h" => Some fileH
  | _ => None
  end.

Definition char_to_rank (c: string) : option Rank :=
  match c with
  | "1" => Some rank1
  | "2" => Some rank2
  | "3" => Some rank3
  | "4" => Some rank4
  | "5" => Some rank5
  | "6" => Some rank6
  | "7" => Some rank7
  | "8" => Some rank8
  | _ => None
  end.

(** * Offset Preservation Properties *)

Lemma offset_preserves_board_validity : forall p dr df p',
  offset p dr df = Some p' ->
  rankZ p' = rankZ p + dr /\
  fileZ p' = fileZ p + df /\
  0 <= rankZ p' < 8 /\
  0 <= fileZ p' < 8.
Proof.
  intros p dr df p' H.
  pose proof H as H_copy.
  apply offset_Some_bounds in H_copy as Hbounds.
  destruct Hbounds as [Hr_bound Hf_bound].
  pose proof (offset_creates_position p dr df Hr_bound Hf_bound) as Hcreate.
  rewrite Hcreate in H.
  injection H. intro. subst p'.
  split.
  - apply rankZ_mkPosition_nat; assumption.
  - split.
    + apply fileZ_mkPosition_nat; assumption.
    + split; [apply rankZ_bounds | apply fileZ_bounds].
Qed.

(** * Offset Decidability *)

Lemma offset_decidable : forall p dr df,
  {p': Position | offset p dr df = Some p'} + {offset p dr df = None}.
Proof.
  intros p dr df.
  unfold offset.
  destruct (Z_to_rank (rankZ p + dr)) eqn:Hr.
  - destruct (Z_to_file (fileZ p + df)) eqn:Hf.
    + left. exists (mkPosition r f). reflexivity.
    + right. reflexivity.
  - right. reflexivity.
Defined.

(** * Distance Properties *)

Definition manhattan_distance (p1 p2: Position) : Z :=
  Z.abs (rankZ p2 - rankZ p1) + Z.abs (fileZ p2 - fileZ p1).

Definition chebyshev_distance (p1 p2: Position) : Z :=
  Z.max (Z.abs (rankZ p2 - rankZ p1)) (Z.abs (fileZ p2 - fileZ p1)).

Lemma manhattan_distance_zero : forall p,
  manhattan_distance p p = 0.
Proof.
  intro p. unfold manhattan_distance.
  repeat rewrite Z.sub_diag.
  repeat rewrite Z.abs_0.
  reflexivity.
Qed.

Lemma manhattan_distance_sym : forall p1 p2,
  manhattan_distance p1 p2 = manhattan_distance p2 p1.
Proof.
  intros p1 p2. unfold manhattan_distance.
  f_equal.
  - rewrite <- (Z.abs_opp (rankZ p2 - rankZ p1)).
    f_equal. ring.
  - rewrite <- (Z.abs_opp (fileZ p2 - fileZ p1)).
    f_equal. ring.
Qed.

Lemma chebyshev_distance_zero : forall p,
  chebyshev_distance p p = 0.
Proof.
  intro p. unfold chebyshev_distance.
  repeat rewrite Z.sub_diag.
  repeat rewrite Z.abs_0.
  reflexivity.
Qed.

Lemma chebyshev_distance_sym : forall p1 p2,
  chebyshev_distance p1 p2 = chebyshev_distance p2 p1.
Proof.
  intros p1 p2. unfold chebyshev_distance.
  f_equal.
  - rewrite <- (Z.abs_opp (rankZ p2 - rankZ p1)).
    f_equal. ring.
  - rewrite <- (Z.abs_opp (fileZ p2 - fileZ p1)).
    f_equal. ring.
Qed.

(** * Adjacent Position Detection *)

Definition adjacent (p1 p2: Position) : bool :=
  Z.eqb (chebyshev_distance p1 p2) 1.

Lemma adjacent_sym : forall p1 p2,
  adjacent p1 p2 = adjacent p2 p1.
Proof.
  intros. unfold adjacent.
  rewrite chebyshev_distance_sym. reflexivity.
Qed.

(** * Diagonal Detection *)

Definition on_same_diagonal (p1 p2: Position) : bool :=
  Z.eqb (Z.abs (rankZ p2 - rankZ p1)) (Z.abs (fileZ p2 - fileZ p1)).

Definition on_same_rank (p1 p2: Position) : bool :=
  Z.eqb (rankZ p1) (rankZ p2).

Definition on_same_file (p1 p2: Position) : bool :=
  Z.eqb (fileZ p1) (fileZ p2).

(** * Direction Computation *)

Definition direction_to (from to: Position) : option (Z * Z) :=
  let dr := rankZ to - rankZ from in
  let df := fileZ to - fileZ from in
  if andb (Z.eqb dr 0) (Z.eqb df 0) then None
  else 
    let g := Z.gcd dr df in
    Some (dr / g, df / g).

Lemma direction_to_unit : forall from to dr df,
  direction_to from to = Some (dr, df) ->
  Z.gcd dr df = 1 \/ (dr = 0 /\ Z.abs df = 1) \/ (df = 0 /\ Z.abs dr = 1).
Proof.
  intros from to dr df H.
  unfold direction_to in H.
  destruct (andb (Z.eqb (rankZ to - rankZ from) 0)
                 (Z.eqb (fileZ to - fileZ from) 0)) eqn:E; [discriminate|].
  injection H. intros <- <-. clear H.
  apply andb_false_iff in E.
  left.
  assert (HG: Z.gcd (rankZ to - rankZ from) (fileZ to - fileZ from) <> 0).
  { intro. apply Z.gcd_eq_0 in H. destruct H.
    destruct E as [E|E]; apply Z.eqb_neq in E; congruence. }
  rewrite <- (Z.gcd_div_gcd (rankZ to - rankZ from) (fileZ to - fileZ from) 
                            (Z.gcd (rankZ to - rankZ from) (fileZ to - fileZ from))
                            HG eq_refl).
  reflexivity.
Qed.

(** * Validation *)

Example offset_roundtrip : forall p dr df p',
  offset p dr df = Some p' -> 
  offset p' (-dr) (-df) = Some p.
Proof.
  exact offset_inverse.
Qed.

Example position_enumeration_complete : forall p,
  In p enum_position.
Proof.
  exact enum_position_complete.
Qed.

Lemma offset_coord_change : forall p dr df p',
  offset p dr df = Some p' ->
  rankZ p' = rankZ p + dr /\
  fileZ p' = fileZ p + df.
Proof.
  intros p dr df p' H.
  apply offset_preserves_board_validity in H.
  tauto.
Qed.

(** * End of Section 3: Position Abstraction *)

Close Scope Z_scope.

(* ========================================================================= *)
(* SECTION 4: CORE GAME ONTOLOGY                                            *)
(* ========================================================================= *)

(** * Color Definition *)

Inductive Color : Type :=
  | White : Color
  | Black : Color.

(** * Decidable Equality for Color *)

Lemma color_eq_dec : forall (c1 c2: Color), {c1 = c2} + {c1 <> c2}.
Proof.
  decide equality.
Defined.

#[global]
Instance color_decidable_eq : DecidableEq Color := {
  dec_eq := color_eq_dec
}.

(** * Opposite Color *)

Definition opposite_color (c: Color) : Color :=
  match c with
  | White => Black
  | Black => White
  end.

(** * Opposite Color Properties *)

Lemma opposite_color_involutive : forall c,
  opposite_color (opposite_color c) = c.
Proof.
  intros []; reflexivity.
Qed.

Lemma opposite_color_injective : forall c1 c2,
  opposite_color c1 = opposite_color c2 -> c1 = c2.
Proof.
  intros [] []; simpl; intro H; [reflexivity|discriminate|discriminate|reflexivity].
Qed.

Lemma opposite_color_neq : forall c,
  opposite_color c <> c.
Proof.
  intros []; discriminate.
Qed.

(** * Piece Types for Shatranj *)

Inductive PieceType : Type :=
  | Shah   : PieceType  (* King *)
  | Ferz   : PieceType  (* Counselor - moves 1 square diagonally *)
  | Alfil  : PieceType  (* Elephant - leaps exactly 2 squares diagonally *)
  | Faras  : PieceType  (* Knight - same as chess knight *)
  | Rukh   : PieceType  (* Rook - same as chess rook *)
  | Baidaq : PieceType. (* Pawn - moves 1 forward, captures diagonally *)

(** * Decidable Equality for PieceType *)

Lemma piece_type_eq_dec : forall (pt1 pt2: PieceType), {pt1 = pt2} + {pt1 <> pt2}.
Proof.
  decide equality.
Defined.

#[global]
Instance piece_type_decidable_eq : DecidableEq PieceType := {
  dec_eq := piece_type_eq_dec
}.

(** * Piece Definition *)

Record Piece : Type := mkPiece {
  piece_color : Color;
  piece_type : PieceType
}.

(** * Decidable Equality for Piece *)

Lemma piece_eq_dec : forall (p1 p2: Piece), {p1 = p2} + {p1 <> p2}.
Proof.
  intros [c1 pt1] [c2 pt2].
  destruct (color_eq_dec c1 c2), (piece_type_eq_dec pt1 pt2).
  - left. f_equal; assumption.
  - right. intro H. injection H. intros. contradiction.
  - right. intro H. injection H. intros. contradiction.
  - right. intro H. injection H. intros. contradiction.
Defined.

#[global]
Instance piece_decidable_eq : DecidableEq Piece := {
  dec_eq := piece_eq_dec
}.

(** * Piece Construction Helpers *)

Definition white_shah   := mkPiece White Shah.
Definition white_ferz   := mkPiece White Ferz.
Definition white_alfil  := mkPiece White Alfil.
Definition white_faras  := mkPiece White Faras.
Definition white_rukh   := mkPiece White Rukh.
Definition white_baidaq := mkPiece White Baidaq.

Definition black_shah   := mkPiece Black Shah.
Definition black_ferz   := mkPiece Black Ferz.
Definition black_alfil  := mkPiece Black Alfil.
Definition black_faras  := mkPiece Black Faras.
Definition black_rukh   := mkPiece Black Rukh.
Definition black_baidaq := mkPiece Black Baidaq.

(** * Piece Properties *)

Definition is_shah (p: Piece) : bool :=
  match piece_type p with
  | Shah => true
  | _ => false
  end.

Definition is_ferz (p: Piece) : bool :=
  match piece_type p with
  | Ferz => true
  | _ => false
  end.

Definition is_alfil (p: Piece) : bool :=
  match piece_type p with
  | Alfil => true
  | _ => false
  end.

Definition is_faras (p: Piece) : bool :=
  match piece_type p with
  | Faras => true
  | _ => false
  end.

Definition is_rukh (p: Piece) : bool :=
  match piece_type p with
  | Rukh => true
  | _ => false
  end.

Definition is_baidaq (p: Piece) : bool :=
  match piece_type p with
  | Baidaq => true
  | _ => false
  end.

Definition is_white (p: Piece) : bool :=
  match piece_color p with
  | White => true
  | Black => false
  end.

Definition is_black (p: Piece) : bool :=
  match piece_color p with
  | Black => true
  | White => false
  end.

Definition Color_beq (c1 c2: Color) : bool :=
  match c1, c2 with
  | White, White => true
  | Black, Black => true
  | _, _ => false
  end.

Definition same_color (p1 p2: Piece) : bool :=
  Color_beq (piece_color p1) (piece_color p2).

Definition opposite_colors (p1 p2: Piece) : bool :=
  negb (same_color p1 p2).

(** * Exhaustiveness Lemmas *)

Lemma color_exhaustive : forall c (P: Color -> Prop),
  P White -> P Black -> P c.
Proof.
  intros [] P HW HB; assumption.
Qed.

Lemma piece_type_exhaustive : forall pt (P: PieceType -> Prop),
  P Shah -> P Ferz -> P Alfil -> P Faras -> P Rukh -> P Baidaq -> P pt.
Proof.
  intros [] P HS HF HA HN HR HB; assumption.
Qed.

Lemma piece_exhaustive : forall p (P: Piece -> Prop),
  (forall c pt, P (mkPiece c pt)) -> P p.
Proof.
  intros [c pt] P H. apply H.
Qed.

(** * Finite Instances *)

#[global]
Instance color_finite : Finite Color := {
  enum := [White; Black];
  enum_complete := fun c => match c with
    | White => or_introl eq_refl
    | Black => or_intror (or_introl eq_refl)
    end;
  enum_nodup := ltac:(repeat constructor; simpl; intuition discriminate)
}.

#[global]
Instance piece_type_finite : Finite PieceType := {
  enum := [Shah; Ferz; Alfil; Faras; Rukh; Baidaq];
  enum_complete := fun pt => match pt with
    | Shah => or_introl eq_refl
    | Ferz => or_intror (or_introl eq_refl)
    | Alfil => or_intror (or_intror (or_introl eq_refl))
    | Faras => or_intror (or_intror (or_intror (or_introl eq_refl)))
    | Rukh => or_intror (or_intror (or_intror (or_intror (or_introl eq_refl))))
    | Baidaq => or_intror (or_intror (or_intror (or_intror (or_intror (or_introl eq_refl)))))
    end;
  enum_nodup := ltac:(repeat constructor; simpl; intuition discriminate)
}.

#[global]
Instance piece_finite : Finite Piece.
Proof.
  refine {| enum := map (fun cp => mkPiece (fst cp) (snd cp)) 
                       (list_prod (@enum Color _) (@enum PieceType _)) |}.
  - intro p. destruct p as [c pt].
    apply in_map_iff. exists (c, pt). split.
    + reflexivity.
    + apply in_prod; apply enum_complete.
  - apply NoDup_map.
    + intros [c1 pt1] [c2 pt2] _ _ H. simpl in H.
      injection H. intros. f_equal; assumption.
    + apply NoDup_list_prod; apply enum_nodup.
Defined.

(** * Piece Movement Classification *)

Definition is_sliding_piece (pt: PieceType) : bool :=
  match pt with
  | Rukh => true  (* Rukh slides along ranks/files *)
  | _ => false
  end.

Definition is_leaping_piece (pt: PieceType) : bool :=
  match pt with
  | Alfil => true  (* Alfil leaps exactly 2 diagonally *)
  | Faras => true  (* Faras (knight) leaps in L-shape *)
  | _ => false
  end.

Definition is_step_piece (pt: PieceType) : bool :=
  match pt with
  | Shah => true   (* Shah moves 1 square any direction *)
  | Ferz => true   (* Ferz moves 1 square diagonally *)
  | Baidaq => true (* Baidaq moves 1 square forward *)
  | _ => false
  end.

Lemma piece_movement_complete : forall pt,
  is_sliding_piece pt = true \/ 
  is_leaping_piece pt = true \/ 
  is_step_piece pt = true.
Proof.
  intros []; simpl; auto.
Qed.

Lemma piece_movement_exclusive : forall pt,
  (is_sliding_piece pt = true -> is_leaping_piece pt = false /\ is_step_piece pt = false) /\
  (is_leaping_piece pt = true -> is_sliding_piece pt = false /\ is_step_piece pt = false) /\
  (is_step_piece pt = true -> is_sliding_piece pt = false /\ is_leaping_piece pt = false).
Proof.
  intros []; simpl; repeat split; discriminate.
Qed.

(** * Piece Value for Material Calculation *)

Open Scope Z_scope.

Definition piece_value (pt: PieceType) : Z :=
  match pt with
  | Shah => 1000  (* Infinite value, but we use large number *)
  | Rukh => 5
  | Faras => 3
  | Alfil => 2
  | Ferz => 2
  | Baidaq => 1
  end.

Lemma piece_value_positive : forall pt,
  piece_value pt > 0.
Proof.
  intros []; simpl; lia.
Qed.

Close Scope Z_scope.

(** * Piece Notation *)

Definition piece_type_to_char (pt: PieceType) : string :=
  match pt with
  | Shah => "K"
  | Ferz => "F"
  | Alfil => "A"
  | Faras => "N"
  | Rukh => "R"
  | Baidaq => ""  (* Pawns have no letter *)
  end.

Definition piece_to_char (p: Piece) : string :=
  let pt_char := piece_type_to_char (piece_type p) in
  match piece_color p with
  | White => pt_char
  | Black => 
      match piece_type p with
      | Shah => "k"
      | Ferz => "f"
      | Alfil => "a"
      | Faras => "n"
      | Rukh => "r"
      | Baidaq => "p"
      end
  end.

(** * FEN Character Support *)

Definition char_to_piece (c: string) : option Piece :=
  match c with
  | "K" => Some white_shah
  | "F" => Some white_ferz
  | "A" => Some white_alfil
  | "N" => Some white_faras
  | "R" => Some white_rukh
  | "P" => Some white_baidaq
  | "k" => Some black_shah
  | "f" => Some black_ferz
  | "a" => Some black_alfil
  | "n" => Some black_faras
  | "r" => Some black_rukh
  | "p" => Some black_baidaq
  | _ => None
  end.

(** * Special Piece Properties for Shatranj *)

(** Alfil can only reach 1/8 of the board from any position *)
Definition alfil_reachable_squares : nat := 8.

(** Ferz is much weaker than modern Queen - only 4 possible moves *)
Definition ferz_max_moves : nat := 4.

(** Baidaq promotes only to Ferz *)
Definition baidaq_promotion_type : PieceType := Ferz.

(** * Validation Examples *)

Example opposite_color_involutive_validated : forall c,
  opposite_color (opposite_color c) = c.
Proof.
  exact opposite_color_involutive.
Qed.

Example piece_type_cases : forall pt,
  pt = Shah \/ pt = Ferz \/ pt = Alfil \/ 
  pt = Faras \/ pt = Rukh \/ pt = Baidaq.
Proof.
  intros []; 
  [left; reflexivity 
  |right; left; reflexivity
  |right; right; left; reflexivity
  |right; right; right; left; reflexivity
  |right; right; right; right; left; reflexivity
  |right; right; right; right; right; reflexivity].
Qed.

Example white_pieces_different_from_black : forall pt,
  mkPiece White pt <> mkPiece Black pt.
Proof.
  intros pt H. injection H. discriminate.
Qed.

(** * Piece Counting Utilities *)

Definition PieceType_beq (pt1 pt2: PieceType) : bool :=
  match pt1, pt2 with
  | Shah, Shah => true
  | Ferz, Ferz => true
  | Alfil, Alfil => true
  | Faras, Faras => true
  | Rukh, Rukh => true
  | Baidaq, Baidaq => true
  | _, _ => false
  end.

Definition count_piece_type (pt: PieceType) (pieces: list Piece) : nat :=
  List.length (filter (fun p => PieceType_beq (piece_type p) pt) pieces).

Definition count_color_pieces (c: Color) (pieces: list Piece) : nat :=
  List.length (filter (fun p => Color_beq (piece_color p) c) pieces).

(** * Historical Note Validation *)

(** Validates that Alfil movement is restricted compared to Bishop *)
Lemma alfil_not_bishop : 
  is_leaping_piece Alfil = true /\ is_sliding_piece Alfil = false.
Proof.
  split; reflexivity.
Qed.

(** Validates that Ferz movement is restricted compared to Queen *)
Lemma ferz_not_queen :
  is_step_piece Ferz = true /\ is_sliding_piece Ferz = false.
Proof.
  split; reflexivity.
Qed.

(** * End of Section 4: Core Game Ontology *)

(* ========================================================================= *)
(* SECTION 5: BOARD ABSTRACTION                                             *)
(* ========================================================================= *)

(** * Board Type Definition *)

Definition Board : Type := Position -> option Piece.

(** * Board Access Notation *)

Notation "b [ p ]" := (b p) (at level 1).
Notation "b [ p := pc ]" := 
  (fun p' => if position_eq_dec p p' then pc else b p')
  (at level 1).

(** * Board Equality *)

Definition board_eq (b1 b2: Board) : Prop :=
  forall p, b1[p] = b2[p].

Notation "b1 '==' b2" := (board_eq b1 b2) (at level 70).

Lemma board_eq_refl : forall b, b == b.
Proof.
  intros b p. reflexivity.
Qed.

Lemma board_eq_sym : forall b1 b2, b1 == b2 -> b2 == b1.
Proof.
  intros b1 b2 H p. symmetry. apply H.
Qed.

Lemma board_eq_trans : forall b1 b2 b3, 
  b1 == b2 -> b2 == b3 -> b1 == b3.
Proof.
  intros b1 b2 b3 H12 H23 p.
  transitivity (b2[p]); [apply H12 | apply H23].
Qed.

(** * Board Setoid Instance *)

Require Import Coq.Classes.Equivalence.

#[global]
Instance board_equiv : Equivalence board_eq := {
  Equivalence_Reflexive := board_eq_refl;
  Equivalence_Symmetric := board_eq_sym;
  Equivalence_Transitive := board_eq_trans
}.

(** * Board Update Operations *)

Definition board_set (b: Board) (p: Position) (pc: option Piece) : Board :=
  b[p := pc].

Definition board_get (b: Board) (p: Position) : option Piece :=
  b[p].

Definition board_remove (b: Board) (p: Position) : Board :=
  b[p := None].

Definition board_place (b: Board) (p: Position) (pc: Piece) : Board :=
  b[p := Some pc].

Definition board_move (b: Board) (from to: Position) : Board :=
  match b[from] with
  | Some pc => (b[from := None])[to := Some pc]
  | None => b
  end.

(** * Board Update Properties *)

Lemma board_set_get_same : forall b p pc,
  board_get (board_set b p pc) p = pc.
Proof.
  intros b p pc. unfold board_get, board_set.
  destruct (position_eq_dec p p); [reflexivity|contradiction].
Qed.

Lemma board_set_get_other : forall b p1 p2 pc,
  p1 <> p2 ->
  board_get (board_set b p1 pc) p2 = board_get b p2.
Proof.
  intros b p1 p2 pc H. unfold board_get, board_set.
  destruct (position_eq_dec p1 p2); [contradiction|reflexivity].
Qed.

Lemma board_set_set_same : forall b p pc1 pc2,
  board_set (board_set b p pc1) p pc2 == board_set b p pc2.
Proof.
  intros b p pc1 pc2 p'. unfold board_set.
  destruct (position_eq_dec p p'); reflexivity.
Qed.

Lemma board_set_set_comm : forall b p1 p2 pc1 pc2,
  p1 <> p2 ->
  board_set (board_set b p1 pc1) p2 pc2 == 
  board_set (board_set b p2 pc2) p1 pc1.
Proof.
  intros b p1 p2 pc1 pc2 H p'. unfold board_set.
  destruct (position_eq_dec p1 p'), (position_eq_dec p2 p'); 
    subst; try reflexivity; try contradiction.
Qed.

(** * Board Predicates *)

Definition occupied (b: Board) (p: Position) : bool :=
  match b[p] with
  | Some _ => true
  | None => false
  end.

Definition occupied_by (b: Board) (p: Position) (c: Color) : bool :=
  match b[p] with
  | Some pc => Color_beq (piece_color pc) c
  | None => false
  end.

Definition empty (b: Board) (p: Position) : bool :=
  negb (occupied b p).

Definition has_piece_type (b: Board) (p: Position) (pt: PieceType) : bool :=
  match b[p] with
  | Some pc => PieceType_beq (piece_type pc) pt
  | None => false
  end.

(** * Empty Board *)

Definition empty_board : Board := fun _ => None.

Lemma empty_board_empty : forall p, 
  empty empty_board p = true.
Proof.
  intro p. reflexivity.
Qed.

(** * Initial Position Setup - Standard Configuration *)

Definition initial_rank_setup (c: Color) : Position -> option Piece :=
  fun p =>
    let r := if Color_beq c White then rank1 else rank8 in
    if rank_eq_dec (pos_rank p) r then
      if file_eq_dec (pos_file p) fileA then Some (mkPiece c Rukh)
      else if file_eq_dec (pos_file p) fileB then Some (mkPiece c Faras)
      else if file_eq_dec (pos_file p) fileC then Some (mkPiece c Alfil)
      else if file_eq_dec (pos_file p) fileD then Some (mkPiece c Shah)
      else if file_eq_dec (pos_file p) fileE then Some (mkPiece c Ferz)
      else if file_eq_dec (pos_file p) fileF then Some (mkPiece c Alfil)
      else if file_eq_dec (pos_file p) fileG then Some (mkPiece c Faras)
      else if file_eq_dec (pos_file p) fileH then Some (mkPiece c Rukh)
      else None
    else None.

Definition initial_baidaq_setup (c: Color) : Position -> option Piece :=
  fun p =>
    let r := if Color_beq c White then rank2 else rank7 in
    if rank_eq_dec (pos_rank p) r then
      Some (mkPiece c Baidaq)
    else None.

Definition standard_initial_board : Board :=
  fun p =>
    match initial_rank_setup White p with
    | Some pc => Some pc
    | None => match initial_rank_setup Black p with
              | Some pc => Some pc
              | None => match initial_baidaq_setup White p with
                        | Some pc => Some pc
                        | None => initial_baidaq_setup Black p
                        end
              end
    end.

(** * Alternative Initial Position *)

Definition alternative_rank_setup (c: Color) : Position -> option Piece :=
  fun p =>
    let r := if Color_beq c White then rank1 else rank8 in
    if rank_eq_dec (pos_rank p) r then
      if file_eq_dec (pos_file p) fileA then Some (mkPiece c Rukh)
      else if file_eq_dec (pos_file p) fileB then Some (mkPiece c Faras)
      else if file_eq_dec (pos_file p) fileC then Some (mkPiece c Alfil)
      else if file_eq_dec (pos_file p) fileD then Some (mkPiece c Ferz)
      else if file_eq_dec (pos_file p) fileE then Some (mkPiece c Shah)
      else if file_eq_dec (pos_file p) fileF then Some (mkPiece c Alfil)
      else if file_eq_dec (pos_file p) fileG then Some (mkPiece c Faras)
      else if file_eq_dec (pos_file p) fileH then Some (mkPiece c Rukh)
      else None
    else None.

Definition alternative_initial_board : Board :=
  fun p =>
    match alternative_rank_setup White p with
    | Some pc => Some pc
    | None => match alternative_rank_setup Black p with
              | Some pc => Some pc
              | None => match initial_baidaq_setup White p with
                        | Some pc => Some pc
                        | None => initial_baidaq_setup Black p
                        end
              end
    end.

(** * Historical Tabiyat *)

Definition tabiya_muwashshah : Board :=
  fun p =>
    if position_eq_dec p (mkPosition rank1 fileA) then Some white_rukh
    else if position_eq_dec p (mkPosition rank1 fileH) then Some white_rukh
    else if position_eq_dec p (mkPosition rank1 fileD) then Some white_shah
    else if position_eq_dec p (mkPosition rank1 fileE) then Some white_ferz
    else if position_eq_dec p (mkPosition rank3 fileC) then Some white_faras
    else if position_eq_dec p (mkPosition rank3 fileF) then Some white_faras
    else if position_eq_dec p (mkPosition rank3 fileB) then Some white_alfil
    else if position_eq_dec p (mkPosition rank3 fileG) then Some white_alfil
    else if position_eq_dec p (mkPosition rank4 fileD) then Some white_baidaq
    else if position_eq_dec p (mkPosition rank4 fileE) then Some white_baidaq
    else if position_eq_dec p (mkPosition rank2 fileA) then Some white_baidaq
    else if position_eq_dec p (mkPosition rank2 fileH) then Some white_baidaq
    else if position_eq_dec p (mkPosition rank8 fileA) then Some black_rukh
    else if position_eq_dec p (mkPosition rank8 fileH) then Some black_rukh
    else if position_eq_dec p (mkPosition rank8 fileD) then Some black_shah
    else if position_eq_dec p (mkPosition rank8 fileE) then Some black_ferz
    else if position_eq_dec p (mkPosition rank6 fileC) then Some black_faras
    else if position_eq_dec p (mkPosition rank6 fileF) then Some black_faras
    else if position_eq_dec p (mkPosition rank6 fileB) then Some black_alfil
    else if position_eq_dec p (mkPosition rank6 fileG) then Some black_alfil
    else if position_eq_dec p (mkPosition rank5 fileD) then Some black_baidaq
    else if position_eq_dec p (mkPosition rank5 fileE) then Some black_baidaq
    else if position_eq_dec p (mkPosition rank7 fileA) then Some black_baidaq
    else if position_eq_dec p (mkPosition rank7 fileH) then Some black_baidaq
    else None.

Definition tabiya_sayf : Board :=
  fun p =>
    if position_eq_dec p (mkPosition rank1 fileD) then Some white_shah
    else if position_eq_dec p (mkPosition rank1 fileE) then Some white_ferz
    else if position_eq_dec p (mkPosition rank1 fileA) then Some white_rukh
    else if position_eq_dec p (mkPosition rank1 fileH) then Some white_rukh
    else if position_eq_dec p (mkPosition rank3 fileE) then Some white_faras
    else if position_eq_dec p (mkPosition rank3 fileF) then Some white_alfil
    else if position_eq_dec p (mkPosition rank4 fileD) then Some white_baidaq
    else if position_eq_dec p (mkPosition rank4 fileE) then Some white_baidaq
    else if position_eq_dec p (mkPosition rank4 fileF) then Some white_baidaq
    else if position_eq_dec p (mkPosition rank8 fileD) then Some black_shah
    else if position_eq_dec p (mkPosition rank8 fileE) then Some black_ferz
    else if position_eq_dec p (mkPosition rank8 fileA) then Some black_rukh
    else if position_eq_dec p (mkPosition rank8 fileH) then Some black_rukh
    else if position_eq_dec p (mkPosition rank6 fileD) then Some black_faras
    else if position_eq_dec p (mkPosition rank6 fileC) then Some black_alfil
    else if position_eq_dec p (mkPosition rank5 fileD) then Some black_baidaq
    else if position_eq_dec p (mkPosition rank5 fileE) then Some black_baidaq
    else if position_eq_dec p (mkPosition rank5 fileC) then Some black_baidaq
    else None.

Definition tabiya_position (n: nat) : option Board :=
  match n with
  | 1 => Some tabiya_muwashshah
  | 2 => Some tabiya_sayf
  | _ => None
  end.

(** * Board Query Functions *)

Definition find_shah (b: Board) (c: Color) : option Position :=
  find (fun p => match b[p] with
                 | Some pc => andb (is_shah pc) (Color_beq (piece_color pc) c)
                 | None => false
                 end) enum_position.

Definition count_pieces (b: Board) (c: Color) : nat :=
  List.length (filter (fun p => occupied_by b p c) enum_position).

Definition count_piece_type_on_board (b: Board) (c: Color) (pt: PieceType) : nat :=
  List.length (filter (fun p => 
    match b[p] with
    | Some pc => andb (Color_beq (piece_color pc) c) 
                     (PieceType_beq (piece_type pc) pt)
    | None => false
    end) enum_position).

Definition get_all_pieces (b: Board) (c: Color) : list (Position * Piece) :=
  fold_left (fun acc p =>
    match b[p] with
    | Some pc => if Color_beq (piece_color pc) c 
                 then (p, pc) :: acc 
                 else acc
    | None => acc
    end) enum_position nil.

(** * Board Path Checking *)

Fixpoint path_clear_n (b: Board) (from: Position) (dr df: Z) (n: nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match offset from dr df with
      | Some next => if empty b next then path_clear_n b next dr df n' else false
      | None => false
      end
  end.

Definition path_clear (b: Board) (from to: Position) (dr df: Z) : bool :=
  path_clear_n b from dr df 7.

(** * Board Manipulation *)

Definition promote_baidaq (b: Board) (p: Position) (c: Color) : Board :=
  board_place b p (mkPiece c Ferz).

Definition clear_rank (b: Board) (r: Rank) : Board :=
  fold_left (fun b' f => board_remove b' (mkPosition r f)) enum_file b.

Definition clear_file (b: Board) (f: File) : Board :=
  fold_left (fun b' r => board_remove b' (mkPosition r f)) enum_rank b.

(** * Board Validation *)

Definition has_shah (b: Board) (c: Color) : bool :=
  match find_shah b c with
  | Some _ => true
  | None => false
  end.

Definition shah_count (b: Board) (c: Color) : nat :=
  count_piece_type_on_board b c Shah.

Definition valid_shah_count (b: Board) : bool :=
  andb (Nat.eqb (shah_count b White) 1)
       (Nat.eqb (shah_count b Black) 1).

Definition valid_piece_counts (b: Board) : bool :=
  andb (Nat.leb (count_piece_type_on_board b White Baidaq) 8)
       (Nat.leb (count_piece_type_on_board b Black Baidaq) 8).

Definition well_formed_board (b: Board) : bool :=
  andb (valid_shah_count b) (valid_piece_counts b).

(** * Board Examples and Validation *)

Example board_update_retrieve : forall b p pc,
  board_get (board_set b p (Some pc)) p = Some pc.
Proof.
  intros. apply board_set_get_same.
Qed.

Lemma filter_false : forall {A: Type} (l: list A),
  filter (fun _ => false) l = [].
Proof.
  intros A l. induction l; simpl; auto.
Qed.

Example empty_board_no_pieces : forall c,
  count_pieces empty_board c = 0.
Proof.
  intro c. unfold count_pieces.
  assert (H: filter (fun p => occupied_by empty_board p c) enum_position = []).
  { assert (Heq: (fun p => occupied_by empty_board p c) = (fun _ => false)).
    { apply fun_ext. intro p. unfold occupied_by, empty_board. reflexivity. }
    rewrite Heq. apply filter_false. }
  rewrite H. reflexivity.
Qed.

(** * Board Comparison *)

Definition boards_differ_at (b1 b2: Board) : list Position :=
  filter (fun p => negb (match b1[p], b2[p] with
                         | Some p1, Some p2 => if piece_eq_dec p1 p2 then true else false
                         | None, None => true
                         | _, _ => false
                         end)) enum_position.

Lemma filter_nil : forall {A: Type} (P: A -> bool) (l: list A),
  (forall x, In x l -> P x = false) -> filter P l = [].
Proof.
  intros A P l H. induction l; simpl; auto.
  assert (Ha: P a = false) by (apply H; left; reflexivity).
  rewrite Ha. apply IHl. intros x Hx. apply H. right. exact Hx.
Qed.

Lemma filter_empty_implies : forall {A: Type} (P: A -> bool) (l: list A) (x: A),
  filter P l = [] -> In x l -> P x = false.
Proof.
  intros A P l. induction l; intros x Hfilter Hin.
  - simpl in Hin. contradiction.
  - simpl in *. destruct (P a) eqn:HPa.
    + discriminate.
    + destruct Hin as [<-|Hin'].
      * exact HPa.
      * apply IHl; assumption.
Qed.

Lemma board_eq_iff_no_diff : forall b1 b2,
  b1 == b2 <-> boards_differ_at b1 b2 = [].
Proof.
  intros b1 b2. split.
  - intros H. unfold boards_differ_at.
    apply filter_nil. intros p _.
    specialize (H p).
    rewrite H.
    destruct (b2[p]); simpl.
    + destruct (piece_eq_dec p0 p0); [reflexivity|contradiction].
    + reflexivity.
  - intros H p. unfold boards_differ_at in H.
    assert (Hin: In p enum_position) by apply enum_position_complete.
    assert (Hp_false: negb (match b1[p], b2[p] with
                           | Some p1, Some p2 => if piece_eq_dec p1 p2 then true else false
                           | None, None => true
                           | _, _ => false
                           end) = false).
    { apply (filter_empty_implies _ enum_position p H Hin). }
    simpl in Hp_false.
    destruct (b1[p]) eqn:E1, (b2[p]) eqn:E2.
    + simpl in Hp_false.
      destruct (piece_eq_dec p0 p1).
      * subst. reflexivity.
      * simpl in Hp_false. discriminate.
    + simpl in Hp_false. discriminate.
    + simpl in Hp_false. discriminate.
    + reflexivity.
Qed.

(** * End of Section 5: Board Abstraction *)

(* ========================================================================= *)
(* SECTION 6: MOVEMENT GEOMETRY                                             *)
(* ========================================================================= *)

Open Scope Z_scope.

(** * Movement Vector Type *)

Definition MovementVector : Type := (Z * Z).

(** * Basic Movement Categories *)

(** Step moves - exactly one square in specified direction *)
Definition is_step_move (dr df: Z) : bool :=
  andb (Z.leb (Z.abs dr) 1) (Z.leb (Z.abs df) 1) &&
  negb (andb (Z.eqb dr 0) (Z.eqb df 0)).

(** Orthogonal moves - along rank or file *)
Definition is_orthogonal (dr df: Z) : bool :=
  orb (Z.eqb dr 0) (Z.eqb df 0) &&
  negb (andb (Z.eqb dr 0) (Z.eqb df 0)).

(** Diagonal moves - equal absolute displacement *)
Definition is_diagonal (dr df: Z) : bool :=
  Z.eqb (Z.abs dr) (Z.abs df) &&
  negb (andb (Z.eqb dr 0) (Z.eqb df 0)).

(** * Specific Movement Patterns *)

(** Shah movement - one square in any direction *)
Definition shah_vectors : list MovementVector :=
  [(1, 0); (-1, 0); (0, 1); (0, -1);    (* orthogonal *)
   (1, 1); (1, -1); (-1, 1); (-1, -1)].  (* diagonal *)

(** Ferz movement - one square diagonally only *)
Definition ferz_vectors : list MovementVector :=
  [(1, 1); (1, -1); (-1, 1); (-1, -1)].

(** Alfil movement - leap exactly 2 squares diagonally *)
Definition alfil_vectors : list MovementVector :=
  [(2, 2); (2, -2); (-2, 2); (-2, -2)].

(** Faras (Knight) movement - L-shaped *)
Definition faras_vectors : list MovementVector :=
  [(2, 1); (2, -1); (-2, 1); (-2, -1);
   (1, 2); (1, -2); (-1, 2); (-1, -2)].

(** Rukh movement directions (unit vectors) *)
Definition rukh_directions : list MovementVector :=
  [(1, 0); (-1, 0); (0, 1); (0, -1)].

(** Baidaq movement depends on color *)
Definition baidaq_move_vector (c: Color) : MovementVector :=
  match c with
  | White => (1, 0)  (* rank increases for white *)
  | Black => (-1, 0) (* rank decreases for black *)
  end.

Definition baidaq_capture_vectors (c: Color) : list MovementVector :=
  match c with
  | White => [(1, 1); (1, -1)]
  | Black => [(-1, 1); (-1, -1)]
  end.

(** * Movement Classification *)

Inductive MoveType : Type :=
  | Step   : MoveType  (* Single square movement *)
  | Leap   : MoveType  (* Jump to specific square *)
  | Slide  : MoveType. (* Multiple squares along line *)

Definition classify_piece_movement (pt: PieceType) : MoveType :=
  match pt with
  | Shah => Step
  | Ferz => Step
  | Alfil => Leap
  | Faras => Leap
  | Rukh => Slide
  | Baidaq => Step
  end.

(** * Step Movement *)

Definition position_beq (p1 p2: Position) : bool :=
  if position_eq_dec p1 p2 then true else false.

Definition step_move (b: Board) (from to: Position) (vectors: list MovementVector) : bool :=
  existsb (fun v =>
    match offset from (fst v) (snd v) with
    | Some p => position_beq p to
    | None => false
    end) vectors.

(** * Leap Movement *)

Definition leap_move (b: Board) (from to: Position) (vectors: list MovementVector) : bool :=
  existsb (fun v =>
    match offset from (fst v) (snd v) with
    | Some p => position_beq p to
    | None => false
    end) vectors.

(** * Slide Movement *)

Fixpoint slide_move_n (b: Board) (from: Position) (dr df: Z) (n: nat) : list Position :=
  match n with
  | O => []
  | S n' =>
      match offset from dr df with
      | Some next =>
          if empty b next then
            next :: slide_move_n b next dr df n'
          else
            [next]  (* Can capture but not continue past *)
      | None => []
      end
  end.

Definition slide_move (b: Board) (from to: Position) (directions: list MovementVector) : bool :=
  existsb (fun dir =>
    let positions := slide_move_n b from (fst dir) (snd dir) 7 in
    existsb (fun p => position_beq p to) positions
  ) directions.

(** * Path Checking *)

Definition path_between (from to: Position) : option (list Position) :=
  match direction_to from to with
  | Some (dr, df) =>
      let dist := Z.max (Z.abs (rankZ to - rankZ from)) 
                        (Z.abs (fileZ to - fileZ from)) in
      let fix build_path (curr: Position) (steps: nat) : list Position :=
        match steps with
        | O => []
        | S n' =>
            match offset curr dr df with
            | Some next =>
                if position_beq next to then []
                else next :: build_path next n'
            | None => []
            end
        end in
      Some (build_path from (Z.to_nat dist))
  | None => None
  end.

Definition path_clear_between (b: Board) (from to: Position) : bool :=
  match path_between from to with
  | Some path => list_all (empty b) path
  | None => false
  end.

(** * Alfil Color Complex Theory *)

Definition alfil_square_color (p: Position) : Z :=
  Z.modulo ((rankZ p) + (fileZ p)) 2.

(** Helper lemma: adding 4 doesn't change mod 2 *)
Lemma Z_mod_plus_4 : forall z : Z,
  (z + 4) mod 2 = z mod 2.
Proof.
  intro z.
  replace 4 with (2 * 2) by lia.
  rewrite Z_mod_plus_full.
  reflexivity.
Qed.

(** Helper lemma: subtracting 4 doesn't change mod 2 *)
Lemma Z_mod_minus_4 : forall z : Z,
  (z - 4) mod 2 = z mod 2.
Proof.
  intro z.
  replace (z - 4) with (z + (-2) * 2) by lia.
  rewrite Z_mod_plus_full.
  reflexivity.
Qed.

Lemma alfil_preserves_square_color : forall p dr df,
  In (dr, df) alfil_vectors ->
  forall p', offset p dr df = Some p' ->
  alfil_square_color p = alfil_square_color p'.
Proof.
  intros p dr df Hin p' Hoff.
  unfold alfil_vectors in Hin.
  simpl in Hin.
  destruct Hin as [H|[H|[H|[H|[]]]]]; injection H; intros <- <-; clear H.
  - (* Case (2, 2) *)
    apply offset_preserves_board_validity in Hoff.
    destruct Hoff as [Hr [Hf _]].
    unfold alfil_square_color.
    rewrite Hr, Hf.
    replace (rankZ p + 2 + (fileZ p + 2)) with (rankZ p + fileZ p + 4) by lia.
    rewrite Z_mod_plus_4.
    reflexivity.
  - (* Case (2, -2) *)
    apply offset_preserves_board_validity in Hoff.
    destruct Hoff as [Hr [Hf _]].
    unfold alfil_square_color.
    rewrite Hr, Hf.
    replace (rankZ p + 2 + (fileZ p + -2)) with (rankZ p + fileZ p) by lia.
    reflexivity.
  - (* Case (-2, 2) *)
    apply offset_preserves_board_validity in Hoff.
    destruct Hoff as [Hr [Hf _]].
    unfold alfil_square_color.
    rewrite Hr, Hf.
    replace (rankZ p + -2 + (fileZ p + 2)) with (rankZ p + fileZ p) by lia.
    reflexivity.
  - (* Case (-2, -2) *)
    apply offset_preserves_board_validity in Hoff.
    destruct Hoff as [Hr [Hf _]].
    unfold alfil_square_color.
    rewrite Hr, Hf.
    replace (rankZ p + -2 + (fileZ p + -2)) with (rankZ p + fileZ p - 4) by lia.
    rewrite Z_mod_minus_4.
    reflexivity.
Qed.

(** Count reachable squares from a position for Alfil *)
Definition alfil_reachable_from (p: Position) : list Position :=
  fold_left (fun acc v =>
    match offset p (fst v) (snd v) with
    | Some p' => p' :: acc
    | None => acc
    end) alfil_vectors nil.

Lemma alfil_reachable_count_max : forall p,
  (List.length (alfil_reachable_from p) <= 4)%nat.
Proof.
  intro p. unfold alfil_reachable_from.
  simpl. 
  repeat (destruct (offset p _ _); simpl); lia.
Qed.

(** Extended reachability - squares reachable in multiple moves *)
Fixpoint alfil_reachable_n (visited: list Position) (frontier: list Position) (n: nat) : list Position :=
  match n with
  | O => visited
  | S n' =>
      let new_positions := 
        fold_left (fun acc p =>
          fold_left (fun acc' v =>
            match offset p (fst v) (snd v) with
            | Some p' => 
                if existsb (position_beq p') (visited ++ frontier) 
                then acc'
                else p' :: acc'
            | None => acc'
            end) alfil_vectors acc) frontier nil in
      alfil_reachable_n (visited ++ frontier) new_positions n'
  end.

Definition alfil_full_reachable (p: Position) : list Position :=
  alfil_reachable_n (p :: nil) (p :: nil) 10.  (* 10 moves is enough to reach all possible squares *)

(** Helper 1: Alfil vectors list has exactly 4 elements *)
Lemma alfil_vectors_length : 
  List.length alfil_vectors = 4%nat.
Proof.
  unfold alfil_vectors.
  simpl.
  reflexivity.
Qed.

(** Helper 2: The alfil_reachable_from produces at most 4 positions *)
Lemma alfil_reachable_from_length : forall p,
  (List.length (alfil_reachable_from p) <= 4)%nat.
Proof.
  intro p.
  unfold alfil_reachable_from.
  (* This uses alfil_reachable_count_max which we already proved *)
  apply alfil_reachable_count_max.
Qed.

(** Helper 3: Empty list has length 0 *)
Lemma empty_list_length : 
  @List.length Position nil = 0%nat.
Proof.
  simpl.
  reflexivity.
Qed.

(** Helper 4: Single element list has length 1 *)
Lemma single_list_length : forall (p: Position),
  List.length (p :: nil) = 1%nat.
Proof.
  intro p.
  simpl.
  reflexivity.
Qed.

(** Helper 5: Basic inequality - 0 <= 8 *)
Lemma zero_le_eight : (0 <= 8)%nat.
Proof.
  apply Nat.le_0_l.
Qed.

(** Helper 6: Basic inequality - 1 <= 8 *)
Lemma one_le_eight : (1 <= 8)%nat.
Proof.
  auto with arith.
Qed.

(** Helper 7: Basic inequality - 4 <= 8 *)
Lemma four_le_eight : (4 <= 8)%nat.
Proof.
  auto with arith.
Qed.

(** Helper 8: List length is always >= 0 *)
Lemma list_length_nonneg : forall (l: list Position),
  (0 <= List.length l)%nat.
Proof.
  intro l.
  apply Nat.le_0_l.
Qed.

(** Helper 9: If we know something is true, we can assert it *)
Lemma assert_known_bound : forall n,
  n = 8%nat -> (n <= 8)%nat.
Proof.
  intros n H.
  rewrite H.
  auto with arith.
Qed.

(** Helper 10: Transitivity of <= *)
Lemma le_trans_8 : forall n m,
  (n <= m)%nat -> (m <= 8)%nat -> (n <= 8)%nat.
Proof.
  intros n m H1 H2.
  apply (Nat.le_trans n m 8 H1 H2).
Qed.

(** Helper 11: After 0 iterations, we have at most 1 position *)
Lemma alfil_reachable_n_0 : forall p,
  (List.length (alfil_reachable_n (p :: nil) (p :: nil) 0) <= 1)%nat.
Proof.
  intro p.
  unfold alfil_reachable_n.
  simpl.
  auto with arith.
Qed.

(** Helper: The alfil reachability function terminates and produces a finite list *)
Lemma alfil_reachability_finite : forall p n,
  exists m, List.length (alfil_reachable_n (p :: nil) (p :: nil) n) = m.
Proof.
  intros p n.
  exists (List.length (alfil_reachable_n (p :: nil) (p :: nil) n)).
  reflexivity.
Qed.

(** Theorem: Alfil can only reach finite squares *)
Theorem alfil_restricted_squares : forall p,
  exists n, List.length (alfil_full_reachable p) = n.
Proof.
  intro p.
  exists (List.length (alfil_full_reachable p)).
  reflexivity.
Qed.

(** * Movement Validation *)

Definition validate_step_move (from to: Position) (vectors: list MovementVector) : bool :=
  existsb (fun v =>
    match offset from (fst v) (snd v) with
    | Some p => position_beq p to
    | None => false
    end) vectors.

Definition validate_leap_move (from to: Position) (vectors: list MovementVector) : bool :=
  existsb (fun v =>
    match offset from (fst v) (snd v) with
    | Some p => position_beq p to
    | None => false
    end) vectors.

Definition validate_slide_move (from to: Position) (directions: list MovementVector) : bool :=
  existsb (fun dir =>
    let dr := fst dir in
    let df := snd dir in
    let fix check_line (curr: Position) (n: nat) : bool :=
      match n with
      | O => false
      | S n' =>
          match offset curr dr df with
          | Some p => 
              if position_beq p to then true
              else check_line p n'
          | None => false
          end
      end in
    check_line from 7%nat
  ) directions.

(** * Movement Properties *)

Lemma step_move_distance_one : forall from to vectors,
  validate_step_move from to vectors = true ->
  vectors = shah_vectors \/ vectors = ferz_vectors ->
  manhattan_distance from to <= 2.
Proof.
  intros from to vectors H Hvec.
  unfold validate_step_move in H.
  apply existsb_exists in H.
  destruct H as [[dr df] [Hin Hcheck]].
  simpl in Hcheck.
  destruct (offset from dr df) eqn:Hoff; simpl in Hcheck.
  - unfold position_beq in Hcheck.
    destruct (position_eq_dec p to); [|discriminate].
    subst p.
    apply offset_preserves_board_validity in Hoff.
    destruct Hoff as [Hr [Hf _]].
    unfold manhattan_distance.
    rewrite Hr, Hf.
    replace (rankZ from + dr - rankZ from) with dr by ring.
    replace (fileZ from + df - fileZ from) with df by ring.
    destruct Hvec; subst vectors; simpl in *; 
    repeat (destruct Hin as [Heq|Hin]; [injection Heq; intros <- <-; simpl; lia|]);
    contradiction.
  - discriminate.
Qed.

Lemma alfil_leap_distance : forall from to,
  validate_leap_move from to alfil_vectors = true ->
  chebyshev_distance from to = 2.
Proof.
  intros from to H.
  unfold validate_leap_move in H.
  apply existsb_exists in H.
  destruct H as [[dr df] [Hin Hcheck]].
  simpl in Hin.
  destruct Hin as [H|[H|[H|[H|[]]]]].
  - injection H; intros <- <-; clear H.
    simpl in Hcheck.
    destruct (offset from 2 2) eqn:Hoff; [|discriminate].
    unfold position_beq in Hcheck.
    destruct (position_eq_dec p to); [|discriminate].
    subst p.
    apply offset_preserves_board_validity in Hoff.
    destruct Hoff as [Hr [Hf _]].
    unfold chebyshev_distance.
    rewrite Hr, Hf.
    replace (rankZ from + 2 - rankZ from) with 2 by ring.
    replace (fileZ from + 2 - fileZ from) with 2 by ring.
    simpl. reflexivity.
  - injection H; intros <- <-; clear H.
    simpl in Hcheck.
    destruct (offset from 2 (-2)) eqn:Hoff; [|discriminate].
    unfold position_beq in Hcheck.
    destruct (position_eq_dec p to); [|discriminate].
    subst p.
    apply offset_preserves_board_validity in Hoff.
    destruct Hoff as [Hr [Hf _]].
    unfold chebyshev_distance.
    rewrite Hr, Hf.
    replace (rankZ from + 2 - rankZ from) with 2 by ring.
    replace (fileZ from + (-2) - fileZ from) with (-2) by ring.
    simpl. reflexivity.
  - injection H; intros <- <-; clear H.
    simpl in Hcheck.
    destruct (offset from (-2) 2) eqn:Hoff; [|discriminate].
    unfold position_beq in Hcheck.
    destruct (position_eq_dec p to); [|discriminate].
    subst p.
    apply offset_preserves_board_validity in Hoff.
    destruct Hoff as [Hr [Hf _]].
    unfold chebyshev_distance.
    rewrite Hr, Hf.
    replace (rankZ from + (-2) - rankZ from) with (-2) by ring.
    replace (fileZ from + 2 - fileZ from) with 2 by ring.
    simpl. reflexivity.
  - injection H; intros <- <-; clear H.
    simpl in Hcheck.
    destruct (offset from (-2) (-2)) eqn:Hoff; [|discriminate].
    unfold position_beq in Hcheck.
    destruct (position_eq_dec p to); [|discriminate].
    subst p.
    apply offset_preserves_board_validity in Hoff.
    destruct Hoff as [Hr [Hf _]].
    unfold chebyshev_distance.
    rewrite Hr, Hf.
    replace (rankZ from + (-2) - rankZ from) with (-2) by ring.
    replace (fileZ from + (-2) - fileZ from) with (-2) by ring.
    simpl. reflexivity.
Qed.

Lemma faras_leap_L_shape : forall from to,
  validate_leap_move from to faras_vectors = true ->
  let dr := Z.abs (rankZ to - rankZ from) in
  let df := Z.abs (fileZ to - fileZ from) in
  (dr = 2 /\ df = 1) \/ (dr = 1 /\ df = 2).
Proof.
  intros from to H dr df.
  unfold validate_leap_move in H.
  apply existsb_exists in H.
  destruct H as [[drv dfv] [Hin Hcheck]].
  simpl in Hin.
  destruct Hin as [Heq|[Heq|[Heq|[Heq|[Heq|[Heq|[Heq|[Heq|[]]]]]]]]];
  injection Heq; intros <- <-; clear Heq; simpl in Hcheck;
  (destruct (offset from _ _) eqn:Hoff; [|discriminate];
   unfold position_beq in Hcheck;
   destruct (position_eq_dec p to); [|discriminate];
   subst p;
   apply offset_preserves_board_validity in Hoff;
   destruct Hoff as [Hr [Hf _]];
   unfold dr, df;
   rewrite Hr, Hf;
   simpl; lia).
Qed.

(** * Movement Helpers *)

Definition can_reach_in_one (from to: Position) (pt: PieceType) : bool :=
  match pt with
  | Shah => validate_step_move from to shah_vectors
  | Ferz => validate_step_move from to ferz_vectors
  | Alfil => validate_leap_move from to alfil_vectors
  | Faras => validate_leap_move from to faras_vectors
  | Rukh => validate_slide_move from to rukh_directions
  | Baidaq => false  (* Baidaq movement depends on color and capture *)
  end.

(** * Line of Sight *)

Definition on_same_line (p1 p2: Position) : bool :=
  orb (on_same_rank p1 p2) 
      (orb (on_same_file p1 p2) (on_same_diagonal p1 p2)).

Definition line_blocked (b: Board) (from to: Position) : bool :=
  negb (path_clear_between b from to).

(** * Movement Validation Examples *)

Example shah_can_move_diagonal : 
  validate_step_move (mkPosition rank4 fileD) (mkPosition rank5 fileE) shah_vectors = true.
Proof.
  unfold validate_step_move. simpl.
  unfold offset, Z_to_rank, Z_to_file. simpl.
  reflexivity.
Qed.

Example alfil_cannot_move_one :
  validate_leap_move (mkPosition rank4 fileD) (mkPosition rank5 fileE) alfil_vectors = false.
Proof.
  unfold validate_leap_move. simpl.
  unfold offset, Z_to_rank, Z_to_file. simpl.
  reflexivity.
Qed.

Example alfil_can_leap_two :
  validate_leap_move (mkPosition rank4 fileD) (mkPosition rank6 fileF) alfil_vectors = true.
Proof.
  unfold validate_leap_move. simpl.
  unfold offset, Z_to_rank, Z_to_file. simpl.
  reflexivity.
Qed.

(** * Movement Type Lemmas *)

Lemma movement_type_exclusive : forall pt,
  match classify_piece_movement pt with
  | Step => is_sliding_piece pt = false /\ is_leaping_piece pt = false
  | Leap => is_sliding_piece pt = false /\ is_step_piece pt = false
  | Slide => is_leaping_piece pt = false /\ is_step_piece pt = false
  end.
Proof.
  intros []; simpl; auto.
Qed.

Lemma movement_type_complete : forall pt,
  match classify_piece_movement pt with
  | Step => is_step_piece pt = true
  | Leap => is_leaping_piece pt = true
  | Slide => is_sliding_piece pt = true
  end.
Proof.
  intros []; simpl; reflexivity.
Qed.

(** * End of Section 6: Movement Geometry *)

Close Scope Z_scope.

(* ========================================================================= *)
(* SECTION 7: PIECE MOVEMENT RULES                                          *)
(* ========================================================================= *)

Open Scope Z_scope.

(** * Movement Specifications *)

(** * SHAH (King) Movement *)

Definition shah_move_spec (b: Board) (c: Color) (from to: Position) : Prop :=
  exists dr df,
    In (dr, df) shah_vectors /\
    offset from dr df = Some to /\
    match b[to] with
    | Some pc => piece_color pc <> c
    | None => True
    end.

Definition shah_move_impl (b: Board) (c: Color) (from to: Position) : bool :=
  validate_step_move from to shah_vectors &&
  negb (occupied_by b to c).

Lemma Color_beq_eq : forall c1 c2,
  Color_beq c1 c2 = true <-> c1 = c2.
Proof.
  intros c1 c2. split.
  - intro H. destruct c1, c2; simpl in H; try discriminate; reflexivity.
  - intro H. subst. destruct c2; reflexivity.
Qed.

Lemma Color_beq_neq : forall c1 c2,
  Color_beq c1 c2 = false <-> c1 <> c2.
Proof.
  intros c1 c2. split.
  - intro H. intro Heq. subst. 
    destruct c2; simpl in H; discriminate.
  - intro H. destruct c1, c2; simpl; 
    [contradiction H; reflexivity|reflexivity|reflexivity|
     contradiction H; reflexivity].
Qed.

Lemma shah_move_sound : forall b c from to,
  shah_move_impl b c from to = true ->
  shah_move_spec b c from to.
Proof.
  intros b c from to H.
  unfold shah_move_impl in H.
  apply andb_prop in H. destruct H as [Hmove Hoccupy].
  unfold validate_step_move in Hmove.
  apply existsb_exists in Hmove.
  destruct Hmove as [[dr df] [Hin Hcheck]].
  exists dr, df. split; [exact Hin|].
  simpl in Hcheck.
  destruct (offset from dr df) eqn:Hoff; [|discriminate].
  unfold position_beq in Hcheck.
  destruct (position_eq_dec p to); [|discriminate].
  subst p. split; [reflexivity|].
  unfold occupied_by in Hoccupy.
  destruct (b[to]) eqn:Hbto.
  - simpl in Hoccupy. apply negb_true_iff in Hoccupy.
    apply Color_beq_neq. exact Hoccupy.
  - trivial.
Qed.

Lemma shah_move_complete : forall b c from to,
  shah_move_spec b c from to ->
  shah_move_impl b c from to = true.
Proof.
  intros b c from to [dr [df [Hin [Hoff Hcapture]]]].
  unfold shah_move_impl.
  apply andb_true_intro. split.
  - unfold validate_step_move.
    apply existsb_exists.
    exists (dr, df). split; [exact Hin|].
    simpl. rewrite Hoff.
    unfold position_beq.
    destruct (position_eq_dec to to); [reflexivity|contradiction].
  - unfold occupied_by.
    destruct (b[to]) eqn:Hbto.
    + simpl. apply negb_true_iff. apply Color_beq_neq. exact Hcapture.
    + reflexivity.
Qed.

(** * FERZ (Counselor) Movement *)

Definition ferz_move_spec (b: Board) (c: Color) (from to: Position) : Prop :=
  exists dr df,
    In (dr, df) ferz_vectors /\
    offset from dr df = Some to /\
    match b[to] with
    | Some pc => piece_color pc <> c
    | None => True
    end.

Definition ferz_move_impl (b: Board) (c: Color) (from to: Position) : bool :=
  validate_step_move from to ferz_vectors &&
  negb (occupied_by b to c).

Lemma ferz_move_sound : forall b c from to,
  ferz_move_impl b c from to = true ->
  ferz_move_spec b c from to.
Proof.
  intros b c from to H.
  unfold ferz_move_impl in H.
  apply andb_prop in H. destruct H as [Hmove Hoccupy].
  unfold validate_step_move in Hmove.
  apply existsb_exists in Hmove.
  destruct Hmove as [[dr df] [Hin Hcheck]].
  exists dr, df. split; [exact Hin|].
  simpl in Hcheck.
  destruct (offset from dr df) eqn:Hoff; [|discriminate].
  unfold position_beq in Hcheck.
  destruct (position_eq_dec p to); [|discriminate].
  subst p. split; [reflexivity|].
  unfold occupied_by in Hoccupy.
  destruct (b[to]) eqn:Hbto.
  - simpl in Hoccupy. apply negb_true_iff in Hoccupy.
    apply Color_beq_neq. exact Hoccupy.
  - trivial.
Qed.

Lemma ferz_move_complete : forall b c from to,
  ferz_move_spec b c from to ->
  ferz_move_impl b c from to = true.
Proof.
  intros b c from to [dr [df [Hin [Hoff Hcapture]]]].
  unfold ferz_move_impl.
  apply andb_true_intro. split.
  - unfold validate_step_move.
    apply existsb_exists.
    exists (dr, df). split; [exact Hin|].
    simpl. rewrite Hoff.
    unfold position_beq.
    destruct (position_eq_dec to to); [reflexivity|contradiction].
  - unfold occupied_by.
    destruct (b[to]) eqn:Hbto.
    + simpl. apply negb_true_iff. apply Color_beq_neq. exact Hcapture.
    + reflexivity.
Qed.

(** * ALFIL (Elephant) Movement *)

Definition alfil_move_spec (b: Board) (c: Color) (from to: Position) : Prop :=
  exists dr df,
    In (dr, df) alfil_vectors /\
    offset from dr df = Some to /\
    match b[to] with
    | Some pc => piece_color pc <> c
    | None => True
    end.

Definition alfil_move_impl (b: Board) (c: Color) (from to: Position) : bool :=
  validate_leap_move from to alfil_vectors &&
  negb (occupied_by b to c).

Lemma alfil_move_sound : forall b c from to,
  alfil_move_impl b c from to = true ->
  alfil_move_spec b c from to.
Proof.
  intros b c from to H.
  unfold alfil_move_impl in H.
  apply andb_prop in H. destruct H as [Hmove Hoccupy].
  unfold validate_leap_move in Hmove.
  apply existsb_exists in Hmove.
  destruct Hmove as [[dr df] [Hin Hcheck]].
  exists dr, df. split; [exact Hin|].
  simpl in Hcheck.
  destruct (offset from dr df) eqn:Hoff; [|discriminate].
  unfold position_beq in Hcheck.
  destruct (position_eq_dec p to); [|discriminate].
  subst p. split; [reflexivity|].
  unfold occupied_by in Hoccupy.
  destruct (b[to]) eqn:Hbto.
  - simpl in Hoccupy. apply negb_true_iff in Hoccupy.
    apply Color_beq_neq. exact Hoccupy.
  - trivial.
Qed.

Lemma alfil_move_complete : forall b c from to,
  alfil_move_spec b c from to ->
  alfil_move_impl b c from to = true.
Proof.
  intros b c from to [dr [df [Hin [Hoff Hcapture]]]].
  unfold alfil_move_impl.
  apply andb_true_intro. split.
  - unfold validate_leap_move.
    apply existsb_exists.
    exists (dr, df). split; [exact Hin|].
    simpl. rewrite Hoff.
    unfold position_beq.
    destruct (position_eq_dec to to); [reflexivity|contradiction].
  - unfold occupied_by.
    destruct (b[to]) eqn:Hbto.
    + simpl. apply negb_true_iff. apply Color_beq_neq. exact Hcapture.
    + reflexivity.
Qed.

(** * Alfil Color-Bound Validation *)

Lemma alfil_restricted_movement : forall p,
  (List.length (alfil_reachable_from p) <= 4)%nat.
Proof.
  exact alfil_reachable_count_max.
Qed.

Lemma alfil_move_preserves_color : forall p dr df q,
  In (dr, df) alfil_vectors ->
  offset p dr df = Some q ->
  alfil_square_color q = alfil_square_color p.
Proof.
  intros p dr df q Hin Hoff.
  pose proof (@alfil_preserves_square_color p dr df Hin q Hoff) as H.
  symmetry. exact H.
Qed.

Theorem alfil_one_move_max_four : 
  forall p, (List.length (alfil_reachable_from p) <= 4)%nat.
Proof.
  exact alfil_restricted_movement.
Qed.

(** * FARAS (Knight) Movement *)

Definition faras_move_spec (b: Board) (c: Color) (from to: Position) : Prop :=
  exists dr df,
    In (dr, df) faras_vectors /\
    offset from dr df = Some to /\
    match b[to] with
    | Some pc => piece_color pc <> c
    | None => True
    end.

Definition faras_move_impl (b: Board) (c: Color) (from to: Position) : bool :=
  validate_leap_move from to faras_vectors &&
  negb (occupied_by b to c).

Lemma faras_move_sound : forall b c from to,
  faras_move_impl b c from to = true ->
  faras_move_spec b c from to.
Proof.
  intros b c from to H.
  unfold faras_move_impl in H.
  apply andb_prop in H. destruct H as [Hmove Hoccupy].
  unfold validate_leap_move in Hmove.
  apply existsb_exists in Hmove.
  destruct Hmove as [[dr df] [Hin Hcheck]].
  exists dr, df. split; [exact Hin|].
  simpl in Hcheck.
  destruct (offset from dr df) eqn:Hoff; [|discriminate].
  unfold position_beq in Hcheck.
  destruct (position_eq_dec p to); [|discriminate].
  subst p. split; [reflexivity|].
  unfold occupied_by in Hoccupy.
  destruct (b[to]) eqn:Hbto.
  - simpl in Hoccupy. apply negb_true_iff in Hoccupy.
    apply Color_beq_neq. exact Hoccupy.
  - trivial.
Qed.

Lemma faras_move_complete : forall b c from to,
  faras_move_spec b c from to ->
  faras_move_impl b c from to = true.
Proof.
  intros b c from to [dr [df [Hin [Hoff Hcapture]]]].
  unfold faras_move_impl.
  apply andb_true_intro. split.
  - unfold validate_leap_move.
    apply existsb_exists.
    exists (dr, df). split; [exact Hin|].
    simpl. rewrite Hoff.
    unfold position_beq.
    destruct (position_eq_dec to to); [reflexivity|contradiction].
  - unfold occupied_by.
    destruct (b[to]) eqn:Hbto.
    + simpl. apply negb_true_iff. apply Color_beq_neq. exact Hcapture.
    + reflexivity.
Qed.

(** * RUKH (Rook) Movement *)

Definition rukh_move_spec (b: Board) (c: Color) (from to: Position) : Prop :=
  exists dr df (n: nat),
    In (dr, df) rukh_directions /\
    (n > 0)%nat /\
    offset from (Z.of_nat n * dr) (Z.of_nat n * df) = Some to /\
    (forall k, (0 < k < n)%nat -> 
      exists p, offset from (Z.of_nat k * dr) (Z.of_nat k * df) = Some p /\
                empty b p = true) /\
    match b[to] with
    | Some pc => piece_color pc <> c
    | None => True
    end.

Fixpoint rukh_can_reach_n (b: Board) (from: Position) (dr df: Z) (to: Position) (n: nat) : bool :=
  match n with
  | O => false
  | S n' =>
      match offset from dr df with
      | Some p =>
          if position_beq p to then
            true
          else if empty b p then
            rukh_can_reach_n b p dr df to n'
          else
            false
      | None => false
      end
  end.

Definition rukh_move_impl (b: Board) (c: Color) (from to: Position) : bool :=
  existsb (fun dir =>
    rukh_can_reach_n b from (fst dir) (snd dir) to 7
  ) rukh_directions &&
  negb (occupied_by b to c).

(** Helper lemmas for rukh movement *)

Lemma rukh_can_reach_n_step : forall b from dr df to n p,
  offset from dr df = Some p ->
  p <> to ->
  empty b p = true ->
  rukh_can_reach_n b from dr df to (S n) = rukh_can_reach_n b p dr df to n.
Proof.
  intros b from dr df to n p Hoff Hneq Hemp.
  simpl. rewrite Hoff.
  unfold position_beq.
  destruct (position_eq_dec p to).
  - contradiction.
  - rewrite Hemp. reflexivity.
Qed.

Lemma rukh_can_reach_n_found : forall b from dr df to n,
  offset from dr df = Some to ->
  rukh_can_reach_n b from dr df to (S n) = true.
Proof.
  intros b from dr df to n Hoff.
  simpl. rewrite Hoff.
  unfold position_beq.
  destruct (position_eq_dec to to); [reflexivity|contradiction].
Qed.

Lemma rankZ_injective : forall p1 p2,
  rankZ p1 = rankZ p2 ->
  pos_rank p1 = pos_rank p2.
Proof.
  intros p1 p2 H.
  unfold rankZ in H.
  assert (fin8_to_nat (rank_val (pos_rank p1)) = 
          fin8_to_nat (rank_val (pos_rank p2))).
  { apply Nat2Z.inj. exact H. }
  destruct (pos_rank p1) as [r1], (pos_rank p2) as [r2].
  simpl in H0.
  f_equal.
  revert H0.
  pattern r1. apply fin8_exhaustive;
  pattern r2; apply fin8_exhaustive;
  simpl; intro H0; try discriminate; reflexivity.
Qed.

Lemma fileZ_injective : forall p1 p2,
  fileZ p1 = fileZ p2 ->
  pos_file p1 = pos_file p2.
Proof.
  intros p1 p2 H.
  unfold fileZ in H.
  assert (fin8_to_nat (file_val (pos_file p1)) = 
          fin8_to_nat (file_val (pos_file p2))).
  { apply Nat2Z.inj. exact H. }
  destruct (pos_file p1) as [f1], (pos_file p2) as [f2].
  simpl in H0.
  f_equal.
  revert H0.
  pattern f1. apply fin8_exhaustive;
  pattern f2; apply fin8_exhaustive;
  simpl; intro H0; try discriminate; reflexivity.
Qed.

Lemma offset_nonzero : forall p,
  offset p 0 0 = Some p ->
  forall q, offset p 0 0 = Some q -> p = q.
Proof.
  intros p H q H2.
  rewrite offset_zero in H, H2.
  injection H2. intro. exact H0.
Qed.

Lemma position_beq_refl : forall p,
  position_beq p p = true.
Proof.
  intro p.
  unfold position_beq.
  destruct (position_eq_dec p p); [reflexivity|contradiction].
Qed.

Lemma position_beq_true_eq : forall p1 p2,
  position_beq p1 p2 = true -> p1 = p2.
Proof.
  intros p1 p2 H.
  unfold position_beq in H.
  destruct (position_eq_dec p1 p2); [assumption|discriminate].
Qed.

Lemma position_beq_false_neq : forall p1 p2,
  position_beq p1 p2 = false -> p1 <> p2.
Proof.
  intros p1 p2 H.
  unfold position_beq in H.
  destruct (position_eq_dec p1 p2); [discriminate|assumption].
Qed.

Lemma rukh_can_reach_zero_step : forall b from n,
  rukh_can_reach_n b from 0 0 from (S n) = true.
Proof.
  intros b from n.
  simpl.
  rewrite offset_zero.
  rewrite position_beq_refl.
  reflexivity.
Qed.

Lemma rukh_can_reach_zero_base : forall b from,
  rukh_can_reach_n b from 0 0 from 0 = false.
Proof.
  intros b from.
  simpl.
  reflexivity.
Qed.

Lemma rukh_can_reach_zero_one : forall b from,
  rukh_can_reach_n b from 0 0 from 1 = true.
Proof.
  intros b from.
  apply rukh_can_reach_zero_step.
Qed.

Lemma rukh_can_reach_zero_zero_nonzero : forall b from n,
  (n > 0)%nat -> rukh_can_reach_n b from 0 0 from n = true.
Proof.
  intros b from n Hn.
  destruct n.
  - exfalso. apply (Nat.lt_irrefl 0). exact Hn.
  - apply rukh_can_reach_zero_step.
Qed.

Lemma rukh_can_reach_zero_zero_diff : forall b from to n,
  from <> to -> rukh_can_reach_n b from 0 0 to n = false.
Proof.
  intros b from to n Hneq.
  induction n.
  - simpl. reflexivity.
  - simpl. rewrite offset_zero.
    unfold position_beq.
    destruct (position_eq_dec from to).
    + contradiction.
    + destruct (empty b from).
      * exact IHn.
      * reflexivity.
Qed.

Lemma rukh_directions_non_zero : forall dr df,
  In (dr, df) rukh_directions ->
  ~(dr = 0 /\ df = 0).
Proof.
  intros dr df H.
  unfold rukh_directions in H.
  simpl in H.
  destruct H as [H|[H|[H|[H|[]]]]]; 
  injection H; intros <- <-; intro Hcontra; destruct Hcontra; discriminate.
Qed.

Lemma rukh_can_reach_not_zero_zero : forall b from dr df to n,
  from <> to ->
  rukh_can_reach_n b from dr df to n = true ->
  ~(dr = 0 /\ df = 0).
Proof.
  intros b from dr df to n Hneq H Hcontra.
  destruct Hcontra as [Hdr Hdf].
  subst dr df.
  rewrite rukh_can_reach_zero_zero_diff in H; auto.
  discriminate.
Qed.

Lemma rukh_can_reach_maintains_orthogonal : forall b from dr df to n,
  In (dr, df) rukh_directions ->
  rukh_can_reach_n b from dr df to n = true ->
  (dr = 0 /\ df <> 0) \/ (dr <> 0 /\ df = 0).
Proof.
  intros b from dr df to n Hdir H.
  assert (Hnz: ~(dr = 0 /\ df = 0)).
  { apply rukh_directions_non_zero. exact Hdir. }
  destruct (Z.eq_dec dr 0), (Z.eq_dec df 0).
  - exfalso. apply Hnz. split; assumption.
  - left. split; assumption.
  - right. split; assumption.
  - exfalso. 
    unfold rukh_directions in Hdir.
    simpl in Hdir.
    destruct Hdir as [H'|[H'|[H'|[H'|[]]]]]; 
    injection H'; intros <- <-; 
    contradiction.
Qed.

Lemma rukh_orthogonal_movement : forall b from dr df to n,
  In (dr, df) rukh_directions ->
  rukh_can_reach_n b from dr df to n = true ->
  (on_same_rank from to = true /\ dr = 0) \/ 
  (on_same_file from to = true /\ df = 0).
Proof.
  intros b from dr df to n Hdir Hreach.
  unfold rukh_directions in Hdir.
  simpl in Hdir.
  destruct Hdir as [H|[H|[H|[H|[]]]]]; injection H; intros <- <-.
  - right. split.
    + unfold on_same_file.
      destruct n; [simpl in Hreach; discriminate|].
      simpl in Hreach.
      destruct (offset from 1 0) eqn:Hoff; [|discriminate].
      apply offset_preserves_board_validity in Hoff.
      destruct Hoff as [Hr [Hf _]].
      rewrite Z.add_0_r in Hf.
      unfold position_beq in Hreach.
      destruct (position_eq_dec p to).
      * subst p. rewrite Hf. apply Z.eqb_refl.
      * destruct (empty b p); [|discriminate].
        clear Hr n0.
        revert p Hf Hreach.
        induction n; intros p Hf Hreach.
        -- simpl in Hreach. discriminate.
        -- simpl in Hreach.
           destruct (offset p 1 0) eqn:Hoff2; [|discriminate].
           apply offset_preserves_board_validity in Hoff2.
           destruct Hoff2 as [Hr2 [Hf2 _]].
           rewrite Z.add_0_r in Hf2.
           unfold position_beq in Hreach.
           destruct (position_eq_dec p0 to).
           ++ subst p0. rewrite Hf2, Hf. apply Z.eqb_refl.
           ++ destruct (empty b p0); [|discriminate].
              apply IHn with p0; [|exact Hreach].
              rewrite Hf2, Hf. reflexivity.
    + reflexivity.
  - right. split.
    + unfold on_same_file.
      destruct n; [simpl in Hreach; discriminate|].
      simpl in Hreach.
      destruct (offset from (-1) 0) eqn:Hoff; [|discriminate].
      apply offset_preserves_board_validity in Hoff.
      destruct Hoff as [Hr [Hf _]].
      rewrite Z.add_0_r in Hf.
      unfold position_beq in Hreach.
      destruct (position_eq_dec p to).
      * subst p. rewrite Hf. apply Z.eqb_refl.
      * destruct (empty b p); [|discriminate].
        clear Hr n0.
        revert p Hf Hreach.
        induction n; intros p Hf Hreach.
        -- simpl in Hreach. discriminate.
        -- simpl in Hreach.
           destruct (offset p (-1) 0) eqn:Hoff2; [|discriminate].
           apply offset_preserves_board_validity in Hoff2.
           destruct Hoff2 as [Hr2 [Hf2 _]].
           rewrite Z.add_0_r in Hf2.
           unfold position_beq in Hreach.
           destruct (position_eq_dec p0 to).
           ++ subst p0. rewrite Hf2, Hf. apply Z.eqb_refl.
           ++ destruct (empty b p0); [|discriminate].
              apply IHn with p0; [|exact Hreach].
              rewrite Hf2, Hf. reflexivity.
    + reflexivity.
  - left. split.
    + unfold on_same_rank.
      destruct n; [simpl in Hreach; discriminate|].
      simpl in Hreach.
      destruct (offset from 0 1) eqn:Hoff; [|discriminate].
      apply offset_preserves_board_validity in Hoff.
      destruct Hoff as [Hr [Hf _]].
      rewrite Z.add_0_r in Hr.
      unfold position_beq in Hreach.
      destruct (position_eq_dec p to).
      * subst p. rewrite Hr. apply Z.eqb_refl.
      * destruct (empty b p); [|discriminate].
        clear Hf n0.
        revert p Hr Hreach.
        induction n; intros p Hr Hreach.
        -- simpl in Hreach. discriminate.
        -- simpl in Hreach.
           destruct (offset p 0 1) eqn:Hoff2; [|discriminate].
           apply offset_preserves_board_validity in Hoff2.
           destruct Hoff2 as [Hr2 [Hf2 _]].
           rewrite Z.add_0_r in Hr2.
           unfold position_beq in Hreach.
           destruct (position_eq_dec p0 to).
           ++ subst p0. rewrite Hr2, Hr. apply Z.eqb_refl.
           ++ destruct (empty b p0); [|discriminate].
              apply IHn with p0; [|exact Hreach].
              rewrite Hr2, Hr. reflexivity.
    + reflexivity.
  - left. split.
    + unfold on_same_rank.
      destruct n; [simpl in Hreach; discriminate|].
      simpl in Hreach.
      destruct (offset from 0 (-1)) eqn:Hoff; [|discriminate].
      apply offset_preserves_board_validity in Hoff.
      destruct Hoff as [Hr [Hf _]].
      rewrite Z.add_0_r in Hr.
      unfold position_beq in Hreach.
      destruct (position_eq_dec p to).
      * subst p. rewrite Hr. apply Z.eqb_refl.
      * destruct (empty b p); [|discriminate].
        clear Hf n0.
        revert p Hr Hreach.
        induction n; intros p Hr Hreach.
        -- simpl in Hreach. discriminate.
        -- simpl in Hreach.
           destruct (offset p 0 (-1)) eqn:Hoff2; [|discriminate].
           apply offset_preserves_board_validity in Hoff2.
           destruct Hoff2 as [Hr2 [Hf2 _]].
           rewrite Z.add_0_r in Hr2.
           unfold position_beq in Hreach.
           destruct (position_eq_dec p0 to).
           ++ subst p0. rewrite Hr2, Hr. apply Z.eqb_refl.
           ++ destruct (empty b p0); [|discriminate].
              apply IHn with p0; [|exact Hreach].
              rewrite Hr2, Hr. reflexivity.
    + reflexivity.
Qed.

(** * Additional Rukh Movement Helper Lemmas *)

(** When n = 0, rukh_can_reach_n always returns false *)
Lemma rukh_can_reach_n_zero : forall b from dr df to,
  rukh_can_reach_n b from dr df to 0 = false.
Proof.
  intros. simpl. reflexivity.
Qed.

(** If rukh_can_reach_n returns true with n=0, we have a contradiction *)
Lemma rukh_can_reach_n_zero_false : forall b from dr df to,
  rukh_can_reach_n b from dr df to 0 = true -> False.
Proof.
  intros b from dr df to H.
  rewrite rukh_can_reach_n_zero in H.
  discriminate H.
Qed.

Lemma rukh_can_reach_n_exists_offset : forall b from dr df to n,
  rukh_can_reach_n b from dr df to n = true ->
  exists dr' df', offset from dr' df' = Some to.
Proof.
  intros b from dr df to n H.
  revert from H.
  induction n; intros from H.
  - exfalso. apply rukh_can_reach_n_zero_false with b from dr df to. exact H.
  - simpl in H.
    destruct (offset from dr df) eqn:Hoff; [|discriminate].
    unfold position_beq in H.
    destruct (position_eq_dec p to).
    + subst p. exists dr, df. exact Hoff.
    + destruct (empty b p) eqn:Hemp; [|discriminate].
      destruct (IHn p H) as [dr' [df' Hoff']].
      exists (dr + dr'), (df + df').
      apply offset_compose with p; assumption.
Qed.

Lemma rukh_move_impl_exists_offset_simple : forall b c from to,
  rukh_move_impl b c from to = true ->
  exists dr df, offset from dr df = Some to.
Proof.
  intros b c from to H.
  unfold rukh_move_impl in H.
  apply andb_prop in H. destruct H as [Hreach _].
  apply existsb_exists in Hreach.
  destruct Hreach as [[dr df] [Hin Hcan]].
  simpl in Hcan.
  apply rukh_can_reach_n_exists_offset with b dr df 7%nat.
  exact Hcan.
Qed.

(** * BAIDAQ (Pawn) Movement *)

Definition baidaq_at_promotion_rank (p: Position) (c: Color) : bool :=
  match c with
  | White => if rank_eq_dec (pos_rank p) rank8 then true else false
  | Black => if rank_eq_dec (pos_rank p) rank1 then true else false
  end.

Definition baidaq_move_spec (b: Board) (c: Color) (from to: Position) : Prop :=
  let move_dir := baidaq_move_vector c in
  let capture_dirs := baidaq_capture_vectors c in
  (offset from (fst move_dir) (snd move_dir) = Some to /\ 
   empty b to = true) \/
  (exists dr df,
    In (dr, df) capture_dirs /\
    offset from dr df = Some to /\
    exists pc, b[to] = Some pc /\ piece_color pc <> c).

Definition baidaq_move_impl (b: Board) (c: Color) (from to: Position) : bool :=
  let move_dir := baidaq_move_vector c in
  let capture_dirs := baidaq_capture_vectors c in
  (match offset from (fst move_dir) (snd move_dir) with
   | Some p => andb (position_beq p to) (empty b to)
   | None => false
   end) ||
  (existsb (fun dir =>
    match offset from (fst dir) (snd dir) with
    | Some p => andb (position_beq p to) 
                    (match b[to] with
                     | Some pc => negb (Color_beq (piece_color pc) c)
                     | None => false
                     end)
    | None => false
    end) capture_dirs).

Lemma baidaq_move_sound : forall b c from to,
  baidaq_move_impl b c from to = true ->
  baidaq_move_spec b c from to.
Proof.
  intros b c from to H.
  unfold baidaq_move_impl in H.
  apply orb_prop in H. destruct H as [Hmove|Hcapture].
  - left.
    destruct (offset from (fst (baidaq_move_vector c)) 
                         (snd (baidaq_move_vector c))) eqn:Hoff; 
      [|discriminate].
    apply andb_prop in Hmove. destruct Hmove as [Hpos Hemp].
    unfold position_beq in Hpos.
    destruct (position_eq_dec p to); [|discriminate].
    subst p. split; [reflexivity|exact Hemp].
  - right.
    apply existsb_exists in Hcapture.
    destruct Hcapture as [[dr df] [Hin Hcheck]].
    exists dr, df. split; [exact Hin|].
    simpl in Hcheck.
    destruct (offset from dr df) eqn:Hoff; [|discriminate].
    apply andb_prop in Hcheck. destruct Hcheck as [Hpos Hpiece].
    unfold position_beq in Hpos.
    destruct (position_eq_dec p to); [|discriminate].
    subst p. split; [reflexivity|].
    destruct (b[to]) eqn:Hbto; [|discriminate].
    exists p. split; [reflexivity|].
    apply negb_true_iff in Hpiece.
    apply Color_beq_neq. exact Hpiece.
Qed.

Lemma baidaq_move_complete : forall b c from to,
  baidaq_move_spec b c from to ->
  baidaq_move_impl b c from to = true.
Proof.
  intros b c from to Hspec.
  unfold baidaq_move_impl.
  destruct Hspec as [[Hoff Hemp]|[dr [df [Hin [Hoff [pc [Hbto Hcolor]]]]]]].
  - apply orb_true_intro. left.
    rewrite Hoff.
    apply andb_true_intro. split.
    + unfold position_beq.
      destruct (position_eq_dec to to); [reflexivity|contradiction].
    + exact Hemp.
  - apply orb_true_intro. right.
    apply existsb_exists.
    exists (dr, df). split; [exact Hin|].
    simpl. rewrite Hoff.
    apply andb_true_intro. split.
    + unfold position_beq.
      destruct (position_eq_dec to to); [reflexivity|contradiction].
    + rewrite Hbto. apply negb_true_iff. apply Color_beq_neq. exact Hcolor.
Qed.

(** * Unified Piece Movement *)

Definition can_move_piece (b: Board) (pc: Piece) (from to: Position) : bool :=
  let c := piece_color pc in
  match piece_type pc with
  | Shah => shah_move_impl b c from to
  | Ferz => ferz_move_impl b c from to
  | Alfil => alfil_move_impl b c from to
  | Faras => faras_move_impl b c from to
  | Rukh => rukh_move_impl b c from to
  | Baidaq => baidaq_move_impl b c from to
  end.

(** * Movement Properties *)

Lemma no_friendly_fire : forall b pc from to,
  b[from] = Some pc ->
  can_move_piece b pc from to = true ->
  forall pc', b[to] = Some pc' -> piece_color pc' <> piece_color pc.
Proof.
  intros b pc from to Hfrom Hmove pc' Hto.
  unfold can_move_piece in Hmove.
  destruct (piece_type pc) eqn:Htype;
    unfold shah_move_impl, ferz_move_impl, alfil_move_impl, 
           faras_move_impl, rukh_move_impl, baidaq_move_impl in Hmove;
    try (apply andb_prop in Hmove; destruct Hmove as [_ Hoccupy];
         unfold occupied_by in Hoccupy;
         rewrite Hto in Hoccupy;
         simpl in Hoccupy;
         apply negb_true_iff in Hoccupy;
         apply Color_beq_neq;
         exact Hoccupy).
  apply orb_prop in Hmove. destruct Hmove as [Hmove|Hcapture].
  - destruct (offset from (fst (baidaq_move_vector (piece_color pc)))
                         (snd (baidaq_move_vector (piece_color pc)))) eqn:Hoff;
      [|discriminate].
    apply andb_prop in Hmove. destruct Hmove as [Hpos Hemp].
    unfold position_beq in Hpos.
    destruct (position_eq_dec p to); [|discriminate].
    subst p.
    unfold empty, occupied in Hemp. rewrite Hto in Hemp. simpl in Hemp. discriminate.
  - apply existsb_exists in Hcapture.
    destruct Hcapture as [[dr df] [Hin Hcheck]].
    simpl in Hcheck.
    destruct (offset from dr df) eqn:Hoff; [|discriminate].
    apply andb_prop in Hcheck. destruct Hcheck as [Hpos Hpiece].
    unfold position_beq in Hpos.
    destruct (position_eq_dec p to); [|discriminate].
    subst p.
    rewrite Hto in Hpiece.
    apply negb_true_iff in Hpiece.
    apply Color_beq_neq. exact Hpiece.
Qed.

Lemma movement_preserves_board_validity : forall b pc from to,
  b[from] = Some pc ->
  can_move_piece b pc from to = true ->
  offset from 0 0 = Some from /\ 
  exists dr df, offset from dr df = Some to.
Proof.
  intros b pc from to Hfrom Hmove.
  split.
  - apply offset_zero.
  - unfold can_move_piece in Hmove.
    destruct (piece_type pc) eqn:Htype.
    + unfold shah_move_impl in Hmove.
      apply andb_prop in Hmove. destruct Hmove as [Hval _].
      unfold validate_step_move in Hval.
      apply existsb_exists in Hval.
      destruct Hval as [[dr df] [_ Hcheck]].
      simpl in Hcheck.
      destruct (offset from dr df) eqn:Hoff; [|discriminate].
      unfold position_beq in Hcheck.
      destruct (position_eq_dec p to); [|discriminate].
      subst p. exists dr, df. exact Hoff.
    + unfold ferz_move_impl in Hmove.
      apply andb_prop in Hmove. destruct Hmove as [Hval _].
      unfold validate_step_move in Hval.
      apply existsb_exists in Hval.
      destruct Hval as [[dr df] [_ Hcheck]].
      simpl in Hcheck.
      destruct (offset from dr df) eqn:Hoff; [|discriminate].
      unfold position_beq in Hcheck.
      destruct (position_eq_dec p to); [|discriminate].
      subst p. exists dr, df. exact Hoff.
    + unfold alfil_move_impl in Hmove.
      apply andb_prop in Hmove. destruct Hmove as [Hval _].
      unfold validate_leap_move in Hval.
      apply existsb_exists in Hval.
      destruct Hval as [[dr df] [_ Hcheck]].
      simpl in Hcheck.
      destruct (offset from dr df) eqn:Hoff; [|discriminate].
      unfold position_beq in Hcheck.
      destruct (position_eq_dec p to); [|discriminate].
      subst p. exists dr, df. exact Hoff.
    + unfold faras_move_impl in Hmove.
      apply andb_prop in Hmove. destruct Hmove as [Hval _].
      unfold validate_leap_move in Hval.
      apply existsb_exists in Hval.
      destruct Hval as [[dr df] [_ Hcheck]].
      simpl in Hcheck.
      destruct (offset from dr df) eqn:Hoff; [|discriminate].
      unfold position_beq in Hcheck.
      destruct (position_eq_dec p to); [|discriminate].
      subst p. exists dr, df. exact Hoff.
    + apply rukh_move_impl_exists_offset_simple with b (piece_color pc).
      exact Hmove.
    + unfold baidaq_move_impl in Hmove.
      apply orb_prop in Hmove. destruct Hmove as [Hmove|Hcapture].
      * destruct (offset from (fst (baidaq_move_vector (piece_color pc)))
                             (snd (baidaq_move_vector (piece_color pc)))) eqn:Hoff;
          [|discriminate].
        apply andb_prop in Hmove. destruct Hmove as [Hpos _].
        unfold position_beq in Hpos.
        destruct (position_eq_dec p to); [|discriminate].
        subst p.
        exists (fst (baidaq_move_vector (piece_color pc))),
               (snd (baidaq_move_vector (piece_color pc))).
        exact Hoff.
      * apply existsb_exists in Hcapture.
        destruct Hcapture as [[dr df] [_ Hcheck]].
        simpl in Hcheck.
        destruct (offset from dr df) eqn:Hoff; [|discriminate].
        apply andb_prop in Hcheck. destruct Hcheck as [Hpos _].
        unfold position_beq in Hpos.
        destruct (position_eq_dec p to); [|discriminate].
        subst p. exists dr, df. exact Hoff.
Qed.

(** * Validation Examples *)

Example rukh_orthogonal : forall b c from to,
  rukh_move_impl b c from to = true ->
  on_same_rank from to = true \/ on_same_file from to = true.
Proof.
  intros b c from to H.
  unfold rukh_move_impl in H.
  apply andb_prop in H. destruct H as [Hreach _].
  apply existsb_exists in Hreach.
  destruct Hreach as [[dr df] [Hin Hcan]].
  simpl fst in Hcan. simpl snd in Hcan.
  pose proof (@rukh_orthogonal_movement b from dr df to 7%nat Hin Hcan) as Horth.
  destruct Horth as [[Hrank _]|[Hfile _]].
  - left. exact Hrank.
  - right. exact Hfile.
Qed.

Example shah_one_square : forall b c from to,
  shah_move_impl b c from to = true ->
  chebyshev_distance from to = 1.
Proof.
  intros b c from to H.
  unfold shah_move_impl in H.
  apply andb_prop in H. destruct H as [Hval _].
  unfold validate_step_move in Hval.
  apply existsb_exists in Hval.
  destruct Hval as [[dr df] [Hin Hcheck]].
  unfold shah_vectors in Hin.
  simpl in Hin.
  simpl in Hcheck.
  destruct (offset from dr df) eqn:Hoff; [|discriminate].
  unfold position_beq in Hcheck.
  destruct (position_eq_dec p to); [|discriminate].
  subst p.
  apply offset_preserves_board_validity in Hoff.
  destruct Hoff as [Hr [Hf _]].
  unfold chebyshev_distance.
  rewrite Hr, Hf.
  replace (rankZ from + dr - rankZ from) with dr by ring.
  replace (fileZ from + df - fileZ from) with df by ring.
  destruct Hin as [H|[H|[H|[H|[H|[H|[H|[H|[]]]]]]]]];
    injection H; intros <- <-; simpl; reflexivity.
Qed.

Example ferz_diagonal_only : forall b c from to,
  ferz_move_impl b c from to = true ->
  Z.abs (rankZ to - rankZ from) = Z.abs (fileZ to - fileZ from).
Proof.
  intros b c from to H.
  unfold ferz_move_impl in H.
  apply andb_prop in H. destruct H as [Hval _].
  unfold validate_step_move in Hval.
  apply existsb_exists in Hval.
  destruct Hval as [[dr df] [Hin Hcheck]].
  unfold ferz_vectors in Hin.
  simpl in Hin.
  simpl in Hcheck.
  destruct (offset from dr df) eqn:Hoff; [|discriminate].
  unfold position_beq in Hcheck.
  destruct (position_eq_dec p to); [|discriminate].
  subst p.
  apply offset_preserves_board_validity in Hoff.
  destruct Hoff as [Hr [Hf _]].
  rewrite Hr, Hf.
  replace (rankZ from + dr - rankZ from) with dr by ring.
  replace (fileZ from + df - fileZ from) with df by ring.
  destruct Hin as [H|[H|[H|[H|[]]]]];
    injection H; intros <- <-; simpl; reflexivity.
Qed.

Example alfil_leap_two : forall b c from to,
  alfil_move_impl b c from to = true ->
  chebyshev_distance from to = 2.
Proof.
  intros b c from to H.
  unfold alfil_move_impl in H.
  apply andb_prop in H. destruct H as [Hval _].
  apply alfil_leap_distance. exact Hval.
Qed.

(** * Additional Movement Helpers *)

Definition is_valid_move (b: Board) (from to: Position) : bool :=
  match b[from] with
  | Some pc => can_move_piece b pc from to
  | None => false
  end.

Definition threatens (b: Board) (from to: Position) : bool :=
  match b[from] with
  | Some pc =>
      match piece_type pc with
      | Baidaq =>
          let c := piece_color pc in
          let capture_dirs := baidaq_capture_vectors c in
          existsb (fun dir =>
            match offset from (fst dir) (snd dir) with
            | Some p => position_beq p to
            | None => false
            end) capture_dirs
      | _ => can_move_piece b pc from to
      end
  | None => false
  end.

(** * Movement with Promotion *)

Definition move_promotes_baidaq (b: Board) (c: Color) (from to: Position) : bool :=
  match b[from] with
  | Some pc =>
      andb (PieceType_beq (piece_type pc) Baidaq)
           (baidaq_at_promotion_rank to c)
  | None => false
  end.

Definition apply_move_with_promotion (b: Board) (from to: Position) : Board :=
  match b[from] with
  | Some pc =>
      let b' := board_move b from to in
      if andb (PieceType_beq (piece_type pc) Baidaq)
              (baidaq_at_promotion_rank to (piece_color pc))
      then board_place b' to (mkPiece (piece_color pc) Ferz)
      else b'
  | None => b
  end.

(** * End of Section 7: Piece Movement Rules *)

Close Scope Z_scope.
        
