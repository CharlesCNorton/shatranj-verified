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

Ltac solve_decidable :=
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

Fixpoint nat_to_fin8_aux (n: nat) : Fin8 :=
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
  
