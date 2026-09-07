#[global] Set Warnings "-intuition-auto-with-star".

From Coinduction Require Import all.
Require Import Program.Tactics.

Ltac inv H := inversion H; clear H; subst.

(* [inv], [rewrite_everywhere], [..._except] are general purpose *)

Ltac rewrite_everywhere_except lem X :=
  progress ((repeat match goal with [H: _ |- _] =>
                 match H with X => fail 1 | _ => rewrite lem in H end
             end); repeat rewrite lem).

Ltac rewrite_everywhere lem :=
  progress ((repeat match goal with [H: _ |- _] => rewrite lem in H end); repeat rewrite lem).

Global Tactic Notation "intros !" := repeat intro.

Ltac flatten_goal :=
  match goal with
  | |- context[match ?x with | _ => _ end] => let Heq := fresh "Heq" in destruct x eqn:Heq
  end.

Ltac flatten_hyp h :=
  match type of h with
  | context[match ?x with | _ => _ end] => let Heq := fresh "Heq" in destruct x eqn:Heq
  end.

Ltac flatten_all :=
  match goal with
  | h: context[match ?x with | _ => _ end] |- _ => let Heq := fresh "Heq" in destruct x eqn:Heq
  | |- context[match ?x with | _ => _ end] => let Heq := fresh "Heq" in destruct x eqn:Heq
  end.

(* inv by name of the Inductive relation *)
Ltac invn f :=
    match goal with
    | [ id: f |- _ ] => inv id
    | [ id: f _ |- _ ] => inv id
    | [ id: f _ _ |- _ ] => inv id
    | [ id: f _ _ _ |- _ ] => inv id
    | [ id: f _ _ _ _ |- _ ] => inv id
    | [ id: f _ _ _ _ _ |- _ ] => inv id
    | [ id: f _ _ _ _ _ _ |- _ ] => inv id
    | [ id: f _ _ _ _ _ _ _ |- _ ] => inv id
    | [ id: f _ _ _ _ _ _ _ _ |- _ ] => inv id
    end.

(* destruct by name of the Inductive relation *)
Ltac destructn f :=
    match goal with
    | [ id: f |- _ ] => destruct id
    | [ id: f _ |- _ ] => destruct id
    | [ id: f _ _ |- _ ] => destruct id
    | [ id: f _ _ _ |- _ ] => destruct id
    | [ id: f _ _ _ _ |- _ ] => destruct id
    | [ id: f _ _ _ _ _ |- _ ] => destruct id
    | [ id: f _ _ _ _ _ _ |- _ ] => destruct id
    | [ id: f _ _ _ _ _ _ _ |- _ ] => destruct id
    | [ id: f _ _ _ _ _ _ _ _ |- _ ] => destruct id
    end.

(* apply by name of the Inductive relation *)
Ltac appn f :=
    match goal with
    | [ id: f |- _ ] => apply id
    | [ id: f _ |- _ ] => apply id
    | [ id: f _ _ |- _ ] => apply id
    | [ id: f _ _ _ |- _ ] => apply id
    | [ id: f _ _ _ _ |- _ ] => apply id
    | [ id: f _ _ _ _ _ |- _ ] => apply id
    | [ id: f _ _ _ _ _ _ |- _ ] => apply id
    | [ id: f _ _ _ _ _ _ _ |- _ ] => apply id
    | [ id: f _ _ _ _ _ _ _ _ |- _ ] => apply id
    end.

(* eapply by name of the Inductive relation *)
Ltac break H :=
  repeat match type of H with
          | exists X, _  => destruct H
          |  _ /\ _ => destruct H
          |  _ \/ _ => destruct H
          |  _ /\ _ => split
          end.

Ltac crunch :=
  repeat match goal with
          | [ H : exists X, _ |- _ ] => destruct H
          | [ H : _ /\ _ |- _ ] => destruct H
          | [ H : _ \/ _ |- _ ] => destruct H
          | [ |- _ /\ _ ] => split
          end.

(* Oft-used induction tactic for general IHs. *)
Tactic Notation "hinduction" hyp(IND) "before" hyp(H)
  := move IND before H; revert_until IND; induction IND.

Ltac under_forall tac :=
  let guard := fresh "guard" in
  assert (guard : True) by constructor;
  intros;
  tac ();
  revert_until guard;
  clear guard.

Ltac to_mon_core :=
  cbn; progress (autorewrite with to_mon_obs; autorewrite with to_mon_go).
Ltac to_mon := under_forall ltac:(fun _ => to_mon_core).
Ltac to_mon_in h :=
  cbn in h;
  progress (autorewrite with to_mon_obs in h; autorewrite with to_mon_go in h).
Tactic Notation "to_mon" "in" ident(h) := to_mon_in h.


Ltac copy h :=
  let foo := fresh "cpy" in
  assert (foo := h).

(* eapply by name of the Inductive relation *)
Ltac eappn f :=
    match goal with
    | [ id: f |- _ ] => eapply id
    | [ id: f _ |- _ ] => eapply id
    | [ id: f _ _ |- _ ] => eapply id
    | [ id: f _ _ _ |- _ ] => eapply id
    | [ id: f _ _ _ _ |- _ ] => eapply id
    | [ id: f _ _ _ _ _ |- _ ] => eapply id
    | [ id: f _ _ _ _ _ _ |- _ ] => eapply id
    | [ id: f _ _ _ _ _ _ _ |- _ ] => eapply id
    | [ id: f _ _ _ _ _ _ _ _ |- _ ] => eapply id
    end.

Ltac saturate H :=
  match goal with
          | [ H1 : forall a b, ?R a b -> _,
              H2 : forall a b, ?R b a -> _,
                H : ?R ?A ?B  |- _ ] => pose proof (H1 A B H);
                                        pose proof (H2 B A H);
                                        clear H; crunch
          end.

(* in goal: elem -> b elem -> gfp b -> b gfp *)

Ltac step_ :=
  match goal with
  | |- gfp ?b ?x ?y ?z => apply ((gfp_fp b x y z))
  | |- elem ?R ?x ?y ?z => apply (b_chain R x y z)
  | |- gfp ?b ?x ?y => apply ((gfp_fp b x y))
  | |- elem ?R ?x ?y => apply (b_chain R x y)
  | |- gfp ?b ?x => apply ((gfp_fp b x))
  | |- elem ?R ?x => apply (b_chain R x)
  end.
