#[global] Set Warnings "-intuition-auto-with-star".

From Coinduction Require Import all.
Require Import Program.Tactics.

Ltac inv H := inversion H; clear H; subst.

(* [inv], [rewrite_everywhere], [..._except] are general purpose *)

Ltac rewrite_everywhere_except lem X :=
  progress ((repeat match goal with [H: _ |- _] =>
                 match H with X => fail 1 | _ => rewrite lem in H end
             end); repeat rewrite lem).

Global Tactic Notation "intros !" := repeat intro.

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
