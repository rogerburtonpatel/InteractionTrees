(** * MWE: elpi [accumulate] resurrects a [specialize]d section hypothesis

    Depends only on rocq-coinduction; compile with [rocq compile AccumulateSpecializeMWE.v].
    It is deliberately not listed in [_CoqProject].

    Tested with:
    - rocq-coinduction master 07d2a09 (elpi tactics), Rocq 9.2.0, rocq-elpi 3.5.1:
      BUG.  After [accumulate], [HP] is shown with the section hypothesis's
      original type [forall n, n = n], although it was specialized to [0 = 0].
      The tactic engine accepts [HP 1], and the error appears only at [Qed]:
        Error: Illegal application (Non-functional construction):
        The expression HP0 of type 0 = 0 cannot be applied to the term 1 : nat
    - The same commit with [ocaml_tactics] in place of [tactics]: OK.  [HP] stays
      [0 = 0], and [pose proof (HP 1)] is rejected right away at the tactic.
    - rocq-coinduction 1.21 (OCaml tactics), Rocq 9.1.1: OK, same as [ocaml_tactics].

    To trigger it, you need [specialize] on a section [Hypothesis]/[Context],
    then [accumulate].  A local hypothesis does not trigger it, and nothing goes
    wrong without [accumulate].  The specialized hypothesis need not mention the
    chain [R].
 *)

From Coinduction Require Import lattice tower tactics.

Section mwe.
  Variable b : mon (nat -> Prop).
  Hypothesis HP : forall n : nat, n = n.
  Hypothesis Hb : forall (R : Chain b) n, b (elem R) n.

  Goal forall R : Chain b, elem R 0.
  Proof.
    intro R.
    specialize (HP 0).
    Check HP.                    (* HP : 0 = 0                    -- as expected *)
    accumulate H.
    Check HP.                    (* HP : forall n : nat, n = n    -- wrong *)
    pose proof (HP 1) as Hback.  (* should fail here, but is accepted *)
    apply Hb.
  Fail Qed.                           (* kernel: HP0 : 0 = 0 cannot be applied to 1 *)
Fail End mwe.
