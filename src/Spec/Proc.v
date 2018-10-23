Require Import Helpers.RelationAlgebra.

Global Set Implicit Arguments.
Global Generalizable Variables T R Op State.
Global Set Printing Projections.

(** Syntax: free monad over a type family of operations *)
Inductive proc (Op: Type -> Type) (T : Type) : Type :=
| Prim (op : Op T)
| Ret (v : T)
| Bind (T1 : Type) (p1 : proc Op T1) (p2 : T1 -> proc Op T).
Arguments Prim {Op T}.
Arguments Ret {Op T} v.

(** Semantics: defined using big-step execution relations *)

Definition OpSemantics Op State := forall T, Op T -> relation State T.
Definition CrashSemantics State := relation State unit.

Record Dynamics Op State :=
  { step: OpSemantics Op State;
    crash_step: CrashSemantics State; }.

Section Dynamics.

  Context `(sem: Dynamics Op State).
  Notation proc := (proc Op).
  Notation step := sem.(step).
  Notation crash_step := sem.(crash_step).

  (** First, we define semantics of running programs with halting (without the
  effect of a crash or recovery) *)

  Fixpoint exec T (p: proc T) : relation State T :=
    match p with
    | Ret v => pure v
    | Prim op => step op
    | Bind p p' => and_then (exec p) (fun v => exec (p' v))
    end.

  Fixpoint exec_crash T (p: proc T) : relation State unit :=
    match p with
    | Ret v => pure tt
    | Prim op => rel_or (pure tt) (step op;; pure tt)
    | Bind p p' => rel_or (pure tt)
                         (rel_or (exec_crash p)
                                 (and_then (exec p)
                                           (fun v => exec_crash (p' v))))
    end.

  Definition exec_recover R (rec: proc R) : relation State R :=
    seq_star (crash_step;; exec_crash rec);;
             (crash_step;; exec rec).

  (* recovery execution *)
  Definition rexec T R (p: proc T) (rec: proc R) : relation State R :=
      exec_crash p;; exec_recover rec.

End Dynamics.

Notation "x <- p1 ; p2" := (Bind p1 (fun x => p2))
                            (at level 60, right associativity).
