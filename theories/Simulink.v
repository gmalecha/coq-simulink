Require Import ExtLib.Structures.Applicative.
Require Import ExtLib.Structures.Functor.
Require Import Coq.Reals.Rdefinitions.
Require Import Coq.Reals.Ranalysis.

Local Open Scope R_scope.

Definition Signal (T : Type) : Type :=
  R -> T.

Instance Applicative_Signal : Applicative Signal.
Admitted.
Instance Functor_Signal : Functor Signal.
Admitted.

Definition Arrow (T U : Type) : Type :=
  Signal T -> Signal U -> Prop.

Definition Compose {T U V} (A : Arrow T U) (B : Arrow U V) : Arrow T V :=
  fun i o =>
    exists m : Signal U, A i m /\ B m o.

Definition Prod {T U V W} (A : Arrow T U) (B : Arrow V W) : Arrow (T * V) (U * W) :=
  fun i o =>
       A (fun t => fst (i t)) (fun t => fst (o t))
    /\ B (fun t => snd (i t)) (fun t => snd (o t)).

Infix "***" := (@Prod _ _ _ _) (at level 30).
Infix ">>>" := (@Compose _ _ _) (at level 20).

Definition Pure {T U} (f : T -> U) : Arrow T U :=
  fun i o => forall t, o t = f (i t).

Definition Delay {T} (delay : R) : Arrow T T :=
  fun i o =>
    forall t, t >= delay -> o t = i (t - delay).

Definition Integrator (init : R) : Arrow R R :=
  fun i o =>
    o 0 = init /\
    exists deriv_pf : forall {t}, t >= 0 -> derivable_pt o t,
      forall t (pf : t >= 0), i t = derive_pt o t (deriv_pf pf).

Definition StateFlow {I O S : Type}
           (trans : S -> I -> S)
           (out : S -> I -> O)
           (init : S)
: Arrow I O :=
  fun i o =>
    exists st : Signal S,
         st 0 = init
      /\ (forall t : R, out (st t) (i t) = o t)
      /\ (forall t : R,
             exists epsilon : R, epsilon > 0 /\
               forall t' : R, t < t' <= t + epsilon ->
                 st t' = trans (st t) (i t)).

Definition If {T} : Arrow (bool * T * T) T :=
  fun i o =>
    forall t, let '(test, tr, fa) := i t in
              o t = if test then tr else fa.

Definition Constant {T} (x : T) : Signal T :=
  fun _ => x.

Definition Loop {I O T} (A : Arrow (I * T) (O * T)) : Arrow I O :=
  fun i o =>
    exists state : Signal T,
      A (fun t => (i t, state t)) (fun t => (o t, state t)).

Definition Dup {T} : Arrow T (T * T) :=
  fun i o => forall t, o t = (i t, i t).

Definition First {T U} : Arrow (T * U) T := Pure fst.
Definition Second {T U} : Arrow (T * U) U := Pure snd.

Definition F (f : R -> R) : Signal R :=
  f.

Definition S2A {T} : Signal T -> Arrow unit T :=
  fun s i o => o = s.

Definition A2S {T} : Arrow unit T -> Signal T -> Prop :=
  fun a s => a (fun _ => tt) s.


(** * Example **)
Definition Exp : Arrow unit R :=
  Loop (Second >>> Integrator 1 >>> Dup).

Goal Exp (Constant tt) (Rtrigo_def.exp).
Proof.
  cbv beta iota zeta delta - [ Rtrigo_def.exp Rge derive_pt derivable_pt  ].
  eexists. eexists.
  split.
  2: reflexivity.
  eexists; split. reflexivity.
  split.
  + apply Rtrigo_def.exp_0.
  + exists (fun _ _ => derivable_pt_exp _).
    intros. rewrite derive_pt_exp. reflexivity.
Qed.

(** * Example: P-controller  **)

Definition LetRec {I O} (P : Arrow (I * O) O)
: Arrow I O :=
  fun i o => P (fun t => (i t, o t)) o.

Definition LetRec' {I O} (P : Signal I -> Signal O -> Signal O -> Prop)
: Arrow I O :=
  fun i o => P i o o.

Require Import Coq.Lists.List.

Section tuple.
  Context {T : Type}.
  Variable F : T -> Type.
  Fixpoint tuple (ls : list T) : Type :=
    match ls with
    | nil => unit
    | l :: nil => F l
    | l :: ls => (F l * tuple ls)
    end%type.
End tuple.

Definition LetRec_tuple {I O : list Type}
           (decls : tuple (fun T => Arrow (tuple (fun x => x) I * tuple (fun x => x) O) T) O)
: Arrow (tuple (fun x => x) I) (tuple (fun x => x) O).
Admitted.

Section with_init.
  Variable initial : R.

  Definition Pcontrol : Arrow unit R :=
    Loop (Second >>> Pure (Rmult (-1)) >>> Integrator initial >>> Dup).

  Definition Pcontrol' : Arrow unit R :=
    LetRec (O:=R * R) (Second >>> Dup >>>
                           ((Second >>> Integrator initial) ***
                            (First >>> Pure (Rmult (-1)))))
    >>> First.

(*
  Definition Pcontrol_tuple : Arrow unit R :=
    LetRec_tuple (I:=nil) (O:=(R : Type):: (R : Type) :: @nil Type)%type
                 ( (!! "x" >>> Integrator initial)
                 , (!! "y" >>> Pure (Rmult (-1))) )
    >>> First.

  Definition Pcontrol'' : Arrow unit R :=
    LetRec' (O:=R * R) (fun _ (u : Signal (R * R)) (o : Signal (R * R)) =>
                          Integrator initial (fmap snd u) (fmap fst o) /\
                          fmap snd o = fmap (Rmult (-1)) (fmap fst u))
    >>> First.

  Definition Arrow_app {T U V} (x : Arrow (T * U) V) (s : Signal T) : Arrow U V :=
    fun i o => x (fun t => (s t, i t)) o.
  Definition Arrow_app' {T V} (x : Arrow T V) (s : Signal T) : Arrow unit V :=
    fun i o => x s o.

  Definition Pcontrol''' : Arrow unit R :=
    LetRec' (O:=R * R) (fun _ (u : Signal (R * R)) (o : Signal (R * R)) =>
                          S2A (fmap fst o) = Arrow_app' (Integrator initial) (fmap snd u) /\
                          fmap snd o = fmap (Rmult (-1)) (fmap fst u))
    >>> First.


  letrec x := integral y
         y := - x
  in x
*)
End with_init.