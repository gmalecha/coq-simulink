Require Import Reals.

Local Open Scope R_scope.

Definition Signal (T : Type) : Type :=
  R -> T.

Definition Arrow (T U : Type) : Type :=
  Signal T -> Signal U -> Prop.

Definition Pure {T U} (f : T -> U) : Arrow T U :=
  fun i o => forall t, o t = f (i t).

Definition Integrator (init : R) : Arrow R R :=
  fun i o =>
    o 0 = init /\
    exists deriv_pf : forall {t}, t >= 0 -> derivable_pt o t,
      forall t (pf : t >= 0), i t = derive_pt o t (deriv_pf pf).

Definition integrator_loop (init : R) (x : Signal R) : Prop :=
  Integrator init x x.

Lemma integrator_loop_exp :
  integrator_loop 1 Rtrigo_def.exp.
Proof.
  cbv beta iota zeta
      delta - [ Rtrigo_def.exp Rge derive_pt derivable_pt ].
  split.
  - apply Rtrigo_def.exp_0.
  - exists (fun _ _ => derivable_pt_exp _).
    intros. rewrite derive_pt_exp. reflexivity.
Qed.

Definition Pcontroller (init : R) (x y : Signal R) : Prop :=
  Integrator init y x /\ Pure (Rmult (-1)) x y.

Lemma Pcontroller_solution :
  Pcontroller 1 (fun t => Rtrigo_def.exp (-t))
              (fun t => -Rtrigo_def.exp (-t)).
Proof.
  cbv beta iota zeta
      delta - [ Rtrigo_def.exp Rge derive_pt derivable_pt ].
  repeat split.
  - rewrite RIneq.Ropp_0. apply Rtrigo_def.exp_0.
  - Check derivable_pt_comp. SearchAbout derivable_pt.
    exists (fun _ _ =>
              derivable_pt_comp
                Ropp Rtrigo_def.exp _
                (derivable_pt_opp _ _ (derivable_pt_id _))
                (derivable_pt_exp _)).
    intros. rewrite (derive_pt_comp Ropp Rtrigo_def.exp).
    rewrite derive_pt_exp. rewrite (derive_pt_opp id).
    rewrite derive_pt_id. field.
  - intros. field.
Qed.

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

Definition Switch {T} (i1 i2 : Signal T)
           (test : Signal bool) (o : Signal T) : Prop :=
  forall t, o t = if test t then i1 t else i2 t.

Definition thermostat (init : R) (temp : Signal R)
           (on : Signal bool) (dtemp : Signal R) :=
  Switch (fun _ => 1) (fun _ => -1) on dtemp /\
  Integrator init dtemp temp /\
  StateFlow (I:=R) (S:=bool) (O:=bool)
            (fun s i => if s
                        then if Rge_dec i 1 then false else true
                        else if Rle_dec i (-1) then true else false)
            (fun s _ => s)
            true dtemp on.

Definition is_lower_bound (P : R -> Prop) (m : R) : Prop :=
  forall x : R, P x -> m <= x.

Definition lower_bounded (P : R -> Prop) :=
  exists m : R, is_lower_bound P m.

Definition is_glb (P : R -> Prop) (m : R) :=
  is_lower_bound P m /\ (forall b : R, is_lower_bound P b -> b <= m).

Lemma glb :
  forall P : R -> Prop,
    lower_bounded P -> (exists x : R, P x) ->
    exists m : R, is_glb P m.
Proof.
  intros.
  pose (Q:=fun x => is_lower_bound P x).
  assert (bound Q).
  { unfold bound, is_upper_bound, lower_bounded,
    Q, is_lower_bound in *.
    destruct H0. exists x. intros. auto. }
  assert (exists x : R, Q x).
  { unfold Q, lower_bounded, is_lower_bound in *.
    auto. }
  pose proof (completeness Q H1 H2) as Hlub.
  destruct Hlub as [lub [Hlub1 Hlub2]]. exists lub.
  unfold Q, is_glb, is_lub, is_upper_bound, is_lower_bound in *.
  split; intros.
  - apply Hlub2; auto.
  - apply Hlub1; auto.
Qed.

Require Import Coq.Logic.Classical.
Require Import Psatz.
Theorem real_induction :
  forall P : R -> Prop,
    P 0 ->
    (forall x : R, (forall y : R, 0 <= y < x -> P y) -> P x) ->
    (forall x : R, P x -> exists y, x < y /\ forall z, x < z < y -> P z) ->
    forall x : R, 0 <= x -> P x.
Proof.
  intros P Base I1 I2.
  cut (~exists x : R, 0 <= x /\ ~P x).
  - intros. apply not_ex_all_not with (n:=x) in H.
    apply not_and_or in H. destruct H; [ tauto | ].
    apply NNPP; assumption.
  - intro Hnot.
    assert (lower_bounded (fun x => 0 <= x /\ ~P x)) as Hlb.
    { unfold lower_bounded, is_lower_bound. exists 0.
      intros. tauto. }
    pose proof (glb (fun x => 0 <= x /\ ~P x) Hlb Hnot) as Hglb.
    destruct Hglb as [xglb Hglb]. unfold is_glb in *.
    assert (0 <= xglb).
    { assert (is_lower_bound (fun x => 0 <= x /\ ~P x) 0).
      { unfold is_lower_bound. intros. tauto. }
      intuition. }
    assert (P xglb \/ ~P xglb) by apply classic.
    destruct H0.
    + specialize (I2 xglb H0). destruct I2.
      assert (is_lower_bound (fun x => 0 <= x /\ ~P x) x).
      { unfold is_lower_bound in *. intros.
        assert (xglb <= x0) by (apply Hglb; assumption).
        destruct H3; [ | subst; tauto ].
        destruct (Rlt_dec x0 x); [ | psatzl R ].
        assert (P x0) by (apply H1; psatzl R).
        tauto. }
      assert (x <= xglb) by (apply Hglb; assumption).
      psatzl R.
    + specialize (I1 xglb). apply H0. apply I1. intros.
      apply NNPP. intro.
      assert (xglb <= y).
      { unfold is_lower_bound in *. apply Hglb. tauto. }
      psatzl R.
Qed.

Lemma thermostat_in_range :
  forall temp on dtemp,
    thermostat 0 temp on dtemp ->
    forall t, -1 <= temp t <= 1.
Proof.
  cbv beta iota zeta
      delta - [ Rge Rle derive_pt derivable_pt ].
  intros temp on dtemp [Hswitch [Hint Hst]] t.
Admitted.