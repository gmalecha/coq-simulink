Require Import Reals.

Local Open Scope R_scope.

Definition Signal (T : Type) : Type :=
  R -> T.

Definition Arrow (T U : Type) : Type :=
  Signal T -> Signal U -> Prop.

Definition Pure {T U} (f : T -> U) : Arrow T U :=
  fun i o => forall t, o t = f (i t).

Require Import Coquelicot.Coquelicot.
Definition Integrator (init : R) : Arrow R R :=
  fun i o =>
    (* Is - init correct? *)
    forall t, is_RInt i 0 t (o t - init).
(*
  fun i o =>
    o 0 = init /\
    exists deriv_pf : forall {t}, t >= 0 -> derivable_pt o t,
      forall t (pf : t >= 0), i t = derive_pt o t (deriv_pf pf).
*)

Definition integrator_loop (init : R) (x : Signal R) : Prop :=
  Integrator init x x.

Lemma integrator_loop_exp :
  integrator_loop 1 Rtrigo_def.exp.
Proof.
  unfold integrator_loop, Integrator. intros.
  rewrite <- Rtrigo_def.exp_0.
  apply is_RInt_exp.
Qed.

Definition Pcontroller (init : R) (x y : Signal R) : Prop :=
  Integrator init y x /\ Pure (Rmult (-1)) x y.

Require Import Psatz.
Lemma Pcontroller_solution :
  Pcontroller 1 (fun t => Rtrigo_def.exp (-t))
              (fun t => -Rtrigo_def.exp (-t)).
Proof.
  unfold Pcontroller, integrator_loop, Integrator.
  split.
  { intros. rewrite <- Rtrigo_def.exp_0. rewrite <- Ropp_0 at 2.
    apply is_RInt_derive with (f:=fun x => exp (-x)).
    { intros. auto_derive; auto. psatzl R. }
    { intros. apply continuous_opp with (f:=fun x => exp (-x)).
      admit. } }
  { unfold Pure. intros. psatzl R. }
Admitted.
(*
  { intros. SearchAbout is_RInt.
    apply is_RInt_comp_opp.
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
*)

Definition StateFlow_ClosedRight {I O S : Type}
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

Definition StateFlow_ClosedLeft {I O S : Type}
           (trans : S -> I -> S)
           (out : S -> I -> O)
           (init : S)
: Arrow I O :=
  fun i o =>
    exists st : Signal S,
         st 0 = init
      /\ (forall t : R, out (st t) (i t) = o t)
      /\ (forall t : R, 0 < t ->
             exists epsilon : R, epsilon > 0 /\
               forall t' : R, t - epsilon <= t' < t ->
                 st t = trans (st t') (i t)).

Definition Switch {T} (i1 i2 : Signal T)
           (test : Signal bool) (o : Signal T) : Prop :=
  forall t, o t = if test t then i1 t else i2 t.

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
Theorem real_induction :
  forall P : R -> Prop,
    P 0 ->
    (forall x : R, 0 < x ->
                   (forall y : R, 0 <= y < x -> P y) -> P x) ->
    (forall x : R,
        0 <= x ->
        P x ->
        exists y, x < y /\ forall z, x < z < y -> P z) ->
    forall x : R, 0 <= x -> P x.
Proof.
  intros P Base I1 I2.
  cut (~exists x : R, 0 < x /\ ~P x).
  - intros. apply not_ex_all_not with (n:=x) in H.
    apply not_and_or in H. destruct H.
    + assert (x = 0) by psatzl R.
      subst; assumption.
    + apply NNPP; assumption.
  - intro Hnot.
    assert (lower_bounded (fun x => 0 < x /\ ~P x)) as Hlb.
    { unfold lower_bounded, is_lower_bound. exists 0.
      intros. psatzl R. }
    pose proof (glb (fun x => 0 < x /\ ~P x) Hlb Hnot) as Hglb.
    destruct Hglb as [xglb Hglb]. unfold is_glb in *.
    assert (0 <= xglb).
    { assert (is_lower_bound (fun x => 0 < x /\ ~P x) 0).
      { unfold is_lower_bound. intros. psatzl R. }
      intuition. }
    assert (P xglb \/ ~P xglb) by apply classic.
    destruct H0.
    + specialize (I2 xglb H H0). destruct I2.
      assert (is_lower_bound (fun x => 0 < x /\ ~P x) x).
      { unfold is_lower_bound in *. intros.
        assert (xglb <= x0) by (apply Hglb; assumption).
        destruct H3; [ | subst; tauto ].
        destruct (Rlt_dec x0 x); [ | psatzl R ].
        assert (P x0) by (apply H1; psatzl R).
        tauto. }
      assert (x <= xglb) by (apply Hglb; assumption).
      psatzl R.
    + assert (0 < xglb).
      { destruct H; auto. subst. tauto. }
      specialize (I1 xglb). apply H0. apply I1; auto.
      intros. apply NNPP. intro.
      assert (xglb <= y).
      { unfold is_lower_bound in *. apply Hglb. split.
        { destruct H2. destruct H2; auto. subst. tauto. }
        { assumption. } }
      psatzl R.
Qed.

Ltac specialize_arith H :=
  repeat match type of H with
         | ?P -> _ =>
           let X := fresh in
           assert P as X by psatzl R;
             specialize (H X); clear X
         end.

Ltac destruct_ite :=
  match goal with
  | [ |- context [ if ?e then _ else _ ] ]
    => destruct e
  end.

Theorem StateFlow_induction :
  forall (I O S : Type) (trans : S -> I -> S)
         (out : S -> I -> O) (init : S)
         (P : I -> S -> O -> Prop)
         (i : Signal I) (o : Signal O),
    StateFlow_ClosedLeft trans out init i o ->
    P (i 0) init (out init (i 0)) ->
    (forall i1 i2 s o, P i1 s o ->
                       P i2 (trans s i2) (out (trans s i2) i2)) ->
    exists st, forall t, 0 <= t -> P (i t) (st t) (o t).
Proof.
  intros I O S trans out init P i o Hst Hinit Hind.
  unfold StateFlow_ClosedLeft in Hst.
  destruct Hst as [st [Hst0 [Hout Htrans]]].
  exists st. intros t Ht.
  apply real_induction
  with (P:=fun t => P (i t) (st t) (o t)).
  - subst. rewrite <- Hout. assumption.
  - intros. specialize (Htrans x H).
    destruct Htrans as [eps [Hsp Htrans]].
    assert (Rmax 0 (x - eps) < x).
    { apply Rmax_lub_lt; psatzl R. }
    assert (x - eps <= Rmax 0 (x - eps)) by apply Rmax_r.
    assert (0 <= Rmax 0 (x - eps)) by apply Rmax_l.
    specialize (Htrans (Rmax 0 (x - eps))). specialize_arith Htrans.
    specialize (Hout x). rewrite Htrans in *.
    rewrite <- Hout. eapply Hind.
    specialize (H0 (Rmax 0 (x - eps))).
    specialize_arith H0. eassumption.
  - (* This case is unnecessary if we assume axiom of choice. *)
    admit.
  - assumption.
Admitted.

Theorem StateFlow_induction_stateless :
  forall (I O S : Type) (trans : S -> I -> S)
         (out : S -> I -> O) (init : S)
         (P : I -> O -> Prop)
         (i : Signal I) (o : Signal O),
    StateFlow_ClosedLeft trans out init i o ->
    P (i 0) (out init (i 0)) ->
    (forall i1 i2 s o, P i1 o ->
                       P i2 (out (trans s i2) i2)) ->
    forall t, 0 <= t -> P (i t) (o t).
Proof.
  intros. eapply StateFlow_induction with (P:=fun i s o => P i o) in H.
  { destruct H. apply H; auto. }
  { assumption. }
  { auto. }
Qed.

(*
Definition ind_inv1 (dtemp : Signal R) (t : R) :=
  (dtemp t = -1 \/ dtemp t = 1).

Definition ind_inv2 (temp dtemp : Signal R) (t : R) :=
  (dtemp t = 1 -> -1 <= temp t < 1) /\
  (dtemp t = -1 -> -1 < temp t <= 1).

Definition ind_inv (temp dtemp : Signal R) (t : R) :=
  ind_inv1 dtemp t /\ ind_inv2 temp dtemp t.

Lemma ind_inv_safe :
  forall temp dtemp t,
    ind_inv temp dtemp t -> safe temp t.
Proof.
  compute. intros. psatzl R.
Qed.
*)

Definition Controller (temp : Signal R) (on : Signal bool) :=
  StateFlow_ClosedLeft
    (I:=R) (S:=bool) (O:=bool)
    (fun s i => if s
                then if Rge_dec i 1 then false else true
                else if Rle_dec i (-1) then true else false)
    (fun s _ => s)
    true temp on.

Definition thermostat (init : R) (temp : Signal R)
           (on : Signal bool) (dtemp : Signal R) :=
  Switch (fun _ => 1) (fun _ => -1) on dtemp /\
  Integrator init dtemp temp /\
  Controller temp on.

Definition ind_inv_Controller (temp : R) (on : bool) : Prop :=
  (on = true /\ temp < 1) \/
  (on = false /\ -1 < temp).

Definition ind_inv_Integrator (dtemp temp : R) : Prop :=
  (dtemp >= 0 /\ -1 <= temp) \/
  (dtemp <= 0 /\ temp <= 1).

Definition safe (temp : R) : Prop :=
  -1 <= temp <= 1.

Lemma ind_inv_safe :
  forall (temp dtemp : Signal R) (on : Signal bool),
    Switch (fun _ => 1) (fun _ => -1) on dtemp /\
    (forall t, 0 <= t -> ind_inv_Controller (temp t) (on t)) /\
    (forall t, 0 <= t -> ind_inv_Integrator (dtemp t) (temp t)) ->
    forall t, 0 <= t -> safe (temp t).
Proof.
  cbv beta iota zeta delta - [ Rge Rle ]. intros. intuition;
  specialize (H t); specialize (H1 t); specialize (H3 t);
  intuition; rewrite H2 in *; psatzl R.
Qed.

Lemma ind_inv_Controller_ok :
  forall (temp : Signal R) (on : Signal bool),
    temp 0 < 1 ->
    Controller temp on ->
    forall t, 0 <= t -> ind_inv_Controller (temp t) (on t).
Proof.
  unfold Controller. intros.
  eapply StateFlow_induction_stateless; eauto.
  { compute. intuition psatzl R. }
  { compute. intros. repeat destruct_ite; try intuition psatzl R. }
(* Old proof without state flow rule *)
(*
  cbv beta iota zeta delta - [ Rge Rle ]. intros temp on Hinit Hst.
  destruct Hst as [st [Hst0 [Hout Htrans]]]. intros.
  eapply real_induction
  with (P:=fun t => (on t = true /\ temp t < 1) \/
                    (on t = false /\ -1 < temp t)).
  - rewrite <- Hout. rewrite Hst0. intuition psatzl R.
  - intros. specialize (Htrans x H0).
    destruct Htrans as [eps [Heps Htrans]].
    specialize (Htrans (x - eps)). specialize_arith Htrans.
    rewrite <- Hout. rewrite Htrans.
    repeat destruct_ite;
      intuition psatzl R.
  - (* This case is unnecessary if we assume axiom of choice. *)
    admit.
  - assumption.
*)
Qed.

Lemma Integrator_init :
  forall s1 s2 init,
    Integrator init s1 s2 ->
    s2 0 = init.
Proof.
  unfold Integrator. intros.
  specialize (H 0).
  assert (is_RInt s1 0 0 zero) by apply is_RInt_point.
  apply is_RInt_unique in H.
  apply is_RInt_unique in H0. rewrite H in H0. unfold zero in *.
  simpl in *. psatzl R.
Qed.

Lemma ind_inv_Integrator_ok :
  forall (dtemp temp : Signal R),
    Integrator 0 dtemp temp ->
    (forall t, 0 <= t ->
               (dtemp t = 1 /\ temp t < 1) \/
               (dtemp t = -1 /\ -1 < temp t)) ->
    forall t, 0 <= t -> ind_inv_Integrator (dtemp t) (temp t).
Proof.
  (* Need something like differential induction. *)
  intros dtemp temp Hint H t Ht.
  apply real_induction
  with (P:=fun t => ind_inv_Integrator (dtemp t) (temp t)).
  { compute. apply Integrator_init in Hint. psatzl R. }
  { unfold ind_inv_Integrator, Integrator in *.
    intros x Hx Hind. admit. }
  { admit. }
  { assumption. }
Admitted.

Lemma thermostat_in_range :
  forall temp on dtemp,
    thermostat 0 temp on dtemp ->
    forall t, 0 <= t -> safe (temp t).
Proof.
  unfold thermostat. intros temp on dtemp Htherm t Ht.
  destruct Htherm as [Hswitch [Hint Hcontrol]].
  eapply ind_inv_safe; [ | assumption ]. split; [ | split ].
  - eassumption.
  - intros. apply ind_inv_Controller_ok.
    + apply Integrator_init in Hint; psatzl R.
    + eassumption.
    + assumption.
  - apply ind_inv_Integrator_ok; try assumption.
    admit.
Admitted.
(*
  intros temp on dtemp [Hswitch [Hint Hst]] t.
  cut (ind_inv temp dtemp t); [ apply ind_inv_safe | ].
  cbv beta iota zeta
      delta - [ Rge Rle derive_pt derivable_pt ] in *.
  split.
  { specialize (Hswitch t). destruct (on t); tauto. }
  destruct Hst as [st [Hst0 [Hst_out Hst]]].
  eapply real_induction with (P:=ind_inv2 temp dtemp);
    cbv beta iota zeta delta - [ Rge Rle ].
  - specialize (Hst_out 0). specialize (Hswitch 0).
    rewrite Hst0 in *. rewrite <- Hst_out in *. rewrite Hswitch.
    psatzl R.
  - intros. split; intros.
    + specialize (Hst x H). destruct Hst as [eps [Heps Hst]].
      specialize (Hst (Rmax 0 (x - eps))).
      match goal with
      | H : ?P -> _ |- _ =>
        match type of P with
        | Prop =>
          let X := fresh in
          assert P as X by admit ;
            specialize (H X)
        end
      end.
      repeat rewrite Hst_out in *; clear Hst_out.
      repeat rewrite Hswitch in *.
      destruct (on x) eqn:?; try solve [ psatzl R ].
      destruct (on (Rmax 0 (x - eps))) eqn:?.
      { destruct (Rge_dec (temp x) 1); try congruence.
        split; [| psatzl R].
        specialize (H0 (Rmax 0 (x - eps))).
        destruct H0. admit.
        rewrite Hswitch in *.
        rewrite Heqb0 in *.
        specialize (H0 eq_refl).
        setoid_rewrite Hswitch in Hint.
        destruct Hint.
        destruct H5.
        admit. }
      { destruct (Rle_dec (temp x) (-1)); try congruence.
        
        
Admitted.
*)