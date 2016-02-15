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
    forall t, 0 <= t -> is_RInt i 0 t (o t - init).
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
        (forall t : R, 0 <= t <= x -> P t) ->
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
    + specialize (I2 xglb H). destruct I2.
      { intros. apply NNPP. intro.
        assert (xglb <= t).
        { unfold is_lower_bound in *. apply Hglb.
          destruct H1. destruct H1; subst; tauto. }
        destruct H1. destruct H4; subst; intuition psatzl R. }
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
    (forall i1 i2 s, P i1 s (out s i1) ->
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
    rewrite <- Hout. erewrite Htrans; eauto. eapply Hind.
    setoid_rewrite <- Hout in H0. eapply H0; eauto.
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
    (forall i1 i2 s, P i1 (out s i1) ->
                     P i2 (out (trans s i2) i2)) ->
    forall t, 0 <= t -> P (i t) (o t).
Proof.
  intros.
  eapply StateFlow_induction with (P:=fun i s o => P i o) in H.
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

Definition real_partition (int : nat -> nonnegreal) :=
  nonneg (int 0%nat) = 0 /\
  (forall (n : nat), int n < int (S n)) /\
  (forall (t : R), exists n : nat, int n <= t < int (S n)).

Definition StateFlow_intervals {I O ST : Type}
           (trans : ST -> I -> ST)
           (out : ST -> I -> O)
           (init : ST)
: Arrow I O :=
  fun i o =>
    exists st : nat -> (nonnegreal * ST),
         snd (st 0%nat) = init
      /\ real_partition (fun n => fst (st n))
      /\ (forall (n : nat) (t : R),
             fst (st n) <= t < fst (st (S n)) ->
             o t = out (snd (st n)) (i t))
      /\ (forall (n : nat),
             snd (st (S n)) = trans (snd (st n)) (i (fst (st (S n)))))
      /\ (forall (n : nat) (t : R),
             fst (st n) <= t < fst (st (S n)) ->
             snd (st n) = trans (snd (st n)) (i t)).

Theorem real_interval_rule :
  forall (P : R -> Prop) (int : nat -> nonnegreal),
    real_partition int ->
    (forall (n : nat),
        (forall (t : R), int n <= t < int (S n) -> P t)) ->
    forall x : R, 0 <= x -> P x.
Proof.
  intros P int Hord Hn x Hx. unfold real_partition in Hord.
  destruct Hord as [Hord0 [Hord1 Hord2]].
  specialize (Hord2 x). destruct Hord2 as [n Hord2].
  eapply Hn; eauto.
Qed.

Theorem real_interval_induction :
  forall (P : R -> Prop) (int : nat -> nonnegreal),
    real_partition int ->
    (forall (n : nat),
        (forall (t : R), 0 <= t < int n -> P t) ->
        (forall (t : R), int n <= t < int (S n) -> P t)) ->
    forall x : R, 0 <= x -> P x.
Proof.
  intros. unfold real_partition in *.
  decompose [and] H; clear H.
  apply real_induction.
  { apply (H0 0%nat).
    { intros. rewrite H2 in *. psatzl R. }
    { rewrite H2. specialize (H4 0%nat). psatzl R. } }
  { intros. specialize (H5 x0). destruct H5.
    eapply H0; eauto. intros.
    apply H3. psatzl R. }
  { intros. specialize (H5 x0). destruct H5.
    exists (int (S x1)). split.
    { tauto. }
    { intros. apply H0 with (n:=x1); [ | psatzl R ].
      intros. apply H3. psatzl R. } }
  { assumption. }
Qed.

Lemma reals_dense :
  forall (x y : R),
    x < y ->
    exists z : R, x < z < y.
Proof.
  intros x y Hxy.
  pose proof (archimed (1/(y - x))).
  destruct H. clear H0.
  generalize dependent (IZR (up (1 / (y - x)))). intros n H.
  pose proof (archimed (n * x)). destruct H0.
  generalize dependent (IZR (up (n * x))). intros m H0 H1.
  exists (m / n).
  assert ((y - x) * / (y - x) = 1) by (apply Rinv_r; psatzl R).
  assert ((y - x) * n > 1).
  { unfold Rdiv in *. rewrite Rmult_1_l in *. psatz R. }
  cut (n * x < m < n * y).
  { assert (n * / n = 1) by (apply Rinv_r; psatz R).
    intros. unfold Rdiv. generalize dependent (/n). intros.
    assert (n > 0) by psatz R.
    clear - H4 H5 H6. split; psatz R. }
  { psatz R. }
Qed.

Lemma closed_continuous :
  forall {T : UniformSpace} (D : T -> Prop),
    closed D ->
    forall (f : R -> T) (u l : R),
      l < u ->
      (forall r, l <= r < u -> D (f r)) ->
      continuous f u ->
      D (f u).
Proof.
  intros. apply NNPP; intro.
  unfold closed, open, continuous, locally, filterlim,
  filter_le, filtermap in *.
  specialize (H _ H3). specialize (H2 _ H).
  simpl in *. destruct H2 as [eps H2].
  cbv beta iota zeta delta - [ not abs ] in H2.
  destruct (reals_dense (Rmax l (u - eps)) u).
  { destruct eps. simpl. unfold Rmax. destruct_ite; psatzl R. }
  apply H2 with (y:=x) in H1; auto.
  { destruct eps. simpl in *. compute.
    destruct_ite; try psatzl R.
    assert (u - pos < x).
    { revert H4. unfold Rmax. destruct_ite; psatzl R. }
    psatzl R. }
  { revert H4. apply Rmax_case_strong; intros; psatzl R. }
Qed.

Lemma real_partition_pos :
  forall int n,
    real_partition int ->
    0 < int (S n).
Proof.
  intros. unfold real_partition in H. destruct H as [H0 [Hsuc ?]].
  induction n.
  { specialize (Hsuc 0%nat). psatzl R. }
  { specialize (Hsuc (S n)). psatzl R. }
Qed.

Theorem StateFlow_induction2 :
  forall (I : UniformSpace) (O ST : Type) (trans : ST -> I -> ST)
         (out : ST -> I -> O) (init : ST)
         (P : I -> ST -> O -> Prop)
         (i : Signal I) (o : Signal O),
    StateFlow_intervals trans out init i o ->
    (forall s o, closed (fun i => P i s (o s i))) ->
    (forall t, 0 < t -> continuous i t) ->
    P (i 0) init (out init (i 0)) ->
    (forall (s : ST) (l u : R),
        0 <= l ->
        (forall t, l <= t < u -> s = trans s (i t)) ->
        (forall t, l <= t < u -> o t = out s (i t)) ->
        P (i l) s (out s (i l)) ->
        (forall t, l < t < u ->
                   P (i t) s (out s (i t)))) ->
    (forall i s, P i s (out s i) ->
                 P i (trans s i) (out (trans s i) i)) ->
    forall t, 0 <= t -> exists st, P (i t) st (o t).
Proof.
  intros I O ST trans out init P i o Hst Hclosed Hcont Hinit
         Hind1 Hind2.
  destruct Hst as [st [Hst0 [Hord [Hout [Htrans Hinner]]]]].
  eapply real_interval_rule; eauto. intros. exists (snd (st n)).
  destruct Hord as [Hord0 [Hord1 Hord2]]. simpl in *.
  erewrite Hout; eauto. generalize dependent t.
  induction n; intros.
  { subst. repeat destruct H.
    { eapply Hind1; eauto; try psatzl R.
      rewrite Hord0. assumption. }
    { rewrite Hord0. assumption. } }
  { assert (P (i (fst (st (S n)))) (snd (st (S n)))
              (out (snd (st (S n))) (i (fst (st (S n)))))).
    { rewrite Htrans. eapply Hind2.
      eapply closed_continuous; eauto. apply Hcont.
      eapply real_partition_pos with (int:=fun n => fst (st n)).
      unfold real_partition; tauto. }
    repeat destruct H.
    { eapply Hind1; eauto.
      pose proof (real_partition_pos (fun n => fst (st n)) n).
      assert (real_partition (fun n : nat => fst (st n)))
        by (unfold real_partition; tauto).
      intuition psatzl R. }
    { eauto. } }
Qed.

Theorem StateFlow_induction2_stateless :
  forall (I : UniformSpace) (O ST : Type) (trans : ST -> I -> ST)
         (out : ST -> I -> O) (init : ST)
         (P : I -> O -> Prop)
         (i : Signal I) (o : Signal O),
    StateFlow_intervals trans out init i o ->
    (forall o, closed (fun i => P i (o i))) ->
    (forall t, 0 < t -> continuous i t) ->
    P (i 0) (out init (i 0)) ->
    (forall (s : ST) (l u : R),
        0 <= l ->
        (forall t, l <= t < u -> s = trans s (i t)) ->
        (forall t, l <= t < u -> o t = out s (i t)) ->
        P (i l) (out s (i l)) ->
        (forall t, l < t < u ->
                   P (i t) (out s (i t)))) ->
    (forall i s, P i (out s i) ->
                 P i (out (trans s i) i)) ->
    forall t, 0 <= t -> P (i t) (o t).
Proof.
  intros.
  eapply StateFlow_induction2 with (P:=fun i _ o => P i o) in H;
    eauto.
  destruct H. apply H; auto.
Qed.

(*
Theorem StateFlow_induction2 :
  forall (I O S : Type) (trans : S -> I -> S)
         (out : S -> I -> O) (init : S)
         (P : I -> S -> O -> Prop)
         (i : Signal I) (o : Signal O),
    StateFlow_ClosedLeft trans out init i o ->
    P (i 0) init (out init (i 0)) ->
    (forall (s : S) (i : Signal I),
        (forall t, 0 <= t -> trans s i = s) ->
        (forall t, 0 <= t -> P (i t) s (out s (i t)))) ->
    

    (forall i1 i2 s o, P i1 s o ->
                       o = out s i1 ->
                       P i2 s o ->
                       P i2 (trans s i2) (out (trans s i2) i2)) ->
    exists st, forall t, 0 <= t -> P (i t) (st t) (o t).

Theorem StateFlow_induction2 :
  forall (I O S : Type) (trans : S -> I -> S)
         (out : S -> I -> O) (init : S)
         (P : I -> S -> O -> Prop)
         (i : Signal I) (o : Signal O),
    StateFlow_ClosedLeft trans out init i o ->
    P (i 0) init (out init (i 0)) ->
    (forall i1 i2 s o, P i1 s o ->
                       o = out s i1 ->
                       P i2 s o ->
                       P i2 (trans s i2) (out (trans s i2) i2)) ->
    exists st, forall t, 0 <= t -> P (i t) (st t) (o t).
Proof.
  intros I O S trans out init P i o Hst Hinit Hind.
  unfold StateFlow_ClosedLeft in Hst.
  destruct Hst as [st [Hst0 [Hout Htrans]]].
  exists st. intros t Ht.
  apply real_induction
  with (P:=fun t => P (i t) (st t) (o t)).
  { subst. rewrite <- Hout. assumption. }
  { intros. specialize (Htrans x H).
    destruct Htrans as [eps [Hsp Htrans]].
    assert (Rmax 0 (x - eps) < x).
    { apply Rmax_lub_lt; psatzl R. }
    assert (x - eps <= Rmax 0 (x - eps)) by apply Rmax_r.
    assert (0 <= Rmax 0 (x - eps)) by apply Rmax_l.
    rewrite <- Hout. erewrite Htrans.
    eapply Hind.
    

SearchAbout ball.
Print ProperFilter.
Lemma ProperFilter_forall_R :
  ProperFilter (fun P
Print R_complete_lim.
SearchAbout is_lub_Rbar.
SearchAbout Rbar_is_lub.


SearchAbout R_complete_lim.
    apply H0.

    specialize (Htrans (Rmax 0 (x - eps))). specialize_arith Htrans.
    pose proof (Hout x) as Houtx. rewrite Htrans in *.
    rewrite <- Houtx. eapply Hind.
    specialize (H0 (Rmax 0 (x - eps))).
    specialize_arith H0.
    + eassumption.
    + symmetry. auto.
  - (* This case is unnecessary if we assume axiom of choice. *)
    admit.
  - assumption.
Admitted.
*)

Definition Controller (temp : Signal R) (on : Signal bool) :=
  StateFlow_intervals
    (I:=R) (ST:=bool) (O:=bool)
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

(*
Lemma ind_inv_Controller_ok :
  forall (temp : Signal R) (on : Signal bool),
    temp 0 = 0 ->
    Controller temp on ->
    forall t, 0 <= t -> ind_inv_Controller (temp t) (on t).
Proof.
  unfold Controller. intros.
  eapply StateFlow_induction2_stateless; eauto.
  cbv beta iota zeta delta - [ Rge Rle ]. intros.
  specialize (H2 t' H3). destruct s.
  { destruct (Rge_dec (temp t') 1); try discriminate.
    intuition psatzl R. }
  { destruct (Rle_dec (temp t') (-1)); try discriminate.
    intuition psatzl R. }
Qed.
*)

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

Lemma Integrator_init :
  forall s1 s2 init,
    Integrator init s1 s2 ->
    s2 0 = init.
Proof.
  unfold Integrator. intros.
  specialize (H 0).
  assert (is_RInt s1 0 0 zero) by apply is_RInt_point.
  apply is_RInt_unique in H; try psatzl R.
  apply is_RInt_unique in H0. rewrite H in H0. unfold zero in *.
  simpl in *. psatzl R.
Qed.

(*
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
    intros x Hx Hind. 
  { admit. }
  { assumption. }
Admitted.
*)

Definition Controller2 (temp : Signal R) (dtemp : Signal R) :=
  StateFlow_intervals
    (I:=R) (ST:=bool) (O:=R)
    (fun s i => if s
                then if Rge_dec i 1 then false else true
                else if Rle_dec i (-1) then true else false)
    (fun s _ => if s then 1 else -1)
    true temp dtemp.

Definition thermostat2 (init : R) (temp : Signal R)
           (dtemp : Signal R) :=
  Integrator init dtemp temp /\
  Controller2 temp dtemp.

Lemma closed_le_r :
  forall (a : R),
    closed (fun x => a <= x).
Proof.
  unfold closed. intros. eapply open_ext.
  { intros. split.
    { apply Rlt_not_le. }
    { simpl. psatzl R. } }
  { apply open_lt. }
Qed.

Lemma closed_le_l :
  forall (a : R),
    closed (fun x => x <= a).
Proof.
  unfold closed. intros. eapply open_ext.
  { intros. split.
    { apply Rgt_not_le. }
    { simpl. psatzl R. } }
  { apply open_gt. }
Qed.

Lemma closed_ge_r :
  forall (a : R),
    closed (fun x => a >= x).
Proof.
  unfold closed. intros. eapply open_ext.
  { intros. split.
    { apply Rgt_not_ge. }
    { simpl. psatzl R. } }
  { apply open_gt. }
Qed.

Lemma closed_ge_l :
  forall (a : R),
    closed (fun x => x >= a).
Proof.
  unfold closed. intros. eapply open_ext.
  { intros. split.
    { apply Rlt_not_ge. }
    { simpl. psatzl R. } }
  { apply open_lt. }
Qed.

Ltac prove_closed :=
  repeat first [ apply closed_true |
                 apply closed_false |
                 apply closed_ge_r |
                 apply closed_le_r |
                 apply closed_ge_l |
                 apply closed_le_l |
                 apply closed_and |
                 apply closed_or ].

Require Import Coq.Classes.RelationClasses.
Require Import RIneq.
Global Instance Reflexive_Rge : Reflexive Rge.
Proof.
  red. intro. apply Req_ge. reflexivity.
Qed.

Global Instance Reflexive_Rle : Reflexive Rle.
Proof.
  red. intro. apply Req_ge. reflexivity.
Qed.

Require Import Setoid Relation_Definitions Reals.
Local Open Scope R.

Add Parametric Relation : R Rle
reflexivity proved by Rle_refl
transitivity proved by Rle_trans
as Rle_setoid_relation.

Add Parametric Morphism : Rplus with
signature Rle ++> Rle ++> Rle as Rplus_Rle_mor.
intros ; apply Rplus_le_compat ; assumption.
Qed.

Add Parametric Morphism : Rminus with
signature Rle ++> Rle --> Rle as Rminus_Rle_mor.
intros ; unfold Rminus ;
apply Rplus_le_compat;
[assumption | apply Ropp_le_contravar ; assumption].
Qed.

Ltac simpl_Rmax :=
  repeat first [rewrite Rbasic_fun.Rmax_left in * by psatzl R |
                rewrite Rbasic_fun.Rmax_right in * by psatzl R ].

Ltac simpl_Rmin :=
  repeat first [rewrite Rbasic_fun.Rmin_left in * by psatzl R |
                rewrite Rbasic_fun.Rmin_right in * by psatzl R ].

Lemma is_RInt_unique_eq :
  forall (f : R -> R) a b l1 l2,
    is_RInt f a b l1 ->
    is_RInt f a b l2 ->
    l1 = l2.
Proof.
  intros. apply is_RInt_unique in H. apply is_RInt_unique in H0.
  congruence.
Qed.

Lemma thermostat_in_range :
  forall temp dtemp,
    thermostat2 0 temp dtemp ->
    forall t, 0 <= t -> safe (temp t).
Proof.
  unfold thermostat2. intros temp dtemp Htherm t Ht.
  destruct Htherm as [Hint Hcontrol].
  unfold Controller2 in Hcontrol.
  eapply StateFlow_induction2_stateless
    with (P:=fun i o => safe i); eauto.
  { intros. prove_closed. }
  { intros. eapply (continuous_RInt_1 dtemp).
    simpl. unfold locally. simpl. unfold Integrator in Hint.
    setoid_rewrite Rminus_0_r in Hint.
    exists {| pos:=t0; cond_pos:=H |}. intros.
    apply Hint. compute in H0. revert H0.
    destruct_ite; intros; psatzl R. }
  { apply Integrator_init in Hint. compute. psatzl R. }
  { cbv beta iota zeta delta - [ Rge Rle ]. intros.
    destruct s.
    { split.
      { unfold Integrator in Hint.
        setoid_rewrite Rminus_0_r in Hint.
        pose proof (Hint l) as Hint_l.
        pose proof (Hint t0) as Hint_t0.
        specialize_arith Hint_l. specialize_arith Hint_t0.
        pose proof (is_RInt_const l t0 1) as Hint_l_t0.
        unfold scal in Hint_l_t0. simpl in Hint_l_t0.
        unfold mult in Hint_l_t0. simpl in Hint_l_t0.
        rewrite Rmult_1_r in Hint_l_t0.
        assert (is_RInt dtemp 0 t0 (temp l + (t0 - l))).
        { apply (is_RInt_Chasles dtemp 0 l t0); auto.
          apply is_RInt_ext with (f:=fun _ : R => 1); auto.
          intros. rewrite H1; auto. simpl_Rmax. simpl_Rmin.
          psatzl R. }
        erewrite is_RInt_unique_eq; eauto. psatzl R. }
      { specialize (H0 t0). specialize_arith H0.
        destruct (Rge_dec (temp t0) 1); try discriminate.
        psatzl R. } }
    { split.
      { specialize (H0 t0). specialize_arith H0.
        destruct (Rle_dec (temp t0) (-1)); try discriminate.
        psatzl R. }
      { unfold Integrator in Hint.
        setoid_rewrite Rminus_0_r in Hint.
        pose proof (Hint l) as Hint_l.
        pose proof (Hint t0) as Hint_t0.
        specialize_arith Hint_l. specialize_arith Hint_t0.
        pose proof (is_RInt_const l t0 (-1)) as Hint_l_t0.
        unfold scal in Hint_l_t0. simpl in Hint_l_t0.
        unfold mult in Hint_l_t0. simpl in Hint_l_t0.
        rewrite <- Ropp_mult_distr_r in Hint_l_t0.
        rewrite Rmult_1_r in Hint_l_t0.
        assert (is_RInt dtemp 0 t0 (temp l - (t0 - l))).
        { apply (is_RInt_Chasles dtemp 0 l t0); auto.
          apply is_RInt_ext with (f:=fun _ : R => -1); auto.
          intros. rewrite H1; auto. simpl_Rmax. simpl_Rmin.
          psatzl R. }
        erewrite is_RInt_unique_eq with (l1:=temp t0); eauto.
        psatzl R. } } }
Qed.
