From iris.bi Require Import lib.laterable.
From iris.proofmode Require Import tactics.
From iris.algebra Require Export excl auth frac_auth gmap gset updates local_updates.
From iris.base_logic Require Export base_logic lib.own.

(* snapshot history *)
Section History.
  Context {A : ofeT}.
  Notation Hist := (gmapUR nat (exclR A)).

  Class histG Σ := HistG { hist_inG :> inG Σ (frac_authR Hist) }.

  Definition histΣ : gFunctors := #[GFunctor (frac_authR Hist)].

  Instance subG_histΣ {Σ} : subG histΣ Σ → histG Σ.
  Proof. solve_inG. Qed.

  Context `{!histG Σ}.

  (* init with ε, t is the next timestamp *)
  Definition hist_gapless (t : nat) (hs : Hist) :=
    (size hs = t) ∧ (∀ t', t' ∈ (dom (gset nat) hs) → t' < t).

  Definition hist γh (hs : Hist) t : iProp Σ :=
    own γh (●F hs) ∗ ⌜hist_gapless t hs⌝.

  Definition hist_snap γh q (hs : Hist) : iProp Σ := own γh (◯F{q} hs).

  Lemma hist_fresh t hs : hist_gapless t hs -> hs !! t = None.
  Proof.
    intros [_ Hmax].
    rewrite -(not_elem_of_dom (D:=gset nat)) => H.
    specialize (Hmax t H).
    lia.
  Qed.

  Lemma hist_gapless0 : hist_gapless 0 ε.
  Proof.
    split. apply: map_size_empty.
    intro. by rewrite dom_empty elem_of_empty.
  Qed.

  Lemma hist_fresh_gapless (t : nat) a (hs : Hist) :
    hist_gapless t hs -> hist_gapless (S t) (<[t := Excl a]> hs).
  Proof.
    intros Hg. inversion Hg as [Hsize Hmax]. split.
    - move: ((hist_fresh t hs) Hg). rewrite -Hsize. apply: map_size_insert.
    - intros t'.
      rewrite dom_insert elem_of_union elem_of_singleton => [[/ltac:(lia)|Ht']].
      specialize (Hmax t' Ht'). lia.
  Qed.

  Lemma hist_alloc : (|==> ∃ γh, hist γh ε O ∗ hist_snap γh 1 ε)%I.
  Proof.
    iMod (own_alloc (●F ε ⋅ ◯F{1} ε)) as (γh) "[Hγh● Hγh◯]"; first by apply frac_auth_valid.
    iModIntro. iExists γh. iFrame. iPureIntro. exact hist_gapless0.
  Qed.

  Lemma hist_update γh q (hsM hs : Hist) t a :
    hist γh hsM t -∗ hist_snap γh q hs ==∗
         hist γh (<[t:=Excl a]> hsM) (S t) ∗ hist_snap γh q (<[t:=Excl a]> hs).
  Proof.
    rewrite /hist /hist_snap.
    iIntros "[H● %] H◯ ".
    iMod (own_update_2 with "H● H◯") as "[$ $]".
    { apply frac_auth_update, alloc_local_update; last done.
      by apply: hist_fresh. }
    iModIntro; iPureIntro. by apply: hist_fresh_gapless.
  Qed.

  (* Laterable is automatically derived.  *)
  Global Instance hist_timeless `{!OfeDiscrete A} γh hs t  : Timeless (hist γh hs t).
  Proof. apply _. Qed.
  Global Instance hist_snap_timeless `{!OfeDiscrete A} γh q hs : Timeless (hist_snap γh q hs).
  Proof. apply _. Qed.
End History.
Typeclasses Opaque hist hist_snap.

(* TODO: vs operation history *)
Section History2.
  Context {A : ofeT}.
  Notation Hist2 := (gmapUR nat (exclR (prodO A A))).

  Class hist2G Σ := Hist2G { hist2_inG :> inG Σ (frac_authR Hist2) }.

  Definition hist2Σ : gFunctors := #[GFunctor (frac_authR Hist2)].

  Instance subG_hist2Σ {Σ} : subG hist2Σ Σ → hist2G Σ.
  Proof. solve_inG. Qed.

  (* TODO:
     - well-formed
       - init with <[0:= (s,s)]>
       - t, t+1 overlap
     - gapless: indep to key type
     - *)

End History2.
