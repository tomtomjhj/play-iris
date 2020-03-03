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

  (* init with <[0 := ...]> *)
  Definition last_op (t : nat) a (hs : Hist) :=
    (size hs = (S t)) ∧
    (∀ t', t' ∈ (dom (gset nat) hs) → t' ≤ t) ∧
    hs !! t = Some (Excl a).

  Definition hist γh (hs : Hist) t a : iProp Σ :=
    own γh (●F hs) ∗ ⌜last_op t a hs⌝.

  Definition hist_snap γh q (hs : Hist) : iProp Σ := own γh (◯F{q} hs).

  Lemma new_timestamp t a hs : last_op t a hs -> hs !! (S t) = None.
  Proof.
    intros (_ & Hmax & _).
    rewrite -(not_elem_of_dom (D:=gset nat)) => H.
    specialize (Hmax (S t) H).
    lia.
  Qed.

  Lemma new_op (t : nat) a b (hs : Hist) :
    last_op t a hs -> last_op (S t) b (<[S t := Excl b]> hs).
  Proof.
    intros (Hsize & Hmax & ?).
    split; [|split]; last by rewrite lookup_insert.
    - rewrite <-Hsize. apply: map_size_insert. rewrite Hsize.
      by apply: new_timestamp.
    - intros t'.
      rewrite dom_insert elem_of_union elem_of_singleton => [[/ltac:(lia)|Ht']].
      specialize (Hmax t' Ht'). lia.
  Qed.

  Lemma hist_update γh q (hsM hs : Hist) t a b :
    hist γh hsM t a -∗ hist_snap γh q hs ==∗
         hist γh (<[S t:=Excl b]> hsM) (S t) b ∗ hist_snap γh q (<[S t:=Excl b]> hs).
  Proof.
    rewrite /hist /hist_snap.
    iIntros "[H● %] H◯ ".
    iMod (own_update_2 with "H● H◯") as "[H● H◯]".
    { apply frac_auth_update, (alloc_local_update _ _ (S t) (Excl b)); last done.
      by apply: new_timestamp. }
    iFrame; iModIntro; iPureIntro. by apply: new_op.
  Qed.

  (* NOTE Timeless requires {!OfeDiscrete A}  *)
End History.
Typeclasses Opaque hist hist_snap.

(* TODO: snapshot before/after. TODO: vs operation history *)
Section History2.
  Context {A : ofeT}.
  Notation Hist2 := (gmapUR nat (exclR (prodO A A))).

  Class hist2G Σ := Hist2G { hist2_inG :> inG Σ (frac_authR Hist2) }.

  Definition hist2Σ : gFunctors := #[GFunctor (frac_authR Hist2)].

  Instance subG_hist2Σ {Σ} : subG hist2Σ Σ → hist2G Σ.
  Proof. solve_inG. Qed.

  (* TODO: well-formed *)

End History2.
