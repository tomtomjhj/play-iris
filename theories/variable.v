From iris.proofmode Require Import tactics.
From iris.algebra Require Import excl auth frac_auth gmap gset.
From iris.base_logic.lib Require Export invariants.
From iris.program_logic Require Export atomic.
From iris.heap_lang Require Import proofmode notation par.

Class histG Σ := HistG {
  hist_inG :> inG Σ (frac_authR (gmapUR mnat (exclR valO)));
  timestamp_inG :> inG Σ (exclR mnatR)
}.
Definition histΣ : gFunctors :=
  #[GFunctor (frac_authR (gmapUR mnat (exclR valO))); GFunctor (exclR mnatR)].
Instance subG_histΣ {Σ} : subG histΣ Σ → histG Σ.
Proof. solve_inG. Qed.

Section var.
  Context `{!heapG Σ} `{histG Σ} (N : namespace).

  Definition new : val := λ: "v", ref "v".
  Definition set : val := λ: "l" "x", "l" <- "x".

  Definition last_op (t : mnat) v (hs : gmapUR mnat (exclR valO)) : iProp Σ :=
    ⌜(∀ (t' : mnat), (t' ∈ (dom (gset mnat) hs) → t' ≤ t))
    ∧ hs !! t = Some (Excl v) ⌝.

  Definition is_hist l γh γt :=
    inv N (∃ v, (l ↦ v) ∗
                (∃ hs (t : mnat),
                    own γh (●F hs) ∗
                    own γt (Excl t) ∗
                    last_op t v hs)).

  Lemma set_spec (l : loc) (γh γt : gname) (q : Qp) (v : val) :
    is_hist l γh γt -∗
    <<< ∀ hs, own γh (◯F{q} hs) >>>
      set #l v @ ⊤ ∖ ↑N
    <<< ∃ (t : mnat),
        own γh (◯F{q} (<[t :=Excl v]> hs)),
        RET #() >>>.
  Proof.
    iIntros "#Hist" (Φ) "AU". wp_lam; wp_let.
    iInv N as (v') ">[Hl H]".
    iDestruct "H" as (hsM tM) "[H● [Ht [% _]]]". rename H0 into tM_max.
    iMod "AU" as (hs) "[H◯ [_ Hclose]]".
    iMod (own_update with "Ht") as "Ht";
      first by apply (cmra_update_exclusive (Excl (S tM))).
    iMod (own_update_2 with "H● H◯") as "[H● H◯]".
    { apply frac_auth_update, (alloc_local_update _ _ (S tM) (Excl v)); last done.
      rewrite <-(not_elem_of_dom (D:=gset mnat)).
      intro. apply tM_max in H0. lia. }
    wp_store. clear v'.
    iMod ("Hclose" with "[H◯]") as "$"; first done.
    iModIntro; iModIntro; iNext.
    iExists v. iSplitL "Hl"; first done.
    iExists (<[S tM:=Excl v]> hsM), (S tM). iFrame.
    iPureIntro. split; last by rewrite lookup_insert.
    intros t'.
    rewrite (dom_insert (M:=gmap mnat) (D:=gset mnat) (A:=excl valO)).
    rewrite elem_of_union elem_of_singleton.
    intro Ht'.
    destruct Ht' as [Ht'|Ht'].
    - by rewrite Ht'.
    - apply tM_max in Ht'. lia.
  Qed.
End var.
