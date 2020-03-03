From iris.proofmode Require Import tactics.
From iris.algebra Require Import excl auth frac_auth gmap gset.
From iris.base_logic.lib Require Export invariants.
From iris.program_logic Require Export atomic.
From iris.heap_lang Require Import proofmode notation par.
From play Require Import history.

Section var.
  Context `{!heapG Σ} `{!@histG valO Σ} (N : namespace).

  Definition new : val := λ: "v", ref "v".
  Definition set : val := λ: "l" "x", "l" <- "x".

  Definition is_hist l γh := inv N (∃ hs t v, (l ↦ v) ∗ hist γh hs t v).

  Lemma set_spec (l : loc) (γh : gname) (q : Qp) (v : val) :
    is_hist l γh -∗
    <<< ∀ hs, hist_snap γh q hs >>>
      set #l v @ ⊤ ∖ ↑N
    <<< ∃ (t : nat), hist_snap γh q (<[t := Excl v]> hs), RET #() >>>.
  Proof.
    iIntros "#Hist" (Φ) "AU". wp_lam; wp_let.
    iInv N as (hsM t v') "[Hl H]".
    iMod "AU" as (hs) "[H◯ [_ Hclose]]".
    wp_store.
    iMod (hist_update with "H H◯") as "[H H◯]".
    iMod ("Hclose" with "[H◯]") as "$"; first done.
    iModIntro; iModIntro; iNext.
    iExists (<[S t:=Excl v]> hsM), (S t), v.
    iFrame.
  Qed.
End var.
