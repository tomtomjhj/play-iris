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

  Definition var_hist γh := inv N (∃ hs t, hist γh hs t).

  Lemma set_spec (l : loc) (γh : gname) (q : Qp) (v : val) :
    var_hist γh -∗
    <<< ∀ w hs, l ↦ w ∗ hist_snap γh q hs >>>
      set #l v @ ⊤ ∖ ↑N
    <<< ∃ (t : nat), l ↦ v ∗ hist_snap γh q (<[t := Excl v]> hs), RET #() >>>.
  Proof.
    iIntros "#Hist" (Φ) "AU". wp_lam; wp_let.
    iInv N as (hsM t) "H".
    iMod "AU" as (w hs) "[[Hl H◯] [_ Hclose]]".
    wp_store.
    iMod (hist_update with "H H◯") as "[H H◯]".
    iMod ("Hclose" with "[Hl H◯]") as "$"; first iFrame.
    iModIntro; iModIntro; iNext.
    iExists (<[t:=Excl v]> hsM), (S t).
    iFrame.
  Qed.
End var.
