From iris.proofmode Require Import tactics.
From iris.algebra Require Import excl auth frac_auth gmap gset.
From iris.base_logic.lib Require Export invariants.
From iris.program_logic Require Export atomic.
From iris.heap_lang Require Import proofmode notation par.

Class histG Σ := HistG {
  hist_inG :> inG Σ (frac_authR (gmapUR positive (exclR valO)))
}.
Definition histΣ : gFunctors :=
  #[GFunctor (frac_authR (gmapUR positive (exclR valO)))].
Instance subG_histΣ {Σ} : subG histΣ Σ → histG Σ.
Proof. solve_inG. Qed.

Section asdf.
  Context `{!heapG Σ} `{histG Σ} (N : namespace).

  Definition new : val := λ: "v", ref "v".
  Definition set : val := λ: "l" "x", "l" <- "x".

  Definition is_hist l γ := inv N ((l ↦ -) ∗ (∃ hs, own γ (●F hs))).

  Lemma set_spec (l : loc) (γ : gname) (q : Qp) (v : val) :
    is_hist l γ -∗
    <<< ∀ hs, own γ (◯F{q} hs) >>>
      set #l v @ ⊤ ∖ ↑N
    <<< ∃ (t:positive),
        own γ (◯F{q} (hs ⋅ {[t:=Excl v]})),
        RET #() >>>.
  Proof.
    iIntros "#Hist" (Φ) "AU". wp_lam; wp_let.
    iInv N as ">[Hl H●]".
    iDestruct "Hl" as (?) "Hl". iDestruct "H●" as (hsM) "H●".
    iMod "AU" as (hs) "[H◯ [_ Hclose]]".
    wp_store.
    iMod ("Hclose" with "[H◯]") as "$". iModIntro; iModIntro; iNext.
    iSplitL "Hl"; eauto.
End asdf.

(* history of variable value *)
