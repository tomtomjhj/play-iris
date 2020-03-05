From iris.proofmode Require Import tactics.
From iris.algebra Require Import excl auth list frac_auth gmap gset.
From iris.base_logic.lib Require Import invariants.
From iris.program_logic Require Import atomic.
From iris.heap_lang Require Import proofmode notation.
From iris_examples Require Import treiber2.
From play Require Import history.

Section stack_stuff.
  Typeclasses Transparent is_stack stack_cont.
  Context `{!heapG Σ, !stackG Σ}.
  Global Instance is_stack_persistent N l γ : Persistent (is_stack N l γ).
  Proof. apply _. Qed.
  Global Instance stack_cont_laterable l γ : Laterable (stack_cont l γ).
  Proof. apply _. Qed.
  Global Instance stack_cont_timeless l γ : Timeless (stack_cont l γ).
  Proof. apply _. Qed.
  Typeclasses Opaque is_stack stack_cont.
End stack_stuff.

Section operation.
  Inductive stack_op := Push of val | Pop of val.
  Canonical Structure stack_opO := leibnizO stack_op.
  (* TODO: linearizability stuff *)
End operation.

Section spec.
  Context `{!heapG Σ, !stackG Σ, !@histG stack_opO Σ} (N : namespace).

  Definition stackN := nroot .@ "stack".
  Notation is_stack := (is_stack stackN).

  Definition stack_histN := nroot .@ "stack_hist".
  Definition stack_hist γs γh :=
    inv stack_histN (∃ hs t ls, stack_cont γs ls ∗ hist γh hs t).

  Lemma new_stack_spec_hist :
    {{{ True }}}
      new_stack #()
    {{{ l γs γh, RET #l; is_stack l γs ∗ stack_hist γs γh ∗ hist_snap γh 1 ε }}}.
  Proof.
    iIntros (Φ) "_ Post".
    iApply wp_fupd.
    wp_lam. wp_alloc ℓ as "Hl".

    iMod (own_alloc (● (Some (Excl [])) ⋅ ◯ (Some (Excl [])))) as (γs) "[Hγs● Hγs◯]";
      first by apply auth_both_valid.
    iMod (inv_alloc stackN _ (stack_inv ℓ γs) with "[Hl Hγs●]") as "#Stack".
    { iNext. rewrite /stack_inv /phys_stack /phys_list.
      iExists []. iFrame. iExists None. by iFrame. }

    iMod (own_alloc (●F ε ⋅ ◯F{1} ε)) as (γh) "[Hγh● Hγh◯]"; first by apply frac_auth_valid.
    iMod (inv_alloc stack_histN _
                    (∃ hs t ls, stack_cont γs ls ∗ hist γh hs t)
            with "[Hγs◯ Hγh●]") as "#Hist".
    { iNext. iExists ε, O, []. rewrite /stack_cont /hist. iFrame. iPureIntro. apply hist_gapless0. }

    iModIntro. iApply "Post". auto with iFrame.
  Qed.

  Lemma push_stack_spec_hist (l : loc) (γs γh : gname) (v : val) :
    is_stack l γs -∗ stack_hist γs γh -∗
    <<< ∀ q hs, hist_snap γh q hs >>>
      push_stack v #l @ ⊤ ∖ ↑stackN ∖ ↑stack_histN
    <<< ∃ t, hist_snap γh q (<[ t := Excl (Push v) ]> hs ), RET #() >>>.
  Proof.
    iIntros "#Stack #Hist" (Φ) "AU".
    awp_apply (push_stack_spec stackN with "Stack").
    iInv stack_histN as (hsM tM lsM) ">[Hsc Hh]".
    iAaccIntro with "Hsc".
    { iIntros "Hsc !>". iSplitR "AU"; [eauto with iFrame|done]. }
    iMod "AU" as (q hs) "[Hhs [_ Hclose]]".
    iMod (hist_update γh q hsM hs tM (Push v) with "Hh Hhs") as "[Hh Hhs]".
    iMod ("Hclose" with "Hhs") as "$".
    iIntros "Hsc !> !>". eauto with iFrame.
  Qed.

  Lemma pop_stack_spec (l : loc) (γs γh : gname) :
    is_stack l γs -∗ stack_hist γs γh -∗
    <<< ∀ q hs, hist_snap γh q hs >>>
      pop_stack #l @ ⊤ ∖ ↑stackN ∖ ↑stack_histN
    <<< ∃ t, hist_snap γh q (<[ t := Excl (Pop #()) ]> hs ), RET #() >>>.
    (* <<< stack_cont γs (match xs with [] => [] | _::xs => xs end)
         , RET (match xs with [] => NONEV | v::_ => SOMEV v end) >>>. *)
  Proof.
  Admitted.
End spec.

Section client.
End client.
