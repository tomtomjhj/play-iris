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
  Definition stack_hist γh := inv stack_histN (∃ hs t, hist γh hs t).

  Lemma new_stack_spec_hist :
    {{{ True }}}
      new_stack #()
    {{{ l γs γh, RET #l; is_stack l γs ∗ stack_cont γs [] ∗ stack_hist γh ∗ hist_snap γh 1 ε }}}.
  Proof.
    iIntros (Φ) "_ Post".
    iApply wp_fupd.
    iMod hist_alloc as (γh) "[Hγh● Hγh◯]".
    iMod (inv_alloc stack_histN _ (∃ hs t, hist γh hs t) with "[Hγh●]") as "Hist"; first eauto.
    wp_apply (new_stack_spec stackN); first done.
    iIntros (l γs) "[Stack Sc] !>". iApply "Post". iFrame.
  Qed.

  Lemma push_stack_spec_hist (l : loc) (γs γh : gname) (v : val) :
    is_stack l γs -∗ stack_hist γh -∗
    <<< ∀ xs q hs, stack_cont γs xs ∗ hist_snap γh q hs >>>
      push_stack v #l @ ⊤ ∖ ↑stackN ∖ ↑stack_histN
    <<< ∃ t, stack_cont γs (v::xs) ∗ hist_snap γh q (<[t := Excl (Push v)]> hs ), RET #() >>>.
  Proof.
    iIntros "#Stack #Hist" (Φ) "AU".
    awp_apply (push_stack_spec stackN with "Stack").
    iInv stack_histN as (hsM tM) ">Hh".
    iApply (aacc_aupd_commit with "AU"); first solve_ndisj.
    iIntros (xs q hs) "[Hsc Hhs]".
    iAaccIntro with "Hsc"; first by auto 10 with iFrame.
    iMod (hist_update γh q hsM hs tM (Push v) with "Hh Hhs") as "[Hh Hhs]".
    eauto 11 with iFrame.
  Qed.

  Lemma pop_stack_spec (l : loc) (γs γh : gname) :
    is_stack l γs -∗ stack_hist γh -∗
    <<< ∀ q hs, hist_snap γh q hs >>>
      pop_stack #l @ ⊤ ∖ ↑stackN ∖ ↑stack_histN
    <<< ∃ t, hist_snap γh q (<[ t := Excl (Pop #()) ]> hs ), RET #() >>>.
    (* <<< stack_cont γs (match xs with [] => [] | _::xs => xs end)
         , RET (match xs with [] => NONEV | v::_ => SOMEV v end) >>>. *)
  Proof.
  Admitted.
End spec.

From iris.heap_lang Require Import lib.par.
Module client.
  Definition produce (s ap: loc) : val :=
    rec: "produce" "n" "i" :=
      if: "i" = "n" then #()
      else let: "e":= !(#ap +ₗ"i") in
           push_stack "e" #s;;
           "produce" "n" ("i" + #1).

  Definition consume (s ac: loc) : val :=
    rec: "consume" "n" "i" :=
      if: "i" = "n" then #()
      else match: pop_stack #s with
             NONE => "consume" "n" "i"
           | SOME "e" => (#ac + "i") <- "e";;
                        "consume" "n" ("i" + #1)
           end.

  Definition exchange (s ap ac : loc) : val :=
    λ: "n", (produce s ap) "n" #0 ||| (consume s ac) "n" #0.

  (* ap ↦∗ ls ∗ ∃ ls', ac ↦∗ ls' ∗ ⌜Permutation ls ls'⌝ *)

End client.
