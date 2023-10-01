From armiris Require Import
  prelude
  proofmode.
From armiris.language Require Export
  weakestpre.

Section armiris_program.
  Context `{!ArmirisProgram}.

  #[local] Lemma wp_adequacy' `{armiris_GS : !ArmirisGS Σ} n blk σ cfg' Q :
    nsteps (step armiris_prog) n (blk, σ) cfg' →
    state_interp σ -∗
    WP blk {{ Q }} -∗
    ▷^n ⌜not_stuck armiris_prog cfg'⌝.
  Proof.
    iInduction n as [| n] "IH" forall (blk σ);
      iIntros "%Hsteps Hsi Hwp";
      invert Hsteps as [| ? ? (blk'' & σ'') ? Hstep Hsteps'].
    - rewrite /not_stuck.
      destruct blk as [| instr blk]; first iSmash.
      iMod (weakestpre.wp_cons with "Hwp Hsi") as "(%blk' & %σ' & %Hstep & Hwp)".
      eauto with step.
    - destruct blk as [| instr blk]; invert Hstep as [? ? ? ? ? Hstep'].
      iMod (weakestpre.wp_cons with "Hwp Hsi") as "(%blk''' & %σ''' & %Hstep & Hwp)".
      efeed pose proof prim_step_deterministic; [apply Hstep' | apply Hstep |]. simplify.
      iModIntro.
      iMod "Hwp" as "(Hsi & Hwp)".
      iApply ("IH" $! _ _ Hsteps' with "Hsi Hwp").
  Qed.
  Lemma wp_adequacy blk Q :
    ( ⊢
      ∀ armiris_GS : ArmirisGS armiris_Σ,
      ([∗list] r ∈ enum register, r ↦ᵣ inhabitant) -∗
      flags↦ inhabitant -∗
      WP blk {{ Q }}
    ) →
    safe armiris_prog (blk, ∅).
  Proof.
    intros Hwp cfg' (n & Hsteps)%rtc_nsteps.
    apply (uPred.pure_soundness (M := iResUR armiris_Σ)), (uPred.laterN_soundness _ n).
    iMod armiris_init as "(%armiris_GS & Hsi & Hregs & Hfl)".
    iDestruct (Hwp with "Hregs Hfl") as "Hwp".
    iApply (wp_adequacy' with "Hsi Hwp"); first done.
  Qed.
End armiris_program.
