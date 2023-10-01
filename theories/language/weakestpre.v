From iris.base_logic Require Export
  lib.iprop.

From armiris Require Import
  prelude
  proofmode.
From armiris.language Require Export
  state_interp.

Implicit Types i j l : Z.
Implicit Types w : word.
Implicit Types lbl : label.
Implicit Types r : register.
Implicit Types cond : condition.
Implicit Types blk : block.
Implicit Types prog : program.
Implicit Types v : value.
Implicit Types fl : flags.
Implicit Types σ : state.

Canonical block_O :=
  leibnizO block.

Class ArmirisProgram :=
  armiris_prog : program.

Section definition.
  Context `{!ArmirisProgram}.
  Context `{armiris_GS : !ArmirisGS Σ}.

  #[local] Definition wp_body (wp : block -d> iPropO Σ -d> iPropO Σ) : block -d> iPropO Σ -d> iPropO Σ :=
    λ blk Q, (
      match blk with
      | [] =>
          |==> Q
      | instr :: blk =>
          ∀ σ,
          state_interp σ ==∗
            ∃ blk' σ',
            ⌜prim_step armiris_prog blk σ instr blk' σ'⌝ ∗
            ▷ |==>
              state_interp σ' ∗
              wp blk' Q

      end
    )%I.

  #[local] Instance wp_body_contractive : Contractive wp_body.
  Proof.
    rewrite /wp_body => n wp1 wp2 Hwp blk Q.
    destruct blk; first done.
    repeat (apply Hwp || f_contractive || f_equiv).
  Qed.

  #[local] Definition wp_def : block → iProp Σ → iProp Σ :=
    fixpoint wp_body.
  #[local] Definition wp_aux : seal (@wp_def).
    Proof. eexists. done. Qed.
  Definition wp :=
    wp_aux.(unseal).
  #[local] Definition wp_unseal : wp = wp_def.
    Proof. rewrite -wp_aux.(seal_eq) //. Qed.
End definition.

Notation "'WP' blk {{ Q } }" := (
  wp blk Q
)(at level 20,
  blk, Q at level 200,
  format "'[hv' WP  blk  {{  '/  ' '[' Q ']'  '/' } } ']'"
) : bi_scope.
Notation "'WP' blk {{ Q } }" := (
  ⊢ wp blk Q
)(at level 20,
  blk, Q at level 200
) : stdpp_scope.

Notation "'{{{' P } } } blk {{{ Q } } }" :=
  (□ (∀ R, P -∗ ▷ (Q -∗ R) -∗ WP blk {{ R }}))%I
( at level 20,
  format "'[hv' {{{  '/  ' '[' P ']'  '/' } } }  '/  ' blk  '/' {{{  '/  ' '[' Q ']'  '/' } } } ']'"
) : bi_scope.
Notation "'{{{' P } } } blk {{{ Q } } }" := (
  ∀ R, P -∗ ▷ (Q -∗ R) -∗ WP blk {{ R }}
) : stdpp_scope.

Section rules.
  Context `{!ArmirisProgram}.
  Context `{armiris_GS : !ArmirisGS Σ}.

  Section wp_body.
    Context (M : block → iProp Σ → iProp Σ).

    #[local] Lemma wp_body_nil Q :
      wp_body M [] Q ⊣⊢
      |==> Q.
    Proof.
      done.
    Qed.
    #[local] Lemma wp_body_nil_1 Q :
      wp_body M [] Q ⊢
      |==> Q.
    Proof.
      rewrite wp_body_nil //.
    Qed.
    #[local] Lemma wp_body_nil_2 Q :
      (|==> Q) ⊢
      wp_body M [] Q.
    Proof.
      rewrite wp_body_nil //.
    Qed.

    #[local] Lemma wp_body_post Q :
      Q ⊢
      wp_body M [] Q.
    Proof.
      rewrite wp_body_nil. iSmash.
    Qed.

    #[local] Lemma wp_body_cons instr blk Q :
      wp_body M (instr :: blk) Q
      ⊣⊢
      ∀ σ,
      state_interp σ ==∗
        ∃ blk' σ',
        ⌜prim_step armiris_prog blk σ instr blk' σ'⌝ ∗
        ▷ |==> (
          state_interp σ' ∗
          M blk' Q
        ).
    Proof.
      done.
    Qed.
    #[local] Lemma wp_body_cons_1 instr blk Q :
      wp_body M (instr :: blk) Q ⊢
        ∀ σ,
        state_interp σ ==∗
          ∃ blk' σ',
          ⌜prim_step armiris_prog blk σ instr blk' σ'⌝ ∗
          ▷ |==> (
            state_interp σ' ∗
            M blk' Q
          ).
    Proof.
      rewrite wp_body_cons //.
    Qed.
    #[local] Lemma wp_body_cons_2 instr blk Q :
      ( ∀ σ,
        state_interp σ ==∗
          ∃ blk' σ',
          ⌜prim_step armiris_prog blk σ instr blk'  σ'⌝ ∗
          ▷ |==> (
            state_interp σ' ∗
            M blk' Q
          )
      ) ⊢
      wp_body M (instr :: blk) Q.
    Proof.
      rewrite wp_body_cons //.
    Qed.

    #[local] Lemma bupd_wp_body blk Q :
      (|==> wp_body M blk Q) ⊢
      wp_body M blk Q.
    Proof.
      destruct blk; first iSmash.
      iIntros "Hwp %σ Hsi".
      iMod ("Hwp" with "Hsi") as ">(%blk' & %σ' & %Hstep & HM)".
      iSmash.
    Qed.

    #[local] Lemma wp_body_mono blk Q1 Q2 :
      ▷ (∀ blk, (Q1 ==∗ Q2) -∗ M blk Q1 ==∗ M blk Q2) -∗
      (Q1 ==∗ Q2) -∗
      wp_body M blk Q1 -∗
      wp_body M blk Q2.
    Proof.
      destruct blk; first iSmash.
      iIntros "HM HQ Hwp %σ Hsi".
      iMod ("Hwp" with "Hsi") as "(%blk' & %σ' & %Hstep & Hwp)".
      iModIntro. iExists blk', σ'. iSplitR; first iSmash. iModIntro.
      iMod "Hwp" as "($ & Hwp)".
      iApply ("HM" with "HQ Hwp").
    Qed.

    #[local] Lemma wp_body_bupd blk Q :
      ▷ (∀ blk, M blk (|==> Q) ==∗ M blk Q) -∗
      wp_body M blk (|==> Q) -∗
      wp_body M blk Q.
    Proof.
      iIntros "HM".
      iApply (wp_body_mono with "[HM]"); iSmash.
    Qed.
  End wp_body.

  Section wp.
    #[local] Lemma wp_unfold blk Q :
      WP blk {{ Q }} ⊣⊢
      wp_body wp blk Q.
    Proof.
      rewrite wp_unseal. apply (fixpoint_unfold wp_body).
    Qed.

    #[global] Instance wp_ne blk n :
      Proper ((≡{n}≡) ==> (≡{n}≡)) (wp blk).
    Proof.
      revert blk. induction (lt_wf n) as [n _ IH]=> blk Q1 Q2 HQ.
      rewrite !wp_unfold /wp_body.
      destruct blk; first solve_proper.
      do 9 f_equiv. f_contractive. do 2 f_equiv.
      apply IH; first done. eapply dist_lt; done.
    Qed.
    #[global] Instance wp_proper blk :
      Proper ((≡) ==> (≡)) (wp blk).
    Proof.
      intros Q1 Q2 HQ.
      apply equiv_dist => n. apply wp_ne. auto.
    Qed.

    Lemma wp_nil Q :
      WP [] {{ Q }} ⊣⊢
      |==> Q.
    Proof.
      rewrite wp_unfold wp_body_nil //.
    Qed.
    Lemma wp_nil_1 Q :
      WP [] {{ Q }} ⊢
      |==> Q.
    Proof.
      rewrite wp_nil //.
    Qed.
    Lemma wp_nil_2 Q :
      (|==> Q) ⊢
      WP [] {{ Q }}.
    Proof.
      rewrite wp_nil //.
    Qed.

    Lemma wp_post Q :
      Q ⊢
      WP [] {{ Q }}.
    Proof.
      rewrite wp_nil. iSmash.
    Qed.

    #[local] Lemma wp_cons instr blk Q :
      WP instr :: blk {{ Q }}
      ⊣⊢
      ∀ σ,
      state_interp σ ==∗
        ∃ blk' σ',
        ⌜prim_step armiris_prog blk σ instr blk' σ'⌝ ∗
        ▷ |==> (
          state_interp σ' ∗
          WP blk' {{ Q }}
        ).
    Proof.
      rewrite wp_unfold wp_body_cons //.
    Qed.
    #[local] Lemma wp_cons_1 instr blk Q :
      WP instr :: blk {{ Q }} ⊢
        ∀ σ,
        state_interp σ ==∗
          ∃ blk' σ',
          ⌜prim_step armiris_prog blk σ instr blk' σ'⌝ ∗
          ▷ |==> (
            state_interp σ' ∗
            WP blk' {{ Q }}
          ).
    Proof.
      rewrite wp_cons //.
    Qed.
    #[local] Lemma wp_cons_2 instr blk Q :
      ( ∀ σ,
        state_interp σ ==∗
          ∃ blk' σ',
          ⌜prim_step armiris_prog blk σ instr blk' σ'⌝ ∗
          ▷ |==> (
            state_interp σ' ∗
            WP blk' {{ Q }}
          )
      ) ⊢
      WP instr :: blk {{ Q }}.
    Proof.
      rewrite wp_cons //.
    Qed.

    Lemma bupd_wp blk Q :
      (|==> WP blk {{ Q }}) ⊢
      WP blk {{ Q }}.
    Proof.
      rewrite wp_unfold. apply bupd_wp_body.
    Qed.

    Lemma wp_strong_mono blk Q1 Q2 :
      (Q1 ==∗ Q2) -∗
      WP blk {{ Q1 }} -∗
      WP blk {{ Q2 }}.
    Proof.
      iLöb as "HLöb" forall (blk).
      rewrite !wp_unfold.
      iApply wp_body_mono. clear blk. iIntros "!> %blk HQ Hwp !>".
      iApply ("HLöb" with "HQ Hwp").
    Qed.
    Lemma wp_mono blk Q1 Q2 :
      (Q1 -∗ Q2) -∗
      WP blk {{ Q1 }} -∗
      WP blk {{ Q2 }}.
    Proof.
      iIntros "HQ".
      iApply wp_strong_mono.
      iSmash.
    Qed.

    Lemma wp_wand blk Q1 Q2 :
      WP blk {{ Q1 }} -∗
      (Q1 -∗ Q2) -∗
      WP blk {{ Q2 }}.
    Proof.
      iIntros "Hwp HQ".
      iApply (wp_mono with "HQ Hwp").
    Qed.
    Lemma wp_wand_l blk Q1 Q2 :
      (Q1 -∗ Q2) ∗ WP blk {{ Q1 }} ⊢
      WP blk {{ Q2 }}.
    Proof.
      iIntros "(HQ & Hwp)".
      iApply (wp_wand with "Hwp HQ").
    Qed.
    Lemma wp_wand_r blk Q1 Q2 :
      WP blk {{ Q1 }} ∗ (Q1 -∗ Q2) ⊢
      WP blk {{ Q2 }}.
    Proof.
      iIntros "(Hwp & HQ)".
      iApply (wp_wand with "Hwp HQ").
    Qed.

    Lemma wp_bupd blk Q :
      WP blk {{ |==> Q }} ⊢
      WP blk {{ Q }}.
    Proof.
      iApply wp_strong_mono. iSmash.
    Qed.

    Lemma wp_frame_l R blk Q :
      R ∗ WP blk {{ Q }} ⊢
      WP blk {{ R ∗ Q }}.
    Proof.
      iIntros "(HR & Hwp)".
      iApply (wp_mono with "[HR] Hwp").
      iSmash.
    Qed.
    Lemma wp_frame_r R blk Q :
      WP blk {{ Q }} ∗ R ⊢
      WP blk {{ Q ∗ R }}.
    Proof.
      iIntros "(Hwp & HR)".
      iApply (wp_mono with "[HR] Hwp").
      iSmash.
    Qed.

    Lemma wp_app_1 blk1 blk2 Q :
      block_nobranching blk1 = true →
      WP blk1 {{ WP blk2 {{ Q }} }} ⊢
      WP blk1 ++ blk2 {{ Q }}.
    Proof.
      intros Hblk1.
      iInduction blk1 as [| instr blk1] "IH" forall (blk2); iIntros "Hwp".
      - iApply bupd_wp.
        iApply (wp_nil_1 with "Hwp").
      - iApply wp_cons_2. iIntros "%σ Hsi".
        iMod (wp_cons_1 with "Hwp Hsi") as "(%blk' & %σ' & %Hstep & Hwp)".
        apply andb_prop in Hblk1 as (Hinstr & Hblk1).
        apply (nobranching_prim_step_rebase (blk1 ++ blk2)) in Hstep as (-> & Hstep); last done.
        iModIntro. iExists (blk1 ++ blk2), σ'. iSplit; first iSmash. iModIntro.
        iMod "Hwp" as "($ & Hwp)".
        iSmash.
    Qed.
    Lemma wp_app_1' blk1 Q1 blk2 Q2 :
      block_nobranching blk1 = true →
      WP blk1 {{ Q1 }} -∗
      (Q1 -∗ WP blk2 {{ Q2 }}) -∗
      WP blk1 ++ blk2 {{ Q2 }}.
    Proof.
      iIntros "%Hblk1 Hwp1 Hwp2".
      iApply wp_app_1; first done.
      iApply (wp_wand with "Hwp1").
      iSmash.
    Qed.
    Lemma wp_app_2 blk1 blk2 Q :
      block_nobranching blk1 = true →
      WP blk1 ++ blk2 {{ Q }} ⊢
      WP blk1 {{ WP blk2 {{ Q }} }}.
    Proof.
      intros Hblk1.
      iInduction blk1 as [| instr blk1] "IH" forall (blk2); iIntros "Hwp".
      - iApply bupd_wp.
        iApply (wp_nil_2 with "Hwp").
      - iApply wp_cons_2. iIntros "%σ Hsi".
        iMod (wp_cons_1 with "Hwp Hsi") as "(%blk' & %σ' & %Hstep & Hwp)".
        apply andb_prop in Hblk1 as (Hinstr & Hblk1).
        apply (nobranching_prim_step_rebase blk1) in Hstep as (-> & Hstep); last done.
        iModIntro. iExists blk1, σ'. iSplit; first iSmash. iModIntro.
        iMod "Hwp" as "($ & Hwp)".
        iSmash.
    Qed.
    Lemma wp_app blk1 blk2 Q :
      block_nobranching blk1 = true →
      WP blk1 {{ WP blk2 {{ Q }} }} ⊣⊢
      WP blk1 ++ blk2 {{ Q }}.
    Proof.
      intros Hblk1. iSplit; [iApply wp_app_1 | iApply wp_app_2]; done.
    Qed.

    #[global] Instance frame_wp p R blk Q1 Q2 :
      Frame p R Q1 Q2 →
      Frame p R (WP blk {{ Q1 }}) (WP blk {{ Q2 }})
    | 2.
    Proof.
      rewrite /Frame => HR. rewrite wp_frame_l.
      iIntros "Hwp".
      iApply (wp_wand with "Hwp").
      rewrite HR. iSmash.
    Qed.

    #[global] Instance elim_model_bupd_wp p P blk Q :
      ElimModal True p false (|==> P) P (WP blk {{ Q }}) (WP blk {{ Q }}).
    Proof.
      rewrite /ElimModal bi.intuitionistically_if_elim bupd_frame_r bi.wand_elim_r bupd_wp //.
    Qed.

    Lemma wp_mov_1 r v blk Q :
      r ↦ᵣ v -∗
      ▷ (
        r ↦ᵣ v -∗
        WP blk {{ Q }}
      ) -∗
      WP MOV r r :: blk {{ Q }}.
    Proof.
      iIntros "Hr Hwp".
      iApply wp_cons. iIntros "%σ Hsi".
      iDestruct (state_interp_registers_lookup with "Hsi Hr") as %Hlookup.
      iMod (state_interp_registers_update v with "Hsi Hr") as "(Hsi & Hr)".
      iModIntro. iExists blk, (<[r := v]> σ). iSplit; first eauto using prim_step.
      iSmash.
    Qed.
    Lemma wp_mov_2 r1 v1 r2 v2 blk Q :
      r1 ↦ᵣ v1 -∗
      r2 ↦ᵣ v2 -∗
      ▷ (
        r1 ↦ᵣ v2 -∗
        r2 ↦ᵣ v2 -∗
        WP blk {{ Q }}
      ) -∗
      WP MOV r1 r2 :: blk {{ Q }}.
    Proof.
      iIntros "Hr1 Hr2 Hwp".
      iApply wp_cons. iIntros "%σ Hsi".
      iDestruct (state_interp_registers_lookup with "Hsi Hr2") as %Hlookup.
      iMod (state_interp_registers_update v2 with "Hsi Hr1") as "(Hsi & Hr1)".
      iModIntro. iExists blk, (<[r1 := v2]> σ). iSplit; first eauto using prim_step.
      iSmash.
    Qed.

    Lemma wp_add_1 r i j blk Q :
      r ↦ᵣ j -∗
      ▷ (
        r ↦ᵣ (j + i) -∗
        WP blk {{ Q }}
      ) -∗
      WP ADD r [[r, i]] :: blk {{ Q }}.
    Proof.
      iIntros "Hr Hwp".
      iApply wp_cons. iIntros "%σ Hsi".
      iDestruct (state_interp_registers_lookup with "Hsi Hr") as %Hlookup.
      iMod (state_interp_registers_update (j + i)%Z with "Hsi Hr") as "(Hsi & Hr)".
      iModIntro. iExists blk, (<[r := #(j + i)]> σ). iSplit; first eauto using prim_step.
      iSmash.
    Qed.
    Lemma wp_add_2 r1 v1 r2 i2 i blk Q :
      r1 ↦ᵣ v1 -∗
      r2 ↦ᵣ i2 -∗
      ▷ (
        r1 ↦ᵣ (i2 + i) -∗
        r2 ↦ᵣ i2 -∗
        WP blk {{ Q }}
      ) -∗
      WP ADD r1 [[r2, i]] :: blk {{ Q }}.
    Proof.
      iIntros "Hr1 Hr2 Hwp".
      iApply wp_cons. iIntros "%σ Hsi".
      iDestruct (state_interp_registers_lookup with "Hsi Hr2") as %Hlookup.
      iMod (state_interp_registers_update (i2 + i)%Z with "Hsi Hr1") as "(Hsi & Hr1)".
      iModIntro. iExists blk, (<[r1 := #(i2 + i)]> σ). iSplit; first eauto using prim_step.
      iSmash.
    Qed.

    Lemma wp_sub_1 r i j blk Q :
      r ↦ᵣ j -∗
      ▷ (
        r ↦ᵣ (j - i) -∗
        WP blk {{ Q }}
      ) -∗
      WP SUB r [[r, i]] :: blk {{ Q }}.
    Proof.
      iIntros "Hr Hwp".
      iApply wp_cons. iIntros "%σ Hsi".
      iDestruct (state_interp_registers_lookup with "Hsi Hr") as %Hlookup.
      iMod (state_interp_registers_update (j - i)%Z with "Hsi Hr") as "(Hsi & Hr)".
      iModIntro. iExists blk, (<[r := #(j - i)]> σ). iSplit; first eauto using prim_step.
      iSmash.
    Qed.
    Lemma wp_sub_2 r1 v1 r2 i2 i blk Q :
      r1 ↦ᵣ v1 -∗
      r2 ↦ᵣ i2 -∗
      ▷ (
        r1 ↦ᵣ (i2 - i)%Z -∗
        r2 ↦ᵣ i2 -∗
        WP blk {{ Q }}
      ) -∗
      WP SUB r1 [[r2, i]] :: blk {{ Q }}.
    Proof.
      iIntros "Hr1 Hr2 Hwp".
      iApply wp_cons. iIntros "%σ Hsi".
      iDestruct (state_interp_registers_lookup with "Hsi Hr2") as %Hlookup.
      iMod (state_interp_registers_update (i2 - i)%Z with "Hsi Hr1") as "(Hsi & Hr1)".
      iModIntro. iExists blk, (<[r1 := #(i2 - i)]> σ). iSplit; first eauto using prim_step.
      iSmash.
    Qed.

    Lemma wp_ldr r1 v' r2 l i v blk Q :
      r1 ↦ᵣ v' -∗
      r2 ↦ᵣ l -∗
      (l + i) ↦ₕ v -∗
      ▷ (
        r1 ↦ᵣ v -∗
        r2 ↦ᵣ l -∗
        (l + i) ↦ₕ v -∗
        WP blk {{ Q }}
      ) -∗
      WP LDR r1 [[r2, i]] :: blk {{ Q }}.
    Proof.
      iIntros "Hr1 Hr2 Hl Hwp".
      iApply wp_cons. iIntros "%σ Hsi".
      iDestruct (state_interp_registers_lookup with "Hsi Hr2") as %Hlookup_r2.
      iDestruct (state_interp_heap_lookup with "Hsi Hl") as %Hlookup_l.
      iMod (state_interp_registers_update v with "Hsi Hr1") as "(Hsi & Hr1)".
      iModIntro. iExists blk, (<[r1 := v]> σ). iSplit; first eauto using prim_step.
      iSmash.
    Qed.

    Lemma wp_str r1 v r2 l i v' blk Q :
      r1 ↦ᵣ v -∗
      r2 ↦ᵣ l -∗
      (l + i) ↦ₕ v' -∗
      ▷ (
        r1 ↦ᵣ v -∗
        r2 ↦ᵣ l -∗
        (l + i) ↦ₕ v -∗
        WP blk {{ Q }}
      ) -∗
      WP STR r1 [[r2, i]] :: blk {{ Q }}.
    Proof.
      iIntros "Hr1 Hr2 Hl Hwp".
      iApply wp_cons. iIntros "%σ Hsi".
      iDestruct (state_interp_registers_lookup with "Hsi Hr1") as %Hlookup_r1.
      iDestruct (state_interp_registers_lookup with "Hsi Hr2") as %Hlookup_r2.
      iDestruct (state_interp_heap_lookup with "Hsi Hl") as %Hlookup_l.
      iMod (state_interp_heap_update v with "Hsi Hl") as "(Hsi & Hl)".
      iModIntro. iExists blk, (<[(l + i)%Z := v]> σ). iSplit; first eauto using prim_step.
      iSmash.
    Qed.

    Lemma wp_cmp_1 r w fl blk Q :
      r ↦ᵣ w -∗
      flags↦ fl -∗
      ▷ (
        r ↦ᵣ w -∗
        flags↦ (w, w) -∗
        WP blk {{ Q }}
      ) -∗
      WP CMP r r :: blk {{ Q }}.
    Proof.
      iIntros "Hr Hfl Hwp".
      iApply wp_cons. iIntros "%σ Hsi".
      iDestruct (state_interp_registers_lookup with "Hsi Hr") as %Hlookup.
      iMod (state_interp_flags_update (w, w) with "Hsi Hfl") as "(Hsi & Hfl)".
      iModIntro. iExists blk, (<[(w, w)]> σ). iSplit; first eauto using prim_step.
      iSmash.
    Qed.
    Lemma wp_cmp_2 r1 w1 r2 w2 fl blk Q :
      r1 ↦ᵣ w1 -∗
      r2 ↦ᵣ w2 -∗
      flags↦ fl -∗
      ▷ (
        r1 ↦ᵣ w1 -∗
        r2 ↦ᵣ w2 -∗
        flags↦ (w1, w2) -∗
        WP blk {{ Q }}
      ) -∗
      WP CMP r1 r2 :: blk {{ Q }}.
    Proof.
      iIntros "Hr1 Hr2 Hfl Hwp".
      iApply wp_cons. iIntros "%σ Hsi".
      iDestruct (state_interp_registers_lookup with "Hsi Hr1") as %Hlookup_r1.
      iDestruct (state_interp_registers_lookup with "Hsi Hr2") as %Hlookup_r2.
      iMod (state_interp_flags_update (w1, w2) with "Hsi Hfl") as "(Hsi & Hfl)".
      iModIntro. iExists blk, (<[(w1, w2)]> σ). iSplit; first eauto using prim_step.
      iSmash.
    Qed.

    Lemma wp_b lbl blk blk' Q :
      armiris_prog !! lbl = Some blk' →
      WP blk' {{ Q }} -∗
      WP B lbl :: blk {{ Q }}.
    Proof.
      iIntros "%Hlookup Hwp".
      iApply wp_cons. iIntros "%σ Hsi".
      iModIntro. iExists blk', σ. iSplit; first eauto using prim_step.
      iSmash.
    Qed.

    Lemma wp_bcond cond lbl blk blk' fl Q :
      armiris_prog !! lbl = Some blk' →
      flags↦ fl -∗
      ▷ (
        flags↦ fl -∗
        WP if condition_eval cond fl then blk' else blk {{ Q }}
      ) -∗
      WP BCOND cond lbl :: blk {{ Q }}.
    Proof.
      iIntros "%Hlookup_lbl Hfl Hwp".
      iApply wp_cons. iIntros "%σ Hsi".
      iDestruct (state_interp_flags_lookup with "Hsi Hfl") as %Hlookup_fl.
      iModIntro. iExists _, σ. iSplit; first eauto using prim_step.
      iSmash.
    Qed.

    Lemma wp_br r blk blk' Q :
      r ↦ᵣ blk' -∗
      ▷ (
        r ↦ᵣ blk' -∗
        WP blk' {{ Q }}
      ) -∗
      WP BR r :: blk {{ Q }}.
    Proof.
      iIntros "Hr Hwp".
      iApply wp_cons. iIntros "%σ Hsi".
      iDestruct (state_interp_registers_lookup with "Hsi Hr") as %Hlookup.
      iModIntro. iExists blk', σ. iSplit; first eauto using prim_step.
      iSmash.
    Qed.

    Lemma wp_bl lbl blk blk' v Q :
      armiris_prog !! lbl = Some blk' →
      X30 ↦ᵣ v -∗
      ▷ (
        X30 ↦ᵣ blk -∗
        WP blk' {{ Q }}
      ) -∗
      WP BL lbl :: blk {{ Q }}.
    Proof.
      iIntros "%Hlookup Hx30 Hwp".
      iApply wp_cons. iIntros "%σ Hsi".
      iMod (state_interp_registers_update blk with "Hsi Hx30") as "(Hsi & Hx30)".
      iModIntro. iExists blk', (<[X30 := ValBlock blk]> σ). iSplit; first eauto using prim_step.
      iSmash.
    Qed.

    Lemma wp_blr_1 blk blk' v Q :
      X30 ↦ᵣ blk' -∗
      ▷ (
        X30 ↦ᵣ blk -∗
        WP blk' {{ Q }}
      ) -∗
      WP BLR X30 :: blk {{ Q }}.
    Proof.
      iIntros "Hx30 Hwp".
      iApply wp_cons. iIntros "%σ Hsi".
      iDestruct (state_interp_registers_lookup with "Hsi Hx30") as %Hlookup.
      iMod (state_interp_registers_update blk with "Hsi Hx30") as "(Hsi & Hx30)".
      iModIntro. iExists blk', (<[X30 := ValBlock blk]> σ). iSplit; first eauto using prim_step.
      iSmash.
    Qed.
    Lemma wp_blr_2 r blk blk' v Q :
      r ↦ᵣ blk' -∗
      X30 ↦ᵣ v -∗
      ▷ (
        r ↦ᵣ blk' -∗
        X30 ↦ᵣ blk -∗
        WP blk' {{ Q }}
      ) -∗
      WP BLR r :: blk {{ Q }}.
    Proof.
      iIntros "Hr Hx30 Hwp".
      iApply wp_cons. iIntros "%σ Hsi".
      iDestruct (state_interp_registers_lookup with "Hsi Hr") as %Hlookup.
      iMod (state_interp_registers_update blk with "Hsi Hx30") as "(Hsi & Hx30)".
      iModIntro. iExists blk', (<[X30 := ValBlock blk]> σ). iSplit; first eauto using prim_step.
      iSmash.
    Qed.
  End wp.
End rules.
