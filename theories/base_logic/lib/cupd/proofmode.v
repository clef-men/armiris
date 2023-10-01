From iris.proofmode Require Import
  class_instances_updates.

From diaframe Require Import
  util_instances.

From armiris Require Import
  prelude.
From armiris Require Export
  proofmode.
From armiris.base_logic Require Export
  lib.cupd.rules.

Section bi_cupd.
  Context `{BiCUpd PROP}.
  Implicit Types P Q R : PROP.

  #[local] Tactic Notation "solve" "with" constr(H) :=
    apply (H _ cupd_bi_bupd).

  #[global] Instance from_assumption_cupd p P Q :
    FromAssumption p P Q →
    KnownRFromAssumption p P (|++> Q).
  Proof.
    solve with @from_assumption_bupd.
  Qed.

  #[global] Instance from_pure_cupd a P ϕ :
    FromPure a P ϕ →
    FromPure a (|++> P) ϕ.
  Proof.
    solve with @from_pure_bupd.
  Qed.

  #[global] Instance into_wand_cupd p q R P Q :
    IntoWand false false R P Q →
    IntoWand p q (|++> R) (|++> P) (|++> Q).
  Proof.
    solve with @into_wand_bupd.
  Qed.

  #[global] Instance into_wand_cupd_persistent p q R P Q :
    IntoWand false q R P Q →
    IntoWand p q (|++> R) P (|++> Q).
  Proof.
    solve with @into_wand_bupd_persistent.
  Qed.

  #[global] Instance into_wand_cupd_args p q R P Q :
    IntoWand p false R P Q →
    IntoWand' p q R (|++> P) (|++> Q).
  Proof.
    solve with @into_wand_bupd_args.
  Qed.

  #[global] Instance from_sep_cupd P Q1 Q2 :
    FromSep P Q1 Q2 →
    FromSep (|++> P) (|++> Q1) (|++> Q2).
  Proof.
    solve with @from_sep_bupd.
  Qed.

  #[global] Instance from_or_cupd P Q1 Q2 :
    FromOr P Q1 Q2 →
    FromOr (|++> P) (|++> Q1) (|++> Q2).
  Proof.
    solve with @from_or_bupd.
  Qed.

  #[global] Instance into_and_cupd P Q1 Q2 :
    IntoAnd false P Q1 Q2 →
    IntoAnd false (|++> P) (|++> Q1) (|++> Q2).
  Proof.
    solve with @into_and_bupd.
  Qed.

  #[global] Instance from_exist_cupd {X} P (Φ : X → PROP) :
    FromExist P Φ →
    FromExist (|++> P) (λ x, |++> Φ x)%I.
  Proof.
    solve with @from_exist_bupd.
  Qed.

  #[global] Instance into_forall_cupd {X} P (Φ : X → PROP) :
    IntoForall P Φ →
    IntoForall (|++> P) (λ x, |++> Φ x)%I.
  Proof.
    solve with @into_forall_bupd.
  Qed.

  #[global] Instance is_except_0_cupd P :
    IsExcept0 P →
    IsExcept0 (|++> P).
  Proof.
    solve with @is_except_0_bupd.
  Qed.

  #[global] Instance from_modal_cupd P :
    FromModal True modality_id (|++> P) (|++> P) P.
  Proof.
    solve with @from_modal_bupd.
  Qed.

  #[global] Instance elim_modal_cupd p P Q :
    ElimModal True p false (|++> P) P (|++> Q) (|++> Q).
  Proof.
    solve with @elim_modal_bupd.
  Qed.

  #[global] Instance elim_modal_bupd_cupd p P Q :
    ElimModal True p false (|==> P) P (|++> Q) (|++> Q) | 10.
  Proof.
    rewrite
      /ElimModal bi.intuitionistically_if_elim
      bupd_cupd cupd_frame_r bi.wand_elim_r.
    by setoid_rewrite cupd_trans.
  Qed.

  #[global] Instance add_modal_cupd P Q :
    AddModal (|++> P) P (|++> Q).
  Proof.
    solve with @add_modal_bupd.
  Qed.

  #[global] Instance frame_cupd p R P Q :
    Frame p R P Q →
    Frame p R (|++> P) (|++> Q)
  | 2.
  Proof.
    rewrite /Frame => <-. rewrite cupd_frame_l //.
  Qed.

  #[global] Instance cupd_strong_modality :
    ModalityStrongMono (PROP := PROP) cupd.
  Proof.
    split.
    - move=> P Q -> //.
    - move=> P Q. rewrite cupd_frame_r //.
  Qed.

  #[global] Instance cupd_compat3 :
    ModalityCompat3 (PROP := PROP) cupd cupd cupd
  | 20.
  Proof.
    rewrite /ModalityCompat3 => P. apply cupd_trans.
  Qed.

  #[global] Instance cupd_bupd_compat3 :
    ModalityCompat3 (PROP := PROP) cupd cupd bupd
  | 100.
  Proof.
    iIntros "%P >>H //".
  Qed.

  #[global] Instance cupd_bupd_compat3' :
    ModalityCompat3 (PROP := PROP) cupd bupd cupd
  | 120.
  Proof.
    iIntros "%P >>H //".
  Qed.

  #[global] Instance cupd_weaker_than_id :
    ModWeaker (PROP := PROP) id cupd
  | 0.
  Proof.
    move=> P. apply cupd_intro.
  Qed.

  #[global] Instance split_mod_cupd :
    SplitLeftModality3 (PROP := PROP) cupd cupd cupd
  | 20.
  Proof.
    split; apply _.
  Qed.

  #[global] Instance collect_modal_cupd P :
    Collect1Modal (|++> P) cupd P
  | 50.
  Proof.
    apply: collect_one_modal_modal.
  Qed.

  #[global] Instance modal_compose_cupd_cupd :
    CombinedModalitySafe (cupd (PROP := PROP)) cupd cupd.
  Proof.
    move=> P. iSmash.
  Qed.

  #[global] Instance combined_bupd_cupd :
    CombinedModalitySafe (bupd (PROP := PROP)) cupd cupd
  | 45.
  Proof.
    move => P. iSmash.
  Qed.

  #[global] Instance combined_cupd_bupd :
    CombinedModalitySafe (cupd (PROP := PROP)) bupd cupd
  | 45.
  Proof.
    move => P. eapply (anti_symm _).
    - iIntros ">$ //".
    - iIntros ">>$ //".
  Qed.
End bi_cupd.
