From armiris Require Import
  prelude.
From armiris.base_logic Require Export
  lib.cupd.definition.

Section bi_cupd.
  Context `{BiCUpd PROP}.
  Implicit Types P Q : PROP.

  Program Definition cupd_bi_bupd : BiBUpd PROP :=
    Build_BiBUpd PROP cupd _.
  Next Obligation.
    split; rewrite /bupd; apply bi_cupd_mixin.
  Qed.

  #[local] Tactic Notation "solve" "with" constr(H) :=
    apply (H _ cupd_bi_bupd).

  #[global] Instance cupd_ne :
    NonExpansive (cupd (PROP := PROP)).
  Proof.
    solve with @bupd_ne.
  Qed.
  #[global] Instance cupd_proper :
    Proper ((≡) ==> (≡)) (cupd (PROP := PROP)).
  Proof.
    solve with @bupd_proper.
  Qed.

  Lemma cupd_intro P :
    P  ⊢ |++> P.
  Proof.
    solve with @bupd_intro.
  Qed.

  Lemma cupd_mono P Q :
    (P ⊢ Q) →
    (|++> P) ⊢ |++> Q.
  Proof.
    solve with @bupd_mono.
  Qed.
  #[global] Instance cupd_mono' :
    Proper ((⊢) ==> (⊢)) (cupd (PROP := PROP)).
  Proof.
    solve with @bupd_mono'.
  Qed.
  #[global] Instance cupd_flip_mono' :
    Proper (flip (⊢) ==> flip (⊢)) (cupd (PROP := PROP)).
  Proof.
    solve with @bupd_flip_mono'.
  Qed.

  Lemma cupd_trans P :
    (|++> |++> P) ⊢ |++> P.
  Proof.
    solve with @bupd_trans.
  Qed.
  Lemma cupd_idemp P :
    (|++> |++> P) ⊣⊢ |++> P.
  Proof.
    solve with @bupd_idemp.
  Qed.

  Lemma cupd_or P Q :
    (|++> P) ∨ (|++> Q) ⊢ |++> P ∨ Q.
  Proof.
    solve with @bupd_or.
  Qed.
  #[global] Instance cupd_or_homomorphism :
    MonoidHomomorphism bi_or bi_or (flip (⊢)) (cupd (PROP := PROP)).
  Proof.
    solve with @bupd_or_homomorphism.
  Qed.
  Lemma cupd_and P Q :
    (|++> P ∧ Q) ⊢ (|++> P) ∧ (|++> Q).
  Proof.
    solve with @bupd_and.
  Qed.
  Lemma cupd_exist X (Φ : X → PROP) :
    (∃ x, |++> Φ x) ⊢ |++> ∃ x, Φ x.
  Proof.
    solve with @bupd_exist.
  Qed.
  Lemma cupd_forall X (Φ : X → PROP) :
    (|++> ∀ x, Φ x)  ⊢∀ x, |++> Φ x.
  Proof.
    solve with @bupd_forall.
  Qed.

  Lemma cupd_sep P Q :
    (|++> P) ∗ (|++> Q) ⊢ |++> P ∗ Q.
  Proof.
    solve with @bupd_sep.
  Qed.
  #[global] Instance cupd_sep_homomorphism :
    MonoidHomomorphism bi_sep bi_sep (flip (⊢)) (cupd (PROP := PROP)).
  Proof.
    solve with @bupd_sep_homomorphism.
  Qed.
  Lemma cupd_frame_l R Q :
    R ∗ (|++> Q) ⊢ |++> R ∗ Q.
  Proof.
    solve with @bupd_frame_l.
  Qed.
  Lemma cupd_frame_r P R :
    (|++> P) ∗ R ⊢ |++> P ∗ R.
  Proof.
    solve with @bupd_frame_r.
  Qed.
  Lemma cupd_wand_l P Q :
    (P -∗ Q) ∗ (|++> P) ⊢ |++> Q.
  Proof.
    solve with @bupd_wand_l.
  Qed.
  Lemma cupd_wand_r P Q :
    (|++> P) ∗ (P -∗ Q) ⊢ |++> Q.
  Proof.
    solve with @bupd_wand_r.
  Qed.

  Lemma big_sepL_cupd {X} (Φ : nat → X → PROP) l :
    ([∗ list] k ↦ x ∈ l, |++> Φ k x) ⊢ |++> [∗ list] k↦x ∈ l, Φ k x.
  Proof.
    solve with @big_sepL_bupd.
  Qed.
  Lemma big_sepM_cupd {X} `{Countable K} (Φ : K → X → PROP) l :
    ([∗ map] k ↦ x ∈ l, |++> Φ k x) ⊢ |++> [∗ map] k ↦ x ∈ l, Φ k x.
  Proof.
    solve with @big_sepM_bupd.
  Qed.
  Lemma big_sepS_cupd `{Countable X} (Φ : X → PROP) l :
    ([∗ set] x ∈ l, |++> Φ x) ⊢ |++> [∗ set] x ∈ l, Φ x.
  Proof.
    solve with @big_sepS_bupd.
  Qed.
  Lemma big_sepMS_cupd `{Countable X} (Φ : X → PROP) l :
    ([∗ mset] x ∈ l, |++> Φ x) ⊢ |++> [∗ mset] x ∈ l, Φ x.
  Proof.
    solve with @big_sepMS_bupd.
  Qed.

  Lemma except_0_cupd P :
    ◇ (|++> P) ⊢ |++> ◇ P.
  Proof.
    solve with @except_0_bupd.
  Qed.

  #[global] Instance cupd_absorbing P :
    Absorbing P →
    Absorbing (|++> P).
  Proof.
    rewrite /Absorbing /bi_absorbingly cupd_frame_l => -> //.
  Qed.

  Lemma bupd_cupd P :
    (|==> P) ⊢ |++> P.
  Proof.
    apply bi_cupd_mixin.
  Qed.
End bi_cupd.
