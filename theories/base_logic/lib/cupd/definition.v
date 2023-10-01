From iris.bi Require Export
  bi.

From armiris Require Import
  prelude.

Class CUpd PROP :=
  cupd : PROP → PROP.
#[global] Hint Mode CUpd ! : typeclass_instances.
#[global] Arguments cupd {_}%type_scope {_} _%bi_scope.
#[global] Typeclasses Opaque cupd.

Notation "|++> P" := (
  cupd P
)(at level 99,
  P at level 200,
  format "'[  ' |++>  '/' P ']'"
) : bi_scope.
Notation "P ++∗ Q" :=
  (P -∗ |++> Q)%I
( at level 99,
  Q at level 200,
  format "'[' P  ++∗  '/' Q ']'"
) : bi_scope.
Notation "P ++∗ Q" := (
  P -∗ |++> Q
) : stdpp_scope.

Record BiCUpdMixin (PROP : bi) `{!BUpd PROP} `{!CUpd PROP} := {
  bi_cupd_mixin_cupd_ne :
    NonExpansive (cupd (PROP := PROP)) ;
  bi_cupd_mixin_cupd_intro P :
    P ⊢ |++> P ;
  bi_cupd_mixin_cupd_mono P Q :
    (P ⊢ Q) →
    (|++> P) ⊢ |++> Q ;
  bi_cupd_mixin_cupd_trans P :
    (|++> |++> P) ⊢ |++> P ;
  bi_cupd_mixin_cupd_frame_r P R :
    (|++> P) ∗ R ⊢ |++> P ∗ R ;
  bi_cupd_mixin_bupd_cupd P :
    (|==> P) ⊢ |++> P
}.

Class BiCUpd PROP `{!BiBUpd PROP} := {
  #[global] bi_cupd_cupd :: CUpd PROP ;
  bi_cupd_mixin : BiCUpdMixin PROP ;
}.
#[global] Hint Mode BiCUpd ! - : typeclass_instances.
#[global] Arguments bi_cupd_cupd : simpl never.
#[global] Arguments Build_BiCUpd {_ _ _} _ : assert.
