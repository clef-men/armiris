From iris.base_logic Require Import
  lib.gen_heap.

From armiris Require Import
  prelude
  proofmode.
From armiris.base_logic Require Import
  lib.auth_excl.
From armiris.language Require Export
  semantics.

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

Canonical flags_O :=
  leibnizO flags.

Class ArmirisGpreS Σ := {
  #[local] armiris_GpreS_registers_GpreS :: gen_heapGpreS register value Σ ;
  #[local] armiris_GpreS_heap_GpreS :: gen_heapGpreS Z value Σ ;
  #[local] armiris_GpreS_flags_G :: AuthExclG Σ flags_O ;
}.

Class ArmirisGS Σ := {
  #[local] armiris_GS_registers_GS :: gen_heapGS register value Σ ;
  #[local] armiris_GS_heap_GS :: gen_heapGS Z value Σ ;
  #[local] armiris_GS_flags_G :: AuthExclG Σ flags_O ;
  armiris_GS_flags_name : gname ;
}.

Definition armiris_Σ := #[
  gen_heapΣ register value ;
  gen_heapΣ Z value ;
  auth_excl_Σ flags_O
].
#[global] Instance subG_armiris_Σ Σ :
  subG armiris_Σ Σ →
  ArmirisGpreS Σ.
Proof.
  solve_inG.
Qed.

Section definitions.
  Context `{armiris_GS : !ArmirisGS Σ}.

  Definition registers_interp rs :=
    gen_heap_interp (hG := armiris_GS_registers_GS) rs.
  Definition registers_mapsto r v :=
    mapsto (hG := armiris_GS_registers_GS) r (DfracOwn 1) v.
  #[global] Arguments registers_mapsto _ _%Z : assert.

  Definition heap_interp heap :=
    gen_heap_interp (hG := armiris_GS_heap_GS) heap.
  Definition heap_mapsto l v :=
    mapsto (hG := armiris_GS_heap_GS) l (DfracOwn 1) v.
  #[global] Arguments heap_mapsto _%Z _%Z : assert.

  Definition flags_interp fl :=
    auth_excl_frag armiris_GS_flags_name fl.
  Definition flags_mapsto fl :=
    auth_excl_auth armiris_GS_flags_name (DfracOwn 1) fl.

  Definition state_interp σ : iProp Σ :=
    (* registers_interp (set_to_map (λ r, (r, σ.(state_registers) r)) (list_to_set (enum register))) ∗ *)
    registers_interp (foldl (λ rs r, <[r := σ.(state_registers) r]> rs) ∅ (enum register)) ∗
    heap_interp σ.(state_heap) ∗
    flags_interp σ.(state_flags).
End definitions.

Notation "r ↦ᵣ v" := (
  registers_mapsto r v
)(at level 20,
  format "r  ↦ᵣ  v"
) : bi_scope.
Notation "l ↦ₕ v" := (
  heap_mapsto l v
)(at level 20,
  format "l  ↦ₕ  v"
) : bi_scope.
Notation "'flags↦' fl" := (
  flags_mapsto fl
)(at level 20,
  format "flags↦  fl"
) : bi_scope.

Section rules.
  Context `{armiris_GS : !ArmirisGS Σ}.

  #[global] Instance registers_mapsto_timeless r v :
    Timeless (r ↦ᵣ v).
  Proof.
    apply _.
  Qed.
  #[global] Instance heap_mapsto_timeless l v :
    Timeless (l ↦ₕ v).
  Proof.
    apply _.
  Qed.
  #[global] Instance flags_mapsto_timeless fl :
    Timeless (flags↦ fl).
  Proof.
    apply _.
  Qed.

  Lemma state_interp_registers_lookup σ r v :
    state_interp σ -∗
    r ↦ᵣ v -∗
    ⌜σ !!! r = v⌝.
  Proof.
    iIntros "(Hregs & Hheap & Hfl) Hr".
    iDestruct (gen_heap_valid with "Hregs Hr") as %Hlookup.
  Admitted.

  Lemma state_interp_heap_lookup σ l v :
    state_interp σ -∗
    l ↦ₕ v -∗
    ⌜σ !! l = Some v⌝.
  Proof.
    iIntros "(Hregs & Hheap & Hfl) Hl".
    iApply (gen_heap_valid with "Hheap Hl").
  Qed.

  Lemma state_interp_flags_lookup σ fl :
    state_interp σ -∗
    flags↦ fl -∗
    ⌜σ.(state_flags) = fl⌝.
  Proof.
    iIntros "(Hregs & Hheap & Hfl1) Hfl2".
    iDestruct (auth_excl_agree_L with "Hfl2 Hfl1") as %->. done.
  Qed.

  Lemma state_interp_registers_update v σ r v' :
    state_interp σ -∗
    r ↦ᵣ v' ==∗
      state_interp (<[r := v]> σ) ∗
      r ↦ᵣ v.
  Proof.
  Admitted.

  Lemma state_interp_heap_update v σ l v' :
    state_interp σ -∗
    l ↦ₕ v' ==∗
      state_interp (<[l := v]> σ) ∗
      l ↦ₕ v.
  Proof.
    iIntros "(Hregs & Hheap & Hfl) Hl".
    iMod (gen_heap_update with "Hheap Hl") as "(Hheap & Hl)".
    iFrame. iSmash.
  Qed.

  Lemma state_interp_flags_update fl σ fl' :
    state_interp σ -∗
    flags↦ fl' ==∗
      state_interp (<[fl]> σ) ∗
      flags↦fl.
  Proof.
    iIntros "(Hregs & Hheap & Hfl1) Hfl2".
    iMod (auth_excl_update' with "Hfl2 Hfl1").
    iFrame. iSmash.
  Qed.
End rules.

Lemma armiris_init `{armiris_GpreS : !ArmirisGpreS Σ} :
  ⊢ |==>
    ∃ _ : ArmirisGS Σ,
    state_interp ∅ ∗
    ([∗list] r ∈ enum register, r ↦ᵣ inhabitant) ∗
    flags↦ inhabitant.
Proof.
Admitted.

#[global] Opaque registers_interp.
#[global] Opaque registers_mapsto.
#[global] Opaque heap_interp.
#[global] Opaque heap_mapsto.
#[global] Opaque flags_interp.
#[global] Opaque flags_mapsto.
#[global] Opaque state_interp.
