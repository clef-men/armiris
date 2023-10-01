From Coq.ssr Require Export
  ssreflect.

From stdpp Require Export
  prelude.

#[export] Set Default Proof Using "Type*".
#[export] Set Suggest Proof Using.

Open Scope general_if_scope.

Class Update A M :=
  update : A → M → M.
#[global] Hint Mode Update - ! : typeclass_instances.
#[global] Arguments update _ _ _ _ !_ / : simpl nomatch, assert.
Notation "<[ a ]>" := (
  update a
)(at level 5,
  right associativity,
  format "<[ a ]>"
) : stdpp_scope.
