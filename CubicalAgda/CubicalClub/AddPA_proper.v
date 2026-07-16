(* Hivatalos Setoid egyenlőség: *)
Add Parametric Relation : AddPA AddPAEquiv
  reflexivity proved by Cong_refl
  symmetry proved by Cong_sym
  transitivity proved by Cong_trans
  as AddPA_setoid.

(* Operátorok regisztrálása: *)
Add Parametric Morphism : Succ with
  signature AddPAEquiv ==> AddPAEquiv as Succ_morphism.
Proof. exact Cong_Succ. Qed.

Add Parametric Morphism : Add with
  signature AddPAEquiv ==> AddPAEquiv ==> AddPAEquiv as Add_morphism.
Proof. exact Cong_Add. Qed. 
