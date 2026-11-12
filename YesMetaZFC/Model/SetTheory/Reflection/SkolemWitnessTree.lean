import YesMetaZFC.Model.SetTheory.Internal.ClosureLetters

/-! # 实际司寇伦见证树及其可数初等分支

规则、有限输入位置列及任务单射均由原模型构造。每条无限枝给出真实
可数内部初等子结构；反向由可数闭集的枚举构造见证位置表和合法枝。
给定可数种子时，原司寇伦闭包工厂实际生产一条包含该种子的枝。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel Descriptive
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

structure Sh_tree_d (ω c X R u C L T E K Q D J Y d h F A : M.Domain) : Prop where
  model : Smdl_d I c X R
  skolem : Ssk_d I ω c X u C L T E K
  positions : Fseq_space_d I ω ω Q
  tasks : M.IsCartesianProduct I D T Q
  index : M.IsSetInjectionFromTo I J D ω
  letters : M.IsCartesianProduct I Y X ω
  left : M.IsSetFunctionFromTo I d Y X
  right : M.IsSetFunctionFromTo I h Y ω
  coordinates : ∀ v x l, M.mem v Y → KPair_d M v x l → Rd_entry_d v x d ∧ Rd_entry_d v l h
  sequences : Fseq_space_d I ω Y F
  tree : Tree_d F A
  nodes : ∀ p, M.mem p A ↔ Cl_word_d hZF ω X T J K Y d h p

theorem Sh_tree_d.elementary_l {ω c X R u C L T E K Q D J Y d h F A f : M.Domain}
    (tree : Sh_tree_d hZF ω c X R u C L T E K Q D J Y d h F A) (hw : M.IsOmega ω)
    (ff : M.IsSetFunctionFromTo I f ω Y) (branch : Branch_d F A f) :
    ∃ N c' R' e, Ssub_d I c c' X R N R' ∧ Selem_d I ω c c' ∧ M.CardinalLessOrEqual I N ω ∧
      Fn0_d ω N e ∧ M.IsRangeOf I N e ∧ Fseq_recode_d I d f e := by
  obtain ⟨e,_,N,fe,_,de,_,range,sub,count,closed⟩ := cl_tree_closed_l hZF hw tree.positions tree.tasks
    (fn0_of_function_l (ZF.modelsKP hZF) tree.index.1) tree.skolem.graph.1 tree.left tree.right tree.sequences tree.nodes ff branch
  obtain ⟨c',R',model,elem⟩ := selem_of_skolem_l I hZF hw tree.model tree.skolem.codes sub
    (tree.skolem.point_mem_l I hZF hw tree.model closed) (tree.skolem.closed_l I sub closed)
  exact ⟨N,c',R',e,model,elem,count,fe.retarget_l (fun i x ix => (range x).mpr ⟨i,ix⟩),range,de⟩

theorem Sh_tree_d.of_closed_l {ω c X R u C L T E K Q D J Y d h F A N e : M.Domain}
    (tree : Sh_tree_d hZF ω c X R u C L T E K Q D J Y d h F A) (hw : M.IsOmega ω)
    (sub : M.MemberSubset N X) (closed : Fc_closed_d I ω T K N)
    (fe : Fn0_d ω N e) (onto : M.IsSetSurjectiveOnto I e ω N) :
    ∃ f, M.IsSetFunctionFromTo I f ω Y ∧ Branch_d F A f ∧ Fseq_recode_d I d f e := by
  obtain ⟨v,fv,run⟩ := cl_witness_l hZF hw tree.positions tree.tasks tree.index tree.skolem.params
    tree.skolem.domain tree.skolem.graph sub closed fe onto
  obtain ⟨f,ff,de,hv⟩ := cl_pair_word_l hZF tree.letters tree.left tree.right tree.coordinates (fe.mono_target_l sub) fv
  exact ⟨f,ff,cl_tree_branch_l hZF tree.left tree.right tree.sequences tree.nodes ff de hv run,de⟩

omit hZF in
/-- 由真实可数种子构造整套树数据及包含种子的实际枝，不预交闭包或初等性。 -/
theorem sh_tree_exists_l (hZFC : M.Models ZFC) {ω c X R B : M.Domain} (hw : M.IsOmega ω)
    (model : Smdl_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) c X R)
    (sub : M.MemberSubset B X) (count : M.CardinalLessOrEqual (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) B ω) :
    let hZF := ZFC.models_zf_l hZFC
    let I₀ := kp_pair_l (ZF.modelsKP hZF)
    ∃ u C L T E K Q D J Y d h F A, Sh_tree_d hZF ω c X R u C L T E K Q D J Y d h F A ∧
      ∃ N e f, M.MemberSubset B N ∧ Fn0_d ω N e ∧ M.IsSetSurjectiveOnto I₀ e ω N ∧
        M.IsSetFunctionFromTo I₀ f ω Y ∧ Branch_d F A f ∧ Fseq_recode_d I₀ d f e := by
  dsimp only
  have hZF := ZFC.models_zf_l hZFC
  let I₀ := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨id,identity⟩ := ZF.exists_identityBijection hZF I₀ ω
  obtain ⟨u,C,L,T,E,K,N,skolem,hull,countN,point,_⟩ := ssk_hull_bound_l I₀ hZFC hw
    ⟨ZF.omega_cardinal_l I₀ hZF hw,id,identity.1⟩ model sub count
  have countT := ZF.countable_product_l I₀ hZF hw (scode_countable_l I₀ hZF hw skolem.codes) ⟨id,identity.1⟩ skolem.labels
  obtain ⟨Q,positions,countQ⟩ := ZF.fseq_countable_space_l I₀ hZF hw (X := ω) ⟨id,identity.1⟩
  obtain ⟨D,tasks⟩ := ZF.exists_cartesianProduct hZF I₀ T Q
  obtain ⟨J,index⟩ := ZF.countable_product_l I₀ hZF hw countT countQ tasks
  obtain ⟨Y,letters⟩ := ZF.exists_cartesianProduct hZF I₀ X ω
  obtain ⟨d,h,left,right,coordinates⟩ := cl_pair_maps_l hZF letters
  obtain ⟨F,sequences⟩ := ZF.fseq_space_exists_l I₀ hZF hw Y
  obtain ⟨A,tree,nodes⟩ := cl_tree_exists_l hZF left right sequences (T := T) (J := J) (K := K)
  have data : Sh_tree_d hZF ω c X R u C L T E K Q D J Y d h F A :=
    ⟨model,skolem,positions,tasks,index,letters,left,right,coordinates,sequences,tree,nodes⟩
  obtain ⟨ι,inj⟩ := countN
  obtain ⟨e,fe,retract⟩ := ZF.injection_retract_l I₀ hZF inj (fun _ h => h) point
  have onto : M.IsSetSurjectiveOnto I₀ e ω N := fun x hx => by
    obtain ⟨i,hi,xi⟩ := inj.1.2.2 x hx
    exact ⟨i,hi,retract x i xi⟩
  obtain ⟨f,ff,branch,de⟩ := data.of_closed_l hZF hw hull.2.1 hull.2.2.1 (fn0_of_function_l (ZF.modelsKP hZF) fe) onto
  exact ⟨u,C,L,T,E,K,Q,D,J,Y,d,h,F,A,data,N,e,f,hull.1,fn0_of_function_l (ZF.modelsKP hZF) fe,onto,ff,branch,de⟩

end YesMetaZFC.SetTheory.Internal
