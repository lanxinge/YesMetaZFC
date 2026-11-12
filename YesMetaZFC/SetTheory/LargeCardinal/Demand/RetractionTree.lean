import YesMetaZFC.SetTheory.Descriptive.Tree.TreeTail
import YesMetaZFC.Model.SetTheory.Demand.Reply
import YesMetaZFC.SetTheory.LargeCardinal.Demand.AlphabetGround
import YesMetaZFC.SetTheory.LargeCardinal.Demand.ProjectionSpace
import YesMetaZFC.SetTheory.Descriptive.Demand.DemandCounterWeave
import YesMetaZFC.Model.SetTheory.Demand.Separated

/-! # 第一层补全精确恢复原双辅助字母域

新增节点只来自原三字母积，因而不引入新字母；每个原字母则由一项
常值节点见证。内部幂集编码因此原样复用。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem td_first_alphabet_l {ω A B C P Y F e one T U x₀ a₀ b₀ : M.Domain}
    (hw : M.IsOmega ω) (space : Fseq_space_d I ω Y F) (pair : M.IsCartesianProduct I P B C)
    (triple : M.IsCartesianProduct I Y A P) (empty : ∀ x, ¬ M.mem x e) (succ : M.SuccessorOf one e)
    (hx : M.mem x₀ A) (ha : M.mem a₀ B) (hb : M.mem b₀ C) (fill : Tr_first_d hZF F one T U) :
    Td_alphabet_d U B C := by
  have bound {side z} (letter : Td_letter_d side U z) : M.mem z (if side then C else B) := by
    obtain ⟨q,i,p,x,a,b,t,hq,ip,px,tab,eq⟩ := letter
    obtain ⟨_,_,fq⟩ := (space q).mp ((fill q).mp hq).1
    obtain ⟨x',_,t',ht,px'⟩ := (triple p).mp (fq.output_mem_of_pairMember ip)
    obtain ⟨_,et⟩ := (I).injective px px'
    obtain ⟨a',ha,b',hb,ab⟩ := (pair t').mp ht
    obtain ⟨ea,eb⟩ := (I).injective (et ▸ tab) ab
    cases side with
    | false => exact eq.symm ▸ ea.symm ▸ ha
    | true => exact eq.symm ▸ eb.symm ▸ hb
  have appears a b (ha : M.mem a B) (hb : M.mem b C) : Td_letter_d false U a ∧ Td_letter_d true U b := by
    obtain ⟨t,tab⟩ := (I).total a b
    obtain ⟨p,px⟩ := (I).total x₀ t
    have hp := (triple p).mpr ⟨x₀,hx,t,(pair t).mpr ⟨a,ha,b,hb,tab⟩,px⟩
    obtain ⟨q,fq,constant⟩ := ZF.exists_constantFunction hZF I (source := one) hp
    have heω := num_mem_l hZF.1 hw (show Num_d 0 e from empty)
    obtain ⟨one',succ',homega⟩ := hw.1.2 e heω
    have ho : M.mem one ω := succ'.eq hZF.1 succ ▸ homega
    have hq : M.mem q U := (fill q).mpr ⟨(space q).mpr ⟨one,ho,fq⟩,Or.inr ⟨one,fq.2.1,fun _ h => h⟩⟩
    have ep := (constant e p).mpr ⟨succ.predecessor_mem,rfl⟩
    exact ⟨⟨q,e,p,x₀,a,b,t,hq,ep,px,tab,rfl⟩,⟨q,e,p,x₀,a,b,t,hq,ep,px,tab,rfl⟩⟩
  exact ⟨fun z => ⟨fun hz => (appears z b₀ hz hb).1,fun hz => bound hz⟩,
    fun z => ⟨fun hz => (appears a₀ z ha hz).2,fun hz => bound hz⟩⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 历史逆像的前缀封闭性

先限制原三图，再用收缩的长度与前缀保持识别实数图的像。
新节点的合成图就是给定旧节点的精确前缀。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Td_pull_d.tree_l {ω A F₀ R π Y F S T : M.Domain}
    (pull : Td_pull_d hZF ω A F π S T) (retract : Tr_retract_d I ω A F₀ R π)
    (inputs : Fseq_space_d I ω A F₀) (space : Fseq_space_d I ω Y F) (tree : Tree_d F S) : Tree_d F T := by
  refine ⟨fun q hq => ((pull q).mp hq).1,?_⟩
  intro q hq q' hq' sub
  obtain ⟨_,n,s,t,a,b,hn,fs,st,node,join⟩ := (pull q).mp hq
  obtain ⟨m,hm,fq'⟩ := (space q').mp hq'
  have mn : M.MemberSubset m n := by
    intro i hi
    obtain ⟨p,_,ip⟩ := fq'.2.2 i hi
    exact (join.1.2 i).mpr ⟨p,ip.elim fun z hz => ⟨z,hz.1,sub z hz.2⟩⟩
  obtain ⟨s',rs⟩ := ZF.exists_restriction hZF I s m
  obtain ⟨a',ra⟩ := ZF.exists_restriction hZF I a m
  obtain ⟨b',rb⟩ := ZF.exists_restriction hZF I b m
  have fs' := rs.isSetFunctionFromTo (fn0_function_l (ZF.modelsKP hZF) fs) mn
  obtain ⟨t',_,st'⟩ := retract.function.2.1 s' ((inputs s').mpr ⟨m,hm,fs'⟩)
  have ft := fn0_function_l (ZF.modelsKP hZF) (retract.length n s t hn fs st)
  have ft' := fn0_function_l (ZF.modelsKP hZF)
    (retract.length m s' t' hm (fn0_of_function_l (ZF.modelsKP hZF) fs') st')
  have rt := (ds_restrict_iff_l I ft' ft.1).mpr (retract.monotone s' s t' t st' st
    ((ds_restrict_iff_l I fs' (fn0_function_l (ZF.modelsKP hZF) fs).1).mp rs))
  have node' := node.restrict_l hZF space tree hm mn rt ra rb
  refine (pull q').mpr ⟨hq',m,s',t',a',b',hm,fn0_of_function_l (ZF.modelsKP hZF) fs',st',node',
    ⟨fq'.1,fq'.2.1⟩,?_⟩
  intro i hi
  obtain ⟨x,y,z,v,p,ix,iy,iz,pair,triple,ip⟩ := join.2 i (mn i hi)
  obtain ⟨p',_,ip'⟩ := fq'.2.2 i hi
  have eq := join.1.1.2 i p' p (ip'.elim fun a ha => ⟨a,ha.1,sub a ha.2⟩) ip
  exact ⟨x,y,z,v,p,(rs.2 i x).mpr ⟨hi,ix⟩,(ra.2 i y).mpr ⟨hi,iy⟩,
    (rb.2 i z).mpr ⟨hi,iz⟩,pair,triple,eq ▸ ip'⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 同一满射辅助图沿历史收缩运输

从原三图分支取精确有限前缀，经逆像节点对应改变实数图，两张辅助图
及第一图的满射性完全保留；共尾节点再合成目标完整分支。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Td_pull_d.projection_l {ω A π Y F S T U V P x y : M.Domain}
    (pull : Td_pull_d hZF ω A F π S T) (hw : M.IsOmega ω)
    (function : M.IsSetFunction I π)
    (space : Fseq_space_d I ω Y F) (tree : Tree_d F S) (alphabet : Td_alphabet_d S U V)
    (pair : M.IsCartesianProduct I P U V) (triple : M.IsCartesianProduct I Y A P)
    (fx : Fn0_d ω A x) (fy : Fn0_d ω A y) (path : Tr_path_d hZF ω π x y)
    (projection : Td_projection_d hZF ω U V Y F T x) : Td_projection_d hZF ω U V Y F S y := by
  obtain ⟨q,a,b,fa,onto,fb,fq,branch,join⟩ := projection
  have xfn := fn0_function_l (ZF.modelsKP hZF) fx
  have yfn := fn0_function_l (ZF.modelsKP hZF) fy
  have afn := fn0_function_l (ZF.modelsKP hZF) fa
  have bfn := fn0_function_l (ZF.modelsKP hZF) fb
  have qfn := fn0_function_l (ZF.modelsKP hZF) fq
  apply td_projection_of_nodes_l hZF hw fy fa onto fb space tree
  intro n hn
  obtain ⟨m,succ,hm⟩ := hw.1.2 n hn
  obtain ⟨s,fs,rs,_⟩ := ds_prefix_l I hZF hw xfn hm
  obtain ⟨t,ft,rt,_⟩ := ds_prefix_l I hZF hw yfn hm
  obtain ⟨u,fu,ru,_⟩ := ds_prefix_l I hZF hw afn hm
  obtain ⟨v,fv,rv,_⟩ := ds_prefix_l I hZF hw bfn hm
  obtain ⟨_,_,q',_,_,_,joined⟩ := tg_join_exists_l I hZF fs fu fv
  have sub := Tg_join_d.subset_l joined join xfn.1 afn.1 bfn.1 (hw.transitive (ZF.modelsKP hZF) m hm)
    ((ds_restrict_iff_l I fs xfn.1).mp rs) ((ds_restrict_iff_l I fu afn.1).mp ru) ((ds_restrict_iff_l I fv bfn.1).mp rv)
  have qtyped : M.IsSetFunctionFromTo I q' m Y := ⟨joined.1.1,joined.1.2,fun i hi => by
    obtain ⟨p,ip⟩ := (joined.1.2 i).mp hi
    exact ⟨p,qfn.output_mem_of_pairMember (ip.elim fun r hr => ⟨r,hr.1,sub r hr.2⟩),ip⟩⟩
  have node : Tg_node_d I m T s u v := ⟨⟨fs.1,fs.2.1⟩,⟨fu.1,fu.2.1⟩,⟨fv.1,fv.2.1⟩,
    q',branch q' ((space q').mpr ⟨m,hm,qtyped⟩) sub,joined⟩
  obtain ⟨_,t',st',node⟩ := (pull.node_l hZF space alphabet pair triple hm).mp node
  have st := path m hm s t rs rt
  -- 两个目标实数前缀使用同一收缩图，须由它的函数性识别。
  have same : t' = t := function.2 s t' t st' st
  exact ⟨m,t,u,v,succ.predecessor_mem,hm,rt,ru,rv,same ▸ node⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 7.12 使用的实际变换树

先沿历史收缩取逆像，再补齐第一层。原辅助域及其编码保持不变；
补全树的满射投影向原树运输，补树先手胜策也向原树运输。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem td_retraction_tree_l {ω A F₀ R π S U V e one a₀ : M.Domain}
    (hw : M.IsOmega ω) (inputs : Fseq_space_d I ω A F₀) (retract : Tr_retract_d I ω A F₀ R π)
    (source : Td_tree_d I ω A S) (alphabet : Td_alphabet_d S U V) (chosen : M.mem a₀ U)
    (separated : Td_separated_d S) (empty : ∀ x, ¬ M.mem x e) (succ : M.SuccessorOf one e) :
    ∃ P Y F T W, M.IsCartesianProduct I P U V ∧ M.IsCartesianProduct I Y A P ∧
      Fseq_space_d I ω Y F ∧ Tree_d F S ∧ Td_pull_d hZF ω A F π S T ∧ Tree_d F T ∧
      Tr_first_d hZF F one T W ∧ Tree_d F W ∧ Td_tree_d I ω A W ∧ Td_alphabet_d W U V ∧ Td_separated_d W := by
  obtain ⟨U',V',P,Y,F,alph,pair,triple,space,tree⟩ := source.space_l hZF hw
  obtain ⟨rfl,rfl⟩ := alph.ext_l hZF.1 alphabet
  obtain ⟨T,pull⟩ := td_pull_exists_l hZF ω A F π S
  have treeT := pull.tree_l hZF retract inputs space tree
  obtain ⟨W,fill⟩ := tr_first_exists_l hZF F one T
  have treeW := fill.tree_l hZF space treeT
  obtain ⟨q,i,p,x,a,b,t,hq,ip,px,tab,eq⟩ := (alphabet.1 a₀).mp chosen
  obtain ⟨n,hn,fq⟩ := (space q).mp (tree.1 q hq)
  obtain ⟨x',hx,t',ht,px'⟩ := (triple p).mp (fq.output_mem_of_pairMember ip)
  obtain ⟨ex,et⟩ := (I).injective px px'
  obtain ⟨a',ha,b',hb,ab⟩ := (pair t').mp ht
  obtain ⟨_,eb⟩ := (I).injective (et ▸ tab) ab
  have letters := td_first_alphabet_l hZF hw space pair triple empty succ (ex.symm ▸ hx) chosen (eb.symm ▸ hb) fill
  exact ⟨P,Y,F,T,W,pair,triple,space,tree,pull,treeT,fill,treeW,
    td_tree_of_l I space treeW pair triple,letters,
    fun z hz hz' => separated.alphabet_l alphabet z ((letters.1 z).mpr hz) ((letters.2 z).mpr hz')⟩

theorem Td_pull_d.filled_projection_l {ω A π S T W U V P Y F e one x y : M.Domain}
    (pull : Td_pull_d hZF ω A F π S T) (fill : Tr_first_d hZF F one T W)
    (hw : M.IsOmega ω) (space : Fseq_space_d I ω Y F) (tree : Tree_d F S) (treeT : Tree_d F T)
    (alphabet : Td_alphabet_d S U V) (pair : M.IsCartesianProduct I P U V) (triple : M.IsCartesianProduct I Y A P)
    (empty : ∀ x, ¬ M.mem x e) (succ : M.SuccessorOf one e) (function : M.IsSetFunction I π)
    (fx : Fn0_d ω A x) (fy : Fn0_d ω A y) (path : Tr_path_d hZF ω π x y)
    (projection : Td_projection_d hZF ω U V Y F W x) : Td_projection_d hZF ω U V Y F S y := by
  obtain ⟨q,a,b,fa,onto,fb,fq,branch,join⟩ := projection
  exact pull.projection_l hZF hw function space tree alphabet pair triple fx fy path
    ⟨q,a,b,fa,onto,fb,fq,(fill.branch_l hZF hw space treeT empty succ fq).mp branch,join⟩

theorem Td_pull_d.filled_counter_l {ω A π S T W U V P Y F one x y : M.Domain}
    (pull : Td_pull_d hZF ω A F π S T) (fill : Tr_first_d hZF F one T W)
    (hw : M.IsOmega ω) (space : Fseq_space_d I ω Y F) (alphabet : Td_alphabet_d S U V)
    (pair : M.IsCartesianProduct I P U V) (triple : M.IsCartesianProduct I Y A P)
    (fx : Fn0_d ω A x) (path : Tr_path_d hZF ω π x y)
    (win : Dg_first_win_d hZF ω U V W x) : Dg_first_win_d hZF ω U V S y := by
  apply win.mono_nodes_l hZF hw
  intro n t a b hn rt node
  obtain ⟨s,fs,rs,_⟩ := ds_prefix_l I hZF hw (fn0_function_l (ZF.modelsKP hZF) fx) hn
  have joined := (pull.node_l hZF space alphabet pair triple hn).mpr
    ⟨fn0_of_function_l (ZF.modelsKP hZF) fs,t,path n hn s t rs rt,node⟩
  obtain ⟨gs,ga,gb,q,hq,join⟩ := joined
  exact ⟨s,rs,gs,ga,gb,q,(fill q).mpr ⟨((pull q).mp hq).1,Or.inl hq⟩,join⟩

end YesMetaZFC.SetTheory.LargeCardinal
