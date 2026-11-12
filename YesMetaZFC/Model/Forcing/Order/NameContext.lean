import YesMetaZFC.Model.Forcing.Order.NameTree
import YesMetaZFC.Model.Forcing.Order.NameLetters

/-! # 名字树的全坐标读取及反向构枝

每个内部长度同时给出查询、原联合枝、枚举、条件和三个自然数列的限制。
位置界使全部根检查和逐位检查最终发生，第一坐标始终是同一实际实数图。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.InnerModel SetTheory.Internal SetTheory.Descriptive
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Nr_tree_d.decode_l {ω X Q T A F₀ A₀ de df Z W H a b c d l r Y dx dh F S q : M.Domain}
    (tree : Nr_tree_d hZF ω X Q T A F₀ A₀ de df Z W H a b c d l r Y dx dh F S)
    (hw : M.IsOmega ω) (fq : M.IsSetFunctionFromTo I q ω Y) (branch : Branch_d F S q) :
    ∃ x h t z s u v w e f, Nr_cols_d hZF a b c d l r dx dh q x h t z s u v w ∧
      Fn0_d ω ω x ∧ M.IsSetFunctionFromTo I s ω A ∧ Fn0_d ω ω u ∧ Fn0_d ω ω v ∧ Fn0_d ω ω w ∧
      Fn0_d ω X e ∧ Fn0_d ω Q f ∧ Branch_d F₀ A₀ s ∧
      Fseq_recode_d I de s e ∧ Fseq_recode_d I df s f ∧ Nr_at_d ω X Q T ω e f x u v w := by
  obtain ⟨x,h,t,z,s,u,v,w,cols⟩ := tree.letters.columns_l hZF fq
  obtain ⟨fx,_,fs,fu,fv,fw⟩ := cols.functions_l hZF tree.letters fq
  obtain ⟨e,fe,se⟩ := ZF.fseq_compose_l I hZF tree.enumeration fs
  obtain ⟨f,ff,sf⟩ := ZF.fseq_compose_l I hZF tree.conditions fs
  have prefixes n (hn : M.mem n ω) : ∃ s₀ e₀ f₀ x₀ u₀ v₀ w₀,
      M.mem s₀ A₀ ∧ Nr_at_d ω X Q T n e₀ f₀ x₀ u₀ v₀ w₀ ∧
      M.IsRestrictionOf I s₀ s n ∧ M.IsRestrictionOf I e₀ e n ∧ M.IsRestrictionOf I f₀ f n ∧
      M.IsRestrictionOf I x₀ x n ∧ M.IsRestrictionOf I u₀ u n ∧ M.IsRestrictionOf I v₀ v n ∧ M.IsRestrictionOf I w₀ w n := by
    obtain ⟨q₀,fq₀,cut,_⟩ := ds_prefix_l I hZF hw fq hn
    have sub := (ds_restrict_iff_l I fq₀ fq.1).mp cut
    obtain ⟨m,x₀,h₀,t₀,z₀,s₀,u₀,v₀,w₀,e₀,f₀,_,typed,cols₀,hs,se₀,sf₀,check⟩ :=
      (tree.nodes q₀).mp (branch q₀ ((tree.sequences q₀).mpr ⟨n,hn,fq₀⟩) sub)
    have eq := typed.domain_eq_l hZF.1 (fn0_of_function_l (ZF.modelsKP hZF) fq₀)
    subst m
    obtain ⟨fx₀,_,fs₀,fu₀,fv₀,fw₀⟩ := cols₀.functions_l hZF tree.letters fq₀
    have fe₀ := se₀.function_l I hZF tree.enumeration fs₀
    have ff₀ := sf₀.function_l I hZF tree.conditions fs₀
    obtain ⟨xx,ss,uu,vv,ww⟩ := cols₀.mono_l hZF cols sub
    exact ⟨s₀,e₀,f₀,x₀,u₀,v₀,w₀,hs,check,(ds_restrict_iff_l I fs₀ fs.1).mpr ss,
      (ds_restrict_iff_l I fe₀ fe.1).mpr (se₀.mono_l I se ss),(ds_restrict_iff_l I ff₀ ff.1).mpr (sf₀.mono_l I sf ss),
      (ds_restrict_iff_l I fx₀ fx.1).mpr xx,(ds_restrict_iff_l I fu₀ fu.1).mpr uu,
      (ds_restrict_iff_l I fv₀ fv.1).mpr vv,(ds_restrict_iff_l I fw₀ fw.1).mpr ww⟩
  have base : Branch_d F₀ A₀ s := by
    intro s₁ hs₁ sub
    obtain ⟨n,hn,fs₁⟩ := (tree.base_space s₁).mp hs₁
    obtain ⟨s₀,_,_,_,_,_,_,hs,_,cut,_⟩ := prefixes n hn
    exact cut.eq hZF.1 ((ds_restrict_iff_l I fs₁ fs.1).mpr sub) ▸ hs
  have checks := nr_branch_l hZF hw (fun n hn => by
    obtain ⟨_,e₀,f₀,x₀,u₀,v₀,w₀,_,check,_,ce,cf,cx,cu,cv,cw⟩ := prefixes n hn
    exact ⟨e₀,f₀,x₀,u₀,v₀,w₀,check,ce,cf,cx,cu,cv,cw⟩)
  exact ⟨x,h,t,z,s,u,v,w,e,f,cols,fn0_of_function_l (ZF.modelsKP hZF) fx,fs,
    fn0_of_function_l (ZF.modelsKP hZF) fu,fn0_of_function_l (ZF.modelsKP hZF) fv,
    fn0_of_function_l (ZF.modelsKP hZF) fw,fn0_of_function_l (ZF.modelsKP hZF) fe,
    fn0_of_function_l (ZF.modelsKP hZF) ff,base,se,sf,checks⟩

theorem Nr_tree_d.of_data_l {ω X Q T A F₀ A₀ de df Z W H a b c d l r Y dx dh F S x s u v w e f : M.Domain}
    (tree : Nr_tree_d hZF ω X Q T A F₀ A₀ de df Z W H a b c d l r Y dx dh F S)
    (fx : Fn0_d ω ω x) (fs : Fn0_d ω A s) (fu : Fn0_d ω ω u) (fv : Fn0_d ω ω v) (fw : Fn0_d ω ω w)
    (branch : Branch_d F₀ A₀ s) (se : Fseq_recode_d I de s e) (sf : Fseq_recode_d I df s f)
    (run : Nr_at_d ω X Q T ω e f x u v w) :
    ∃ q h t z, M.IsSetFunctionFromTo I q ω Y ∧ Branch_d F S q ∧ Nr_cols_d hZF a b c d l r dx dh q x h t z s u v w := by
  obtain ⟨q,h,t,z,fq,cols⟩ := tree.letters.word_l hZF fx fs fu fv fw
  refine ⟨q,h,t,z,fq,?_,cols⟩
  intro q₀ hq₀ sub
  obtain ⟨n,hn,fq₀⟩ := (tree.sequences q₀).mp hq₀
  obtain ⟨x₀,h₀,t₀,z₀,s₀,u₀,v₀,w₀,cols₀⟩ := tree.letters.columns_l hZF fq₀
  obtain ⟨_,_,fs₀,_,_,_⟩ := cols₀.functions_l hZF tree.letters fq₀
  obtain ⟨e₀,_,se₀⟩ := ZF.fseq_compose_l I hZF tree.enumeration fs₀
  obtain ⟨f₀,_,sf₀⟩ := ZF.fseq_compose_l I hZF tree.conditions fs₀
  obtain ⟨xx,ss,uu,vv,ww⟩ := cols₀.mono_l hZF cols sub
  have bound : M.MemberSubset n ω := by
    intro i hi
    obtain ⟨y,_,p,pair,hp⟩ := fq₀.2.2 i hi
    exact fq.input_mem_of_pairMember ⟨p,pair,sub p hp⟩
  exact (tree.nodes q₀).mpr ⟨n,x₀,h₀,t₀,z₀,s₀,u₀,v₀,w₀,e₀,f₀,hn,fn0_of_function_l (ZF.modelsKP hZF) fq₀,cols₀,
    branch s₀ ((tree.base_space s₀).mpr ⟨n,hn,fs₀⟩) ss,se₀,sf₀,
    run.prefix_l bound (se₀.mono_l I se ss) (sf₀.mono_l I sf ss) xx uu vv ww⟩

end YesMetaZFC.Model.Forcing.Internal

/-! ## 从原联合树一次构造固定名字树及坐标对应 -/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.InnerModel SetTheory.Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

structure Nr_link_d {ω X Q C Ys Yg Zg Fs As Fg Ag ds dg hg lg Z W Y a b c d l r F A : M.Domain}
    (joint : Jt_tree_d hZF ω X Q C Ys Yg Zg Fs As Fg Ag ds dg hg lg Z W Y a b c d l r F A)
    (T de df Z' W' H a' b' c' d' l' r' Y' dx dh F' S : M.Domain) : Prop where
  tree : Nr_tree_d hZF ω X Q T Y F A de df Z' W' H a' b' c' d' l' r' Y' dx dh F' S
  projections : Jt_projection_d hZF a c d ds hg lg de df

theorem nr_link_l {ω X Q C Ys Yg Zg Fs As Fg Ag ds dg hg lg Z W Y a b c d l r F A : M.Domain}
    (hw : M.IsOmega ω)
    (joint : Jt_tree_d hZF ω X Q C Ys Yg Zg Fs As Fg Ag ds dg hg lg Z W Y a b c d l r F A) (T : M.Domain) :
    ∃ de df Z' W' H a' b' c' d' l' r' Y' dx dh F' S, Nr_link_d hZF joint T de df Z' W' H a' b' c' d' l' r' Y' dx dh F' S := by
  obtain ⟨de,df,fe,ff,compatible⟩ := joint.projections_l hZF
  obtain ⟨Z',W',H,a',b',c',d',l',r',Y',dx,dh,F',S,tree⟩ := nr_tree_l hZF (T := T) hw fe ff joint.sequences joint.tree
  exact ⟨de,df,Z',W',H,a',b',c',d',l',r',Y',dx,dh,F',S,tree,compatible⟩

end YesMetaZFC.Model.Forcing.Internal
