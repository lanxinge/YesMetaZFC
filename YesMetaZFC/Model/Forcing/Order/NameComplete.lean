import YesMetaZFC.Model.Forcing.Order.NameLetters
import YesMetaZFC.Model.Forcing.Order.GenericHullCollapse
import YesMetaZFC.Model.Forcing.Order.GenericTreeGround
import YesMetaZFC.Model.SetTheory.Internal.Registration
import YesMetaZFC.SetTheory.Card.FiniteParameters
import YesMetaZFC.Model.Forcing.Ground.CheckPool
import YesMetaZFC.Model.Forcing.Order.JointParameters
import YesMetaZFC.Model.SetTheory.Reflection.SkolemWitnessTree
import YesMetaZFC.Model.Forcing.Order.QueryAttempt
import YesMetaZFC.SetTheory.FunctionConstruction
import YesMetaZFC.Model.Forcing.Ground.RealCodeImage
import YesMetaZFC.Model.Forcing.Order.NameContext

/-! # 联合枝的共享枚举与全部登记读取

每个内部长度的联合前缀同时提供两个分量的前缀。相同长度的枚举限制唯一，
故两侧总枚举相等。两张自然数位置表分别恢复条件及固定参数的完整登记关系。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.InnerModel SetTheory.Internal SetTheory.Descriptive
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

structure Jt_prefix_d (X C As Ag n s p e e' f v w s₀ p₀ e₀ f₀ v₀ w₀ : M.Domain) : Prop where
  enumeration : Fn0_d n X e₀
  sh_member : M.mem s₀ As
  gn_member : M.mem p₀ Ag
  sh_cut : M.IsRestrictionOf I s₀ s n
  gn_cut : M.IsRestrictionOf I p₀ p n
  left_cut : M.IsRestrictionOf I e₀ e n
  right_cut : M.IsRestrictionOf I e₀ e' n
  condition_cut : M.IsRestrictionOf I f₀ f n
  register_cut : M.IsRestrictionOf I v₀ v n
  parameter_cut : M.IsRestrictionOf I w₀ w n
  conditions : Rg_at_d n e₀ f₀ v₀
  parameters : Rg_at_d n e₀ C w₀

theorem Jt_tree_d.prefixes_l {ω X Q C Ys Yg Zg Fs As Fg Ag ds dg hg lg Z W Y a b c d l r F A q t z s p v w e e' g f : M.Domain}
    (tree : Jt_tree_d hZF ω X Q C Ys Yg Zg Fs As Fg Ag ds dg hg lg Z W Y a b c d l r F A)
    (hw : M.IsOmega ω) (fq : M.IsSetFunctionFromTo I q ω Y) (branch : Branch_d F A q)
    (cols : Jt_cols_d hZF a b c d l r q t z s p v w)
    (se : Fseq_recode_d I ds s e) (pe : Fseq_recode_d I dg p e') (pg : Fseq_recode_d I hg p g) (gf : Fseq_recode_d I lg g f) :
    ∀ n, M.mem n ω → ∃ s₀ p₀ e₀ f₀ v₀ w₀, Jt_prefix_d hZF X C As Ag n s p e e' f v w s₀ p₀ e₀ f₀ v₀ w₀ := by
  obtain ⟨_,_,fs,fp,fv,fw⟩ := cols.functions_l hZF tree.letters fq
  have fe := se.function_l I hZF tree.sh_enum fs
  have fe' := pe.function_l I hZF tree.gn_enum fp
  have fg := pg.function_l I hZF tree.gn_pair fp
  have ff := gf.function_l I hZF tree.gn_cond fg
  intro n hn
  obtain ⟨q₀,fq₀,cut,_⟩ := ds_prefix_l I hZF hw fq hn
  have sub := (ds_restrict_iff_l I fq₀ fq.1).mp cut
  obtain ⟨m,t₀,z₀,s₀,p₀,v₀,w₀,e₀,g₀,f₀,_,typed,cols₀,hs,hp,se₀,pe₀,pg₀,gf₀,reg,params⟩ :=
    (tree.nodes q₀).mp (branch q₀ ((tree.sequences q₀).mpr ⟨n,hn,fq₀⟩) sub)
  have eq := typed.domain_eq_l hZF.1 (fn0_of_function_l (ZF.modelsKP hZF) fq₀)
  subst m
  obtain ⟨_,_,fs₀,fp₀,fv₀,fw₀⟩ := cols₀.functions_l hZF tree.letters fq₀
  obtain ⟨_,_,ss,pp,vv,ww⟩ := cols₀.mono_l hZF cols sub
  have fe₀ := se₀.function_l I hZF tree.sh_enum fs₀
  have fg₀ := pg₀.function_l I hZF tree.gn_pair fp₀
  have ff₀ := gf₀.function_l I hZF tree.gn_cond fg₀
  exact ⟨s₀,p₀,e₀,f₀,v₀,w₀,fn0_of_function_l (ZF.modelsKP hZF) fe₀,hs,hp,
    (ds_restrict_iff_l I fs₀ fs.1).mpr ss,(ds_restrict_iff_l I fp₀ fp.1).mpr pp,
    (ds_restrict_iff_l I fe₀ fe.1).mpr (se₀.mono_l I se ss),(ds_restrict_iff_l I fe₀ fe'.1).mpr (pe₀.mono_l I pe pp),
    (ds_restrict_iff_l I ff₀ ff.1).mpr (gf₀.mono_l I gf (pg₀.mono_l I pg pp)),
    (ds_restrict_iff_l I fv₀ fv.1).mpr vv,(ds_restrict_iff_l I fw₀ fw.1).mpr ww,reg,params⟩

theorem Jt_tree_d.decode_l {ω X Q C Ys Yg Zg Fs As Fg Ag ds dg hg lg Z W Y a b c d l r F A q : M.Domain}
    (tree : Jt_tree_d hZF ω X Q C Ys Yg Zg Fs As Fg Ag ds dg hg lg Z W Y a b c d l r F A)
    (hw : M.IsOmega ω) (fq : M.IsSetFunctionFromTo I q ω Y) (branch : Branch_d F A q) :
    ∃ t z s p v w e g f, Jt_cols_d hZF a b c d l r q t z s p v w ∧
      M.IsSetFunctionFromTo I s ω Ys ∧ M.IsSetFunctionFromTo I p ω Yg ∧
      Fn0_d ω X e ∧ Fn0_d ω Q f ∧ Fn0_d ω ω v ∧ Fn0_d ω ω w ∧ Branch_d Fs As s ∧ Branch_d Fg Ag p ∧
      Fseq_recode_d I ds s e ∧ Fseq_recode_d I dg p e ∧ Fseq_recode_d I hg p g ∧ Fseq_recode_d I lg g f ∧
      Rg_d e f v ∧ Rg_d e C w := by
  obtain ⟨t,z,s,p,v,w,cols⟩ := tree.letters.columns_l hZF fq
  obtain ⟨_,_,fs,fp,fv,fw⟩ := cols.functions_l hZF tree.letters fq
  obtain ⟨e,fe,se⟩ := ZF.fseq_compose_l I hZF tree.sh_enum fs
  obtain ⟨e',fe',pe⟩ := ZF.fseq_compose_l I hZF tree.gn_enum fp
  obtain ⟨g,fg,pg⟩ := ZF.fseq_compose_l I hZF tree.gn_pair fp
  obtain ⟨f,ff,gf⟩ := ZF.fseq_compose_l I hZF tree.gn_cond fg
  have prefixes := tree.prefixes_l hZF hw fq branch cols se pe pg gf
  -- 每个坐标都落在某个共同内部长度中，两侧总枚举由这些相同限制唯一确定。
  have eq : e = e' := by
    apply (fn0_of_function_l (ZF.modelsKP hZF) fe).ext_l hZF.1 (fn0_of_function_l (ZF.modelsKP hZF) fe')
    intro i hi
    obtain ⟨n,hn,hin,_⟩ := at_upper_l hZF hw hi hi
    obtain ⟨_,_,e₀,_,_,_,node⟩ := prefixes n hn
    obtain ⟨x,_,ix⟩ := node.enumeration.2.1 i hin
    exact ⟨x,((node.left_cut.2 i x).mp ix).2,((node.right_cut.2 i x).mp ix).2⟩
  subst e'
  refine ⟨t,z,s,p,v,w,e,g,f,cols,fs,fp,fn0_of_function_l (ZF.modelsKP hZF) fe,
    fn0_of_function_l (ZF.modelsKP hZF) ff,fn0_of_function_l (ZF.modelsKP hZF) fv,fn0_of_function_l (ZF.modelsKP hZF) fw,
    ?_,?_,se,pe,pg,gf,?_,?_⟩
  · apply (tree_branch_l I hZF hw tree.sh_space fs).mpr
    intro n hn
    obtain ⟨s₀,_,_,_,_,_,node⟩ := prefixes n hn
    exact ⟨s₀,node.sh_member,node.sh_cut⟩
  · apply (tree_branch_l I hZF hw tree.gn_space fp).mpr
    intro n hn
    obtain ⟨_,p₀,_,_,_,_,node⟩ := prefixes n hn
    exact ⟨p₀,node.gn_member,node.gn_cut⟩
  · apply rg_branch_l hZF hw (fn0_of_function_l (ZF.modelsKP hZF) fv)
    intro n hn
    obtain ⟨_,_,e₀,_,v₀,_,node⟩ := prefixes n hn
    exact ⟨e₀,v₀,fun i k x hi hk ik ix => node.conditions i k x hi hk ik ((node.condition_cut.2 i x).mpr ⟨hi,ix⟩),
      node.left_cut,node.register_cut⟩
  · apply rg_branch_l hZF hw (fn0_of_function_l (ZF.modelsKP hZF) fw)
    intro n hn
    obtain ⟨_,_,e₀,_,_,w₀,node⟩ := prefixes n hn
    exact ⟨e₀,w₀,node.parameters,node.left_cut,node.parameter_cut⟩

/-- 共享枚举且登记完整的两条实际分量枝，总能合成原联合树的枝。 -/
theorem Jt_tree_d.of_data_l {ω X Q C Ys Yg Zg Fs As Fg Ag ds dg hg lg Z W Y a b c d l r F A s p v w e g f : M.Domain}
    (tree : Jt_tree_d hZF ω X Q C Ys Yg Zg Fs As Fg Ag ds dg hg lg Z W Y a b c d l r F A)
    (fs : M.IsSetFunctionFromTo I s ω Ys) (bs : Branch_d Fs As s)
    (fp : M.IsSetFunctionFromTo I p ω Yg) (bp : Branch_d Fg Ag p)
    (fv : Fn0_d ω ω v) (fw : Fn0_d ω ω w)
    (se : Fseq_recode_d I ds s e) (pe : Fseq_recode_d I dg p e) (pg : Fseq_recode_d I hg p g) (gf : Fseq_recode_d I lg g f)
    (reg : Rg_d e f v) (params : Rg_d e C w) :
    ∃ q t z, M.IsSetFunctionFromTo I q ω Y ∧ Branch_d F A q ∧ Jt_cols_d hZF a b c d l r q t z s p v w := by
  obtain ⟨q,t,z,fq,cols⟩ := tree.letters.word_l hZF (fn0_of_function_l (ZF.modelsKP hZF) fs)
    (fn0_of_function_l (ZF.modelsKP hZF) fp) fv fw
  have fe := se.function_l I hZF tree.sh_enum fs
  refine ⟨q,t,z,fq,?_,cols⟩
  intro q₀ hq₀ sub
  obtain ⟨n,hn,fq₀⟩ := (tree.sequences q₀).mp hq₀
  obtain ⟨t₀,z₀,s₀,p₀,v₀,w₀,cols₀⟩ := tree.letters.columns_l hZF fq₀
  obtain ⟨_,_,fs₀,fp₀,_,_⟩ := cols₀.functions_l hZF tree.letters fq₀
  obtain ⟨_,_,ss,pp,vv,ww⟩ := cols₀.mono_l hZF cols sub
  obtain ⟨e₀,fe₀,se₀⟩ := ZF.fseq_compose_l I hZF tree.sh_enum fs₀
  obtain ⟨e',fe',pe₀⟩ := ZF.fseq_compose_l I hZF tree.gn_enum fp₀
  have ee := se₀.mono_l I se ss
  have ep := pe₀.mono_l I pe pp
  have eq := ((ds_restrict_iff_l I fe' fe.1).mpr ep).eq hZF.1 ((ds_restrict_iff_l I fe₀ fe.1).mpr ee)
  subst e'
  obtain ⟨g₀,fg₀,pg₀⟩ := ZF.fseq_compose_l I hZF tree.gn_pair fp₀
  obtain ⟨f₀,_,gf₀⟩ := ZF.fseq_compose_l I hZF tree.gn_cond fg₀
  have ff := gf₀.mono_l I gf (pg₀.mono_l I pg pp)
  have reg' : Rg_at_d ω e f v := fun i k x _ _ ik ix => reg i k x ik ix
  have params' : Rg_at_d ω e C w := fun i k x _ _ ik ix => params i k x ik ix
  exact (tree.nodes q₀).mpr ⟨n,t₀,z₀,s₀,p₀,v₀,w₀,e₀,g₀,f₀,hn,fn0_of_function_l (ZF.modelsKP hZF) fq₀,cols₀,
    bs s₀ ((tree.sh_space s₀).mpr ⟨n,hn,fs₀⟩) ss,bp p₀ ((tree.gn_space p₀).mpr ⟨n,hn,fp₀⟩) pp,se₀,pe₀,pg₀,gf₀,
    reg'.prefix_l (fn0_of_function_l (ZF.modelsKP hZF) fe) (fn0_of_function_l (ZF.modelsKP hZF) fe₀) ee ff vv,
    params'.prefix_l (fn0_of_function_l (ZF.modelsKP hZF) fe) (fn0_of_function_l (ZF.modelsKP hZF) fe₀) ee (fun _ h => h) ww⟩

end YesMetaZFC.Model.Forcing.Internal

/-! ## 同一壳与原泛型交中的实际递降列及枚举登记

参数化 DC 的状态域取 N∩H。每轮消费 N 的同一个满枚举，因此所有条件都留在
同一壳和原泛型中，并在 N∩H 中共尾。枚举的最小原像截面给出逐条件登记表。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.InnerModel SetTheory.Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Gh_closed_d.run_l {ω Q T H N e p₀ : M.Domain} (closed : Gh_closed_d Q T H N)
    (hw : M.IsOmega ω) (dc : Dc_d I ω) (fe : M.IsSetFunctionFromTo I e ω N)
    (onto : M.IsSetSurjectiveOnto I e ω N) (hp₀ : M.mem p₀ N) (hpH : M.mem p₀ H) :
    ∃ f v, Fn0_d ω N f ∧ Fn0_d ω ω v ∧ (∀ i p, Entry_d M i p f → M.mem p H) ∧
      (∀ i k p, Entry_d M i k v → Entry_d M i p f → Entry_d M k p e) ∧
      (∀ o, (∀ x, ¬ M.mem x o) → Entry_d M o p₀ f) ∧
      (∀ i j p q, M.SuccessorOf j i → Entry_d M i p f → Entry_d M j q f →
        ∀ a, Entry_d M i a e → Gh_step_d Q T H p a q) ∧
      ∀ p, M.mem p N → M.mem p H → ∃ i q, Entry_d M i q f ∧ Entry_d M q p T := by
  obtain ⟨S,inter⟩ := KP.intersection_exists_d (ZF.modelsKP hZF) N H
  let ρ : Env M 3 := ⟨fun i => [Q,T,H].get i,fun _ => H⟩
  let φ : UnarySchema 5 := { body := gh_step_m (.bound 3) (.bound 4) (.bound 5) (.bound 2) (.bound 1) .newest }
  have sat p a q : φ.denote ((ρ.push p).push a) q ↔ Gh_step_d Q T H p a q := gh_step_sat_l hZF.1 ..
  obtain ⟨f,ff,zero,step⟩ := dc.parameter_l I hZF hw φ ρ fe ((inter p₀).mpr ⟨hp₀,hpH⟩) (by
    intro p a hp ha
    obtain ⟨hp,hH⟩ := (inter p).mp hp
    obtain ⟨q,hq,good⟩ := closed p a hp ha hH
    exact ⟨q,(inter q).mpr ⟨hq,good.1⟩,(sat p a q).mpr good⟩)
  have fn : Fn0_d ω N f := (fn0_of_function_l (ZF.modelsKP hZF) ff).mono_target_l (fun p hp => ((inter p).mp hp).1)
  have kept i p (ip : Entry_d M i p f) : M.mem p H := ((inter p).mp (ff.output_mem_of_pairMember ip)).2
  have rounds i j p q (succ : M.SuccessorOf j i) (ip : Entry_d M i p f) (jq : Entry_d M j q f)
      a (ia : Entry_d M i a e) : Gh_step_d Q T H p a q := (sat p a q).mp (step i j p q succ ip jq a ia)
  -- 条件列复合最小原像截面，得到同一枚举中的真实位置。
  obtain ⟨v,fv,register⟩ := rg_lift_l hZF hw (fn0_of_function_l (ZF.modelsKP hZF) fe) onto fn
  refine ⟨f,v,fn,fv,kept,register,zero,rounds,?_⟩
  intro p hp hH
  obtain ⟨i,hi,ip⟩ := onto p hp
  obtain ⟨j,succ,hj⟩ := hw.1.2 i hi
  obtain ⟨q,_,iq⟩ := ff.2.2 i hi
  obtain ⟨r,_,jr⟩ := ff.2.2 j hj
  exact ⟨j,r,jr,(rounds i j q r succ iq jr p ip).2.2.1 hH⟩

end YesMetaZFC.Model.Forcing.Internal

/-! ## 同一可数壳上的两条配套见证枝

保留给定的 Skolem 树、泛型任务树及原泛型。先把偏序和指定起始条件加入种子，再取
共同闭包壳；同一个满枚举产生 Skolem 枝和泛型枝。全部条件通过实际位置表
登记进该壳，并在原泛型与壳的交中共尾。该交是同一壳模型上的完整泛型；
尚未把这些列合成一棵带符号的树。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.InnerModel SetTheory.Internal SetTheory.Descriptive
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem gh_branches_l {ω c X R a C L T E K W D J Y d h F A H B Z Y' d' h' l r F' A' : M.Domain}
    (hw : M.IsOmega ω) (source : Smem_d I c X R) (trans : M.TransitiveSet X)
    (native : (smdl_structure_l I (R := R) source.1.2.1).Models ZF)
    (P V p₀ : (smdl_structure_l I (R := R) source.1.2.1).Domain)
    (O : Cond_order_d (smdl_structure_l I (R := R) source.1.2.1) P V P)
    (generic : Generic_d (smdl_structure_l I (R := R) source.1.2.1) P V P (fun q => M.mem q.val H))
    (sh : Sh_tree_d hZF ω c X R a C L T E K W D J Y d h F A)
    (gn : Gn_tree_d hZF ω X P.val V.val Z Y' d' h' l r F' A')
    (sub : M.MemberSubset B X) (count : M.CardinalLessOrEqual I B ω) (hp₀ : M.mem p₀.val H) :
    ∃ N cN RN e s p b f u v, M.MemberSubset B N ∧ M.CardinalLessOrEqual I N ω ∧
      Gh_model_d hZF ω c X R N cN RN P.val V.val H ∧ Fn0_d ω N e ∧ M.IsSetSurjectiveOnto I e ω N ∧
      Fn0_d ω N f ∧ Fn0_d ω ω v ∧
      M.IsSetFunctionFromTo I s ω Y ∧ Branch_d F A s ∧ Fseq_recode_d I d s e ∧
      M.IsSetFunctionFromTo I p ω Y' ∧ Branch_d F' A' p ∧ Fseq_recode_d I d' p e ∧
      Fseq_recode_d I h' p b ∧ Fseq_recode_d I l b f ∧ Fseq_recode_d I r b u ∧
      (∀ i q, Entry_d M i q f → M.mem q H) ∧
      (∀ i k q, Entry_d M i k v → Entry_d M i q f → Entry_d M k q e) ∧
      (∀ o, (∀ x, ¬ M.mem x o) → Entry_d M o p₀.val f) ∧
      ∀ q, M.mem q N → M.mem q H → ∃ i t, Entry_d M i t f ∧ Entry_d M t q V.val := by
  let U := smdl_structure_l I (R := R) source.1.2.1
  have inj : Function.Injective (Subtype.val : U.Domain → M.Domain) := fun _ _ eq => Subtype.ext eq
  have full := smem_full_l I source trans
  have edge := image_entry_iff_l Subtype.val inj full (KP.exists_pair (ZF.modelsKP native)) hZF.1
  -- 偏序及起始条件自动加入种子，所有壳内成员资格由这次构造产生。
  let params : Fin 3 → M.Domain := Fin.cases p₀.val (Fin.cases P.val (Fin.cases V.val Fin.elim0))
  have owned i : M.mem (params i) X := Fin.cases p₀.property (Fin.cases P.property (Fin.cases V.property (fun i => Fin.elim0 i))) i
  obtain ⟨S,finite,read⟩ := ZF.finite_params_l I hZF hw params
  obtain ⟨B',union⟩ := KP.exists_unionOfTwo (ZF.modelsKP hZF) B S
  have sub' : M.MemberSubset B' X := fun x hx => ((union x).mp hx).elim (sub x)
    (fun hx => ((read x).mp hx).elim fun i eq => eq.symm ▸ owned i)
  obtain ⟨N,cN,RN,inside,nx,small,closed,model,elem,compatible⟩ := gh_hull_l hZFC hw source trans native
    sh.skolem P V O generic sub' (ZF.countable_union_two_l I hZF hw count (ZF.finite_countable_l I hZF hw finite) union)
  have fixed i : M.mem (params i) N := inside (params i) ((union (params i)).mpr (Or.inr ((read (params i)).mpr ⟨i,rfl⟩)))
  have point := fixed 0
  have hull := gh_model_l hZF hw source trans native model elem P V O (fixed 1) (fixed 2)
    (fun p hp hH => (image_member_l Subtype.val inj full).mpr (generic.proper ⟨p,nx p hp⟩ hH).1)
    (fun p q hp hq hH hqP pq => generic.upward ⟨p,nx p hp⟩ ⟨q,nx q hq⟩ hH
      ((image_member_l Subtype.val inj full).mp hqP) ((edge ⟨p,nx p hp⟩ ⟨q,nx q hq⟩ V).mpr pq))
    ⟨p₀.val,point,hp₀⟩ (by
      intro p q hp hq hH hG
      obtain ⟨r,hr,step⟩ := compatible p q hp hq hH
      exact ⟨r,hr,step.1,step.2.1,step.2.2.1 hG⟩) (by
      intro D hD dense
      obtain ⟨q,hq,step⟩ := compatible p₀.val D point hD hp₀
      exact ⟨q,hq,step.1,step.2.2.2 dense⟩)
  obtain ⟨ι,fi⟩ := small
  obtain ⟨e,fe,back⟩ := ZF.injection_retract_l I hZF fi (fun _ h => h) point
  have onto : M.IsSetSurjectiveOnto I e ω N := fun x hx => by
    obtain ⟨i,hi,xi⟩ := fi.1.2.2 x hx
    exact ⟨i,hi,back x i xi⟩
  have fen := fn0_of_function_l (ZF.modelsKP hZF) fe
  obtain ⟨f,v,ff,fv,kept,register,zero,rounds,cofinal⟩ := compatible.run_l hZF hw (ZFC.dc_l I hZFC hw) fe onto point hp₀
  -- 范围约束来自原泛型的正条件性；不扩大条件列的源模型。
  have fq : Fn0_d ω P.val f := ff.retarget_l (fun i q iq => by
    let q₀ : U.Domain := ⟨q,nx q (ff.bound_l iq).2⟩
    exact (image_member_l Subtype.val inj full).mpr (generic.proper q₀ (kept i q iq)).1)
  obtain ⟨u,fu,run⟩ := gn_deadline_l hZF hw (fn0_function_l (ZF.modelsKP hZF) fq) (by
    intro i j p q succ ip jq
    obtain ⟨x,_,ix⟩ := fe.2.2 i (ff.bound_l ip).1
    exact ⟨(rounds i j p q succ ip jq x ix).2.1,fun D iD dense =>
      (rounds i j p q succ ip jq D iD).2.2.2 dense⟩)
  obtain ⟨s,fs,bs,se⟩ := sh.of_closed_l hZF hw nx closed fen onto
  obtain ⟨p,b,fp,bp,pe,pb,bf,bu⟩ := gn.of_run_l hZF (fen.mono_target_l nx) fq fu run
  exact ⟨N,cN,RN,e,s,p,b,f,u,v,fun x hx => inside x ((union x).mpr (Or.inl hx)),⟨ι,fi⟩,hull,fen,onto,
    ff,fv,fs,bs,se,fp,bp,pe,pb,bf,bu,kept,register,zero,cofinal⟩

end YesMetaZFC.Model.Forcing.Internal

/-! ## 任意壳内登记运行生成完整壳泛型

直接由运行构造滤子，无需预先给定原泛型。任意两个滤子条件的公共加强仍可
取自原条件列，因此仍属于同一个壳。枚举覆盖全部壳内稠密对象，完整初等性
再将这份实际命中证据转换为壳模型上的泛型性。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.InnerModel SetTheory.Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem gr_model_l {ω c X R N d S e f u : M.Domain} (hw : M.IsOmega ω)
    (source : Smem_d I c X R) (trans : M.TransitiveSet X)
    (native : (smdl_structure_l I (R := R) source.1.2.1).Models ZF)
    (model : Ssub_d I c d X R N S) (elem : Selem_d I ω c d)
    (Q T : (smdl_structure_l I (R := R) source.1.2.1).Domain)
    (O : Cond_order_d (smdl_structure_l I (R := R) source.1.2.1) Q T Q)
    (hQ : M.mem Q.val N) (hT : M.mem T.val N)
    (fe : Fn0_d ω N e) (onto : M.IsSetSurjectiveOnto I e ω N)
    (ff : Fn0_d ω Q.val f) (fn : Fn0_d ω N f) (fu : Fn0_d ω ω u)
    (run : Gn_at_d Q.val T.val ω e f u) :
    ∃ H, Gh_model_d hZF ω c X R N d S Q.val T.val H ∧
      (∀ p, M.mem p H ↔ M.mem p Q.val ∧ ∃ i q, Entry_d M i q f ∧ Entry_d M q p T.val) ∧
      ∀ i p, Entry_d M i p f → M.mem p H := by
  let B := smdl_structure_l I (R := R) source.1.2.1
  have inj : Function.Injective (Subtype.val : B.Domain → M.Domain) := fun _ _ eq => Subtype.ext eq
  have full := smem_full_l I source trans
  have order := image_cond_order_l (ZF.modelsKP native) hZF.1 Subtype.val inj full O
  obtain ⟨_,_,H,_,_,members,filter,generated⟩ := gn_run_filter_l hZF hw order fe ff fu run
  have includes i p (ip : Entry_d M i p f) : M.mem p H :=
    (members p).mpr ⟨(ff.bound_l ip).2,i,p,ip,order.refl p (ff.bound_l ip).2⟩
  refine ⟨H,gh_model_l hZF hw source trans native model elem Q T O hQ hT
    (fun p _ hp => (filter.proper p hp).1) (fun p q _ _ hp hq pq => filter.upward p q hp hq pq) ?_ ?_ ?_,members,includes⟩
  · obtain ⟨o,_,ho⟩ := hw.1.1
    obtain ⟨p,hp,op⟩ := fn.2.1 o ho
    exact ⟨p,hp,includes o p op⟩
  · intro p q _ _ hp hq
    obtain ⟨i,r,ir,rp,rq⟩ := generated p q hp hq
    exact ⟨r,(fn.bound_l ir).2,includes i r ir,rp,rq⟩
  · intro D hD dense
    obtain ⟨i,hi,iD⟩ := onto D hD
    obtain ⟨k,hk,ik⟩ := fu.2.1 i hi
    obtain ⟨q,hq,kq⟩ := fn.2.1 k hk
    exact ⟨q,hq,includes k q kq,run.hits i k D q hi hk iD ik kq dense⟩

end YesMetaZFC.Model.Forcing.Internal

/-! ## 任意联合枝给出同一壳及其完整泛型

共享枚举解码出可数初等壳；条件及固定参数的登记把偏序和所有生成条件留在
该壳中。稠密任务分量给出实际命中列，由其上闭包构造完整壳泛型，不预交泛型。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.InnerModel SetTheory.Internal SetTheory.Descriptive
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 从两棵已构造的分量树和原参数列，实际装配全部联合树数据。 -/
theorem jt_context_l {ω c X R u S L T E K Wₛ D J Ys ds hs Fs As Zg Yg dg hg lg rg Fg Ag P V B : M.Domain}
    (hw : M.IsOmega ω) (sh : Sh_tree_d hZF ω c X R u S L T E K Wₛ D J Ys ds hs Fs As)
    (gn : Gn_tree_d hZF ω X P V Zg Yg dg hg lg rg Fg Ag) (hP : M.mem P X) (hV : M.mem V X) (fb : Fn0_d ω X B) :
    ∃ C, Jt_params_d ω X P V C ∧ (∀ i x, Entry_d M i x B → ∃ k, Entry_d M k x C) ∧
      ∃ Z W Y a b c' d' l r F A, Jt_tree_d hZF ω X P C Ys Yg Zg Fs As Fg Ag ds dg hg lg Z W Y a b c' d' l r F A := by
  obtain ⟨C,params,cover⟩ := jt_params_l hZF hw hP hV fb
  obtain ⟨Z,W,Y,a,b,c',d',l,r,F,A,tree⟩ := jt_tree_l hZF (C := C) hw sh.left gn.left gn.right gn.condition
    sh.sequences gn.sequences sh.tree gn.tree
  exact ⟨C,params,cover,Z,W,Y,a,b,c',d',l,r,F,A,tree⟩

theorem jt_model_l {ω c X R u S L T E K Wₛ D J Ys ds hs Fs As Zg Yg dg hg lg rg Fg Ag C Z W Y a b c' d' l r F A q : M.Domain}
    (hw : M.IsOmega ω) (source : Smem_d I c X R) (trans : M.TransitiveSet X)
    (native : (smdl_structure_l I (R := R) source.1.2.1).Models ZF)
    (P V : (smdl_structure_l I (R := R) source.1.2.1).Domain)
    (O : Cond_order_d (smdl_structure_l I (R := R) source.1.2.1) P V P)
    (sh : Sh_tree_d hZF ω c X R u S L T E K Wₛ D J Ys ds hs Fs As)
    (gn : Gn_tree_d hZF ω X P.val V.val Zg Yg dg hg lg rg Fg Ag)
    (joint : Jt_tree_d hZF ω X P.val C Ys Yg Zg Fs As Fg Ag ds dg hg lg Z W Y a b c' d' l r F A)
    (params : Jt_params_d ω X P.val V.val C) (fq : M.IsSetFunctionFromTo I q ω Y) (branch : Branch_d F A q) :
    ∃ N cN RN H t z s p v w e g f, Gh_model_d hZF ω c X R N cN RN P.val V.val H ∧
      M.CardinalLessOrEqual I N ω ∧ Fn0_d ω N e ∧ M.IsRangeOf I N e ∧ Fn0_d ω N f ∧
      Jt_cols_d hZF a b c' d' l r q t z s p v w ∧ Fseq_recode_d I ds s e ∧ Fseq_recode_d I dg p e ∧
      Fseq_recode_d I hg p g ∧ Fseq_recode_d I lg g f ∧
      (∀ p, M.mem p H ↔ M.mem p P.val ∧ ∃ i t, Entry_d M i t f ∧ Entry_d M t p V.val) ∧
      (∀ i p, Entry_d M i p f → M.mem p H) ∧ ∀ i x, Entry_d M i x C → M.mem x N := by
  obtain ⟨t,z,s,p,v,w,e,g,f,cols,fs,fp,_,fq',fv,fw,bs,bp,se,pe,pg,gf,registered,constants⟩ := joint.decode_l hZF hw fq branch
  obtain ⟨N,cN,RN,e₀,model,elem,count,fe,range,se₀⟩ := sh.elementary_l hZF hw fs bs
  have eq := se₀.unique_l I hZF.1 se
  subst e₀
  obtain ⟨e₀,g₀,f₀,u₀,_,_,fu,pe₀,pg₀,gf₀,_,run⟩ := gn.run_l hZF hw fp bp
  have eq := pe₀.unique_l I hZF.1 pe
  subst e₀
  have eq := pg₀.unique_l I hZF.1 pg
  subst g₀
  have eq := gf₀.unique_l I hZF.1 gf
  subst f₀
  -- 条件和固定参数由各自位置表进入刚解码的同一个壳。
  have fn := registered.range_l fe fq' fv
  have fc := constants.range_l fe params.function fw
  obtain ⟨i,iP⟩ := params.conditions
  obtain ⟨j,jV⟩ := params.order
  have onto : M.IsSetSurjectiveOnto I e ω N := fun x hx => ((range x).mp hx).imp fun i ix => ⟨(fe.bound_l ix).1,ix⟩
  obtain ⟨H,hull,members,accepted⟩ := gr_model_l hZF hw source trans native model elem P V O
    (fc.bound_l iP).2 (fc.bound_l jV).2 fe onto fq' fn fu run
  exact ⟨N,cN,RN,H,t,z,s,p,v,w,e,g,f,hull,count,fe,range,fn,cols,se,pe,pg,gf,members,accepted,fun i x ix => (fc.bound_l ix).2⟩

end YesMetaZFC.Model.Forcing.Internal

/-! ## 给定原泛型产生同一联合树的实际枝

固定参数列的值域与额外可数种子一起进入共同壳。第二张登记表由同一枚举的
截面实际构造。联合枝生成的滤子在壳上恰等于给定原泛型，保留指定起始条件。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.InnerModel SetTheory.Internal SetTheory.Descriptive
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem jt_complete_l {ω c X R u S L T E K Wₛ D J Ys ds hs Fs As Zg Yg dg hg lg rg Fg Ag C Z W Y a b c' d' l r F A H B : M.Domain}
    (hw : M.IsOmega ω) (source : Smem_d I c X R) (trans : M.TransitiveSet X)
    (native : (smdl_structure_l I (R := R) source.1.2.1).Models ZF)
    (P V p₀ : (smdl_structure_l I (R := R) source.1.2.1).Domain)
    (O : Cond_order_d (smdl_structure_l I (R := R) source.1.2.1) P V P)
    (generic : Generic_d (smdl_structure_l I (R := R) source.1.2.1) P V P (fun q => M.mem q.val H))
    (sh : Sh_tree_d hZF ω c X R u S L T E K Wₛ D J Ys ds hs Fs As)
    (gn : Gn_tree_d hZF ω X P.val V.val Zg Yg dg hg lg rg Fg Ag)
    (joint : Jt_tree_d hZF ω X P.val C Ys Yg Zg Fs As Fg Ag ds dg hg lg Z W Y a b c' d' l r F A)
    (params : Jt_params_d ω X P.val V.val C) (sub : M.MemberSubset B X) (count : M.CardinalLessOrEqual I B ω)
    (hp₀ : M.mem p₀.val H) :
    ∃ N cN RN H' q t z s p v w e g f, Gh_model_d hZF ω c X R N cN RN P.val V.val H' ∧
      M.CardinalLessOrEqual I N ω ∧ M.MemberSubset B N ∧ Fn0_d ω N e ∧ M.IsSetSurjectiveOnto I e ω N ∧
      Fn0_d ω N f ∧ Fn0_d ω P.val f ∧
      M.IsSetFunctionFromTo I q ω Y ∧ Branch_d F A q ∧ Jt_cols_d hZF a b c' d' l r q t z s p v w ∧
      Fseq_recode_d I ds s e ∧ Fseq_recode_d I dg p e ∧ Fseq_recode_d I hg p g ∧ Fseq_recode_d I lg g f ∧
      (∀ x, M.mem x H' ↔ M.mem x P.val ∧ ∃ i t, Entry_d M i t f ∧ Entry_d M t x V.val) ∧
      M.mem p₀.val H' ∧ (∀ o, (∀ x, ¬ M.mem x o) → Entry_d M o p₀.val f) ∧
      (∀ x, M.mem x N → (M.mem x H' ↔ M.mem x H)) ∧
      ∀ i x, Entry_d M i x C → M.mem x N := by
  let U := smdl_structure_l I (R := R) source.1.2.1
  have inj : Function.Injective (Subtype.val : U.Domain → M.Domain) := fun _ _ eq => Subtype.ext eq
  have full := smem_full_l I source trans
  have edge := image_entry_iff_l Subtype.val inj full (KP.exists_pair (ZF.modelsKP native)) hZF.1
  have fC := fn0_function_l (ZF.modelsKP hZF) params.function
  obtain ⟨B₀,range⟩ := ZF.exists_range_of_setFunction hZF I fC.1 fC.2.1
  have fB := params.function.retarget_l (fun i x ix => (range x).mpr ⟨i,ix⟩)
  have ontoB : M.IsSetSurjectiveOnto I C ω B₀ := fun x hx => ((range x).mp hx).imp fun i ix => ⟨(fB.bound_l ix).1,ix⟩
  obtain ⟨ι,fi,_⟩ := ZF.exists_rightInverseInjection_of_surjection_from_ordinal hZF I
    (hw.isOrdinal (ZF.modelsKP hZF)) (fn0_function_l (ZF.modelsKP hZF) fB) ontoB
  obtain ⟨B',union⟩ := KP.exists_unionOfTwo (ZF.modelsKP hZF) B B₀
  have sub' : M.MemberSubset B' X := fun x hx => ((union x).mp hx).elim (sub x)
    (fun hx => ((range x).mp hx).elim fun _ h => (params.function.bound_l h).2)
  obtain ⟨N,cN,RN,e,s,p,g,f,u₀,v,inside,small,hull,fe,onto,fn,fv,fs,bs,se,fp,bp,pe,pg,gf,_,kept,reg,zero,cofinal⟩ :=
    gh_branches_l hZFC hw source trans native P V p₀ O generic sh gn sub'
      (ZF.countable_union_two_l I hZF hw count ⟨ι,fi⟩ union) hp₀
  have fcN := params.function.retarget_l (fun i x ix => inside x ((union x).mpr (Or.inr ((range x).mpr ⟨i,ix⟩))))
  obtain ⟨w,fw,constants⟩ := rg_lift_l hZF hw fe onto fcN
  obtain ⟨q,t,z,fq,branch,cols⟩ := joint.of_data_l hZF fs bs fp bp fv fw se pe pg gf reg constants
  -- 从同一条件列生成滤子，再以原泛型中的共尾性识别壳上的限制。
  obtain ⟨e₁,g₁,f₁,u₁,_,ff,fu,pe₁,pg₁,gf₁,_,run⟩ := gn.run_l hZF hw fp bp
  have eq := pe₁.unique_l I hZF.1 pe
  subst e₁
  have eq := pg₁.unique_l I hZF.1 pg
  subst g₁
  have eq := gf₁.unique_l I hZF.1 gf
  subst f₁
  obtain ⟨H',model,members,includes⟩ := gr_model_l hZF hw source trans native hull.submodel hull.elementary P V O
    hull.conditions_mem hull.order_mem fe onto ff fn fu run
  have agree x (hx : M.mem x N) : M.mem x H' ↔ M.mem x H := by
    let x₀ : U.Domain := ⟨x,hull.submodel.subset x hx⟩
    constructor
    · intro h
      obtain ⟨hP,i,y,iy,yx⟩ := (members x).mp h
      let y₀ : U.Domain := ⟨y,hull.submodel.subset y (fn.bound_l iy).2⟩
      exact generic.upward y₀ x₀ (kept i y iy) ((image_member_l Subtype.val inj full).mp hP) ((edge y₀ x₀ V).mpr yx)
    · intro h
      obtain ⟨i,y,iy,yx⟩ := cofinal x hx h
      exact (members x).mpr ⟨(image_member_l Subtype.val inj full).mpr (generic.proper x₀ h).1,i,y,iy,yx⟩
  obtain ⟨o,empty,_⟩ := hw.1.1
  exact ⟨N,cN,RN,H',q,t,z,s,p,v,w,e,g,f,model,small,fun x hx => inside x ((union x).mpr (Or.inl hx)),fe,onto,fn,ff,
    fq,branch,cols,se,pe,pg,gf,members,includes o p₀.val (zero o empty),zero,agree,fun i x ix => (fcN.bound_l ix).2⟩

end YesMetaZFC.Model.Forcing.Internal

/-! ## 同一条件列中的实际最早判值位置

逐坐标在 ω 中分离所有成功位置，再取最小位置构成实际函数图。
两张名字位置列由原枚举的真实原像构造，整个无限检查证书不依赖额外选择实例。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.InnerModel SetTheory.Internal
universe u
variable {M : Structure.{u}}

def Nr_hit_d (X Q T b τ x f i k : M.Domain) : Prop := ∃ y p,
  Rd_entry_d i y x ∧ Rd_entry_d k p f ∧ Nr_edge_d X Q T b τ i y p

def nr_hit_m {n} (X Q T b τ x f i k : Term n) : Formula 1 n := set[n] ⟪∃ y p,
  ⌜rd_entry0_m⌝ₚ(⌜i⌝ₛ,y,⌜x⌝ₛ) ∧ ⌜rd_entry0_m⌝ₚ(⌜k⌝ₛ,p,⌜f⌝ₛ) ∧
    ⌜nr_edge_m⌝ₚ(⌜X⌝ₛ,⌜Q⌝ₛ,⌜T⌝ₛ,⌜b⌝ₛ,⌜τ⌝ₛ,⌜i⌝ₛ,y,p)⟫
derive_free_closed nr_hit_m

theorem nr_hit_sat_l (hE : Extensional M) {n} (ρ : Env M n) (X Q T b τ x f i k : Term n) :
    Formula.satisfies ρ (nr_hit_m X Q T b τ x f i k) ↔
      Nr_hit_d (X.eval ρ) (Q.eval ρ) (T.eval ρ) (b.eval ρ) (τ.eval ρ) (x.eval ρ) (f.eval ρ) (i.eval ρ) (k.eval ρ) := by
  simp only [nr_hit_m,Nr_hit_d,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,
    rd_entry0_sat_l hE,nr_edge_sat_l,Definitional.Term.eval_weaken]
  rfl

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)
include hZF

theorem nr_deadline_l {ω X Q T b τ x f : M.Domain} (hw : M.IsOmega ω)
    (total : ∀ i, M.mem i ω → ∃ k, M.mem k ω ∧ Nr_hit_d X Q T b τ x f i k) :
    ∃ u, Fn0_d ω ω u ∧ ∀ i k, Rd_entry_d i k u → Nr_hit_d X Q T b τ x f i k := by
  let ρ : Env M 8 := ⟨fun i => [ω,X,Q,T,b,τ,x,f].get i,fun _ => ω⟩
  let hit : BinarySchema 8 := {
    body := nr_hit_m (.bound 3) (.bound 4) (.bound 5) (.bound 6) (.bound 7) (.bound 8) (.bound 9) (.bound 1) .newest }
  have read i k : hit.denote ρ i k ↔ Nr_hit_d X Q T b τ x f i k := nr_hit_sat_l hZF.1 ..
  let least : BinarySchema 8 := {
    body := .conj (.mem .newest (.bound 2)) (.conj hit.body (set[10] ⟪∀ l ∈ ⌜(.newest : Term 10)⌝ₛ,
      ¬ ⌜nr_hit_m⌝ₚ(⌜(.bound 3 : Term 10)⌝ₛ,⌜(.bound 4 : Term 10)⌝ₛ,⌜(.bound 5 : Term 10)⌝ₛ,
        ⌜(.bound 6 : Term 10)⌝ₛ,⌜(.bound 7 : Term 10)⌝ₛ,⌜(.bound 8 : Term 10)⌝ₛ,⌜(.bound 9 : Term 10)⌝ₛ,
        ⌜(.bound 1 : Term 10)⌝ₛ,l)⟫))
    freeClosed := by simp -implicitDefEqProofs [hit,Definitional.Formula.FreeClosed] }
  have sat i k : least.denote ρ i k ↔ M.mem k ω ∧ Nr_hit_d X Q T b τ x f i k ∧
      ∀ l, M.mem l k → ¬ Nr_hit_d X Q T b τ x f i l := by
    simp only [least,BinarySchema.denote,Formula.satisfies_conj_iff,Formula.satisfies_mem_iff,
      Formula.satisfies_forallMem_iff,Formula.satisfies_neg_iff,nr_hit_sat_l hZF.1,Definitional.Term.eval_weaken]
    exact and_congr Iff.rfl (and_congr (read i k) Iff.rfl)
  have ordinal := hw.isOrdinal (ZF.modelsKP hZF)
  obtain ⟨u,fu,entries⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I least ρ (source := ω) (target := ω) (by
    intro i hi
    obtain ⟨D,sep⟩ := ZF.separation_exists_d hZF (⟨hit.body,hit.freeClosed⟩ : UnarySchema 9) (ρ.push i) ω
    have members k : M.mem k D ↔ M.mem k ω ∧ Nr_hit_d X Q T b τ x f i k := (sep k).trans (and_congr_right fun _ => read i k)
    obtain ⟨k,hk,success⟩ := total i hi
    obtain ⟨l,hl,minimal⟩ := ordinal.wellOrder.least D (fun k hk => ((members k).mp hk).1) ⟨k,(members k).mpr ⟨hk,success⟩⟩
    obtain ⟨hlω,hitl⟩ := (members l).mp hl
    refine ⟨l,(sat i l).mpr ⟨hlω,hitl,?_⟩⟩
    intro j jl hj
    rcases minimal j ((members j).mpr ⟨ordinal.transitive l hlω j jl,hj⟩) with eq | lj
    · exact KP.mem_irrefl_d (ZF.modelsKP hZF) l ((hZF.1.eq_of_same_members l j eq).symm ▸ jl)
    · exact KP.mem_irrefl_d (ZF.modelsKP hZF) l ((ordinal.mem hlω).transitive j jl l lj))
    (fun i _ k l hk hl => by
      obtain ⟨hk,ak,mk⟩ := (sat i k).mp hk
      obtain ⟨hl,al,ml⟩ := (sat i l).mp hl
      rcases ordinal.wellOrder.linear.compare k hk l hl with eq | kl | lk
      · exact hZF.1.eq_of_same_members k l eq
      · exact (ml k kl ak).elim
      · exact (mk l lk al).elim)
    (fun i k _ hk => ((sat i k).mp hk).1)
  exact ⟨u,fn0_of_function_l (ZF.modelsKP hZF) fu,fun i k ik => ((sat i k).mp ((entries i k).mp ik).2).2.1⟩

theorem nr_run_l {ω X Q T N e f x b τ p : M.Domain} (hw : M.IsOmega ω)
    (fe : Fn0_d ω N e) (onto : M.IsSetSurjectiveOnto I e ω N) (ff : Fn0_d ω Q f) (fx : Fn0_d ω ω x)
    (hb : M.mem b N) (hτ : M.mem τ N)
    (root : M.mem b Q ∧ Rd_entry_d p b T ∧ Nr_base_d X Q T ω b τ p)
    (zero : ∀ o, (∀ y, ¬ M.mem y o) → Rd_entry_d o p f)
    (total : ∀ i, M.mem i ω → ∃ k, M.mem k ω ∧ Nr_hit_d X Q T b τ x f i k) :
    ∃ u v w, Fn0_d ω ω u ∧ Fn0_d ω ω v ∧ Fn0_d ω ω w ∧ Nr_at_d ω X Q T ω e f x u v w ∧
      (∀ i k z, Rd_entry_d i k v → Rd_entry_d k z e → z = b) ∧
      (∀ i k z, Rd_entry_d i k w → Rd_entry_d k z e → z = τ) := by
  obtain ⟨u,fu,hit⟩ := nr_deadline_l hZF hw total
  obtain ⟨a,ha,ab⟩ := onto b hb
  obtain ⟨c,hc,cτ⟩ := onto τ hτ
  obtain ⟨v,fv,cv⟩ := ZF.exists_constantFunction hZF I (source := ω) ha
  obtain ⟨w,fw,cw⟩ := ZF.exists_constantFunction hZF I (source := ω) hc
  have ef := fn0_function_l (ZF.modelsKP hZF) fe
  have pf := fn0_function_l (ZF.modelsKP hZF) ff
  have xf := fn0_function_l (ZF.modelsKP hZF) fx
  have selectB i k z (ik : Rd_entry_d i k v) (kz : Rd_entry_d k z e) : z = b :=
    ef.1.2 a z b (((cv i k).mp ik).2 ▸ kz) ab
  have selectT i k z (ik : Rd_entry_d i k w) (kz : Rd_entry_d k z e) : z = τ :=
    ef.1.2 c z τ (((cw i k).mp ik).2 ▸ kz) cτ
  refine ⟨u,v,w,fu,fn0_of_function_l (ZF.modelsKP hZF) fv,fn0_of_function_l (ZF.modelsKP hZF) fw,
    ⟨?_,?_,?_,?_⟩,selectB,selectT⟩
  · exact fun i j a b _ _ ia jb => ((cv i a).mp ia).2.trans ((cv j b).mp jb).2.symm
  · exact fun i j a b _ _ ia jb => ((cw i a).mp ia).2.trans ((cw j b).mp jb).2.symm
  · intro o a' c' p' b' τ' _ _ _ empty oa oc ab' cτ' op
    have ea := ((cv o a').mp oa).2
    have ec := ((cw o c').mp oc).2
    have eb := ef.1.2 a b' b (ea ▸ ab') ab
    have et := ef.1.2 c τ' τ (ec ▸ cτ') cτ
    have ep := pf.1.2 o p' p op (zero o empty)
    exact eb.symm ▸ et.symm ▸ ep.symm ▸ root
  · intro i k a' c' y p' b' τ' _ _ _ _ iy ik kp ia ic ab' cτ'
    have eb := ef.1.2 a b' b (((cv i a').mp ia).2 ▸ ab') ab
    have et := ef.1.2 c τ' τ (((cw i c').mp ic).2 ▸ cτ') cτ
    obtain ⟨y',p'',iy',kp',force⟩ := hit i k ik
    exact eb.symm ▸ et.symm ▸ xf.1.2 i y' y iy' iy ▸ pf.1.2 k p'' p' kp' kp ▸ force

end YesMetaZFC.Model.Forcing.Internal

/-! ## 名字进入原壳后仍解释为同一个实数

返回初等嵌入固定全部自然数，坍塌泛型的每个条件在原泛型中被接受。
实际名字的商值沿提升映射比较，函数的全定义性恢复同一个完整背景实数图。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.InnerModel SetTheory.Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)
variable {c X R : M.Domain} (source : Smem_d (kp_pair_l (ZF.modelsKP hZF)) c X R)
  (trans : M.TransitiveSet X)
include trans

theorem Gh_collapse_d.real_pull_l {N d H B F j e V P U G H₀ x : M.Domain}
    (native : (smdl_structure_l I (R := R) source.1.2.1).Models ZF) :
    let L := smdl_structure_l I (R := R) source.1.2.1
    let E := extension_l L native
    ∀ ω Q T τ : L.Domain, M.IsOmega ω.val →
    Gh_collapse_d hZF ω.val c X N d Q.val T.val H B F j e V P U G →
    M.mem τ.val N → (∀ p, M.mem p N → M.mem p H → M.mem p H₀) →
    Generic_d L Q T Q (fun p => M.mem p.val H₀) → Cond_order_d L Q T Q →
    ∀ k : L.Domain → (E Q T Q (fun p => M.mem p.val H₀)).Domain,
    (∀ a, Gval_d L Q T Q (fun p => M.mem p.val H₀) a (k a)) →
    ∀ {y : (E Q T Q (fun p => M.mem p.val H₀)).Domain},
    Qval_d L Q T Q (fun p => M.mem p.val H₀) τ y →
    Fn0_d (M := E Q T Q (fun p => M.mem p.val H₀)) (k ω) (k ω) y →
    Fn_read_d (N := L) (M := M) (E := E Q T Q (fun p => M.mem p.val H₀)) Subtype.val k y x →
    Fn0_d (M := M) ω.val ω.val x → Fn_bg_d B P U P ω.val ω.val G x ∧
      ∀ b : L.Domain, M.mem b.val N → M.mem b.val H → ∀ i y, Rd_entry_d i y x →
        ∃ p, M.mem p N ∧ M.mem p H ∧ Nr_edge_d X Q.val T.val b.val τ.val i y p := by
  dsimp only
  intro ω Q T τ hw h name accepted generic O k ground y value fn read real
  let L := smdl_structure_l I (R := R) source.1.2.1
  let C := smdl_structure_l I (R := V) h.model.1.2.1
  have small := ZFC.models_zf_l (h.theory.native_l I hZF hw)
  obtain ⟨hwB,_,_,_⟩ := h.numbers_l hZF hw source trans
  let w : C.Domain := ⟨ω.val,hwB⟩
  let p : C.Domain := ⟨P,(h.collapse.function.bound_l h.conditions).2⟩
  let t : C.Domain := ⟨U,(h.collapse.function.bound_l h.order).2⟩
  obtain ⟨τ',hτ,ττ⟩ := h.collapse.function.2.1 τ.val name
  let s : C.Domain := ⟨τ',hτ⟩
  obtain ⟨f,elem,values⟩ := h.embedding.project_l I hZF hw h.model.1 source.1
  have point (a : C.Domain) (b : (L).Domain) (edge : Rd_entry_d a.val b.val j) : f a = b :=
    Subtype.ext (h.embedding.1.1.1.2 _ _ _ (values a) edge)
  have fp : f p = Q := point p Q ((h.inverse_entries Q.val P).mpr h.conditions)
  have ft : f t = T := point t T ((h.inverse_entries T.val U).mpr h.order)
  have fs : f s = τ := point s τ ((h.inverse_entries τ.val τ').mpr ττ)
  have fw : f w = ω := point w ω (h.embedding.omega_l I hZF hw h.transitive trans h.model source hwB)
  -- 返回嵌入逐点固定自然数，并把同一坍塌滤子的条件送回原泛型。
  have fixed (a : C.Domain) (ha : C.mem a w) : (f a).val = a.val :=
    h.embedding.1.1.1.2 _ _ _ (values a) (h.embedding.natural_l hZF hw h.transitive trans h.model source hwB
      a.val ((smem_member_l I h.model.1 h.model.2 a w).mp ha))
  have keep (a : C.Domain) (ha : M.mem a.val G) : M.mem (f a).val H₀ := by
    have old := (h.inverse_entries (f a).val a.val).mp (values a)
    exact accepted (f a).val (h.collapse.function.bound_l old).1 ((h.accepted_l hZF old).mpr ha)
  have order : Cond_order_d C p t p := by
    let ρ : Env C 3 := ⟨fun i => [p,t,p].get i,fun _ => p⟩
    apply (cond_order_sat_l small.1 ρ (.bound 0) (.bound 1) (.bound 2)).mp
    apply (elem (cond_order_m (.bound 0) (.bound 1) (.bound 2)) (by simp -implicitDefEqProofs) ρ).mpr
    apply (cond_order_sat_l native.1 (image_env_l f ρ) (.bound 0) (.bound 1) (.bound 2)).mpr
    change Cond_order_d L (f p) (f t) (f p)
    simpa only [fp,ft] using O
  have g := ((h.model.generic_code_l I hZF.1 h.transitive (ZF.modelsKP small) p t p G).mp h.generic).2
  have ci : Function.Injective (Subtype.val : C.Domain → M.Domain) := fun _ _ eq => Subtype.ext eq
  have li : Function.Injective (Subtype.val : (L).Domain → M.Domain) := fun _ _ eq => Subtype.ext eq
  -- 名字商上的初等提升回拉完整函数图；两边的每个自然数坐标已经识别。
  have pull := fn_value_real_pull_l (ZF.modelsKP hZF) small native f elem Subtype.val ci
    (smem_full_l I h.model h.transitive) Subtype.val li
    (ω := w) (B := p) (R := t) (z := p) (τ := s) (V := fun a => M.mem a.val H₀) (x := x)
    fixed order g
  rw [fp,ft,fw,fs] at pull
  have result := pull generic keep k ground value fn read real
  refine ⟨(fn_bg_read_l I hZF.1 h.model h.transitive small.1 p t p w w G x).mpr (result.code_l small order g),?_⟩
  -- 保留原名字：其每条数字图边都有同一壳泛型中的原条件见证。
  intro b hb bH i y' iy
  obtain ⟨b',hb',bb⟩ := h.collapse.function.2.1 b.val hb
  let b₀ : C.Domain := ⟨b',hb'⟩
  let i₀ : C.Domain := ⟨i,h.transitive ω.val hwB i (real.bound_l iy).1⟩
  let y₀ : C.Domain := ⟨y',h.transitive ω.val hwB y' (real.bound_l iy).2⟩
  have fb : f b₀ = b := point b₀ b ((h.inverse_entries b.val b').mpr bb)
  have ni : (f i₀).val = i := fixed i₀ ((smem_member_l I h.model.1 h.model.2 i₀ w).mpr (real.bound_l iy).1)
  have ny : (f y₀).val = y' := fixed y₀ ((smem_member_l I h.model.1 h.model.2 y₀ w).mpr (real.bound_l iy).2)
  obtain ⟨q,qG,force⟩ := (result.entry_l small order g ci (b := b₀) ((h.accepted_l hZF bb).mp bH) i₀ y₀).mp iy
  have old := (h.inverse_entries (f q).val q.val).mp (values q)
  refine ⟨(f q).val,(h.collapse.function.bound_l old).1,(h.accepted_l hZF old).mpr qG,?_⟩
  let ρ : Env C 8 := ⟨fun a => [p,t,p,b₀,s,i₀,y₀,q].get a,fun _ => s⟩
  have moved := (nentry_sat_l native.1 (image_env_l f ρ) (.bound 0) (.bound 1) (.bound 2) (.bound 3)
    (.bound 4) (.bound 5) (.bound 6) (.bound 7)).mp ((elem nentry0_m nentry0_closed_l ρ).mp
      ((nentry_sat_l small.1 ρ (.bound 0) (.bound 1) (.bound 2) (.bound 3) (.bound 4) (.bound 5) (.bound 6) (.bound 7)).mpr force))
  change Nentry_d (f p) (f t) (f p) (f b₀) (f s) (f i₀) (f y₀) (f q) at moved
  rw [fp,ft,fb,fs] at moved
  simpa only [ni,ny] using (nr_edge_read_l I source trans native.1 Q T b τ (f i₀) (f y₀) (f q)).mpr moved

end YesMetaZFC.Model.Forcing.Internal

/-! ## 联合枝的实际可数传递坍塌

同一联合枝的条件列先生成壳泛型，再随该壳实际坍塌。固定参数和条件列
均保留原坐标，完整内部 ZFC、可数性及全泛型性由构造给出。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.InnerModel SetTheory.Internal SetTheory.Descriptive
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem jt_collapse_l {ω c X R u S L T E K Wₛ D J Ys ds hs Fs As Zg Yg dg hg lg rg Fg Ag C Z W Y a b c' d' l r F A q : M.Domain}
    (hw : M.IsOmega ω) (source : Smem_d I c X R) (trans : M.TransitiveSet X) (certificate : Zc_model_d I ω c X R)
    (P V : (smdl_structure_l I (R := R) source.1.2.1).Domain)
    (O : Cond_order_d (smdl_structure_l I (R := R) source.1.2.1) P V P)
    (sh : Sh_tree_d hZF ω c X R u S L T E K Wₛ D J Ys ds hs Fs As)
    (gn : Gn_tree_d hZF ω X P.val V.val Zg Yg dg hg lg rg Fg Ag)
    (joint : Jt_tree_d hZF ω X P.val C Ys Yg Zg Fs As Fg Ag ds dg hg lg Z W Y a b c' d' l r F A)
    (params : Jt_params_d ω X P.val V.val C) (fq : M.IsSetFunctionFromTo I q ω Y) (branch : Branch_d F A q) :
    ∃ N cN RN H t z s p v w e g f B π j cB RB P' V' G,
      Gh_model_d hZF ω c X R N cN RN P.val V.val H ∧
      Jt_cols_d hZF a b c' d' l r q t z s p v w ∧ Fseq_recode_d I ds s e ∧ Fseq_recode_d I dg p e ∧
      Fseq_recode_d I hg p g ∧ Fseq_recode_d I lg g f ∧
      Gh_collapse_d hZF ω c X N cN P.val V.val H B π j cB RB P' V' G ∧
      (∀ i x, Entry_d M i x f → ∃ y, Rd_entry_d x y π ∧ M.mem y G) ∧
      ∀ i x, Entry_d M i x C → ∃ y, Rd_entry_d x y π ∧ Rd_entry_d y x j := by
  obtain ⟨N,cN,RN,H,t,z,s,p,v,w,e,g,f,hull,count,_,_,ff,cols,se,pe,pg,gf,_,accepted,constants⟩ :=
    jt_model_l hZF hw source trans (ZFC.models_zf_l (certificate.native_l I hZF hw)) P V O sh gn joint params fq branch
  obtain ⟨B,π,j,cB,RB,P',V',G,collapse⟩ := hull.collapse_l hZF hw source trans certificate count
  refine ⟨N,cN,RN,H,t,z,s,p,v,w,e,g,f,B,π,j,cB,RB,P',V',G,hull,cols,se,pe,pg,gf,collapse,?_,?_⟩
  · intro i x ix
    obtain ⟨y,_,xy⟩ := collapse.collapse.function.2.1 x (ff.bound_l ix).2
    exact ⟨y,xy,(collapse.accepted_l hZF xy).mp (accepted i x ix)⟩
  · intro i x ix
    obtain ⟨y,_,xy⟩ := collapse.collapse.function.2.1 x (constants i x ix)
    exact ⟨y,xy,(collapse.inverse_entries x y).mpr xy⟩

end YesMetaZFC.Model.Forcing.Internal

/-! ## 原泛型实数实际产生固定名字树的一条枝

输入固定原名字及任意已接受检查基准；函数性条件由该名字的实际商值产生。
公共加强同时接受函数性、基准和指定条件，再将原名字与基准加入共同壳。
原条件列在壳泛型中共尾，最早判值位置表与固定名字位置列合成第一坐标
恰为原 x 的无限枝，并保留零项加强及名字选择的实际方程。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.InnerModel SetTheory.Internal SetTheory.Descriptive
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Nr_link_d.complete_l {c X R u S L T E K Wₛ D J Ys ds hs Fs As Zg Yg dg hg lg rg Fg Ag C Z W Y a b c' d' l r F A
    de df Zn Wn Hn an bn cn dn ln rn Yn dx dh Fn An H x : M.Domain}
    (source : Smem_d I c X R) (trans : M.TransitiveSet X)
    (ω P V p₀ b₀ τ : (smdl_structure_l I (R := R) source.1.2.1).Domain)
    (hw : M.IsOmega ω.val) (certificate : Zc_model_d I ω.val c X R)
    (O : Cond_order_d (smdl_structure_l I (R := R) source.1.2.1) P V P)
    (generic : Generic_d (smdl_structure_l I (R := R) source.1.2.1) P V P (fun q => M.mem q.val H))
    (sh : Sh_tree_d hZF ω.val c X R u S L T E K Wₛ D J Ys ds hs Fs As)
    (gn : Gn_tree_d hZF ω.val X P.val V.val Zg Yg dg hg lg rg Fg Ag)
    (joint : Jt_tree_d hZF ω.val X P.val C Ys Yg Zg Fs As Fg Ag ds dg hg lg Z W Y a b c' d' l r F A)
    (link : Nr_link_d hZF joint V.val de df Zn Wn Hn an bn cn dn ln rn Yn dx dh Fn An)
    (params : Jt_params_d ω.val X P.val V.val C) (hp₀ : M.mem p₀.val H)
    (hb : M.mem b₀.val H) (real : Fn0_d ω.val ω.val x)
    (named : Fn_value_d (ZFC.models_zf_l (certificate.native_l I hZF hw)) Subtype.val P V P ω τ (fun p => M.mem p.val H) x) :
    ∃ N cN RN H' q q' h' t' z' u' v' w' B π j cB RB P' V' G,
      M.IsSetFunctionFromTo I q' ω.val Yn ∧ Branch_d Fn An q' ∧
      Nr_cols_d hZF an bn cn dn ln rn dx dh q' x h' t' z' q u' v' w' ∧
      M.IsSetFunctionFromTo I q ω.val Y ∧ Branch_d F A q ∧ Gh_model_d hZF ω.val c X R N cN RN P.val V.val H' ∧
      Gh_collapse_d hZF ω.val c X N cN P.val V.val H' B π j cB RB P' V' G ∧
      Fn_bg_d B P' V' P' ω.val ω.val G x ∧ (∃ p, Rd_entry_d p₀.val p π ∧ M.mem p G) ∧
      (∀ i z, Entry_d M i z C → ∃ z', Rd_entry_d z z' π ∧ Rd_entry_d z' z j) ∧
      ∃ e f, ∃ q₀ : (smdl_structure_l I (R := R) source.1.2.1).Domain,
        Fseq_recode_d I de q e ∧ Fseq_recode_d I df q f ∧ M.mem q₀.val H ∧
        Below_d (smdl_structure_l I (R := R) source.1.2.1) P V P q₀ p₀ ∧
        (∀ i k z, Rd_entry_d i k v' → Rd_entry_d k z e → z = b₀.val) ∧
        (∀ i k z, Rd_entry_d i k w' → Rd_entry_d k z e → z = τ.val) ∧
        ∀ o p, (∀ z, ¬ M.mem z o) → Rd_entry_d o p f → p = q₀.val := by
  let U := smdl_structure_l I (R := R) source.1.2.1
  have native := ZFC.models_zf_l (certificate.native_l I hZF hw)
  have inj : Function.Injective (Subtype.val : U.Domain → M.Domain) := fun _ _ eq => Subtype.ext eq
  have full := smem_full_l I source trans
  have member {a b : U.Domain} : M.mem a.val b.val ↔ U.mem a b := image_member_l (M := U) (N := M) Subtype.val inj full
  have edge := image_entry_iff_l Subtype.val inj full (KP.exists_pair (ZF.modelsKP native)) hZF.1
  obtain ⟨k,y,value,ground,fy,graph⟩ := named
  obtain ⟨p,t,w,hp,ct,cw,typed⟩ := fn_name_of_value_l native O generic hb k ground value fy
  have eqw := check_unique_l U native.1 (check_ind_l U native) b₀ ω w t cw ct
  have typed : Fn_name_d U P V P p t t τ := eqw ▸ typed
  obtain ⟨q₁,hq₁,q₁₀,q₁p⟩ := generic.directed p₀ p hp₀ hp
  obtain ⟨q₀,hq₀,q₀₁,q₀b⟩ := generic.directed q₁ b₀ hq₁ hb
  have q₀p := O.trans q₀ q₁ p (generic.proper q₀ hq₀).1 (generic.proper q₁ hq₁).1 (generic.proper p hp).1 q₀₁ q₁p
  have q₀₀ := O.trans q₀ q₁ p₀ (generic.proper q₀ hq₀).1 (generic.proper q₁ hq₁).1 (generic.proper p₀ hp₀).1 q₀₁ q₁₀
  have root : M.mem b₀.val P.val ∧ Rd_entry_d q₀.val b₀.val V.val ∧ Nr_base_d X P.val V.val ω.val b₀.val τ.val q₀.val :=
    ⟨member.mpr (generic.proper b₀ hb).1,(edge q₀ b₀ V).mp q₀b,
      (nr_base_read_l I source trans native.1 P V ω b₀ τ q₀).mpr ⟨t,ct,typed.1,typed.2.1,typed.2.2.1,
        (forces_regular_l O native fn_body_m (fn_env_l t t τ) (fn_env_names_l typed.1 typed.2.1 typed.2.2.1)).1
          p q₀ (generic.proper p hp).1 ⟨(generic.proper q₀ hq₀).1,(generic.proper q₀ hq₀).2,q₀p⟩ typed.2.2.2⟩⟩
  let seed : Fin 3 → M.Domain := Fin.cases b₀.val (Fin.cases τ.val (fun _ => p₀.val))
  obtain ⟨D₀,finite,entries⟩ := ZF.finite_params_l I hZF hw seed
  have sub : M.MemberSubset D₀ X := by
    intro z hz
    obtain ⟨i,rfl⟩ := (entries z).mp hz
    exact Fin.cases b₀.property (Fin.cases τ.property (fun _ => p₀.property)) i
  obtain ⟨N,cN,RN,H',q,t₁,z₁,s₁,p₁,v₁,w₁,e,g,f,hull,count,inside,fe,onto,fn,ff,fq,branch,cols,se,_,pg,gf,members,_,zero,agree,constants⟩ :=
    jt_complete_l hZFC hw source trans native P V q₀ O generic sh gn joint params sub (ZF.finite_countable_l I hZF hw finite) hq₀
  have bN := inside b₀.val ((entries b₀.val).mpr ⟨0,rfl⟩)
  have τN := inside τ.val ((entries τ.val).mpr ⟨1,rfl⟩)
  obtain ⟨o,empty,_⟩ := hw.1.1
  have bH := (members b₀.val).mpr ⟨root.1,o,q₀.val,zero o empty,root.2.1⟩
  obtain ⟨B,π,j,cB,RB,P',V',G,collapse⟩ := hull.collapse_l hZF hw source trans certificate count
  have result := collapse.real_pull_l hZF source trans native ω P V τ hw τN (fun p hp => (agree p hp).mp)
    generic O k ground value fy graph real
  have total i (hi : M.mem i ω.val) : ∃ n, M.mem n ω.val ∧ Nr_hit_d X P.val V.val b₀.val τ.val x f i n := by
    obtain ⟨z,hz,iz⟩ := real.2.1 i hi
    obtain ⟨p,hpN,hpH,force⟩ := result.2 b₀ bN bH i z iz
    obtain ⟨pP,n,r,nr,rp⟩ := (members p).mp hpH
    let i₀ : U.Domain := ⟨i,trans ω.val ω.property i hi⟩
    let z₀ : U.Domain := ⟨z,trans ω.val ω.property z hz⟩
    let p₂ : U.Domain := ⟨p,hull.submodel.subset p hpN⟩
    let r₂ : U.Domain := ⟨r,hull.submodel.subset r (fn.bound_l nr).2⟩
    have rP : U.mem r₂ P := member.mp (ff.bound_l nr).2
    have nz : r₂ ≠ P := fun eq => KP.mem_irrefl_d (ZF.modelsKP native) P (eq ▸ rP)
    exact ⟨n,(ff.bound_l nr).1,z,r,iz,nr,nr_edge_strengthen_l I source trans native P V b₀ τ i₀ z₀ p₂ r₂
      O (generic.proper b₀ hb).1 typed.2.2.1 (member.mp pP) ⟨rP,nz,(edge r₂ p₂ V).mpr rp⟩ force⟩
  obtain ⟨u',v',w',fu,fv,fw,run,selectB,selectT⟩ := nr_run_l hZF hw fe onto ff real bN τN root zero total
  obtain ⟨qe,qf⟩ := link.projections.compatible_l hZF cols se pg gf
  obtain ⟨q',h',t',z',fq',branch',cols'⟩ := link.tree.of_data_l hZF real (fn0_of_function_l (ZF.modelsKP hZF) fq)
    fu fv fw branch qe qf run
  have pH := (members p₀.val).mpr ⟨member.mpr (generic.proper p₀ hp₀).1,o,q₀.val,zero o empty,(edge q₀ p₀ V).mp q₀₀⟩
  obtain ⟨p',_,pp⟩ := collapse.collapse.function.2.1 p₀.val (inside p₀.val ((entries p₀.val).mpr ⟨2,rfl⟩))
  refine ⟨N,cN,RN,H',q,q',h',t',z',u',v',w',B,π,j,cB,RB,P',V',G,fq',branch',cols',fq,branch,hull,collapse,result.1,
    ⟨p',pp,(collapse.accepted_l hZF pp).mp pH⟩,?_,e,f,q₀,qe,qf,hq₀,
    ⟨(generic.proper q₀ hq₀).1,(generic.proper q₀ hq₀).2,q₀₀⟩,selectB,selectT,?_⟩
  · intro i z iz
    obtain ⟨z',_,zz⟩ := collapse.collapse.function.2.1 z (constants i z iz)
    exact ⟨z',zz,(collapse.inverse_entries z z').mpr zz⟩
  · exact fun o p empty op => (fn0_function_l (ZF.modelsKP hZF) ff).1.2 o p q₀.val op (zero o empty)

end YesMetaZFC.Model.Forcing.Internal
