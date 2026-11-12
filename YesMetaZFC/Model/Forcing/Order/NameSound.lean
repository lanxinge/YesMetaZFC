import YesMetaZFC.Model.Forcing.Order.NameComplete
import YesMetaZFC.Model.Forcing.Order.NameValue

/-! # 任意名字树分支的实际传递源及同一查询实数

名字分量与原联合分量通过实际字母投影读取同一枚举和条件列。
联合枝生成完整壳泛型，再将全部逐位检查送到同一传递坍塌，恢复原第一坐标。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.InnerModel SetTheory.Internal SetTheory.Descriptive
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Nr_link_d.sound_l {c X R u S L T E K Wₛ D J Ys ds hs Fs As Zg Yg dg hg lg rg Fg Ag C Z W Y a b c' d' l r F A
    de df Zn Wn Hn an bn cn dn ln rn Yn dx dh Fn An q' : M.Domain}
    (source : Smem_d I c X R) (trans : M.TransitiveSet X)
    (ω P V : (smdl_structure_l I (R := R) source.1.2.1).Domain)
    (hw : M.IsOmega ω.val) (certificate : Zc_model_d I ω.val c X R)
    (O : Cond_order_d (smdl_structure_l I (R := R) source.1.2.1) P V P)
    (sh : Sh_tree_d hZF ω.val c X R u S L T E K Wₛ D J Ys ds hs Fs As)
    (gn : Gn_tree_d hZF ω.val X P.val V.val Zg Yg dg hg lg rg Fg Ag)
    (joint : Jt_tree_d hZF ω.val X P.val C Ys Yg Zg Fs As Fg Ag ds dg hg lg Z W Y a b c' d' l r F A)
    (link : Nr_link_d hZF joint V.val de df Zn Wn Hn an bn cn dn ln rn Yn dx dh Fn An)
    (params : Jt_params_d ω.val X P.val V.val C) (fq' : M.IsSetFunctionFromTo I q' ω.val Yn) (branch' : Branch_d Fn An q') :
    ∃ x h' t' z' q u' v' w' N cN RN H B π j cB RB P' V' G,
      Fn0_d ω.val ω.val x ∧ Nr_cols_d hZF an bn cn dn ln rn dx dh q' x h' t' z' q u' v' w' ∧
      M.IsSetFunctionFromTo I q ω.val Y ∧ Branch_d F A q ∧ Gh_model_d hZF ω.val c X R N cN RN P.val V.val H ∧
      Gh_collapse_d hZF ω.val c X N cN P.val V.val H B π j cB RB P' V' G ∧
      Fn_bg_d B P' V' P' ω.val ω.val G x ∧
      ∀ i z, Entry_d M i z C → ∃ z', Rd_entry_d z z' π ∧ Rd_entry_d z' z j := by
  have native := ZFC.models_zf_l (certificate.native_l I hZF hw)
  obtain ⟨x,h',t',z',q,u',v',w',e,f,cols',fx,fq,fu,fv,fw,_,_,branch,qe,qf,run⟩ := link.tree.decode_l hZF hw fq' branch'
  obtain ⟨N,cN,RN,H,t,z,s,p,v,w,e₀,g,f₀,hull,count,fe,_,ff,cols,se,_,pg,gf,_,accepted,constants⟩ :=
    jt_model_l hZF hw source trans native P V O sh gn joint params fq branch
  obtain ⟨qe₀,qf₀⟩ := link.projections.compatible_l hZF cols se pg gf
  have eqe := qe₀.unique_l I hZF.1 qe
  subst e₀
  have eqf := qf₀.unique_l I hZF.1 qf
  subst f₀
  obtain ⟨B,π,j,cB,RB,P',V',G,collapse⟩ := hull.collapse_l hZF hw source trans certificate count
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,code,_⟩ :=
    nr_value_l hZF source trans native.1 ω P V hw collapse O fe ff fx fu fv fw accepted run
  refine ⟨x,h',t',z',q,u',v',w',N,cN,RN,H,B,π,j,cB,RB,P',V',G,fx,cols',fq,branch,hull,collapse,code,?_⟩
  intro i z iz
  obtain ⟨z',_,zz⟩ := collapse.collapse.function.2.1 z (constants i z iz)
  exact ⟨z',zz,(collapse.inverse_entries z z').mpr zz⟩

end YesMetaZFC.Model.Forcing.Internal
