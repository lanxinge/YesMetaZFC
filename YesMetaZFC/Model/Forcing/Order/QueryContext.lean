import YesMetaZFC.Model.Forcing.Order.QueryTree
import YesMetaZFC.Model.Forcing.Order.NameComplete
import YesMetaZFC.Model.Forcing.Ground.SourceExtension
import YesMetaZFC.Model.Forcing.Ground.QueryTree
import YesMetaZFC.Model.Forcing.Ground.GenericTree
import YesMetaZFC.Model.Forcing.Extension.Choice
import YesMetaZFC.Model.SetTheory.Reflection.ZfcTransfer
import YesMetaZFC.Model.Forcing.Order.QueryAttempt
import YesMetaZFC.Model.Forcing.Order.NameValue

/-! # 正负子树的分支恰为原名字枝加同一根判定

不增加新的无限坐标。有限节点及整枝的枚举、条件列由同两张投影读取，
函数限制唯一性保证根判定属于原来的查询名字。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.InnerModel SetTheory.Internal SetTheory.Descriptive
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Qs_tree_d.branch_l {φ : Formula 1 4} {sign : Bool}
    {ω X Q T A F₀ A₀ de df Z W H a b c d l r Y dx dh F S σ a₀ S' q x h t z s u v w e f : M.Domain}
    {base : Nr_tree_d hZF ω X Q T A F₀ A₀ de df Z W H a b c d l r Y dx dh F S}
    (tree : Qs_tree_d hZF φ sign base σ a₀ S') (hw : M.IsOmega ω)
    (fq : M.IsSetFunctionFromTo I q ω Y) (cols : Nr_cols_d hZF a b c d l r dx dh q x h t z s u v w)
    (se : Fseq_recode_d I de s e) (sf : Fseq_recode_d I df s f) :
    Branch_d F S' q ↔ Branch_d F S q ∧ Qs_at_d φ sign X Q T σ ω a₀ ω e f v w := by
  obtain ⟨_,_,fs,_,fv,fw⟩ := cols.functions_l hZF base.letters fq
  have fe := se.function_l I hZF base.enumeration fs
  have ff := sf.function_l I hZF base.conditions fs
  constructor
  · intro branch
    refine ⟨fun q₀ hq₀ sub => ((tree.nodes q₀).mp (branch q₀ hq₀ sub)).1,?_⟩
    apply qs_branch_l hZF hw
    intro n hn
    obtain ⟨q₀,fq₀,cut,_⟩ := ds_prefix_l I hZF hw fq hn
    have sub := (ds_restrict_iff_l I fq₀ fq.1).mp cut
    obtain ⟨_,m,x₀,h₀,t₀,z₀,s₀,u₀,v₀,w₀,e₀,f₀,_,typed,cols₀,se₀,sf₀,check⟩ :=
      (tree.nodes q₀).mp (branch q₀ ((base.sequences q₀).mpr ⟨n,hn,fq₀⟩) sub)
    have eq := typed.domain_eq_l hZF.1 (fn0_of_function_l (ZF.modelsKP hZF) fq₀)
    subst m
    obtain ⟨_,_,fs₀,_,fv₀,fw₀⟩ := cols₀.functions_l hZF base.letters fq₀
    have fe₀ := se₀.function_l I hZF base.enumeration fs₀
    have ff₀ := sf₀.function_l I hZF base.conditions fs₀
    obtain ⟨_,ss,_,vv,ww⟩ := cols₀.mono_l hZF cols sub
    exact ⟨e₀,f₀,v₀,w₀,check,(ds_restrict_iff_l I fe₀ fe.1).mpr (se₀.mono_l I se ss),
      (ds_restrict_iff_l I ff₀ ff.1).mpr (sf₀.mono_l I sf ss),
      (ds_restrict_iff_l I fv₀ fv.1).mpr vv,(ds_restrict_iff_l I fw₀ fw.1).mpr ww⟩
  · rintro ⟨branch,check⟩ q₀ hq₀ sub
    obtain ⟨n,hn,fq₀⟩ := (base.sequences q₀).mp hq₀
    obtain ⟨x₀,h₀,t₀,z₀,s₀,u₀,v₀,w₀,cols₀⟩ := base.letters.columns_l hZF fq₀
    obtain ⟨_,_,fs₀,_,_,_⟩ := cols₀.functions_l hZF base.letters fq₀
    obtain ⟨e₀,_,se₀⟩ := ZF.fseq_compose_l I hZF base.enumeration fs₀
    obtain ⟨f₀,_,sf₀⟩ := ZF.fseq_compose_l I hZF base.conditions fs₀
    obtain ⟨_,ss,_,vv,ww⟩ := cols₀.mono_l hZF cols sub
    have bound : M.MemberSubset n ω := by
      intro i hi
      obtain ⟨y,_,p,pair,hp⟩ := fq₀.2.2 i hi
      exact fq.input_mem_of_pairMember ⟨p,pair,sub p hp⟩
    exact (tree.nodes q₀).mpr ⟨branch q₀ hq₀ sub,n,x₀,h₀,t₀,z₀,s₀,u₀,v₀,w₀,e₀,f₀,hn,
      fn0_of_function_l (ZF.modelsKP hZF) fq₀,cols₀,se₀,sf₀,
      check.prefix_l bound (se₀.mono_l I se ss) (sf₀.mono_l I sf ss) vv ww⟩

end YesMetaZFC.Model.Forcing.Internal

/-! ## 原泛型接受的正负条件产生同一查询点的真实分支

指定名字和检查基准先进入共同壳；原条件列的零项同时加强该正负条件。
名字位置列始终选择同一对原对象，故整枝的根判定由原力迫的单调性给出。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.InnerModel SetTheory.Internal SetTheory.Descriptive
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Qs_tree_d.complete_l {φ : Formula 1 4} (hc : φ.FreeClosed) {sign : Bool}
    {c X R u S L T E K Wₛ D J Ys ds hs Fs As Zg Yg dg hg lg rg Fg Ag C Z W Y a b c' d' l r F A
      de df Zn Wn Hn an bn cn dn ln rn Yn dx dh Fn An Aq H x : M.Domain}
    (source : Smem_d I c X R) (trans : M.TransitiveSet X)
    (ω P V σ a₀ p₀ b₀ τ : (smdl_structure_l I (R := R) source.1.2.1).Domain)
    (hw : M.IsOmega ω.val) (certificate : Zc_model_d I ω.val c X R)
    (O : Cond_order_d (smdl_structure_l I (R := R) source.1.2.1) P V P)
    (generic : Generic_d (smdl_structure_l I (R := R) source.1.2.1) P V P (fun q => M.mem q.val H))
    (sh : Sh_tree_d hZF ω.val c X R u S L T E K Wₛ D J Ys ds hs Fs As)
    (gn : Gn_tree_d hZF ω.val X P.val V.val Zg Yg dg hg lg rg Fg Ag)
    (joint : Jt_tree_d hZF ω.val X P.val C Ys Yg Zg Fs As Fg Ag ds dg hg lg Z W Y a b c' d' l r F A)
    (link : Nr_link_d hZF joint V.val de df Zn Wn Hn an bn cn dn ln rn Yn dx dh Fn An)
    (tree : Qs_tree_d hZF φ sign link.tree σ.val a₀.val Aq)
    (params : Jt_params_d ω.val X P.val V.val C) (hp₀ : M.mem p₀.val H) (hb : M.mem b₀.val H)
    (real : Fn0_d ω.val ω.val x)
    (named : Fn_value_d (ZFC.models_zf_l (certificate.native_l I hZF hw)) Subtype.val P V P ω τ (fun p => M.mem p.val H) x)
    (name : Name_d (smdl_structure_l I (R := R) source.1.2.1) P σ)
    (force : Qs_force_d φ sign P V σ ω a₀ τ b₀ p₀) :
    ∃ N cN RN H' q q' h' t' z' u' v' w' B π j cB RB P' V' G,
      M.IsSetFunctionFromTo I q' ω.val Yn ∧ Branch_d Fn Aq q' ∧
      Nr_cols_d hZF an bn cn dn ln rn dx dh q' x h' t' z' q u' v' w' ∧
      M.IsSetFunctionFromTo I q ω.val Y ∧ Branch_d F A q ∧ Gh_model_d hZF ω.val c X R N cN RN P.val V.val H' ∧
      Gh_collapse_d hZF ω.val c X N cN P.val V.val H' B π j cB RB P' V' G ∧
      Fn_bg_d B P' V' P' ω.val ω.val G x ∧ (∃ p, Rd_entry_d p₀.val p π ∧ M.mem p G) ∧
      ∀ i z, Entry_d M i z C → ∃ z', Rd_entry_d z z' π ∧ Rd_entry_d z' z j := by
  let U := smdl_structure_l I (R := R) source.1.2.1
  have native := ZFC.models_zf_l (certificate.native_l I hZF hw)
  have nτ : Name_d U P τ := by
    obtain ⟨_,_,value,_⟩ := named
    exact qval_name_l value
  obtain ⟨N,cN,RN,H',q,q',h',t',z',u',v',w',B,π,j,cB,RB,P',V',G,
      fq',branch',cols,fq,branch,hull,collapse,code,accept,constants,e,f,q₀,se,sf,_,below,baseIndex,nameIndex,zero⟩ :=
    link.complete_l hZFC source trans ω P V p₀ b₀ τ hw certificate O generic sh gn joint params hp₀ hb real named
  have root := (qs_check_read_l I source trans native.1 hc sign P V σ ω a₀ b₀ τ q₀).mpr
    (force.strengthen_l native O hc (generic.proper b₀ hb).1 name nτ (generic.proper p₀ hp₀).1 below)
  have signed : Qs_at_d φ sign X P.val V.val σ.val ω.val a₀.val ω.val e f v' w' := by
    intro o i j p b τ' _ _ _ empty oi oj ib jτ op
    exact (baseIndex o i b oi ib).symm ▸ (nameIndex o j τ' oj jτ).symm ▸ (zero o p empty op).symm ▸ root
  exact ⟨N,cN,RN,H',q,q',h',t',z',u',v',w',B,π,j,cB,RB,P',V',G,
    fq',(tree.branch_l hZF hw fq' cols se sf).mpr ⟨branch',signed⟩,cols,fq,branch,hull,collapse,code,accept,constants⟩

end YesMetaZFC.Model.Forcing.Internal

/-! ## 同一大泛型扩张中原正负树的实际分支

原模型的名字和接受条件沿其规范呈示同构搬运，背景泛型则取扩张中的
实际滤子集合。全部有限树、登记和内部 ZFC 证书均由规范像保持，随后
直接使用原构枝定理。所得分支属于原树的像，第一坐标仍是给定实数。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.InnerModel SetTheory.Internal SetTheory.Descriptive
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Qs_tree_d.extension_complete_l {φ : Formula 1 4} (hc : φ.FreeClosed) {sign : Bool}
    {c X R u S L T E K Wₛ D J Ys ds hs Fs As Zg Yg dg hg lg rg Fg Ag C Z W Y a b c' d' l r F A
      de df Zn Wn Hn an bn cn dn ln rn Yn dx dh Fn An Aq : M.Domain}
    (source : Smem_d I c X R) (trans : M.TransitiveSet X)
    (ω P V σ a₀ p₀ b₀ τ : (smdl_structure_l I (R := R) source.1.2.1).Domain)
    (hw : M.IsOmega ω.val) (certificate : Zc_model_d I ω.val c X R)
    (O : Cond_order_d (smdl_structure_l I (R := R) source.1.2.1) P V P)
    {H : M.Domain → Prop} (generic : Generic_d M P.val V.val P.val H)
    (j : M.Domain → (extension_l M hZF P.val V.val P.val H).Domain) (ji : Function.Injective j)
    (jf : ∀ z y, y ∈ j z ↔ ∃ t, M.mem t z ∧ j t = y)
    (ground : ∀ z, Gval_d M P.val V.val P.val H z (j z))
    (sh : Sh_tree_d hZF ω.val c X R u S L T E K Wₛ D J Ys ds hs Fs As)
    (gn : Gn_tree_d hZF ω.val X P.val V.val Zg Yg dg hg lg rg Fg Ag)
    (joint : Jt_tree_d hZF ω.val X P.val C Ys Yg Zg Fs As Fg Ag ds dg hg lg Z W Y a b c' d' l r F A)
    (link : Nr_link_d hZF joint V.val de df Zn Wn Hn an bn cn dn ln rn Yn dx dh Fn An)
    (tree : Qs_tree_d hZF φ sign link.tree σ.val a₀.val Aq)
    (params : Jt_params_d ω.val X P.val V.val C) (hp₀ : H p₀.val) (hb : H b₀.val)
    {x : (extension_l M hZF P.val V.val P.val H).Domain} (real : Fn0_d (j ω.val) (j ω.val) x)
    (named : Fn_value_d (ZFC.models_zf_l (certificate.native_l I hZF hw)) (j ∘ Subtype.val)
      P V P ω τ (H ∘ Subtype.val) x)
    (name : Name_d (smdl_structure_l I (R := R) source.1.2.1) P σ)
    (force : Qs_force_d φ sign P V σ ω a₀ τ b₀ p₀) :
    let U := extension_l M hZF P.val V.val P.val H
    ∃ q : U.Domain, Fn0_d (j ω.val) (j Yn) q ∧ Branch_d (j Fn) (j Aq) q ∧
      ∀ i v, Entry_d U i v x ↔ ∃ z t, Entry_d U i z q ∧ KPair_d U z v t := by
  let N := smdl_structure_l I (R := R) source.1.2.1
  let U := extension_l M hZF P.val V.val P.val H
  have native := ZFC.models_zf_l (certificate.native_l I hZF hw)
  have ni : Function.Injective (Subtype.val : N.Domain → M.Domain) := fun _ _ eq => Subtype.ext eq
  have nf := smem_full_l I source trans
  have O' := image_cond_order_l (ZF.modelsKP native) hZF.1 Subtype.val ni nf O
  have hUZFC := preserves_zfc_l O' hZFC generic
  have hU := ZFC.models_zf_l hUZFC
  have hw' : U.IsOmega (j ω.val) := image_omega_l (hEN := hU.1) j ji jf hZF
    (internal_foundation_l O' hZF generic) hw (fun D => KP.difference_exists_d (ZF.modelsKP hU) D (j ω.val))
  obtain ⟨source',trans',native',G,_,e,point,onto,elem,trace,g,values⟩ :=
    Smem_d.extension_source_l hZF source trans native O generic j ji jf ground
  let N' := smdl_structure_l (kp_pair_l (ZF.modelsKP hU)) (R := j R) source'.1.2.1
  let f : N.Domain → N'.Domain := fun a => ⟨j a.val,(image_member_l j ji jf).mpr a.property⟩
  have eq : e = f := funext fun a => Subtype.ext (point a)
  subst e
  -- 同构只发生在原集合模型及其规范呈示之间；原查询名字仍为 f τ。
  have O'' := em_order_l native.1 native'.1 f elem O
  have named' := values ω τ x named
  have force' := force.image_l native.1 native'.1 f elem hc
  have name' := (em_name_l native.1 native'.1 f elem).mp name
  have certificate' := image_zc_model_l j ji jf hZF hU hw hw' certificate
  -- 原有限节点及内部证书全部搬运，允许在目标中构造新的无限枝。
  have sh' := image_sh_tree_l hZF hU j ji jf hw hw' sh
  have gn' := image_gn_tree_l j ji jf hZF hU hw hw' gn
  have joint' := image_jt_tree_l hZF hU j ji jf hw hw' joint
  have link' := image_nr_link_l hZF hU j ji jf hw hw' joint link
  have tree' := image_qs_tree_l hZF hU j ji jf hc hw hw' tree
  have params' := image_jt_params_l hZF hU j ji jf params
  obtain ⟨_,_,_,_,_,q,_,_,_,_,_,_,_,_,_,_,_,_,_,_,fq,branch,cols,_⟩ :=
    tree'.complete_l hUZFC hc source' trans' (f ω) (f P) (f V) (f σ) (f a₀) (f p₀) (f b₀) (f τ)
      hw' certificate' O'' g sh' gn' joint' link' params' ((trace p₀).mpr hp₀) ((trace b₀).mpr hb)
      real named' name' force'
  refine ⟨q,fn0_of_function_l (ZF.modelsKP hU) fq,branch,fun i v => (cols.query.2 i v).trans ?_⟩
  -- 第一坐标是字母的实际左坐标，直接满足截面秩反射所用的投影方程。
  constructor
  · rintro ⟨z,iz,zv⟩
    have hz := fq.output_mem_of_pairMember iz
    obtain ⟨a,_,t,_,pair⟩ := (link'.tree.letters.product z).mp hz
    have za := (link'.tree.letters.read z a t hz pair).1
    have eq := link'.tree.letters.query.1.2 z a v za zv
    exact ⟨z,t,iz,eq ▸ pair⟩
  · rintro ⟨z,t,iz,pair⟩
    exact ⟨z,iz,(link'.tree.letters.read z v t (fq.output_mem_of_pairMember iz) pair).1⟩

end YesMetaZFC.Model.Forcing.Internal

/-! ## 正负根判定反射到读取原查询的同一坍塌泛型

根基准、名字、判定条件均来自原名字运行，沿同一返回初等图反射。
固定参数使用该图的实际原像；不在坍塌后另选名字或另造泛型。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.InnerModel SetTheory.Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem qs_value_l {φ : Formula 1 4} (hc : φ.FreeClosed) {sign : Bool}
    {c X R N d H B π j cB RB P' V' G e f x u v w : M.Domain}
    (source : Smem_d I c X R) (trans : M.TransitiveSet X)
    (native : Extensional (smdl_structure_l I (R := R) source.1.2.1))
    (ω P V σ a₀ : (smdl_structure_l I (R := R) source.1.2.1).Domain) (hw : M.IsOmega ω.val)
    (h : Gh_collapse_d hZF ω.val c X N d P.val V.val H B π j cB RB P' V' G)
    (O : Cond_order_d (smdl_structure_l I (R := R) source.1.2.1) P V P)
    (fe : Fn0_d ω.val N e) (ff : Fn0_d ω.val N f) (fx : Fn0_d ω.val ω.val x)
    (fu : Fn0_d ω.val ω.val u) (fv : Fn0_d ω.val ω.val v) (fw : Fn0_d ω.val ω.val w)
    (accepted : ∀ i p, Rd_entry_d i p f → M.mem p H) (run : Nr_at_d ω.val X P.val V.val ω.val e f x u v w)
    (signed : Qs_at_d φ sign X P.val V.val σ.val ω.val a₀.val ω.val e f v w)
    (σ' a' : (smdl_structure_l I (R := RB) h.model.1.2.1).Domain)
    (imageσ : Rd_entry_d σ.val σ'.val π) (imagea : Rd_entry_d a₀.val a'.val π) :
    let C := smdl_structure_l I (R := RB) h.model.1.2.1
    let hC := ZFC.models_zf_l (h.theory.native_l I hZF hw)
    let p : C.Domain := ⟨P',(h.collapse.function.bound_l h.conditions).2⟩
    let t : C.Domain := ⟨V',(h.collapse.function.bound_l h.order).2⟩
    ∃ hwB : M.mem ω.val B, ∃ τ' b' p' : C.Domain, M.mem b'.val G ∧ M.mem p'.val G ∧
      Qs_force_d φ sign p t σ' ⟨ω.val,hwB⟩ a' τ' b' p' ∧
      Fn_value_d hC Subtype.val p t p ⟨ω.val,hwB⟩ τ' (fun p => M.mem p.val G) x := by
  let L := smdl_structure_l I (R := R) source.1.2.1
  let C := smdl_structure_l I (R := RB) h.model.1.2.1
  have small := ZFC.models_zf_l (h.theory.native_l I hZF hw)
  obtain ⟨o,i,k,b,τ,p₀,empty,oi,ok,ib,kτ,op,_,hwB,τ',ττ,named,b',p',bb,pp,bG,pG⟩ :=
    nr_value_l hZF source trans native ω P V hw h O fe ff fx fu fv fw accepted run
  let Ω : C.Domain := ⟨ω.val,hwB⟩
  let P₁ : C.Domain := ⟨P',(h.collapse.function.bound_l h.conditions).2⟩
  let V₁ : C.Domain := ⟨V',(h.collapse.function.bound_l h.order).2⟩
  have root := signed o i k p₀ b τ (fv.bound_l oi).1 (fv.bound_l oi).2 (fw.bound_l ok).2 empty oi ok ib kτ op
  obtain ⟨g,elem,values⟩ := h.embedding.project_l I hZF hw h.model.1 source.1
  have point (z : C.Domain) (y : M.Domain) (yz : Rd_entry_d y z.val π) : (g z).val = y :=
    h.embedding.1.1.1.2 _ _ _ (values z) ((h.inverse_entries y z.val).mpr yz)
  have gP : g P₁ = P := Subtype.ext (point P₁ P.val h.conditions)
  have gV : g V₁ = V := Subtype.ext (point V₁ V.val h.order)
  have gσ : g σ' = σ := Subtype.ext (point σ' σ.val imageσ)
  have ga : g a' = a₀ := Subtype.ext (point a' a₀.val imagea)
  have gΩ : g Ω = ω := Subtype.ext (h.embedding.1.1.1.2 _ _ _ (values Ω)
    (h.embedding.omega_l I hZF hw h.transitive trans h.model source hwB))
  let ρ : Env C 8 := ⟨fun i => [P₁,V₁,σ',Ω,a',τ',b',p'].get i,fun _ => σ'⟩
  have old : Formula.satisfies (image_env_l g ρ) (qs_force0_m φ sign) := by
    apply (qs_force_sat_l native hc sign _ (.bound 0) (.bound 1) (.bound 2) (.bound 3) (.bound 4) (.bound 5) (.bound 6) (.bound 7)).mpr
    change Qs_force_d φ sign (g P₁) (g V₁) (g σ') (g Ω) (g a') (g τ') (g b') (g p')
    rw [gP,gV,gσ,gΩ,ga]
    exact (qs_check_read_l I source trans native hc sign P V σ ω a₀ (g b') (g τ') (g p')).mp
      (by simpa only [point b' b bb,point τ' τ ττ,point p' p₀ pp] using root)
  exact ⟨hwB,τ',b',p',bG,pG,
    (qs_force_sat_l small.1 hc sign ρ (.bound 0) (.bound 1) (.bound 2) (.bound 3) (.bound 4) (.bound 5) (.bound 6) (.bound 7)).mp
      ((elem (qs_force0_m φ sign) (qs_force0_closed_l hc sign) ρ).mpr old),named⟩

end YesMetaZFC.Model.Forcing.Internal

/-! ## 任意正负枝生成保持原查询的传递源和被接受判定

固定参数的登记保证它们进入分支的同一初等壳。实际坍塌后，完整名字图和
正负根条件共用同一个查询名字、检查基准及壳泛型。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.InnerModel SetTheory.Internal SetTheory.Descriptive
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Qs_tree_d.sound_l {φ : Formula 1 4} (hc : φ.FreeClosed) {sign : Bool}
    {c X R u S L T E K Wₛ D J Ys ds hs Fs As Zg Yg dg hg lg rg Fg Ag C Z W Y a b c' d' l r F A
      de df Zn Wn Hn an bn cn dn ln rn Yn dx dh Fn An Aq q' : M.Domain}
    (source : Smem_d I c X R) (trans : M.TransitiveSet X)
    (ω P V σ a₀ : (smdl_structure_l I (R := R) source.1.2.1).Domain)
    (hw : M.IsOmega ω.val) (certificate : Zc_model_d I ω.val c X R)
    (O : Cond_order_d (smdl_structure_l I (R := R) source.1.2.1) P V P)
    (sh : Sh_tree_d hZF ω.val c X R u S L T E K Wₛ D J Ys ds hs Fs As)
    (gn : Gn_tree_d hZF ω.val X P.val V.val Zg Yg dg hg lg rg Fg Ag)
    (joint : Jt_tree_d hZF ω.val X P.val C Ys Yg Zg Fs As Fg Ag ds dg hg lg Z W Y a b c' d' l r F A)
    (link : Nr_link_d hZF joint V.val de df Zn Wn Hn an bn cn dn ln rn Yn dx dh Fn An)
    (tree : Qs_tree_d hZF φ sign link.tree σ.val a₀.val Aq)
    (params : Jt_params_d ω.val X P.val V.val C)
    (σC : ∃ i, Rd_entry_d i σ.val C) (aC : ∃ i, Rd_entry_d i a₀.val C)
    (fq' : M.IsSetFunctionFromTo I q' ω.val Yn) (branch' : Branch_d Fn Aq q') :
    ∃ x h' t' z' q u' v' w' N cN RN H B π j cB RB P' V' G,
      Fn0_d ω.val ω.val x ∧ Nr_cols_d hZF an bn cn dn ln rn dx dh q' x h' t' z' q u' v' w' ∧
      M.IsSetFunctionFromTo I q ω.val Y ∧ Branch_d F A q ∧ Gh_model_d hZF ω.val c X R N cN RN P.val V.val H ∧
      ∃ collapse : Gh_collapse_d hZF ω.val c X N cN P.val V.val H B π j cB RB P' V' G,
        (∀ i z, Entry_d M i z C → ∃ z', Rd_entry_d z z' π ∧ Rd_entry_d z' z j) ∧
        let U := smdl_structure_l I (R := RB) collapse.model.1.2.1
        let hU := ZFC.models_zf_l (collapse.theory.native_l I hZF hw)
        let p : U.Domain := ⟨P',(collapse.collapse.function.bound_l collapse.conditions).2⟩
        let t : U.Domain := ⟨V',(collapse.collapse.function.bound_l collapse.order).2⟩
        ∃ hwB : M.mem ω.val B, ∃ σ' a' τ' b' p' : U.Domain,
          Rd_entry_d σ.val σ'.val π ∧ Rd_entry_d a₀.val a'.val π ∧ M.mem b'.val G ∧ M.mem p'.val G ∧
          Qs_force_d φ sign p t σ' ⟨ω.val,hwB⟩ a' τ' b' p' ∧
          Fn_value_d hU Subtype.val p t p ⟨ω.val,hwB⟩ τ' (fun p => M.mem p.val G) x := by
  have native := ZFC.models_zf_l (certificate.native_l I hZF hw)
  have base : Branch_d Fn An q' := fun q hq sub => ((tree.nodes q).mp (branch' q hq sub)).1
  obtain ⟨x,h',t',z',q,u',v',w',e,f,cols',fx,fq,fu,fv,fw,_,_,branch,qe,qf,run⟩ := link.tree.decode_l hZF hw fq' base
  have signed := ((tree.branch_l hZF hw fq' cols' qe qf).mp branch').2
  obtain ⟨N,cN,RN,H,t,z,s,p,v,w,e₀,g,f₀,hull,count,fe,_,ff,cols,se,_,pg,gf,_,accepted,constants⟩ :=
    jt_model_l hZF hw source trans native P V O sh gn joint params fq branch
  obtain ⟨qe₀,qf₀⟩ := link.projections.compatible_l hZF cols se pg gf
  have eqe := qe₀.unique_l I hZF.1 qe
  subst e₀
  have eqf := qf₀.unique_l I hZF.1 qf
  subst f₀
  obtain ⟨B,π,j,cB,RB,P',V',G,collapse⟩ := hull.collapse_l hZF hw source trans certificate count
  obtain ⟨i,iσ⟩ := σC
  obtain ⟨k,ka⟩ := aC
  obtain ⟨σ',hσ',imageσ⟩ := collapse.collapse.function.2.1 σ.val (constants i σ.val iσ)
  obtain ⟨a',ha',imagea⟩ := collapse.collapse.function.2.1 a₀.val (constants k a₀.val ka)
  obtain ⟨hwB,τ',b',p',bG,pG,force,named⟩ := qs_value_l hZF hc source trans native.1 ω P V σ a₀ hw collapse O
    fe ff fx fu fv fw accepted run signed ⟨σ',hσ'⟩ ⟨a',ha'⟩ imageσ imagea
  refine ⟨x,h',t',z',q,u',v',w',N,cN,RN,H,B,π,j,cB,RB,P',V',G,fx,cols',fq,branch,hull,collapse,?_,
    hwB,⟨σ',hσ'⟩,⟨a',ha'⟩,τ',b',p',imageσ,imagea,bG,pG,force,named⟩
  intro i z iz
  obtain ⟨z',_,zz⟩ := collapse.collapse.function.2.1 z (constants i z iz)
  exact ⟨z',zz,(collapse.inverse_entries z z').mpr zz⟩

end YesMetaZFC.Model.Forcing.Internal

/-! ## 固定参数下同时构造正负两棵实际树

Woodin 序列、规范实数并名字和收益参数均先登记。两棵树共用同一联合树、
同一名字树和第一坐标，只在根力迫断言的符号上不同。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.InnerModel SetTheory.Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem qs_context_l {φ : Formula 1 4} (hc : φ.FreeClosed)
    {ω c X R u S L T E K Wₛ D J Ys ds hs Fs As Zg Yg dg hg lg rg Fg Ag P V B A₀ σ a₀ : M.Domain}
    (hw : M.IsOmega ω) (sh : Sh_tree_d hZF ω c X R u S L T E K Wₛ D J Ys ds hs Fs As)
    (gn : Gn_tree_d hZF ω X P V Zg Yg dg hg lg rg Fg Ag)
    (hP : M.mem P X) (hV : M.mem V X) (hA : M.mem A₀ X) (hσ : M.mem σ X) (ha₀ : M.mem a₀ X) (fb : Fn0_d ω X B) :
    ∃ C, Jt_params_d ω X P V C ∧ (∃ i, Rd_entry_d i A₀ C) ∧ (∃ i, Rd_entry_d i σ C) ∧ (∃ i, Rd_entry_d i a₀ C) ∧
      (∀ i x, Rd_entry_d i x B → ∃ k, Rd_entry_d k x C) ∧
      ∃ Z W Y a b c' d' l r F A, ∃ joint : Jt_tree_d hZF ω X P C Ys Yg Zg Fs As Fg Ag ds dg hg lg Z W Y a b c' d' l r F A,
      ∃ de df Zn Wn Hn an bn cn dn ln rn Yn dx dh Fn An,
      ∃ link : Nr_link_d hZF joint V de df Zn Wn Hn an bn cn dn ln rn Yn dx dh Fn An,
      ∃ positive negative, Qs_tree_d hZF φ true link.tree σ a₀ positive ∧ Qs_tree_d hZF φ false link.tree σ a₀ negative := by
  let params : Fin 3 → M.Domain := fun i => [A₀,σ,a₀].get i
  obtain ⟨C,registered,points,cover⟩ := jt_params_finite_l hZF hw hP hV fb params
    (Fin.cases hA (Fin.cases hσ (Fin.cases ha₀ (fun i => Fin.elim0 i))))
  obtain ⟨Z,W,Y,a,b,c',d',l,r,F,A,joint⟩ := jt_tree_l hZF (C := C) hw sh.left gn.left gn.right gn.condition
    sh.sequences gn.sequences sh.tree gn.tree
  obtain ⟨de,df,Zn,Wn,Hn,an,bn,cn,dn,ln,rn,Yn,dx,dh,Fn,An,link⟩ := nr_link_l hZF hw joint V
  obtain ⟨positive,pos⟩ := qs_tree_l hZF hc true link.tree σ a₀
  obtain ⟨negative,neg⟩ := qs_tree_l hZF hc false link.tree σ a₀
  exact ⟨C,registered,points 0,points 1,points 2,cover,Z,W,Y,a,b,c',d',l,r,F,A,joint,
    de,df,Zn,Wn,Hn,an,bn,cn,dn,ln,rn,Yn,dx,dh,Fn,An,link,positive,negative,pos,neg⟩

end YesMetaZFC.Model.Forcing.Internal
