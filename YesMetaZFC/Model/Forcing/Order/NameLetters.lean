import YesMetaZFC.Model.SetTheory.Internal.ClosureLetters
import YesMetaZFC.Model.SetTheory.Internal.Registration
import YesMetaZFC.SetTheory.Card.FiniteSequenceComposition

/-! # 两条见证列和两张登记表的实际配对字母

字母为 (A×B)×(ω×ω)。三次已有配对构造给出六张投影图；任意同长度的
四张实际函数图合成一条字母列。坐标图形及其前缀包含关系统一保存。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.InnerModel SetTheory.Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

structure Jt_letters_d (ω A B Z W Y a b c d l r : M.Domain) : Prop where
  pair₁ : M.IsCartesianProduct I Z A B
  pair₂ : M.IsCartesianProduct I W ω ω
  pair₃ : M.IsCartesianProduct I Y Z W
  a_fn : M.IsSetFunctionFromTo I a Y Z
  b_fn : M.IsSetFunctionFromTo I b Y W
  c_fn : M.IsSetFunctionFromTo I c Z A
  d_fn : M.IsSetFunctionFromTo I d Z B
  l_fn : M.IsSetFunctionFromTo I l W ω
  r_fn : M.IsSetFunctionFromTo I r W ω
  read₁ : ∀ z x y, M.mem z Z → KPair_d M z x y → Rd_entry_d z x c ∧ Rd_entry_d z y d
  read₂ : ∀ z i j, M.mem z W → KPair_d M z i j → Rd_entry_d z i l ∧ Rd_entry_d z j r
  read₃ : ∀ z x y, M.mem z Y → KPair_d M z x y → Rd_entry_d z x a ∧ Rd_entry_d z y b

structure Jt_cols_d (a b c d l r q t z s p v w : M.Domain) : Prop where
  qt : Fseq_recode_d I a q t
  qz : Fseq_recode_d I b q z
  ts : Fseq_recode_d I c t s
  tp : Fseq_recode_d I d t p
  zv : Fseq_recode_d I l z v
  zw : Fseq_recode_d I r z w

def jt_cols_m {n} (a b c d l r q t z s p v w : Term n) : Formula 1 n :=
  .conj (fseq_recode_m (𝒞 := kpair_convention_l) a q t) (.conj (fseq_recode_m (𝒞 := kpair_convention_l) b q z)
    (.conj (fseq_recode_m (𝒞 := kpair_convention_l) c t s) (.conj (fseq_recode_m (𝒞 := kpair_convention_l) d t p)
      (.conj (fseq_recode_m (𝒞 := kpair_convention_l) l z v) (fseq_recode_m (𝒞 := kpair_convention_l) r z w)))))
derive_free_closed jt_cols_m

theorem jt_cols_sat_l {n} (ρ : Env M n) (a b c d l r q t z s p v w : Term n) :
    Formula.satisfies ρ (jt_cols_m a b c d l r q t z s p v w) ↔
      Jt_cols_d hZF (a.eval ρ) (b.eval ρ) (c.eval ρ) (d.eval ρ) (l.eval ρ) (r.eval ρ)
        (q.eval ρ) (t.eval ρ) (z.eval ρ) (s.eval ρ) (p.eval ρ) (v.eval ρ) (w.eval ρ) := by
  simp only [jt_cols_m,Formula.satisfies_conj_iff,fseq_recode_sat_l I]
  exact ⟨fun ⟨a,b,c,d,e,f⟩ => ⟨a,b,c,d,e,f⟩,fun h => ⟨h.qt,h.qz,h.ts,h.tp,h.zv,h.zw⟩⟩

theorem jt_letters_l (ω A B : M.Domain) : ∃ Z W Y a b c d l r, Jt_letters_d hZF ω A B Z W Y a b c d l r := by
  obtain ⟨Z,pair₁⟩ := ZF.exists_cartesianProduct hZF I A B
  obtain ⟨W,pair₂⟩ := ZF.exists_cartesianProduct hZF I ω ω
  obtain ⟨Y,pair₃⟩ := ZF.exists_cartesianProduct hZF I Z W
  obtain ⟨c,d,fc,fd,read₁⟩ := cl_pair_maps_l hZF pair₁
  obtain ⟨l,r,fl,fr,read₂⟩ := cl_pair_maps_l hZF pair₂
  obtain ⟨a,b,fa,fb,read₃⟩ := cl_pair_maps_l hZF pair₃
  exact ⟨Z,W,Y,a,b,c,d,l,r,pair₁,pair₂,pair₃,fa,fb,fc,fd,fl,fr,read₁,read₂,read₃⟩

theorem Jt_cols_d.functions_l {ω A B Z W Y a b c d l r n q t z s p v w : M.Domain}
    (letters : Jt_letters_d hZF ω A B Z W Y a b c d l r) (fq : M.IsSetFunctionFromTo I q n Y)
    (cols : Jt_cols_d hZF a b c d l r q t z s p v w) :
    M.IsSetFunctionFromTo I t n Z ∧ M.IsSetFunctionFromTo I z n W ∧ M.IsSetFunctionFromTo I s n A ∧
      M.IsSetFunctionFromTo I p n B ∧ M.IsSetFunctionFromTo I v n ω ∧ M.IsSetFunctionFromTo I w n ω := by
  have ft := cols.qt.function_l I hZF letters.a_fn fq
  have fz := cols.qz.function_l I hZF letters.b_fn fq
  exact ⟨ft,fz,cols.ts.function_l I hZF letters.c_fn ft,cols.tp.function_l I hZF letters.d_fn ft,
    cols.zv.function_l I hZF letters.l_fn fz,cols.zw.function_l I hZF letters.r_fn fz⟩

theorem Jt_cols_d.mono_l {a b c d l r q t z s p v w q' t' z' s' p' v' w' : M.Domain}
    (cols : Jt_cols_d hZF a b c d l r q t z s p v w) (cols' : Jt_cols_d hZF a b c d l r q' t' z' s' p' v' w')
    (sub : M.MemberSubset q q') : M.MemberSubset t t' ∧ M.MemberSubset z z' ∧ M.MemberSubset s s' ∧
      M.MemberSubset p p' ∧ M.MemberSubset v v' ∧ M.MemberSubset w w' := by
  have tt := cols.qt.mono_l I cols'.qt sub
  have zz := cols.qz.mono_l I cols'.qz sub
  exact ⟨tt,zz,cols.ts.mono_l I cols'.ts tt,cols.tp.mono_l I cols'.tp tt,cols.zv.mono_l I cols'.zv zz,cols.zw.mono_l I cols'.zw zz⟩

theorem Jt_cols_d.unique_l {a b c d l r q t z s p v w t' z' s' p' v' w' : M.Domain}
    (cols : Jt_cols_d hZF a b c d l r q t z s p v w) (cols' : Jt_cols_d hZF a b c d l r q t' z' s' p' v' w') :
    t = t' ∧ z = z' ∧ s = s' ∧ p = p' ∧ v = v' ∧ w = w' := by
  have eq := cols.qt.unique_l I hZF.1 cols'.qt
  subst t'
  have eq := cols.qz.unique_l I hZF.1 cols'.qz
  subst z'
  exact ⟨rfl,rfl,cols.ts.unique_l I hZF.1 cols'.ts,cols.tp.unique_l I hZF.1 cols'.tp,
    cols.zv.unique_l I hZF.1 cols'.zv,cols.zw.unique_l I hZF.1 cols'.zw⟩

theorem Jt_letters_d.columns_l {ω A B Z W Y a b c d l r n q : M.Domain}
    (letters : Jt_letters_d hZF ω A B Z W Y a b c d l r) (fq : M.IsSetFunctionFromTo I q n Y) :
    ∃ t z s p v w, Jt_cols_d hZF a b c d l r q t z s p v w := by
  obtain ⟨t,ft,qt⟩ := ZF.fseq_compose_l I hZF letters.a_fn fq
  obtain ⟨z,fz,qz⟩ := ZF.fseq_compose_l I hZF letters.b_fn fq
  obtain ⟨s,_,ts⟩ := ZF.fseq_compose_l I hZF letters.c_fn ft
  obtain ⟨p,_,tp⟩ := ZF.fseq_compose_l I hZF letters.d_fn ft
  obtain ⟨v,_,zv⟩ := ZF.fseq_compose_l I hZF letters.l_fn fz
  obtain ⟨w,_,zw⟩ := ZF.fseq_compose_l I hZF letters.r_fn fz
  exact ⟨t,z,s,p,v,w,qt,qz,ts,tp,zv,zw⟩

theorem Jt_letters_d.word_l {ω A B Z W Y a b c d l r n s p v w : M.Domain}
    (letters : Jt_letters_d hZF ω A B Z W Y a b c d l r)
    (fs : Fn0_d n A s) (fp : Fn0_d n B p) (fv : Fn0_d n ω v) (fw : Fn0_d n ω w) :
    ∃ q t z, M.IsSetFunctionFromTo I q n Y ∧ Jt_cols_d hZF a b c d l r q t z s p v w := by
  obtain ⟨t,ft,ts,tp⟩ := cl_pair_word_l hZF letters.pair₁ letters.c_fn letters.d_fn letters.read₁ fs fp
  obtain ⟨z,fz,zv,zw⟩ := cl_pair_word_l hZF letters.pair₂ letters.l_fn letters.r_fn letters.read₂ fv fw
  obtain ⟨q,fq,qt,qz⟩ := cl_pair_word_l hZF letters.pair₃ letters.a_fn letters.b_fn letters.read₃
    (fn0_of_function_l (ZF.modelsKP hZF) ft) (fn0_of_function_l (ZF.modelsKP hZF) fz)
  exact ⟨q,t,z,fq,qt,qz,ts,tp,zv,zw⟩

end YesMetaZFC.Model.Forcing.Internal

/-! ## 共享枚举、条件登记及常量登记的实际联合树

两个分量节点使用同一个有限枚举图。第一张位置表登记条件列，第二张位置表
登记固定参数列。通过原公式分离构造树；前缀时两侧枚举的限制唯一性保持共享。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.InnerModel SetTheory.Internal SetTheory.Descriptive
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

def Jt_word_d (ω Y As Ag ds dg hg lg a b c d l r C q : M.Domain) : Prop := ∃ n t z s p v w e g f,
  M.mem n ω ∧ Fn0_d n Y q ∧ Jt_cols_d hZF a b c d l r q t z s p v w ∧ M.mem s As ∧ M.mem p Ag ∧
    Fseq_recode_d I ds s e ∧ Fseq_recode_d I dg p e ∧ Fseq_recode_d I hg p g ∧ Fseq_recode_d I lg g f ∧
      Rg_at_d n e f v ∧ Rg_at_d n e C w

def jt_word_m {m} (ω Y As Ag ds dg hg lg a b c d l r C q : Term m) : Formula 1 m := set[m] ⟪∃ n t z s p v w e g f,
  n ∈ ⌜ω⌝ₛ ∧ ⌜fn0_m⌝ₚ(n,⌜Y⌝ₛ,⌜q⌝ₛ) ∧
  ⌜jt_cols_m⌝ₚ(⌜a⌝ₛ,⌜b⌝ₛ,⌜c⌝ₛ,⌜d⌝ₛ,⌜l⌝ₛ,⌜r⌝ₛ,⌜q⌝ₛ,t,z,s,p,v,w) ∧ s ∈ ⌜As⌝ₛ ∧ p ∈ ⌜Ag⌝ₛ ∧
  ⌜fseq_recode_m (𝒞 := kpair_convention_l)⌝ₚ(⌜ds⌝ₛ,s,e) ∧ ⌜fseq_recode_m (𝒞 := kpair_convention_l)⌝ₚ(⌜dg⌝ₛ,p,e) ∧
  ⌜fseq_recode_m (𝒞 := kpair_convention_l)⌝ₚ(⌜hg⌝ₛ,p,g) ∧ ⌜fseq_recode_m (𝒞 := kpair_convention_l)⌝ₚ(⌜lg⌝ₛ,g,f) ∧
  ⌜rg_at_m⌝ₚ(n,e,f,v) ∧ ⌜rg_at_m⌝ₚ(n,e,⌜C⌝ₛ,w)⟫
derive_free_closed jt_word_m

theorem jt_word_sat_l {m} (ρ : Env M m) (ω Y As Ag ds dg hg lg a b c d l r C q : Term m) :
    Formula.satisfies ρ (jt_word_m ω Y As Ag ds dg hg lg a b c d l r C q) ↔
      Jt_word_d hZF (ω.eval ρ) (Y.eval ρ) (As.eval ρ) (Ag.eval ρ) (ds.eval ρ) (dg.eval ρ) (hg.eval ρ) (lg.eval ρ)
        (a.eval ρ) (b.eval ρ) (c.eval ρ) (d.eval ρ) (l.eval ρ) (r.eval ρ) (C.eval ρ) (q.eval ρ) := by
  simp only [jt_word_m,Jt_word_d,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,Formula.satisfies_mem_iff,
    fn0_sat_l hZF.1,jt_cols_sat_l hZF,fseq_recode_sat_l I,rg_at_sat_l hZF.1,Definitional.Term.eval_weaken]
  rfl

structure Jt_tree_d (ω X Q C Ys Yg Zg Fs As Fg Ag ds dg hg lg Z W Y a b c d l r F A : M.Domain) : Prop where
  letters : Jt_letters_d hZF ω Ys Yg Z W Y a b c d l r
  sh_enum : M.IsSetFunctionFromTo I ds Ys X
  gn_enum : M.IsSetFunctionFromTo I dg Yg X
  gn_pair : M.IsSetFunctionFromTo I hg Yg Zg
  gn_cond : M.IsSetFunctionFromTo I lg Zg Q
  sh_space : Fseq_space_d I ω Ys Fs
  gn_space : Fseq_space_d I ω Yg Fg
  sh_tree : Tree_d Fs As
  gn_tree : Tree_d Fg Ag
  sequences : Fseq_space_d I ω Y F
  tree : Tree_d F A
  nodes : ∀ q, M.mem q A ↔ Jt_word_d hZF ω Y As Ag ds dg hg lg a b c d l r C q

theorem jt_tree_l {ω X Q C Ys Yg Zg Fs As Fg Ag ds dg hg lg : M.Domain} (hw : M.IsOmega ω)
    (dS : M.IsSetFunctionFromTo I ds Ys X) (dG : M.IsSetFunctionFromTo I dg Yg X)
    (hG : M.IsSetFunctionFromTo I hg Yg Zg) (lG : M.IsSetFunctionFromTo I lg Zg Q)
    (sS : Fseq_space_d I ω Ys Fs) (sG : Fseq_space_d I ω Yg Fg) (tS : Tree_d Fs As) (tG : Tree_d Fg Ag) :
    ∃ Z W Y a b c d l r F A, Jt_tree_d hZF ω X Q C Ys Yg Zg Fs As Fg Ag ds dg hg lg Z W Y a b c d l r F A := by
  obtain ⟨Z,W,Y,a,b,c,d,l,r,letters⟩ := jt_letters_l hZF ω Ys Yg
  obtain ⟨F,space⟩ := ZF.fseq_space_exists_l I hZF hw Y
  let ρ : Env M 15 := ⟨fun i => [ω,Y,As,Ag,ds,dg,hg,lg,a,b,c,d,l,r,C].get i,fun _ => ω⟩
  let φ : UnarySchema 15 := {
    body := jt_word_m (.bound 1) (.bound 2) (.bound 3) (.bound 4) (.bound 5) (.bound 6) (.bound 7) (.bound 8)
      (.bound 9) (.bound 10) (.bound 11) (.bound 12) (.bound 13) (.bound 14) (.bound 15) .newest }
  have sat q : φ.denote ρ q ↔ Jt_word_d hZF ω Y As Ag ds dg hg lg a b c d l r C q := jt_word_sat_l hZF ..
  obtain ⟨A,sep⟩ := ZF.separation_exists_d hZF φ ρ F
  have nodes q : M.mem q A ↔ Jt_word_d hZF ω Y As Ag ds dg hg lg a b c d l r C q := by
    rw [sep q]
    change (M.mem q F ∧ φ.denote ρ q) ↔ _
    rw [sat q]
    exact ⟨And.right,fun ⟨n,t,z,s,p,v,w,e,g,f,hn,fq,cols,hs,hp,se,pe,pg,gf,reg,params⟩ =>
      ⟨(space q).mpr ⟨n,hn,fn0_function_l (ZF.modelsKP hZF) fq⟩,n,t,z,s,p,v,w,e,g,f,hn,fq,cols,hs,hp,se,pe,pg,gf,reg,params⟩⟩
  refine ⟨Z,W,Y,a,b,c,d,l,r,F,A,letters,dS,dG,hG,lG,sS,sG,tS,tG,space,⟨fun q hq => ((sep q).mp hq).1,?_⟩,nodes⟩
  intro q hq q' hq' sub
  obtain ⟨m,t,z,s,p,v,w,e,g,f,_,fq,cols,hs,hp,se,pe,pg,gf,reg,params⟩ := (nodes q).mp hq
  have fq := fn0_function_l (ZF.modelsKP hZF) fq
  obtain ⟨_,_,fs,_,_,_⟩ := cols.functions_l hZF letters fq
  have fe := se.function_l I hZF dS fs
  obtain ⟨n,hn,fq'⟩ := (space q').mp hq'
  obtain ⟨t',z',s',p',v',w',cols'⟩ := letters.columns_l hZF fq'
  obtain ⟨_,_,fs',fp',_,_⟩ := cols'.functions_l hZF letters fq'
  obtain ⟨_,_,ss,pp,vv,ww⟩ := cols'.mono_l hZF cols sub
  obtain ⟨e',fe',se'⟩ := ZF.fseq_compose_l I hZF dS fs'
  obtain ⟨e'',fe'',pe'⟩ := ZF.fseq_compose_l I hZF dG fp'
  have ee := se'.mono_l I se ss
  have ep := pe'.mono_l I pe pp
  have eq := ((ds_restrict_iff_l I fe'' fe.1).mpr ep).eq hZF.1 ((ds_restrict_iff_l I fe' fe.1).mpr ee)
  subst e''
  obtain ⟨g',fg',pg'⟩ := ZF.fseq_compose_l I hZF hG fp'
  obtain ⟨f',_,gf'⟩ := ZF.fseq_compose_l I hZF lG fg'
  have ff := gf'.mono_l I gf (pg'.mono_l I pg pp)
  exact (nodes q').mpr ⟨n,t',z',s',p',v',w',e',g',f',hn,fn0_of_function_l (ZF.modelsKP hZF) fq',cols',
    tS.2 s hs s' ((sS s').mpr ⟨n,hn,fs'⟩) ss,tG.2 p hp p' ((sG p').mpr ⟨n,hn,fp'⟩) pp,se',pe',pg',gf',
    reg.prefix_l (fn0_of_function_l (ZF.modelsKP hZF) fe) (fn0_of_function_l (ZF.modelsKP hZF) fe') ee ff vv,
    params.prefix_l (fn0_of_function_l (ZF.modelsKP hZF) fe) (fn0_of_function_l (ZF.modelsKP hZF) fe') ee (fun _ h => h) ww⟩

end YesMetaZFC.Model.Forcing.Internal

/-! ## 联合字母直接读取同一枚举值与条件值

把原坐标投影实际复合成两张集合图；任何有限或无限列的多级解码都等于
沿这两张图逐项读取。后续名字节点因而无需复制联合树的内部坐标格式。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.InnerModel SetTheory.Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 保存实际复合图，故同一投影可在扩张中读取新出现的无限列。 -/
def Jt_projection_d (a c d ds hg lg de df : M.Domain) : Prop := ∃ s p g,
  Fseq_recode_d I c a s ∧ Fseq_recode_d I ds s de ∧ Fseq_recode_d I d a p ∧
    Fseq_recode_d I hg p g ∧ Fseq_recode_d I lg g df

theorem Jt_projection_d.compatible_l {a b c d l r ds hg lg de df q t z s p v w e g f : M.Domain}
    (projection : Jt_projection_d hZF a c d ds hg lg de df)
    (cols : Jt_cols_d hZF a b c d l r q t z s p v w) (se : Fseq_recode_d I ds s e)
    (pg : Fseq_recode_d I hg p g) (gf : Fseq_recode_d I lg g f) : Fseq_recode_d I de q e ∧ Fseq_recode_d I df q f := by
  obtain ⟨_,_,_,cS,ce,cG,cP,cf⟩ := projection
  exact ⟨(cols.qt.comp_l I cols.ts cS).comp_l I se ce,
    ((cols.qt.comp_l I cols.tp cG).comp_l I pg cP).comp_l I gf cf⟩

theorem Jt_tree_d.projections_l {ω X Q C Ys Yg Zg Fs As Fg Ag ds dg hg lg Z W Y a b c d l r F A : M.Domain}
    (tree : Jt_tree_d hZF ω X Q C Ys Yg Zg Fs As Fg Ag ds dg hg lg Z W Y a b c d l r F A) :
    ∃ de df, M.IsSetFunctionFromTo I de Y X ∧ M.IsSetFunctionFromTo I df Y Q ∧ Jt_projection_d hZF a c d ds hg lg de df := by
  obtain ⟨aS,fS,cS⟩ := ZF.fseq_compose_l I hZF tree.letters.c_fn tree.letters.a_fn
  obtain ⟨de,fe,ce⟩ := ZF.fseq_compose_l I hZF tree.sh_enum fS
  obtain ⟨aG,fG,cG⟩ := ZF.fseq_compose_l I hZF tree.letters.d_fn tree.letters.a_fn
  obtain ⟨aP,fP,cP⟩ := ZF.fseq_compose_l I hZF tree.gn_pair fG
  obtain ⟨df,ff,cf⟩ := ZF.fseq_compose_l I hZF tree.gn_cond fP
  exact ⟨de,df,fe,ff,aS,aG,aP,cS,ce,cG,cP,cf⟩

end YesMetaZFC.Model.Forcing.Internal

/-! ## 查询实数、联合字母、期限和两个名字位置的实际字母表

最外层直接采用 ω×辅助字母表，故树的第一坐标就是原对局实数。
辅助字母为 (联合字母×ω)×(ω×ω)，后三个自然数依次记录期限及两个固定位置。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.InnerModel SetTheory.Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

structure Nr_letters_d (ω A Z W H a b c d l r Y dx dh : M.Domain) : Prop where
  auxiliary : Jt_letters_d hZF ω A ω Z W H a b c d l r
  product : M.IsCartesianProduct I Y ω H
  query : M.IsSetFunctionFromTo I dx Y ω
  witness : M.IsSetFunctionFromTo I dh Y H
  read : ∀ q x h, M.mem q Y → KPair_d M q x h → Rd_entry_d q x dx ∧ Rd_entry_d q h dh

structure Nr_cols_d (a b c d l r dx dh q x h t z s u v w : M.Domain) : Prop where
  query : Fseq_recode_d I dx q x
  witness : Fseq_recode_d I dh q h
  auxiliary : Jt_cols_d hZF a b c d l r h t z s u v w

def nr_cols_m {n} (a b c d l r dx dh q x h t z s u v w : Term n) : Formula 1 n :=
  .conj (fseq_recode_m (𝒞 := kpair_convention_l) dx q x)
    (.conj (fseq_recode_m (𝒞 := kpair_convention_l) dh q h) (jt_cols_m a b c d l r h t z s u v w))
derive_free_closed nr_cols_m

theorem nr_cols_sat_l {n} (ρ : Env M n) (a b c d l r dx dh q x h t z s u v w : Term n) :
    Formula.satisfies ρ (nr_cols_m a b c d l r dx dh q x h t z s u v w) ↔
      Nr_cols_d hZF (a.eval ρ) (b.eval ρ) (c.eval ρ) (d.eval ρ) (l.eval ρ) (r.eval ρ) (dx.eval ρ) (dh.eval ρ)
        (q.eval ρ) (x.eval ρ) (h.eval ρ) (t.eval ρ) (z.eval ρ) (s.eval ρ) (u.eval ρ) (v.eval ρ) (w.eval ρ) := by
  simp only [nr_cols_m,Formula.satisfies_conj_iff,fseq_recode_sat_l I,jt_cols_sat_l hZF]
  exact ⟨fun ⟨a,b,c⟩ => ⟨a,b,c⟩,fun h => ⟨h.query,h.witness,h.auxiliary⟩⟩

theorem nr_letters_l (ω A : M.Domain) : ∃ Z W H a b c d l r Y dx dh,
    Nr_letters_d hZF ω A Z W H a b c d l r Y dx dh := by
  obtain ⟨Z,W,H,a,b,c,d,l,r,aux⟩ := jt_letters_l hZF ω A ω
  obtain ⟨Y,product⟩ := ZF.exists_cartesianProduct hZF I ω H
  obtain ⟨dx,dh,fx,fh,read⟩ := cl_pair_maps_l hZF product
  exact ⟨Z,W,H,a,b,c,d,l,r,Y,dx,dh,aux,product,fx,fh,read⟩

theorem Nr_cols_d.functions_l {ω A Z W H a b c d l r Y dx dh n q x h t z s u v w : M.Domain}
    (letters : Nr_letters_d hZF ω A Z W H a b c d l r Y dx dh) (fq : M.IsSetFunctionFromTo I q n Y)
    (cols : Nr_cols_d hZF a b c d l r dx dh q x h t z s u v w) :
    M.IsSetFunctionFromTo I x n ω ∧ M.IsSetFunctionFromTo I h n H ∧ M.IsSetFunctionFromTo I s n A ∧
      M.IsSetFunctionFromTo I u n ω ∧ M.IsSetFunctionFromTo I v n ω ∧ M.IsSetFunctionFromTo I w n ω := by
  have fx := cols.query.function_l I hZF letters.query fq
  have fh := cols.witness.function_l I hZF letters.witness fq
  obtain ⟨_,_,fs,fu,fv,fw⟩ := cols.auxiliary.functions_l hZF letters.auxiliary fh
  exact ⟨fx,fh,fs,fu,fv,fw⟩

theorem Nr_letters_d.columns_l {ω A Z W H a b c d l r Y dx dh n q : M.Domain}
    (letters : Nr_letters_d hZF ω A Z W H a b c d l r Y dx dh) (fq : M.IsSetFunctionFromTo I q n Y) :
    ∃ x h t z s u v w, Nr_cols_d hZF a b c d l r dx dh q x h t z s u v w := by
  obtain ⟨x,_,qx⟩ := ZF.fseq_compose_l I hZF letters.query fq
  obtain ⟨h,fh,qh⟩ := ZF.fseq_compose_l I hZF letters.witness fq
  obtain ⟨t,z,s,u,v,w,aux⟩ := letters.auxiliary.columns_l hZF fh
  exact ⟨x,h,t,z,s,u,v,w,qx,qh,aux⟩

theorem Nr_cols_d.mono_l {a b c d l r dx dh q x h t z s u v w q' x' h' t' z' s' u' v' w' : M.Domain}
    (cols : Nr_cols_d hZF a b c d l r dx dh q x h t z s u v w)
    (next : Nr_cols_d hZF a b c d l r dx dh q' x' h' t' z' s' u' v' w') (sub : M.MemberSubset q q') :
    M.MemberSubset x x' ∧ M.MemberSubset s s' ∧ M.MemberSubset u u' ∧ M.MemberSubset v v' ∧ M.MemberSubset w w' := by
  obtain ⟨_,_,ss,uu,vv,ww⟩ := cols.auxiliary.mono_l hZF next.auxiliary (cols.witness.mono_l I next.witness sub)
  exact ⟨cols.query.mono_l I next.query sub,ss,uu,vv,ww⟩

theorem Nr_cols_d.unique_l {a b c d l r dx dh q x h t z s u v w x' h' t' z' s' u' v' w' : M.Domain}
    (cols : Nr_cols_d hZF a b c d l r dx dh q x h t z s u v w)
    (next : Nr_cols_d hZF a b c d l r dx dh q x' h' t' z' s' u' v' w') :
    x = x' ∧ h = h' ∧ t = t' ∧ z = z' ∧ s = s' ∧ u = u' ∧ v = v' ∧ w = w' := by
  have ex := cols.query.unique_l I hZF.1 next.query
  have eh := cols.witness.unique_l I hZF.1 next.witness
  subst x' h'
  exact ⟨rfl,rfl,cols.auxiliary.unique_l hZF next.auxiliary⟩

theorem Nr_letters_d.word_l {ω A Z W H a b c d l r Y dx dh n x s u v w : M.Domain}
    (letters : Nr_letters_d hZF ω A Z W H a b c d l r Y dx dh)
    (fx : Fn0_d n ω x) (fs : Fn0_d n A s) (fu : Fn0_d n ω u) (fv : Fn0_d n ω v) (fw : Fn0_d n ω w) :
    ∃ q h t z, M.IsSetFunctionFromTo I q n Y ∧ Nr_cols_d hZF a b c d l r dx dh q x h t z s u v w := by
  obtain ⟨h,t,z,fh,cols⟩ := letters.auxiliary.word_l hZF fs fu fv fw
  obtain ⟨q,fq,qx,qh⟩ := cl_pair_word_l hZF letters.product letters.query letters.witness letters.read
    fx (fn0_of_function_l (ZF.modelsKP hZF) fh)
  exact ⟨q,h,t,z,fq,qx,qh,cols⟩

end YesMetaZFC.Model.Forcing.Internal
