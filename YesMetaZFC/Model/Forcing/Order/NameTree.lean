import YesMetaZFC.Model.Forcing.Order.QueryAttempt
import YesMetaZFC.Model.Forcing.Order.NameLetters

/-! # 查询实数与原联合枝的实际名字树

节点同时属于原联合树，并沿它的两张真实投影读取枚举和条件列。
名字位置、函数性和数字判值均在该节点内检查；分离及前缀定理构造实际树。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.InnerModel SetTheory.Internal SetTheory.Descriptive
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

def Nr_word_d (ω X Q T Y A₀ de df a b c d l r dx dh q : M.Domain) : Prop := ∃ n x h t z s u v w e f,
  M.mem n ω ∧ Fn0_d n Y q ∧ Nr_cols_d hZF a b c d l r dx dh q x h t z s u v w ∧ M.mem s A₀ ∧
    Fseq_recode_d I de s e ∧ Fseq_recode_d I df s f ∧ Nr_at_d ω X Q T n e f x u v w

def nr_word_m {m} (ω X Q T Y A₀ de df a b c d l r dx dh q : Term m) : Formula 1 m := set[m] ⟪∃ n x h t z s u v w e f,
  n ∈ ⌜ω⌝ₛ ∧ ⌜fn0_m⌝ₚ(n,⌜Y⌝ₛ,⌜q⌝ₛ) ∧
  ⌜nr_cols_m⌝ₚ(⌜a⌝ₛ,⌜b⌝ₛ,⌜c⌝ₛ,⌜d⌝ₛ,⌜l⌝ₛ,⌜r⌝ₛ,⌜dx⌝ₛ,⌜dh⌝ₛ,⌜q⌝ₛ,x,h,t,z,s,u,v,w) ∧ s ∈ ⌜A₀⌝ₛ ∧
  ⌜fseq_recode_m (𝒞 := kpair_convention_l)⌝ₚ(⌜de⌝ₛ,s,e) ∧
  ⌜fseq_recode_m (𝒞 := kpair_convention_l)⌝ₚ(⌜df⌝ₛ,s,f) ∧
  ⌜nr_at_m⌝ₚ(⌜ω⌝ₛ,⌜X⌝ₛ,⌜Q⌝ₛ,⌜T⌝ₛ,n,e,f,x,u,v,w)⟫
derive_free_closed nr_word_m

theorem nr_word_sat_l {m} (ρ : Env M m) (ω X Q T Y A₀ de df a b c d l r dx dh q : Term m) :
    Formula.satisfies ρ (nr_word_m ω X Q T Y A₀ de df a b c d l r dx dh q) ↔
      Nr_word_d hZF (ω.eval ρ) (X.eval ρ) (Q.eval ρ) (T.eval ρ) (Y.eval ρ) (A₀.eval ρ) (de.eval ρ) (df.eval ρ)
        (a.eval ρ) (b.eval ρ) (c.eval ρ) (d.eval ρ) (l.eval ρ) (r.eval ρ) (dx.eval ρ) (dh.eval ρ) (q.eval ρ) := by
  simp only [nr_word_m,Nr_word_d,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,Formula.satisfies_mem_iff,
    fn0_sat_l hZF.1,nr_cols_sat_l hZF,fseq_recode_sat_l I,nr_at_sat_l hZF.1,Definitional.Term.eval_weaken]
  rfl

structure Nr_tree_d (ω X Q T A F₀ A₀ de df Z W H a b c d l r Y dx dh F S : M.Domain) : Prop where
  letters : Nr_letters_d hZF ω A Z W H a b c d l r Y dx dh
  enumeration : M.IsSetFunctionFromTo I de A X
  conditions : M.IsSetFunctionFromTo I df A Q
  base_space : Fseq_space_d I ω A F₀
  base_tree : Tree_d F₀ A₀
  sequences : Fseq_space_d I ω Y F
  tree : Tree_d F S
  nodes : ∀ q, M.mem q S ↔ Nr_word_d hZF ω X Q T Y A₀ de df a b c d l r dx dh q

theorem nr_tree_l {ω X Q T A F₀ A₀ de df : M.Domain} (hw : M.IsOmega ω)
    (fe : M.IsSetFunctionFromTo I de A X) (ff : M.IsSetFunctionFromTo I df A Q)
    (space₀ : Fseq_space_d I ω A F₀) (tree₀ : Tree_d F₀ A₀) :
    ∃ Z W H a b c d l r Y dx dh F S, Nr_tree_d hZF ω X Q T A F₀ A₀ de df Z W H a b c d l r Y dx dh F S := by
  obtain ⟨Z,W,H,a,b,c,d,l,r,Y,dx,dh,letters⟩ := nr_letters_l hZF ω A
  obtain ⟨F,space⟩ := ZF.fseq_space_exists_l I hZF hw Y
  let ρ : Env M 16 := ⟨fun i => [ω,X,Q,T,Y,A₀,de,df,a,b,c,d,l,r,dx,dh].get i,fun _ => ω⟩
  let φ : UnarySchema 16 := {
    body := nr_word_m (.bound 1) (.bound 2) (.bound 3) (.bound 4) (.bound 5) (.bound 6) (.bound 7) (.bound 8)
      (.bound 9) (.bound 10) (.bound 11) (.bound 12) (.bound 13) (.bound 14) (.bound 15) (.bound 16) .newest }
  have sat q : φ.denote ρ q ↔ Nr_word_d hZF ω X Q T Y A₀ de df a b c d l r dx dh q := nr_word_sat_l hZF ..
  obtain ⟨S,sep⟩ := ZF.separation_exists_d hZF φ ρ F
  have nodes q : M.mem q S ↔ Nr_word_d hZF ω X Q T Y A₀ de df a b c d l r dx dh q := by
    rw [sep q]
    change (M.mem q F ∧ φ.denote ρ q) ↔ _
    rw [sat q]
    refine ⟨And.right,fun h => ?_⟩
    obtain ⟨n,x,h',t,z,s,u,v,w,e,f,hn,fq,cols,hs,se,sf,check⟩ := h
    exact ⟨(space q).mpr ⟨n,hn,fn0_function_l (ZF.modelsKP hZF) fq⟩,
      n,x,h',t,z,s,u,v,w,e,f,hn,fq,cols,hs,se,sf,check⟩
  refine ⟨Z,W,H,a,b,c,d,l,r,Y,dx,dh,F,S,letters,fe,ff,space₀,tree₀,space,⟨fun q hq => ((sep q).mp hq).1,?_⟩,nodes⟩
  intro q hq q' hq' sub
  obtain ⟨m,x,h,t,z,s,u,v,w,e,f,_,fq,cols,hs,se,sf,check⟩ := (nodes q).mp hq
  have fq := fn0_function_l (ZF.modelsKP hZF) fq
  obtain ⟨n,hn,fq'⟩ := (space q').mp hq'
  obtain ⟨x',h',t',z',s',u',v',w',cols'⟩ := letters.columns_l hZF fq'
  obtain ⟨_,_,fs',_,_,_⟩ := cols'.functions_l hZF letters fq'
  obtain ⟨xx,ss,uu,vv,ww⟩ := cols'.mono_l hZF cols sub
  obtain ⟨e',_,se'⟩ := ZF.fseq_compose_l I hZF fe fs'
  obtain ⟨f',_,sf'⟩ := ZF.fseq_compose_l I hZF ff fs'
  have bound : M.MemberSubset n m := by
    intro i hi
    obtain ⟨y,_,p,pair,hp⟩ := fq'.2.2 i hi
    exact fq.input_mem_of_pairMember ⟨p,pair,sub p hp⟩
  exact (nodes q').mpr ⟨n,x',h',t',z',s',u',v',w',e',f',hn,fn0_of_function_l (ZF.modelsKP hZF) fq',cols',
    tree₀.2 s hs s' ((space₀ s').mpr ⟨n,hn,fs'⟩) ss,se',sf',
    check.prefix_l bound (se'.mono_l I se ss) (sf'.mono_l I sf ss) xx uu vv ww⟩

end YesMetaZFC.Model.Forcing.Internal
