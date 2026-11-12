import YesMetaZFC.Model.Forcing.Order.QueryAttempt
import YesMetaZFC.Model.Forcing.Order.NameTree

/-! # 同一名字树中的实际正负子树

正负树只加强原树的根检查，保持原字母表、第一坐标及名字位置。
节点由分离实际构造；短前缀尚未看见全部根位置时，检查自然保持。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.InnerModel SetTheory.Internal SetTheory.Descriptive
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

def Qs_word_d (φ : Formula 1 4) (sign : Bool) (X Q T σ ω a₀ Y de df a b c d l r dx dh q : M.Domain) : Prop :=
  ∃ n x h t z s u v w e f, M.mem n ω ∧ Fn0_d n Y q ∧ Nr_cols_d hZF a b c d l r dx dh q x h t z s u v w ∧
    Fseq_recode_d I de s e ∧ Fseq_recode_d I df s f ∧ Qs_at_d φ sign X Q T σ ω a₀ n e f v w

def qs_word_m {m} (φ : Formula 1 4) (sign : Bool) (X Q T σ ω a₀ Y de df a b c d l r dx dh q : Term m) : Formula 1 m :=
  set[m] ⟪∃ n x h t z s u v w e f, n ∈ ⌜ω⌝ₛ ∧ ⌜fn0_m⌝ₚ(n,⌜Y⌝ₛ,⌜q⌝ₛ) ∧
    ⌜nr_cols_m⌝ₚ(⌜a⌝ₛ,⌜b⌝ₛ,⌜c⌝ₛ,⌜d⌝ₛ,⌜l⌝ₛ,⌜r⌝ₛ,⌜dx⌝ₛ,⌜dh⌝ₛ,⌜q⌝ₛ,x,h,t,z,s,u,v,w) ∧
    ⌜fseq_recode_m (𝒞 := kpair_convention_l)⌝ₚ(⌜de⌝ₛ,s,e) ∧
    ⌜fseq_recode_m (𝒞 := kpair_convention_l)⌝ₚ(⌜df⌝ₛ,s,f) ∧
    ⌜qs_at_m φ sign⌝ₚ(⌜X⌝ₛ,⌜Q⌝ₛ,⌜T⌝ₛ,⌜σ⌝ₛ,⌜ω⌝ₛ,⌜a₀⌝ₛ,n,e,f,v,w)⟫

@[simp] theorem qs_word_closed_l {m} {φ : Formula 1 4} (hc : φ.FreeClosed) (sign : Bool)
    (X Q T σ ω a₀ Y de df a b c d l r dx dh q : Term m)
    (hX : X.freeSupport = []) (hQ : Q.freeSupport = []) (hT : T.freeSupport = []) (hσ : σ.freeSupport = [])
    (hw : ω.freeSupport = []) (ha₀ : a₀.freeSupport = []) (hY : Y.freeSupport = [])
    (hde : de.freeSupport = []) (hdf : df.freeSupport = []) (ha : a.freeSupport = []) (hb : b.freeSupport = [])
    (hc' : c.freeSupport = []) (hd : d.freeSupport = []) (hl : l.freeSupport = []) (hr : r.freeSupport = [])
    (hx : dx.freeSupport = []) (hh : dh.freeSupport = []) (hq : q.freeSupport = []) :
    (qs_word_m φ sign X Q T σ ω a₀ Y de df a b c d l r dx dh q).FreeClosed := by
  simp -implicitDefEqProofs [qs_word_m,Definitional.Formula.FreeClosed,hc,hX,hQ,hT,hσ,hw,ha₀,hY,hde,hdf,ha,hb,hc',hd,hl,hr,hx,hh,hq]

theorem qs_word_sat_l {m} {φ : Formula 1 4} (hc : φ.FreeClosed) (sign : Bool) (ρ : Env M m)
    (X Q T σ ω a₀ Y de df a b c d l r dx dh q : Term m) :
    Formula.satisfies ρ (qs_word_m φ sign X Q T σ ω a₀ Y de df a b c d l r dx dh q) ↔
      Qs_word_d hZF φ sign (X.eval ρ) (Q.eval ρ) (T.eval ρ) (σ.eval ρ) (ω.eval ρ) (a₀.eval ρ) (Y.eval ρ)
        (de.eval ρ) (df.eval ρ) (a.eval ρ) (b.eval ρ) (c.eval ρ) (d.eval ρ) (l.eval ρ) (r.eval ρ) (dx.eval ρ) (dh.eval ρ) (q.eval ρ) := by
  simp only [qs_word_m,Qs_word_d,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,Formula.satisfies_mem_iff,
    fn0_sat_l hZF.1,nr_cols_sat_l hZF,fseq_recode_sat_l I,qs_at_sat_l hZF.1 hc,Definitional.Term.eval_weaken]
  rfl

structure Qs_tree_d (φ : Formula 1 4) (sign : Bool)
    {ω X Q T A F₀ A₀ de df Z W H a b c d l r Y dx dh F S : M.Domain}
    (base : Nr_tree_d hZF ω X Q T A F₀ A₀ de df Z W H a b c d l r Y dx dh F S) (σ a₀ S' : M.Domain) : Prop where
  tree : Tree_d F S'
  nodes : ∀ q, M.mem q S' ↔ M.mem q S ∧ Qs_word_d hZF φ sign X Q T σ ω a₀ Y de df a b c d l r dx dh q

theorem qs_tree_l {φ : Formula 1 4} (hc : φ.FreeClosed) (sign : Bool)
    {ω X Q T A F₀ A₀ de df Z W H a b c d l r Y dx dh F S : M.Domain}
    (base : Nr_tree_d hZF ω X Q T A F₀ A₀ de df Z W H a b c d l r Y dx dh F S) (σ a₀ : M.Domain) :
    ∃ S', Qs_tree_d hZF φ sign base σ a₀ S' := by
  let ρ : Env M 17 := ⟨fun i => [X,Q,T,σ,ω,a₀,Y,de,df,a,b,c,d,l,r,dx,dh].get i,fun _ => X⟩
  let ψ : UnarySchema 17 := {
    body := qs_word_m φ sign (.bound 1) (.bound 2) (.bound 3) (.bound 4) (.bound 5) (.bound 6) (.bound 7) (.bound 8)
      (.bound 9) (.bound 10) (.bound 11) (.bound 12) (.bound 13) (.bound 14) (.bound 15) (.bound 16) (.bound 17) .newest
    freeClosed := by simp -implicitDefEqProofs [hc] }
  have sat q : ψ.denote ρ q ↔ Qs_word_d hZF φ sign X Q T σ ω a₀ Y de df a b c d l r dx dh q := qs_word_sat_l hZF hc sign ..
  obtain ⟨S',sep⟩ := ZF.separation_exists_d hZF ψ ρ S
  have nodes q : M.mem q S' ↔ M.mem q S ∧ Qs_word_d hZF φ sign X Q T σ ω a₀ Y de df a b c d l r dx dh q :=
    (sep q).trans (and_congr_right fun _ => sat q)
  refine ⟨S',⟨⟨fun q hq => base.tree.1 q ((nodes q).mp hq).1,?_⟩,nodes⟩⟩
  intro q hq q' hq' sub
  obtain ⟨old,m,x,h,t,z,s,u,v,w,e,f,_,fq,cols,se,sf,check⟩ := (nodes q).mp hq
  have fq := fn0_function_l (ZF.modelsKP hZF) fq
  obtain ⟨n,hn,fq'⟩ := (base.sequences q').mp hq'
  obtain ⟨x',h',t',z',s',u',v',w',cols'⟩ := base.letters.columns_l hZF fq'
  obtain ⟨_,_,fs',_,_,_⟩ := cols'.functions_l hZF base.letters fq'
  obtain ⟨_,ss,_,vv,ww⟩ := cols'.mono_l hZF cols sub
  obtain ⟨e',_,se'⟩ := ZF.fseq_compose_l I hZF base.enumeration fs'
  obtain ⟨f',_,sf'⟩ := ZF.fseq_compose_l I hZF base.conditions fs'
  have bound : M.MemberSubset n m := by
    intro i hi
    obtain ⟨y,_,p,pair,hp⟩ := fq'.2.2 i hi
    exact fq.input_mem_of_pairMember ⟨p,pair,sub p hp⟩
  exact (nodes q').mpr ⟨base.tree.2 q old q' hq' sub,n,x',h',t',z',s',u',v',w',e',f',hn,
    fn0_of_function_l (ZF.modelsKP hZF) fq',cols',se',sf',
    check.prefix_l bound (se'.mono_l I se ss) (sf'.mono_l I sf ss) vv ww⟩

end YesMetaZFC.Model.Forcing.Internal
