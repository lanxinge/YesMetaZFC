import YesMetaZFC.Model.SetTheory.Demand.Reply
import YesMetaZFC.Model.SetTheory.Demand.Untag
import YesMetaZFC.SetTheory.Descriptive.Tree.HistoryTree

/-! # 双辅助字母域的不交不变量

以两个不同标签复制辅助字母。原实数坐标不变；解码双射诱导整棵树的
逆像，保留全部内部有限前缀和无限分支。不交性随后只依赖树本身。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel Descriptive
universe u
variable {M : Structure.{u}}

def Td_separated_d (S : M.Domain) : Prop :=
  ∀ z, Td_letter_d false S z → ¬ Td_letter_d true S z

def td_separated_m {d} (S : Term d) : Formula 1 d := set[d] ⟪
  ∀ z, ⌜td_letter_m false⌝ₚ(⌜S⌝ₛ,z) → ¬ ⌜td_letter_m true⌝ₚ(⌜S⌝ₛ,z)⟫
derive_free_closed td_separated_m

theorem td_separated_sat_l (hE : Extensional M) {d} (ρ : Env M d) (S : Term d) :
    Formula.satisfies ρ (td_separated_m S) ↔ Td_separated_d (S.eval ρ) := by
  simp only [td_separated_m,Td_separated_d,Formula.satisfies_forall_iff,Formula.satisfies_imp_iff,
    Formula.satisfies_neg_iff,td_letter_sat_l hE,Definitional.Term.eval_weaken]
  rfl

theorem Td_separated_d.alphabet_l {S A B : M.Domain}
    (h : Td_separated_d S) (alphabet : Td_alphabet_d S A B) :
    ∀ z, M.mem z A → ¬ M.mem z B :=
  fun z ha hb => h z ((alphabet.1 z).mp ha) ((alphabet.2 z).mp hb)

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 原树先实际重编码；两个标签集合不相交，故最小出现域也不相交。 -/
theorem Td_tree_d.separate_l {ω A S : M.Domain} (hw : M.IsOmega ω) (tree : Td_tree_d I ω A S) :
    ∃ e o U V T U' V', e ≠ o ∧ Td_alphabet_d S U V ∧
      Td_tree_d I ω A T ∧ Td_separated_d T ∧ Td_alphabet_d T U' V' ∧
      Nonempty (Td_retag_d hZF ω A S U V e o T U' V') := by
  obtain ⟨U,V,P,Y,F,alphabet,pair,triple,space,old⟩ := tree.space_l hZF hw
  obtain ⟨e,he⟩ := KP.exists_empty (ZF.modelsKP hZF)
  obtain ⟨o,so,_⟩ := hw.1.2 e (num_mem_l hZF.1 hw (show Num_d 0 e from he))
  have ne : e ≠ o := fun eq => he e (eq.symm ▸ so.predecessor_mem)
  obtain ⟨_,Uc,Vc,cu,cv,disjoint,_⟩ := ZF.tagged_union_exists_d hZF I ne U V
  obtain ⟨Pc,pairc⟩ := ZF.exists_cartesianProduct hZF I Uc Vc
  obtain ⟨Yc,triplec⟩ := ZF.exists_cartesianProduct hZF I A Pc
  have decode x (hx : M.mem x Yc) : ∃ y, M.mem y Y ∧ Td_tag_d e o x y := by
    obtain ⟨r,hr,t,ht,xt⟩ := (triplec x).mp hx
    obtain ⟨c,hc,d,hd,td⟩ := (pairc t).mp ht
    obtain ⟨a,ha,ca⟩ := (cu c).mp hc
    obtain ⟨b,hb,db⟩ := (cv d).mp hd
    obtain ⟨u,ub⟩ := (I).total a b
    obtain ⟨y,yu⟩ := (I).total r u
    exact ⟨y,(triple y).mpr ⟨r,hr,u,(pair u).mpr ⟨a,ha,b,hb,ub⟩,yu⟩,
      r,a,b,t,c,d,u,xt,td,ca,db,yu,ub⟩
  have encode y (hy : M.mem y Y) : ∃ x, M.mem x Yc ∧ Td_tag_d e o x y := by
    obtain ⟨r,hr,u,hu,yu⟩ := (triple y).mp hy
    obtain ⟨a,ha,b,hb,ub⟩ := (pair u).mp hu
    obtain ⟨c,ca⟩ := (I).total e a
    obtain ⟨d,db⟩ := (I).total o b
    obtain ⟨t,td⟩ := (I).total c d
    obtain ⟨x,xt⟩ := (I).total r t
    exact ⟨x,(triplec x).mpr ⟨r,hr,t,(pairc t).mpr
      ⟨c,(cu c).mpr ⟨a,ha,ca⟩,d,(cv d).mpr ⟨b,hb,db⟩,td⟩,xt⟩,
      r,a,b,t,c,d,u,xt,td,ca,db,yu,ub⟩
  let ρ : Env M 2 := ⟨fun i => [e,o].get i,fun _ => e⟩
  let φ : BinarySchema 2 := { body := td_tag_m (.bound 2) (.bound 3) (.bound 1) .newest }
  have sat x y : φ.denote ρ x y ↔ Td_tag_d e o x y := td_tag_sat_l hZF.1 ..
  obtain ⟨f,fn,graph⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ
    (source := Yc) (target := Y) (fun x hx => (decode x hx).imp fun y hy => (sat x y).mpr hy.2)
    (fun x _ y z hy hz => (td_tag_unique_l hZF.1 ((sat x y).mp hy) ((sat x z).mp hz)).mp rfl)
    (fun x y hx xy => by
      obtain ⟨z,hz,xz⟩ := decode x hx
      exact ((td_tag_unique_l hZF.1 xz ((sat x y).mp xy)).mp rfl) ▸ hz)
  have entry x y : Rd_entry_d x y f ↔ M.mem x Yc ∧ Td_tag_d e o x y :=
    (graph x y).trans (and_congr_right fun _ => sat x y)
  have bij : M.IsSetBijectionFromTo I f Yc Y := ⟨⟨fn,fun x x' y xy x'y =>
    (td_tag_unique_l hZF.1 ((entry x y).mp xy).2 ((entry x' y).mp x'y).2).mpr rfl⟩,
    fun y hy => (encode y hy).imp fun x hx => ⟨hx.1,(entry x y).mpr hx⟩⟩
  obtain ⟨Fc,spacec⟩ := ZF.fseq_space_exists_l I hZF hw Yc
  obtain ⟨T,pull⟩ := tr_pull_exists_l I hZF f Fc S
  have newTree := pull.tree_l I hZF fn spacec space old
  have letter (side : Bool) (z : M.Domain) (h : Td_letter_d side T z) : M.mem z (if side then Vc else Uc) := by
    obtain ⟨q,i,p,x,a,b,t,hq,ip,px,ab,eq⟩ := h
    obtain ⟨n,_,fq⟩ := (spacec q).mp (newTree.1 q hq)
    obtain ⟨x',_,t',ht,px'⟩ := (triplec p).mp (fq.output_mem_of_pairMember ip)
    have et := (kpair_injective_l M px px').2
    subst t'
    obtain ⟨a',ha,b',hb,ab'⟩ := (pairc t).mp ht
    obtain ⟨ea,eb⟩ := kpair_injective_l M ab ab'
    subst a' b'
    cases side <;> exact eq.symm ▸ (by assumption)
  have separated : Td_separated_d T := fun z left right => disjoint z ⟨letter false z left,letter true z right⟩
  obtain ⟨K,bK,rK,_⟩ := ZF.fseq_recode_l I hZF hw spacec space bij
  have lift (side : Bool) {a z} (ha : Td_letter_d side S a)
      (az : KPair_d M z (if side then o else e) a) : Td_letter_d side T z := by
    obtain ⟨q,i,p,x,b,c,t,hq,ip,pt,bc,eq⟩ := ha
    obtain ⟨q',hq',qq'⟩ := bK.2 q (old.1 q hq)
    have recode := ((rK q' q).mp qq').2
    have hqT := (pull q').mpr ⟨hq',q,hq,recode⟩
    obtain ⟨p',ip',pp'⟩ := (recode.2 i p).mp ip
    obtain ⟨r,b',c',t',z',w',u,p't,t'w,z'b,w'c,pu,ubc⟩ := ((entry p' p).mp pp').2
    obtain ⟨ex,et⟩ := (I).injective pt pu
    subst r u
    obtain ⟨eb,ec⟩ := (I).injective bc ubc
    subst b' c'
    refine ⟨q',i,p',x,z',w',t',hqT,ip',p't,t'w,?_⟩
    cases side
    · exact (I).unique az (eq.symm ▸ z'b)
    · exact (I).unique az (eq.symm ▸ w'c)
  have letters : Td_alphabet_d T Uc Vc := by
    constructor
    · intro z
      exact ⟨fun hz => ((cu z).mp hz).elim fun a ha => lift false ((alphabet.1 a).mp ha.1) ha.2,
        letter false z⟩
    · intro z
      exact ⟨fun hz => ((cv z).mp hz).elim fun a ha => lift true ((alphabet.2 a).mp ha.1) ha.2,
        letter true z⟩
  exact ⟨e,o,U,V,T,Uc,Vc,ne,alphabet,td_tree_of_l I spacec newTree pairc triplec,separated,letters,
    ⟨⟨P,Y,F,Pc,Yc,Fc,f,pair,triple,pairc,triplec,space,spacec,old,bij,entry,pull,cu,cv⟩⟩⟩

end YesMetaZFC.SetTheory.Internal
