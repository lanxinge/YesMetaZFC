import YesMetaZFC.SetTheory.LargeCardinal.Absorption.Trace
import YesMetaZFC.Model.Forcing.Functions.ValueIsomorphism
import YesMetaZFC.Model.SetTheory.Demand.Reply
import YesMetaZFC.Model.SetTheory.Game.NodeEmbedding
import YesMetaZFC.Model.Forcing.Ground.TreeShift
import YesMetaZFC.Model.SetTheory.Embedding.Theory
import YesMetaZFC.Model.Forcing.Collapse.NameCode
import YesMetaZFC.Model.Forcing.Extension.FunctionNames
import YesMetaZFC.Model.Forcing.TwoStep.ProductExtension
import YesMetaZFC.SetTheory.CumulativeFunction
import YesMetaZFC.Model.SetTheory.Embedding.RankFixed
import YesMetaZFC.Model.SetTheory.Embedding.PredicateTrace
import YesMetaZFC.Model.SetTheory.Internal.RealTrace
import YesMetaZFC.Model.Forcing.Embedding.Rank
import YesMetaZFC.SetTheory.LargeCardinal.Demand.UntagGeneral

/-! # 7.23 辅助树的有限非反驳条件

第二坐标第零项选择函数名字，随后依次选择大条件。小条件的后续各项
不得反驳旧稠密集要求；两个条件的共尾偶数坐标不得反驳任何已出现的函数值。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project Descriptive Model.Forcing.Internal
universe u
variable {M : Structure.{u}}

def ag_mem_body_m : Formula 1 2 := .neg (.mem .newest (.bound 1))

def Ag_demand_d (Q T b q p d : M.Domain) : Prop := ∃ s, Check_d M b p s ∧
  ¬ Forces_d M Q T Q ag_mem_body_m ((⟨fun _ => d,fun _ => d⟩ : Env M 1).push s) q

def ag_demand_m {n} (Q T b q p d : Term n) : Formula 1 n := .existsE
  (.conj (check_m b.weaken p.weaken .newest)
    (.neg (force_at_m ag_mem_body_m (Fin.cases .newest (fun _ => d.weaken))
      Q.weaken T.weaken Q.weaken q.weaken)))
derive_free_closed ag_mem_body_m
@[simp] theorem ag_demand_m_freeClosed {n} (Q T b q p d : Term n)
    (hQ : Q.freeSupport = []) (hT : T.freeSupport = []) (hb : b.freeSupport = [])
    (hq : q.freeSupport = []) (hp : p.freeSupport = []) (hd : d.freeSupport = []) :
    (ag_demand_m Q T b q p d).FreeClosed := by
  simp only [ag_demand_m,Definitional.Formula.FreeClosed]
  constructor
  · exact check_m_freeClosed _ _ _ (by simpa using hb) (by simpa using hp) rfl
  · exact force_at_closed_l _ _ _ _ _ _ ag_mem_body_m_freeClosed
      (Fin.cases rfl (fun _ => by simpa using hd))
      (by simpa using hQ) (by simpa using hT) (by simpa using hQ) (by simpa using hq)

theorem ag_demand_sat_l (hE : Extensional M) {n} (ρ : Env M n) (Q T b q p d : Term n) :
    Formula.satisfies ρ (ag_demand_m Q T b q p d) ↔
      Ag_demand_d (Q.eval ρ) (T.eval ρ) (b.eval ρ) (q.eval ρ) (p.eval ρ) (d.eval ρ) := by
  simp only [ag_demand_m,Ag_demand_d,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,
    check_sat_l M hE,Formula.satisfies_neg_iff,force_at_sat_l,Definitional.Term.eval_weaken]
  apply exists_congr
  intro s
  apply and_congr_right
  intro _
  apply not_congr
  exact forces_env_l hE ag_mem_body_m ag_mem_body_m_freeClosed _ _
    (Fin.cases rfl (Fin.cases (Definitional.Term.eval_weaken ρ s d) (fun i => Fin.elim0 i))) _

def ag_value_body_m : Formula 1 3 := .neg (entry_m (.bound 1) (.bound 2) .newest)

def Ag_value_d (C R c τ q p i x : M.Domain) : Prop := ∃ s t v,
  Check_d M c i s ∧ Check_d M c x t ∧ KPair_d M v q p ∧
    ¬ Forces_d M C R C ag_value_body_m
      (⟨fun k => [τ,s,t].get k,fun _ => τ⟩ : Env M 3) v

def ag_value_m {n} (C R c τ q p i x : Term n) : Formula 1 n := set[n] ⟪∃ s t v,
  ⌜check_m⌝ₚ(⌜c⌝ₛ,⌜i⌝ₛ,s) ∧ ⌜check_m⌝ₚ(⌜c⌝ₛ,⌜x⌝ₛ,t) ∧ ⌜kpair_m⌝ₚ(v,⌜q⌝ₛ,⌜p⌝ₛ) ∧
  ¬ ⌜(fun C R τ s t v => force_at_m ag_value_body_m (Fin.cases τ (Fin.cases s (fun _ => t))) C R C v)⌝ₚ
    (⌜C⌝ₛ,⌜R⌝ₛ,⌜τ⌝ₛ,s,t,v)⟫
derive_free_closed ag_value_body_m
@[simp] theorem ag_value_m_freeClosed {n} (C R c τ q p i x : Term n)
    (hC : C.freeSupport = []) (hR : R.freeSupport = []) (hc : c.freeSupport = [])
    (hτ : τ.freeSupport = []) (hq : q.freeSupport = []) (hp : p.freeSupport = [])
    (hi : i.freeSupport = []) (hx : x.freeSupport = []) :
    (ag_value_m C R c τ q p i x).FreeClosed := by
  simp only [ag_value_m,Definitional.Formula.FreeClosed]
  refine ⟨check_m_freeClosed _ _ _ (by simpa using hc) (by simpa using hi) rfl,
    check_m_freeClosed _ _ _ (by simpa using hc) (by simpa using hx) rfl,
    kpair_m_freeClosed _ _ _ rfl (by simpa using hq) (by simpa using hp),?_⟩
  exact force_at_closed_l _ _ _ _ _ _ ag_value_body_m_freeClosed
    (Fin.cases (by simpa using hτ) (Fin.cases rfl (fun _ => rfl)))
    (by simpa using hC) (by simpa using hR) (by simpa using hC) rfl

theorem ag_value_sat_l (hE : Extensional M) {n} (ρ : Env M n) (C R c τ q p i x : Term n) :
    Formula.satisfies ρ (ag_value_m C R c τ q p i x) ↔
      Ag_value_d (C.eval ρ) (R.eval ρ) (c.eval ρ) (τ.eval ρ) (q.eval ρ) (p.eval ρ) (i.eval ρ) (x.eval ρ) := by
  simp only [ag_value_m,Ag_value_d,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,
    check_sat_l M hE,kpair_sat_l M hE,Formula.satisfies_neg_iff,force_at_sat_l,Definitional.Term.eval_weaken]
  apply exists_congr; intro s
  apply exists_congr; intro t
  apply exists_congr; intro v
  apply and_congr_right; intro _
  apply and_congr_right; intro _
  apply and_congr_right; intro _
  apply not_congr
  exact forces_env_l hE ag_value_body_m ag_value_body_m_freeClosed _ _
    (Fin.cases (by
      change τ.weaken.weaken.weaken.eval (((ρ.push s).push t).push v) = τ.eval ρ
      simp only [Definitional.Term.eval_weaken])
      (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i)))) _

structure Ag_aux_d (I : kpair_convention_l.Interpretation M)
    (ω Q T P U C R b c A h a v : M.Domain) : Prop where
  names : ∀ i p, Entry_d M i p v → (i = b → M.mem p A) ∧ (i ≠ b → M.mem p P)
  decreasing : ∀ i j p r, Entry_d M i p v → Entry_d M j r v → M.SuccessorOf i j → j ≠ b → Entry_d M p r U
  dense : ∀ i d l p n y x q, Entry_d M i d a → Entry_d M l p v → M.SuccessorOf l i →
    Entry_d M n y h → KPair_d M y x q → Gm_even_d I ω n → (M.mem l n ∨ l = n) →
      Ag_demand_d Q T b q p d
  values : ∀ n y x q p τ i k z w r, Entry_d M n y h → KPair_d M y x q → Gm_even_d I ω n → n ≠ b →
    Entry_d M n p v → Entry_d M b τ v → Entry_d M i z h → KPair_d M z w r →
    M.mem k ω → M.IsOrdinalAddition I i k k → (M.mem i n ∨ i = n) → Ag_value_d C R c τ q p k w

def ag_aux_m {d} (ω Q T P U C R b c A h a v : Term d) : Formula 1 d := set[d] ⟪
  (∀ i p, ⌜entry_m⌝ₚ(i,p,⌜v⌝ₛ) → (i = ⌜b⌝ₛ → p ∈ ⌜A⌝ₛ) ∧ (i ≠ ⌜b⌝ₛ → p ∈ ⌜P⌝ₛ)) ∧
  (∀ i j p r, ⌜entry_m⌝ₚ(i,p,⌜v⌝ₛ) → ⌜entry_m⌝ₚ(j,r,⌜v⌝ₛ) →
    ⌜Formula.isSuccessor⌝ₚ(i,j) → j ≠ ⌜b⌝ₛ → ⌜entry_m⌝ₚ(p,r,⌜U⌝ₛ)) ∧
  (∀ i d l p n y x q, ⌜entry_m⌝ₚ(i,d,⌜a⌝ₛ) → ⌜entry_m⌝ₚ(l,p,⌜v⌝ₛ) →
    ⌜Formula.isSuccessor⌝ₚ(l,i) → ⌜entry_m⌝ₚ(n,y,⌜h⌝ₛ) → ⌜kpair_m⌝ₚ(y,x,q) →
    ⌜(gm_even_m (𝒞 := kpair_convention_l))⌝ₚ(⌜ω⌝ₛ,n) → (l ∈ n ∨ l = n) →
      ⌜ag_demand_m⌝ₚ(⌜Q⌝ₛ,⌜T⌝ₛ,⌜b⌝ₛ,q,p,d)) ∧
  (∀ n y x q p τ i k z w r, ⌜entry_m⌝ₚ(n,y,⌜h⌝ₛ) → ⌜kpair_m⌝ₚ(y,x,q) →
    ⌜(gm_even_m (𝒞 := kpair_convention_l))⌝ₚ(⌜ω⌝ₛ,n) → n ≠ ⌜b⌝ₛ →
    ⌜entry_m⌝ₚ(n,p,⌜v⌝ₛ) → ⌜entry_m⌝ₚ(⌜b⌝ₛ,τ,⌜v⌝ₛ) → ⌜entry_m⌝ₚ(i,z,⌜h⌝ₛ) →
    ⌜kpair_m⌝ₚ(z,w,r) → k ∈ ⌜ω⌝ₛ → ⌜Formula.isOrdinalAddition kpair_convention_l⌝ₚ(i,k,k) →
    (i ∈ n ∨ i = n) → ⌜ag_value_m⌝ₚ(⌜C⌝ₛ,⌜R⌝ₛ,⌜c⌝ₛ,τ,q,p,k,w))⟫
derive_free_closed ag_aux_m

theorem ag_aux_sat_l (I : kpair_convention_l.Interpretation M) (hE : Extensional M)
    {d} (ρ : Env M d) (ω Q T P U C R b c A h a v : Term d) :
    Formula.satisfies ρ (ag_aux_m ω Q T P U C R b c A h a v) ↔
      Ag_aux_d I (ω.eval ρ) (Q.eval ρ) (T.eval ρ) (P.eval ρ) (U.eval ρ) (C.eval ρ) (R.eval ρ)
        (b.eval ρ) (c.eval ρ) (A.eval ρ) (h.eval ρ) (a.eval ρ) (v.eval ρ) := by
  simp only [ag_aux_m,Formula.satisfies_conj_iff,Formula.satisfies_forall_iff,Formula.satisfies_imp_iff,
    entry_sat_l M hE,Formula.satisfies_extensionalEq_iff_eq hE,Formula.extensionalNe,
    Formula.satisfies_neg_iff,Formula.satisfies_mem_iff,Formula.satisfies_isSuccessor_iff,
    kpair_sat_l M hE,gm_even_sat_l I hE,Formula.satisfies_disj_iff,ag_demand_sat_l hE,
    Formula.satisfies_isOrdinalAddition_iff I hE,ag_value_sat_l hE,Definitional.Term.eval_weaken]
  exact ⟨fun ⟨a,b,c,d⟩ => ⟨a,b,c,d⟩,fun h => ⟨h.names,h.decreasing,h.dense,h.values⟩⟩

theorem Ag_aux_d.restrict_l {I : kpair_convention_l.Interpretation M}
    {ω Q T P U C R b c A h a v h' a' v' : M.Domain}
    (aux : Ag_aux_d I ω Q T P U C R b c A h a v)
    (hs : M.MemberSubset h' h) (as : M.MemberSubset a' a) (vs : M.MemberSubset v' v) :
    Ag_aux_d I ω Q T P U C R b c A h' a' v' := by
  have edge {s t i x} (sub : M.MemberSubset s t) (ix : Entry_d M i x s) : Entry_d M i x t :=
    ix.elim fun p hp => ⟨p,hp.1,sub p hp.2⟩
  exact ⟨fun i p ip => aux.names i p (edge vs ip),
    fun i j p r ip jr => aux.decreasing i j p r (edge vs ip) (edge vs jr),
    fun i d l p n y x q id lp li ny => aux.dense i d l p n y x q (edge as id) (edge vs lp) li (edge hs ny),
    fun n y x q p τ i k z w r ny yx en nz np bτ iz =>
      aux.values n y x q p τ i k z w r (edge hs ny) yx en nz (edge vs np) (edge vs bτ) (edge hs iz)⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 实际名字值与泛型共尾条件上的非反驳

正向由真值定理得到每个泛型条件上的非反驳；反向只须这些非反驳条件
在给定泛型中共尾。规范名字唯一性把各次见证统一到同一赋值。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project Model.Forcing.Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)

theorem ag_demand_of_value_l {Q T b q p d : M.Domain}
    (O : Cond_order_d M Q T Q) {H : M.Domain → Prop} (generic : Generic_d M Q T Q H)
    (hb : M.mem b Q) (hq : H q)
    (j : M.Domain → (extension_l M hZF Q T Q H).Domain)
    (checks : ∀ x t, Check_d M b x t → Qval_d M Q T Q H t (j x))
    {D : (extension_l M hZF Q T Q H).Domain} (value : Qval_d M Q T Q H d D)
    (member : (extension_l M hZF Q T Q H).mem (j p) D) : Ag_demand_d Q T b q p d := by
  obtain ⟨s,check,_,_⟩ := zf_check_l M hZF hb p
  let ρ := (⟨fun _ => d,fun _ => d⟩ : Env M 1).push s
  let η := (⟨fun _ => D,fun _ => D⟩ : Env (extension_l M hZF Q T Q H) 1).push (j p)
  have values : Env_val_d hZF ρ η := by
    intro t; cases t with
    | free _ => exact value
    | bound k => exact Fin.cases (checks p s check) (fun _ => value) k
  refine ⟨s,check,fun no => ?_⟩
  have denied := (forcing_truth_l O hZF generic ag_mem_body_m ag_mem_body_m_freeClosed ρ η values).mp ⟨q,hq,no⟩
  exact denied member

theorem ag_value_of_cofinal_demand_l {Q T b p d : M.Domain}
    (O : Cond_order_d M Q T Q) {H : M.Domain → Prop} (generic : Generic_d M Q T Q H)
    (hb : M.mem b Q)
    (j : M.Domain → (extension_l M hZF Q T Q H).Domain)
    (checks : ∀ x t, Check_d M b x t → Qval_d M Q T Q H t (j x))
    {D : (extension_l M hZF Q T Q H).Domain} (value : Qval_d M Q T Q H d D)
    (cofinal : ∀ r, H r → ∃ q, H q ∧ Entry_d M q r T ∧ Ag_demand_d Q T b q p d) :
    (extension_l M hZF Q T Q H).mem (j p) D := by
  obtain ⟨s,check,_,_⟩ := zf_check_l M hZF hb p
  let ρ := (⟨fun _ => d,fun _ => d⟩ : Env M 1).push s
  let η := (⟨fun _ => D,fun _ => D⟩ : Env (extension_l M hZF Q T Q H) 1).push (j p)
  have values : Env_val_d hZF ρ η := by
    intro t; cases t with
    | free _ => exact value
    | bound k => exact Fin.cases (checks p s check) (fun _ => value) k
  apply Classical.byContradiction
  intro denied
  obtain ⟨r,hr,forced⟩ := (forcing_truth_l O hZF generic ag_mem_body_m ag_mem_body_m_freeClosed ρ η values).mpr denied
  obtain ⟨q,hq,qr,s',check',no⟩ := cofinal r hr
  have eq := check_unique_l M hZF.1 (check_ind_l M hZF) b p s' s check' check
  subst s'
  exact no ((forces_regular_l O hZF ag_mem_body_m ρ (env_val_name_l hZF values)).1 r q
    (generic.proper r hr).1 ⟨(generic.proper q hq).1,(generic.proper q hq).2,qr⟩ forced)

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 积共尾非反驳给出函数名字的真实坐标值

规范名字的唯一性统一各回合的检查见证。若积扩张否定指定条目，真值定理
给出泛型中的反驳条件；同轮共尾加强违反辅助树的值约束。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project Model.Forcing.Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)

theorem ag_entry_of_cofinal_value_l {C R c τ i x : M.Domain}
    (O : Cond_order_d M C R C) {G : M.Domain → Prop} (generic : Generic_d M C R C G)
    (hc : M.mem c C)
    (j : M.Domain → (extension_l M hZF C R C G).Domain)
    (checks : ∀ x t, Check_d M c x t → Qval_d M C R C G t (j x))
    {y : (extension_l M hZF C R C G).Domain} (value : Qval_d M C R C G τ y)
    (cofinal : ∀ p, G p → ∃ v, G v ∧ Entry_d M v p R ∧ ∃ q r, KPair_d M v q r ∧ Ag_value_d C R c τ q r i x) :
    Entry_d (extension_l M hZF C R C G) (j i) (j x) y := by
  let E := extension_l M hZF C R C G
  obtain ⟨s,cs,_,_⟩ := zf_check_l M hZF hc i
  obtain ⟨t,ct,_,_⟩ := zf_check_l M hZF hc x
  let ρ : Env M 3 := ⟨fun k => [τ,s,t].get k,fun _ => τ⟩
  let η : Env E 3 := ⟨fun k => [y,j i,j x].get k,fun _ => y⟩
  have values : Env_val_d hZF ρ η := by
    intro a; cases a with
    | free _ => exact value
    | bound k => exact Fin.cases value (Fin.cases (checks i s cs) (Fin.cases (checks x t ct) (fun k => Fin.elim0 k))) k
  apply Classical.byContradiction
  intro denied
  have no : Formula.satisfies η ag_value_body_m := by
    simpa only [ag_value_body_m,Formula.satisfies_neg_iff,entry_sat_l E (extension_ext_l O hZF generic)] using! denied
  obtain ⟨p,hp,forced⟩ := (forcing_truth_l O hZF generic ag_value_body_m ag_value_body_m_freeClosed ρ η values).mpr no
  obtain ⟨v,hv,vp,q,r,pair,s',t',v',cs',ct',pair',notforced⟩ := cofinal p hp
  have es := check_unique_l M hZF.1 (check_ind_l M hZF) c i s' s cs' cs
  have et := check_unique_l M hZF.1 (check_ind_l M hZF) c x t' t ct' ct
  have ev := kpair_unique_l M hZF.1 pair' pair
  subst s' t' v'
  exact notforced ((forces_regular_l O hZF ag_value_body_m ρ (env_val_name_l hZF values)).1 p v
    (generic.proper p hp).1 ⟨(generic.proper v hv).1,(generic.proper v hv).2,vp⟩ forced)

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 7.23 辅助树的实际构造

节点由同域三图合成：原合法历史、稠密名字列、函数名字后接大条件列。
全部非反驳条件由原力迫公式表达；限制三图同时保持合法性和这些条件。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project Descriptive InnerModel Internal Model.Forcing.Internal
universe u
variable {M : Structure.{u}}

def Ag_node_d (I : kpair_convention_l.Interpretation M)
    (ω Q T P U C R b c N A R₀ D V q : M.Domain) : Prop :=
  ∃ n h a v, M.mem n ω ∧ Fn0_d n A h ∧ M.mem h R₀ ∧ Fn0_d n D a ∧ Fn0_d n V v ∧
    Tg_join_d I n h a v q ∧ Ag_aux_d I ω Q T P U C R b c N h a v

def ag_node_m {d} (ω Q T P U C R b c N A R₀ D V q : Term d) : Formula 1 d := set[d] ⟪∃ n h a v,
  n ∈ ⌜ω⌝ₛ ∧ ⌜fn0_m⌝ₚ(n,⌜A⌝ₛ,h) ∧ h ∈ ⌜R₀⌝ₛ ∧ ⌜fn0_m⌝ₚ(n,⌜D⌝ₛ,a) ∧
  ⌜fn0_m⌝ₚ(n,⌜V⌝ₛ,v) ∧ ⌜tg_join_m⌝ₚ(n,h,a,v,⌜q⌝ₛ) ∧
  ⌜ag_aux_m⌝ₚ(⌜ω⌝ₛ,⌜Q⌝ₛ,⌜T⌝ₛ,⌜P⌝ₛ,⌜U⌝ₛ,⌜C⌝ₛ,⌜R⌝ₛ,⌜b⌝ₛ,⌜c⌝ₛ,⌜N⌝ₛ,h,a,v)⟫
derive_free_closed ag_node_m

theorem ag_node_sat_l (I : kpair_convention_l.Interpretation M) (hE : Extensional M)
    {d} (ρ : Env M d) (ω Q T P U C R b c N A R₀ D V q : Term d) :
    Formula.satisfies ρ (ag_node_m ω Q T P U C R b c N A R₀ D V q) ↔
      Ag_node_d I (ω.eval ρ) (Q.eval ρ) (T.eval ρ) (P.eval ρ) (U.eval ρ) (C.eval ρ) (R.eval ρ)
        (b.eval ρ) (c.eval ρ) (N.eval ρ) (A.eval ρ) (R₀.eval ρ) (D.eval ρ) (V.eval ρ) (q.eval ρ) := by
  simp only [ag_node_m,Ag_node_d,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,
    Formula.satisfies_mem_iff,fn0_sat_l hE,tg_join_sat_l I hE,ag_aux_sat_l I hE,Definitional.Term.eval_weaken]
  rfl

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

structure Ag_tree_d (ω Q T P U C R b c N A R₀ D V Z Y F S : M.Domain) : Prop where
  second : ∀ v, M.mem v V ↔ M.mem v N ∨ M.mem v P
  pair : M.IsCartesianProduct I Z D V
  triple : M.IsCartesianProduct I Y A Z
  space : Fseq_space_d I ω Y F
  nodes : ∀ q, M.mem q S ↔ M.mem q F ∧ Ag_node_d I ω Q T P U C R b c N A R₀ D V q

theorem ag_tree_l {ω : M.Domain} (hw : M.IsOmega ω) (Q T P U C R b c N A R₀ D : M.Domain) :
    ∃ V Z Y F S, Ag_tree_d hZF ω Q T P U C R b c N A R₀ D V Z Y F S := by
  obtain ⟨V,second⟩ := KP.exists_unionOfTwo (ZF.modelsKP hZF) N P
  obtain ⟨Z,pair⟩ := ZF.exists_cartesianProduct hZF I D V
  obtain ⟨Y,triple⟩ := ZF.exists_cartesianProduct hZF I A Z
  obtain ⟨F,space⟩ := ZF.fseq_space_exists_l I hZF hw Y
  let ρ : Env M 14 := ⟨fun i => [ω,Q,T,P,U,C,R,b,c,N,A,R₀,D,V].get i,fun _ => ω⟩
  let φ : UnarySchema 14 := {
    body := ag_node_m (.bound 1) (.bound 2) (.bound 3) (.bound 4) (.bound 5) (.bound 6) (.bound 7)
      (.bound 8) (.bound 9) (.bound 10) (.bound 11) (.bound 12) (.bound 13) (.bound 14) .newest }
  obtain ⟨S,read⟩ := ZF.separation_exists_d hZF φ ρ F
  exact ⟨V,Z,Y,F,S,second,pair,triple,space,fun q =>
    (read q).trans (and_congr_right fun _ => ag_node_sat_l I hZF.1 ..)⟩

theorem Ag_tree_d.tree_l {ω Q T P U C R b c N A R₀ D V Z Y F S F₀ : M.Domain}
    (aux : Ag_tree_d hZF ω Q T P U C R b c N A R₀ D V Z Y F S)
    (inputs : Fseq_space_d I ω A F₀) (legal : Tree_d F₀ R₀) : Tree_d F S := by
  refine ⟨fun q hq => ((aux.nodes q).mp hq).1,?_⟩
  intro q hq q' hq' sub
  obtain ⟨_,n,h,a,v,hn,fh,hr,fa,fv,join,conditions⟩ := (aux.nodes q).mp hq
  obtain ⟨m,hm,fq'⟩ := (aux.space q').mp hq'
  have mn : M.MemberSubset m n := by
    intro i hi
    obtain ⟨p,_,ip⟩ := fq'.2.2 i hi
    exact (join.1.2 i).mpr ⟨p,ip.elim fun z hz => ⟨z,hz.1,sub z hz.2⟩⟩
  obtain ⟨h',rh⟩ := ZF.exists_restriction hZF I h m
  obtain ⟨a',ra⟩ := ZF.exists_restriction hZF I a m
  obtain ⟨v',rv⟩ := ZF.exists_restriction hZF I v m
  have fh' := rh.isSetFunctionFromTo (fn0_function_l (ZF.modelsKP hZF) fh) mn
  have fa' := ra.isSetFunctionFromTo (fn0_function_l (ZF.modelsKP hZF) fa) mn
  have fv' := rv.isSetFunctionFromTo (fn0_function_l (ZF.modelsKP hZF) fv) mn
  have sh := (ds_restrict_iff_l I fh' (fn0_function_l (ZF.modelsKP hZF) fh).1).mp rh
  have sa := (ds_restrict_iff_l I fa' (fn0_function_l (ZF.modelsKP hZF) fa).1).mp ra
  have sv := (ds_restrict_iff_l I fv' (fn0_function_l (ZF.modelsKP hZF) fv).1).mp rv
  refine (aux.nodes q').mpr ⟨hq',m,h',a',v',hm,fn0_of_function_l (ZF.modelsKP hZF) fh',
    legal.2 h hr h' ((inputs h').mpr ⟨m,hm,fh'⟩) sh,
    fn0_of_function_l (ZF.modelsKP hZF) fa',fn0_of_function_l (ZF.modelsKP hZF) fv',
    ⟨⟨fq'.1,fq'.2.1⟩,?_⟩,conditions.restrict_l sh sa sv⟩
  intro i hi
  obtain ⟨x,y,z,w,p,ix,iy,iz,wp,pw,ip⟩ := join.2 i (mn i hi)
  obtain ⟨p',_,ip'⟩ := fq'.2.2 i hi
  have eq := join.1.1.2 i p' p (ip'.elim fun r hr => ⟨r,hr.1,sub r hr.2⟩) ip
  exact ⟨x,y,z,w,p,(rh.2 i x).mpr ⟨hi,ix⟩,(ra.2 i y).mpr ⟨hi,iy⟩,
    (rv.2 i z).mpr ⟨hi,iz⟩,wp,pw,eq ▸ ip'⟩

theorem Ag_tree_d.demanding_l {ω Q T P U C R b c N A R₀ D V Z Y F S F₀ : M.Domain}
    (aux : Ag_tree_d hZF ω Q T P U C R b c N A R₀ D V Z Y F S)
    (inputs : Fseq_space_d I ω A F₀) (legal : Tree_d F₀ R₀) : Td_tree_d I ω A S :=
  td_tree_of_l I aux.space (aux.tree_l hZF inputs legal) aux.pair aux.triple

theorem Ag_tree_d.root_l {ω Q T P U C R b c N A R₀ D V Z Y F S e : M.Domain}
    (aux : Ag_tree_d hZF ω Q T P U C R b c N A R₀ D V Z Y F S)
    (hw : M.IsOmega ω) (empty : ∀ x, ¬ M.mem x e) (root : M.mem e R₀) : M.mem e S := by
  have he := num_mem_l hZF.1 hw (show Num_d 0 e from empty)
  have no i x : ¬ Entry_d M i x e := fun ⟨p,_,hp⟩ => empty p hp
  have fn X : Fn0_d e X e := fn0_of_function_l (ZF.modelsKP hZF) (ds_empty_fun_l I empty)
  refine (aux.nodes e).mpr ⟨(aux.space e).mpr ⟨e,he,ds_empty_fun_l I empty⟩,
    e,e,e,e,he,fn A,root,fn D,fn V,⟨tg_graph_empty_l I empty,fun i hi => (empty i hi).elim⟩,?_⟩
  exact ⟨fun i p ip => (no i p ip).elim,fun i _ p _ ip => (no i p ip).elim,
    fun i d _ _ _ _ _ _ id => (no i d id).elim,fun n y _ _ _ _ _ _ _ _ _ ny => (no n y ny).elim⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 专用辅助树的实际第一字母域

任意稠密名字都能出现在一项节点中：首个大坐标只选择已有函数名字，
尚无大条件或旧值约束。故第一最小出现域恰为原稠密名字族。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project Descriptive InnerModel Internal Model.Forcing.Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Ag_tree_d.letter_l {ω Q T P U C R b c N A R₀ D V Z Y F S : M.Domain}
    (aux : Ag_tree_d hZF ω Q T P U C R b c N A R₀ D V Z Y F S)
    {side : Bool} {z} (letter : Td_letter_d side S z) :
    if side then M.mem z V else M.mem z D := by
  obtain ⟨q,i,p,x,a,v,t,hq,ip,px,av,eq⟩ := letter
  obtain ⟨_,_,fq⟩ := (aux.space q).mp ((aux.nodes q).mp hq).1
  obtain ⟨x',_,t',ht,px'⟩ := (aux.triple p).mp (fq.output_mem_of_pairMember ip)
  obtain ⟨_,et⟩ := kpair_injective_l M px px'
  obtain ⟨a',ha,v',hv,av'⟩ := (aux.pair t').mp ht
  obtain ⟨ea,ev⟩ := kpair_injective_l M (et ▸ av) av'
  cases side
  · exact eq.symm ▸ ea.symm ▸ ha
  · exact eq.symm ▸ ev.symm ▸ hv

theorem Ag_tree_d.first_l {ω X Q T E B A F₀ R₀ P U C R b c N D V Z Y F S d τ x q : M.Domain}
    (game : Ag_game_d hZF ω X Q T E B A F₀ R₀)
    (aux : Ag_tree_d hZF ω Q T P U C R b c N A R₀ D V Z Y F S)
    (hw : M.IsOmega ω) (empty : ∀ z, ¬ M.mem z b)
    (hx : M.mem x X) (hq : M.mem q Q) (hd : M.mem d D) (hτ : M.mem τ N) :
    Td_letter_d false S d ∧ Td_letter_d true S τ := by
  have hb := num_mem_l hZF.1 hw (show Num_d 0 b from empty)
  obtain ⟨n,succ,hn⟩ := hw.1.2 b hb
  have one i (hi : M.mem i n) : i = b :=
    ((succ i).mp hi).elim (fun hi => (empty i hi).elim) (hZF.1.eq_of_same_members i b)
  obtain ⟨y,pair⟩ := (I).total x q
  have hy := (game.alphabet y).mpr (Or.inl ((game.pair y).mpr ⟨x,hx,q,hq,pair⟩))
  obtain ⟨h,fh,hvalues⟩ := ZF.exists_constantFunction hZF I (source := n) hy
  obtain ⟨a,fa,avalues⟩ := ZF.exists_constantFunction hZF I (source := n) hd
  obtain ⟨v,fv,vvalues⟩ := ZF.exists_constantFunction hZF I (source := n) ((aux.second τ).mpr (Or.inl hτ))
  have legal : M.mem h R₀ := by
    refine (game.legal h).mpr ⟨(game.space h).mpr ⟨n,hn,fh⟩,fun i z iz => ?_⟩
    obtain ⟨hi,eq⟩ := (hvalues i z).mp iz
    subst z
    have eq := one i hi
    subst i
    exact ⟨fun _ => ⟨x,q,hx,hq,pair,fun k _ bk _ => (empty k bk.predecessor_mem).elim⟩,
      fun odd => (odd (gm_even_zero_l I hZF hw empty)).elim⟩
  have conditions : Ag_aux_d I ω Q T P U C R b c N h a v := by
    refine ⟨?_,?_,?_,?_⟩
    · intro i p ip
      obtain ⟨hi,eq⟩ := (vvalues i p).mp ip
      exact ⟨fun _ => eq.symm ▸ hτ,fun nz => (nz (one i hi)).elim⟩
    · intro i j p r ip jr ij _
      have eq := one i (fv.input_mem_of_pairMember ip)
      exact (empty j (eq ▸ ij.predecessor_mem)).elim
    · intro i d l p _ _ _ _ _ lp li
      have eq := one l (fv.input_mem_of_pairMember lp)
      exact (empty i (eq ▸ li.predecessor_mem)).elim
    · intro i y _ _ _ _ _ _ _ _ _ iy _ _ nz
      exact (nz (one i (fh.input_mem_of_pairMember iy))).elim
  obtain ⟨_,_,t,_,_,_,join⟩ := tg_join_exists_l I hZF fh fa fv
  have fh₀ := fn0_of_function_l (ZF.modelsKP hZF) fh
  have fa₀ := fn0_of_function_l (ZF.modelsKP hZF) fa
  have fv₀ := fn0_of_function_l (ZF.modelsKP hZF) fv
  have typed := join.typed_l hZF fh₀ fa₀ fv₀ aux.pair aux.triple
  have ht : M.mem t S := (aux.nodes t).mpr ⟨(aux.space t).mpr
    ⟨n,hn,fn0_function_l (ZF.modelsKP hZF) typed⟩,n,h,a,v,hn,fh₀,legal,fa₀,fv₀,join,conditions⟩
  obtain ⟨y',d',τ',w,p,iy,id,it,wp,pw,ip⟩ := join.2 b succ.predecessor_mem
  have ed := ((avalues b d').mp id).2
  have et := ((vvalues b τ').mp it).2
  exact ⟨⟨t,b,p,y',d',τ',w,ht,ip,pw,wp,ed.symm⟩,
    ⟨t,b,p,y',d',τ',w,ht,ip,pw,wp,et.symm⟩⟩

theorem Ag_tree_d.alphabet_l {ω X Q T E B A F₀ R₀ P U C R b c N D V Z Y F S : M.Domain}
    (game : Ag_game_d hZF ω X Q T E B A F₀ R₀)
    (aux : Ag_tree_d hZF ω Q T P U C R b c N A R₀ D V Z Y F S)
    (hw : M.IsOmega ω) (empty : ∀ z, ¬ M.mem z b)
    (inh : ∃ x, M.mem x X) (nonempty : ∃ q, M.mem q Q) (names : ∃ τ, M.mem τ N) :
    ∃ V₀, Td_alphabet_d S D V₀ ∧ M.MemberSubset V₀ V := by
  obtain ⟨D₀,V₀,alphabet⟩ := td_alphabet_exists_l hZF S
  have eq : D₀ = D := hZF.1.eq_of_same_members D₀ D (fun d => by
    constructor
    · intro hd
      exact aux.letter_l hZF ((alphabet.1 d).mp hd)
    · intro hd
      obtain ⟨x,hx⟩ := inh
      obtain ⟨q,hq⟩ := nonempty
      obtain ⟨τ,hτ⟩ := names
      exact (alphabet.1 d).mpr (aux.first_l hZF game hw empty hx hq hd hτ).1)
  subst D₀
  exact ⟨V₀,alphabet,fun z hz => aux.letter_l hZF ((alphabet.2 z).mp hz)⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 原树像中的分支逐项回读原生有限约束

取同一三坐标分支的长度 n 前缀，沿成员满包含拉回原节点。配对单射性
识别其三个坐标，因此所有非反驳约束都在原强迫模型中读取。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project Descriptive InnerModel Internal Model.Forcing.Internal
universe u v
variable {M : Structure.{u}} {N : Structure.{v}} (hM : M.Models ZF) (hN : N.Models ZF)
  (j : M.Domain → N.Domain) (inj : Function.Injective j)
  (full : ∀ a y, N.mem y (j a) ↔ ∃ x, M.mem x a ∧ j x = y)
local notation "I" => kp_pair_l (ZF.modelsKP hM)
local notation "J" => kp_pair_l (ZF.modelsKP hN)
include inj full

theorem Ag_tree_d.prefix_l {ω Q T P U C R b c D A R₀ L V Z Y F S : M.Domain}
    (tree : Ag_tree_d hM ω Q T P U C R b c D A R₀ L V Z Y F S)
    (hw : M.IsOmega ω) (hw' : N.IsOmega (j ω))
    {X₀ X₁ X₂ f a v q : N.Domain}
    (ff : Fn0_d (j ω) X₀ f) (fa : Fn0_d (j ω) X₁ a) (fv : Fn0_d (j ω) X₂ v)
    (fq : Fn0_d (j ω) (j Y) q) (branch : Branch_d (j F) (j S) q)
    (join : Tg_join_d J (j ω) f a v q) {n : M.Domain} (hn : M.mem n ω) :
    ∃ h₀ a₀ v₀, Fn0_d n A h₀ ∧ M.mem h₀ R₀ ∧ Fn0_d n L a₀ ∧ Fn0_d n V v₀ ∧
      Ag_aux_d I ω Q T P U C R b c D h₀ a₀ v₀ ∧
      N.IsRestrictionOf J (j h₀) f (j n) ∧ N.IsRestrictionOf J (j a₀) a (j n) ∧
      N.IsRestrictionOf J (j v₀) v (j n) := by
  have entry := image_entry_iff_l j inj full (KP.exists_pair (ZF.modelsKP hM)) hN.1
  have member {x y : M.Domain} : N.mem (j x) (j y) ↔ M.mem x y := image_member_l j inj full
  obtain ⟨t,ft,cut,_⟩ := ds_prefix_l J hN hw' (fn0_function_l (ZF.modelsKP hN) fq) (member.mpr hn)
  have tS := branch t ((image_fseq_l hM hN j inj full hw hw' tree.space t).mpr ⟨j n,member.mpr hn,ft⟩)
    ((ds_restrict_iff_l J ft (fn0_function_l (ZF.modelsKP hN) fq).1).mp cut)
  obtain ⟨t₀,ht₀,eqt⟩ := (full S t).mp tS
  subst t
  obtain ⟨_,m,h₀,a₀,v₀,hm,fh₀,hr,fa₀,fv₀,joined,aux⟩ := (tree.nodes t₀).mp ht₀
  have typed := joined.typed_l hM fh₀ fa₀ fv₀ tree.pair tree.triple
  have mapped : N.IsSetFunctionFromTo J (j t₀) (j m) (j Y) :=
    image_function_l j inj full (fn0_function_l (ZF.modelsKP hM) typed)
  have eq := inj (mapped.2.1.eq hN.1 ft.2.1)
  subst m
  have coords i (hi : M.mem i n) : ∃ x d p,
      Entry_d M i x h₀ ∧ Entry_d N (j i) (j x) f ∧ Entry_d M i d a₀ ∧ Entry_d N (j i) (j d) a ∧
      Entry_d M i p v₀ ∧ Entry_d N (j i) (j p) v := by
    obtain ⟨x,d,p,z,y,ix,id,ip,zp,yz,iy⟩ := joined.2 i hi
    have iy' := ((cut.2 (j i) (j y)).mp ((entry i y t₀).mp iy)).2
    obtain ⟨x',d',p',z',y',ix',id',ip',zp',yz',iy''⟩ := join.2 (j i)
      (member.mpr (hw.transitive (ZF.modelsKP hM) n hn i hi))
    have eq := (fn0_function_l (ZF.modelsKP hN) fq).1.2 (j i) (j y) y' iy' iy''
    obtain ⟨ex,ez⟩ := (J).injective (eq ▸ image_kpair_l j full yz) yz'
    obtain ⟨ed,ep⟩ := (J).injective (ez ▸ image_kpair_l j full zp) zp'
    exact ⟨x,d,p,ix,ex.symm ▸ ix',id,ed.symm ▸ id',ip,ep.symm ▸ ip'⟩
  have restrict {B s X g} (fs : Fn0_d n B s) (fg : Fn0_d (j ω) X g)
      (points : ∀ i y, Entry_d M i y s → Entry_d N (j i) (j y) g) : N.IsRestrictionOf J (j s) g (j n) := by
    have mapped : N.IsSetFunctionFromTo J (j s) (j n) (j B) :=
      image_function_l j inj full (fn0_function_l (ZF.modelsKP hM) fs)
    apply (ds_restrict_iff_l J mapped (fn0_function_l (ZF.modelsKP hN) fg).1).mpr
    intro z hz
    obtain ⟨r,hr,rj⟩ := (full s z).mp hz
    obtain ⟨i,y,pair⟩ := (fn0_function_l (ZF.modelsKP hM) fs).1.1 r hr
    obtain ⟨w,wp,wg⟩ := points i y ⟨r,pair,hr⟩
    exact (rj ▸ (J).unique wp (image_kpair_l j full pair)) ▸ wg
  refine ⟨h₀,a₀,v₀,fh₀,hr,fa₀,fv₀,aux,restrict fh₀ ff ?_,restrict fa₀ fa ?_,restrict fv₀ fv ?_⟩
  · intro i y iy
    obtain ⟨x,_,_,ix,ix',_⟩ := coords i (fh₀.bound_l iy).1
    exact congrArg j ((fn0_function_l (ZF.modelsKP hM) fh₀).1.2 i x y ix iy) ▸ ix'
  · intro i y iy
    obtain ⟨_,d,_,_,_,id,id',_⟩ := coords i (fa₀.bound_l iy).1
    exact congrArg j ((fn0_function_l (ZF.modelsKP hM) fa₀).1.2 i d y id iy) ▸ id'
  · intro i y iy
    obtain ⟨_,_,p,_,_,_,_,ip,ip'⟩ := coords i (fv₀.bound_l iy).1
    exact congrArg j ((fn0_function_l (ZF.modelsKP hM) fv₀).1.2 i p y ip iy) ▸ ip'

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 无限辅助分支的原生强迫约束

每项断言取一个同时覆盖其全部坐标的真实有限前缀。图条目在环境中读出，
强迫及非反驳断言仍属于原生模型；不要求无限图属于该模型。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project Descriptive InnerModel Internal Model.Forcing.Internal
universe u v
variable {M : Structure.{u}} {N : Structure.{v}} (hM : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hM)

structure Ag_read_d (ω Q T P U C R b c D : M.Domain) (j : M.Domain → N.Domain) (f a v : N.Domain) : Prop where
  names : ∀ i p, Entry_d N (j i) (j p) v → (i = b → M.mem p D) ∧ (i ≠ b → M.mem p P)
  decreasing : ∀ i k p r, Entry_d N (j i) (j p) v → Entry_d N (j k) (j r) v →
    M.SuccessorOf i k → k ≠ b → Entry_d M p r U
  dense : ∀ i d l p n y x q, Entry_d N (j i) (j d) a → Entry_d N (j l) (j p) v → M.SuccessorOf l i →
    Entry_d N (j n) (j y) f → KPair_d M y x q → Gm_even_d I ω n → (M.mem l n ∨ l = n) →
      Ag_demand_d Q T b q p d
  values : ∀ n y x q p τ i k z w r, Entry_d N (j n) (j y) f → KPair_d M y x q →
    Gm_even_d I ω n → n ≠ b → Entry_d N (j n) (j p) v → Entry_d N (j b) (j τ) v →
    Entry_d N (j i) (j z) f → KPair_d M z w r → M.mem k ω → M.IsOrdinalAddition I i k k →
    (M.mem i n ∨ i = n) → Ag_value_d C R c τ q p k w

variable (hN : N.Models ZF) (j : M.Domain → N.Domain) (inj : Function.Injective j)
  (full : ∀ a y, N.mem y (j a) ↔ ∃ x, M.mem x a ∧ j x = y)
local notation "J" => kp_pair_l (ZF.modelsKP hN)
include inj full

theorem Ag_tree_d.read_l {ω Q T P U C R b c D A R₀ L V Z Y F S : M.Domain}
    (tree : Ag_tree_d hM ω Q T P U C R b c D A R₀ L V Z Y F S)
    (hw : M.IsOmega ω) (hw' : N.IsOmega (j ω)) (empty : ∀ x, ¬ M.mem x b)
    {X₀ X₁ X₂ f a v q : N.Domain}
    (ff : Fn0_d (j ω) X₀ f) (fa : Fn0_d (j ω) X₁ a) (fv : Fn0_d (j ω) X₂ v)
    (fq : Fn0_d (j ω) (j Y) q) (branch : Branch_d (j F) (j S) q)
    (join : Tg_join_d J (j ω) f a v q) : Ag_read_d hM ω Q T P U C R b c D j f a v := by
  have member {x y : M.Domain} : N.mem (j x) (j y) ↔ M.mem x y := image_member_l j inj full
  have pull {s g n i x} (cut : N.IsRestrictionOf J (j s) g (j n)) (hi : M.mem i n)
      (ix : Entry_d N (j i) (j x) g) : Entry_d M i x s :=
    (image_entry_iff_l j inj full (KP.exists_pair (ZF.modelsKP hM)) hN.1 i x s).mpr
      ((cut.2 (j i) (j x)).mpr ⟨member.mpr hi,ix⟩)
  have finite {n} (hn : M.mem n ω) := tree.prefix_l hM hN j inj full hw hw' ff fa fv fq branch join hn
  refine ⟨?_,?_,?_,?_⟩
  · intro i p ip
    have hi := member.mp (fv.bound_l ip).1
    obtain ⟨n,succ,hn⟩ := hw.1.2 i hi
    obtain ⟨_,_,_,_,_,_,_,aux,_,_,rv⟩ := finite hn
    exact aux.names i p (pull rv succ.predecessor_mem ip)
  · intro i k p r ip kr ik ne
    have hi := member.mp (fv.bound_l ip).1
    obtain ⟨n,succ,hn⟩ := hw.1.2 i hi
    obtain ⟨_,_,_,_,_,_,_,aux,_,_,rv⟩ := finite hn
    exact aux.decreasing i k p r (pull rv succ.predecessor_mem ip)
      (pull rv ((succ k).mpr (Or.inl ik.predecessor_mem)) kr) ik ne
  · intro i d l p n y x q id lp li ny pair even ln
    have hn := member.mp (ff.bound_l ny).1
    obtain ⟨m,succ,hm⟩ := hw.1.2 n hn
    obtain ⟨_,_,_,_,_,_,_,aux,rh,ra,rv⟩ := finite hm
    have lm : M.mem l m := ln.elim (fun h => (succ l).mpr (Or.inl h)) (fun eq => eq.symm ▸ succ.predecessor_mem)
    have im := (hw.members_areOrdinals (ZF.modelsKP hM) m hm).transitive l lm i li.predecessor_mem
    exact aux.dense i d l p n y x q (pull ra im id) (pull rv lm lp) li
      (pull rh succ.predecessor_mem ny) pair even ln
  · intro n y x q p τ i k z w r ny pair even nz np bτ iz pair' hk add hin
    have hn := member.mp (ff.bound_l ny).1
    obtain ⟨m,succ,hm⟩ := hw.1.2 n hn
    obtain ⟨_,_,_,_,_,_,_,aux,rh,_,rv⟩ := finite hm
    have im : M.mem i m := hin.elim (fun h => (succ i).mpr (Or.inl h)) (fun eq => eq.symm ▸ succ.predecessor_mem)
    have bn : M.mem b n := by
      have hb := num_mem_l hM.1 hw (show Num_d 0 b from empty)
      rcases (hw.isOrdinal (ZF.modelsKP hM)).wellOrder.linear.compare b hb n hn with eq | bn | nb
      · exact (nz (hM.1.eq_of_same_members b n eq).symm).elim
      · exact bn
      · exact (empty n nb).elim
    exact aux.values n y x q p τ i k z w r (pull rh succ.predecessor_mem ny) pair even nz
      (pull rv succ.predecessor_mem np) (pull rv ((succ b).mpr (Or.inl bn)) bτ)
      (pull rh im iz) pair' hk add hin

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 原专用辅助树沿完整初等腿运输

十八个参数始终是同一小、大力迫、名字族、合法树与辅助树的像。
强迫谓词只在源、目标各自的原生模型中解释，不宣称它对传递包含绝对。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

def ag_tree_m {d} (v : Fin 18 → Term d) : Formula 1 d := set[d] ⟪
  (∀ x, x ∈ ⌜v 13⌝ₛ ↔ x ∈ ⌜v 9⌝ₛ ∨ x ∈ ⌜v 3⌝ₛ) ∧
  ⌜(Formula.isCartesianProduct kpair_convention_l)⌝ₚ(⌜v 14⌝ₛ,⌜v 12⌝ₛ,⌜v 13⌝ₛ) ∧
  ⌜(Formula.isCartesianProduct kpair_convention_l)⌝ₚ(⌜v 15⌝ₛ,⌜v 10⌝ₛ,⌜v 14⌝ₛ) ∧
  ⌜(fseq_space_m (𝒞 := kpair_convention_l))⌝ₚ(⌜v 0⌝ₛ,⌜v 15⌝ₛ,⌜v 16⌝ₛ) ∧
  (∀ q, q ∈ ⌜v 17⌝ₛ ↔ q ∈ ⌜v 16⌝ₛ ∧
    ⌜ag_node_m⌝ₚ(⌜v 0⌝ₛ,⌜v 1⌝ₛ,⌜v 2⌝ₛ,⌜v 3⌝ₛ,⌜v 4⌝ₛ,⌜v 5⌝ₛ,⌜v 6⌝ₛ,
      ⌜v 7⌝ₛ,⌜v 8⌝ₛ,⌜v 9⌝ₛ,⌜v 10⌝ₛ,⌜v 11⌝ₛ,⌜v 12⌝ₛ,⌜v 13⌝ₛ,q))⟫

@[simp] theorem ag_tree_closed_l {d} (v : Fin 18 → Term d) (hv : ∀ i, (v i).freeSupport = []) :
    (ag_tree_m v).FreeClosed := by
  simp -implicitDefEqProofs [ag_tree_m,Definitional.Formula.FreeClosed,hv]

theorem ag_tree_sat_l {d} (ρ : Env M d) (v : Fin 18 → Term d) :
    Formula.satisfies ρ (ag_tree_m v) ↔
      Ag_tree_d hZF ((v 0).eval ρ) ((v 1).eval ρ) ((v 2).eval ρ) ((v 3).eval ρ) ((v 4).eval ρ)
        ((v 5).eval ρ) ((v 6).eval ρ) ((v 7).eval ρ) ((v 8).eval ρ) ((v 9).eval ρ)
        ((v 10).eval ρ) ((v 11).eval ρ) ((v 12).eval ρ) ((v 13).eval ρ) ((v 14).eval ρ)
        ((v 15).eval ρ) ((v 16).eval ρ) ((v 17).eval ρ) := by
  simp only [ag_tree_m,Formula.satisfies_conj_iff,Formula.satisfies_forall_iff,
    Formula.satisfies_iff_iff,Formula.satisfies_disj_iff,Formula.satisfies_mem_iff,
    Formula.satisfies_isCartesianProduct_iff I,fseq_space_sat_l I hZF.1,
    ag_node_sat_l I hZF.1,Definitional.Term.eval_weaken]
  exact ⟨fun ⟨a,b,c,d,e⟩ => ⟨a,b,c,d,e⟩,fun h => ⟨h.second,h.pair,h.triple,h.space,h.nodes⟩⟩

/-- 第十九项是第二最小字母域；第一最小字母域就是第十二项稠密名字族。 -/
structure Ag_frame_d (v : Fin 19 → M.Domain) : Prop where
  omega : M.IsOmega (v 0)
  empty : ∀ x, ¬ M.mem x (v 7)
  auxiliary : Ag_tree_d hZF (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) (v 8)
    (v 9) (v 10) (v 11) (v 12) (v 13) (v 14) (v 15) (v 16) (v 17)
  tree : Tree_d (v 16) (v 17)
  alphabet : Td_alphabet_d (v 17) (v 12) (v 18)

def ag_frame_m {d} (v : Fin 19 → Term d) : Formula 1 d :=
  .conj (Formula.isOmega (v 0)) (.conj (Formula.isEmpty (v 7))
    (.conj (ag_tree_m (fun i => v i.castSucc))
      (.conj (tree_m (v 16) (v 17)) (td_alphabet_m (v 17) (v 12) (v 18)))))

@[simp] theorem ag_frame_closed_l {d} (v : Fin 19 → Term d) (hv : ∀ i, (v i).freeSupport = []) :
    (ag_frame_m v).FreeClosed := by
  simp -implicitDefEqProofs [ag_frame_m,Definitional.Formula.FreeClosed,hv]

theorem ag_frame_sat_l {d} (ρ : Env M d) (v : Fin 19 → Term d) :
    Formula.satisfies ρ (ag_frame_m v) ↔ Ag_frame_d hZF (fun i => (v i).eval ρ) := by
  simp only [ag_frame_m,Formula.satisfies_conj_iff,Formula.satisfies_isOmega_iff,
    Formula.satisfies_isEmpty_iff,ag_tree_sat_l hZF,tree_sat_l,td_alphabet_sat_l hZF.1]
  exact ⟨fun ⟨a,b,c,d,e⟩ => ⟨a,b,c,d,e⟩,fun h => ⟨h.omega,h.empty,h.auxiliary,h.tree,h.alphabet⟩⟩

theorem Ag_frame_d.native_map_l {Ω c d X R Y S j : M.Domain}
    (hw : M.IsOmega Ω) (source : Smdl_d I c X R) (target : Smdl_d I d Y S)
    (map : Smap_d I Ω c d X Y j)
    (hX : (smdl_structure_l I (R := R) source.2.1).Models ZF)
    (hY : (smdl_structure_l I (R := S) target.2.1).Models ZF)
    {v : Fin 19 → (smdl_structure_l I (R := R) source.2.1).Domain}
    {w : Fin 19 → (smdl_structure_l I (R := S) target.2.1).Domain}
    (frame : Ag_frame_d hX v) (points : ∀ i, Rd_entry_d (v i).val (w i).val j) : Ag_frame_d hY w := by
  let ρ := (⟨v,fun _ => v 0⟩ : Env _ 19)
  let η := (⟨w,fun _ => w 0⟩ : Env _ 19)
  exact (ag_frame_sat_l hY η Term.bound).mp
    ((smap_source_l I hZF hw source target map (ag_frame_m Term.bound)
      (ag_frame_closed_l _ (fun _ => rfl)) ρ η points).mp ((ag_frame_sat_l hX ρ Term.bound).mpr frame))

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 7.23 专用博弈与两类规范名字的统一构造

先固定同一小坍缩、大坍缩及实际积。稠密名字的编码、函数名字的全扩张覆盖，
合法树和辅助树全部引用这些同一对象；不存在另行提供的名字覆盖假设。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project Descriptive InnerModel Internal Model.Forcing.Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 全部参数保留为实际对象；构造只在下面的存在定理中作出。 -/
structure Ag_forcing_d (ω κ δ X : M.Domain) where
  Q : M.Domain
  T : M.Domain
  P : M.Domain
  U : M.Domain
  C : M.Domain
  R : M.Domain
  b : M.Domain
  c : M.Domain
  small_space : Fseq_space_d I ω κ Q
  big_space : Fseq_space_d I ω δ P
  small_order : Cond_order_d M Q T Q
  big_order : Cond_order_d M P U P
  product_order : Cond_order_d M C R C
  small_edges : ∀ q r, Entry_d M q r T ↔ M.mem q Q ∧ M.mem r Q ∧ M.MemberSubset r q
  big_edges : ∀ p r, Entry_d M p r U ↔ M.mem p P ∧ M.mem r P ∧ M.MemberSubset r p
  product : Prod_d hZF Q T P U C R
  empty : ∀ x, ¬ M.mem x b
  small_base : M.mem b Q
  big_base : M.mem b P
  product_base : KPair_d M c b b
  base_mem : M.mem c C
  top : ∀ p, M.mem p C → Entry_d M p c R
  t : M.Domain
  w : M.Domain
  Z : M.Domain
  a : M.Domain
  f : M.Domain
  s : M.Domain
  W : M.Domain
  N : M.Domain
  check_omega : Check_d M c ω t
  check_letters : Check_d M c X w
  graph_product : M.IsCartesianProduct I Z ω X
  check_product : Check_d M c Z a
  fallback : M.IsSetFunctionFromTo I f ω X
  check_fallback : Check_d M c f s
  function_pool : Name_pool_d M C a s W
  chosen_function : M.mem s N
  function_family : ∀ v, M.mem v N ↔ M.mem v W ∧ ∀ p, M.mem p C → p ≠ C →
    Forces_d M C R C fn_body_m (fn_env_l t w v) p
  function_cover : ∀ G (generic : Generic_d M C R C G),
    ∀ d x y : (extension_l M hZF C R C G).Domain,
      Qval_d M C R C G t d → Qval_d M C R C G w x →
      (extension_l M hZF C R C G).IsSetFunctionFromTo
        (kpair_interpretation_l _ (extension_ext_l product_order hZF generic)
          (internal_pair_l product_order hZF generic)) y d x →
      ∃ v, M.mem v N ∧ Qval_d M C R C G v y
  dp : M.Domain
  du : M.Domain
  Wd : M.Domain
  D : M.Domain
  K : M.Domain
  check_big : Check_d M b P dp
  check_order : Check_d M b U du
  dense_pool : Name_pool_d M Q dp dp Wd
  power : M.IsPowerSetOf K δ
  dense_code : M.CardinalLessOrEqual I D K
  chosen_dense : M.mem dp D
  dense_family : ∀ s, M.mem s D ↔ M.mem s Wd ∧ ∀ p, M.mem p Q → p ≠ Q →
    Forces_d M Q T Q dn_s.body ((ord_env_l M dp du).push s) p
  dense_cover : ∀ H, Generic_d M Q T Q H → ∀ P' U' E : (extension_l M hZF Q T Q H).Domain,
    Qval_d M Q T Q H dp P' → Qval_d M Q T Q H du U' →
    Dense_set_d (extension_l M hZF Q T Q H) P' U' P' E →
    ∃ s, M.mem s D ∧ Qval_d M Q T Q H s E

theorem ag_forcing_l (hZFC : M.Models ZFC) {ω κ δ X : M.Domain}
    (hw : M.IsOmega ω) (above : M.mem ω δ)
    (regular : M.IsRegularCardinal I δ) (strong : M.IsStrongLimitCardinal I δ)
    (small : M.MemberSubset κ δ) (inh : ∃ x, M.mem x X) : Nonempty (Ag_forcing_d hZF ω κ δ X) := by
  obtain ⟨Q,T,qs,O,qt⟩ := fseq_collapse_order_l hZF hw κ
  obtain ⟨P,U,b,dp,du,Wd,D,K,ps,L,pt,empty,hb,cdp,cdu,dpool,power,_,code,chosen,dfamily,dcover⟩ :=
    fseq_dense_names_code_l hZFC hw above regular strong small qs O qt
  have hbω := num_mem_l hZF.1 hw (show Num_d 0 b from empty)
  have hbP := (ps b).mpr ⟨b,hbω,ds_empty_fun_l I empty⟩
  obtain ⟨C,R,product,OP⟩ := product_order_l hZF O L
  obtain ⟨c,pair⟩ := (I).total b b
  obtain ⟨hc,top⟩ := product.top_l hZF hb hbP
    (fun q hq => (qt q b).mpr ⟨hq,hb,fun x hx => (empty x hx).elim⟩)
    (fun p hp => (pt p b).mpr ⟨hp,hbP,fun x hx => (empty x hx).elim⟩) pair
  obtain ⟨t,w,Z,a,f,s,W,N,ct,cw,pairZ,ca,fn,cs,fpool,fchosen,ffamily,fcover⟩ :=
    function_names_l hZF OP hc top inh (D := ω)
  exact ⟨⟨Q,T,P,U,C,R,b,c,qs,ps,O,L,OP,qt,pt,product,empty,hb,hbP,pair,hc,top,
    t,w,Z,a,f,s,W,N,ct,cw,pairZ,ca,fn,cs,fpool,fchosen,ffamily,fcover,
    dp,du,Wd,D,K,cdp,cdu,dpool,power,code,chosen,dfamily,dcover⟩⟩

structure Ag_system_d {ω κ δ X : M.Domain} (p : Ag_forcing_d hZF ω κ δ X) where
  E : M.Domain
  B : M.Domain
  A : M.Domain
  F₀ : M.Domain
  R₀ : M.Domain
  V : M.Domain
  Z : M.Domain
  Y : M.Domain
  F : M.Domain
  S : M.Domain
  V₀ : M.Domain
  source : Ag_game_d hZF ω X p.Q p.T E B A F₀ R₀
  all_dense : ∀ D, M.mem D E ↔ Dense_set_d M p.Q p.T p.Q D
  auxiliary : Ag_tree_d hZF ω p.Q p.T p.P p.U p.C p.R p.b p.c p.N A R₀ p.D V Z Y F S
  alphabet : Td_alphabet_d S p.D V₀
  second_bound : M.MemberSubset V₀ V

theorem Ag_forcing_d.system_l {ω κ δ X : M.Domain} (p : Ag_forcing_d hZF ω κ δ X)
    (hw : M.IsOmega ω) (inh : ∃ x, M.mem x X) : Nonempty (Ag_system_d hZF p) := by
  obtain ⟨E,B,A,F₀,R₀,source,all⟩ := ag_game_l hZF hw X p.small_order
  obtain ⟨V,Z,Y,F,S,aux⟩ := ag_tree_l hZF hw p.Q p.T p.P p.U p.C p.R p.b p.c p.N A R₀ p.D
  obtain ⟨V₀,alphabet,bound⟩ := aux.alphabet_l hZF source hw p.empty inh ⟨p.b,p.small_base⟩ ⟨p.s,p.chosen_function⟩
  exact ⟨⟨E,B,A,F₀,R₀,V,Z,Y,F,S,V₀,source,all,aux,alphabet,bound⟩⟩

/-- 7.12 所需的非空第一辅助域、合法后继和内在树均由同一构造自动提供。 -/
theorem Ag_system_d.ready_l {ω κ δ X : M.Domain} {p : Ag_forcing_d hZF ω κ δ X}
    (s : Ag_system_d hZF p) (hw : M.IsOmega ω) (inh : ∃ x, M.mem x X) :
    M.mem p.b s.R₀ ∧
      (∀ h, M.mem h s.R₀ → ∃ t, M.mem t s.R₀ ∧ Step_d I ω h t) ∧
      Td_tree_d I ω s.A s.S ∧ M.mem p.dp p.D ∧ M.CardinalLessOrEqual I p.D p.K := by
  exact ⟨s.source.root_l hZF hw p.empty,
    s.source.pruned_l hZF hw ⟨p.b,p.small_base⟩ inh,
    s.auxiliary.demanding_l hZF s.source.space (s.source.tree_l hZF),p.chosen_dense,p.dense_code⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 专用合法博弈的低秩界与小坍缩参数下界

小条件域、旧稠密集族和实数字母积均属于同一极限秩层。
反向读取一项常值条件又证明：原走法字母表的秩严格高于 κ。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive Model.Forcing.Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Ag_system_d.rank_mem_l {ω κ δ X W : M.Domain} {p : Ag_forcing_d hZF ω κ δ X}
    (s : Ag_system_d hZF p) (hw : M.IsOmega ω) (limit : M.IsLimitOrdinal δ)
    (above : M.mem ω δ) (small : M.mem κ δ) (rank : V_d I δ W) (letters : M.mem X W) :
    M.mem p.Q W ∧ M.mem s.E W ∧ M.mem s.A W ∧ M.mem s.F₀ W ∧ M.mem s.R₀ W := by
  have hω := ZF.v_ordinal_mem_l I hZF rank above
  have hκ := ZF.v_ordinal_mem_l I hZF rank small
  have hQ := ZF.v_fseq_mem_l I hZF rank limit hw hω hκ p.small_space
  obtain ⟨D,power⟩ := ZF.exists_powerSet hZF p.Q
  have hE := v_subset_mem_l I rank (v_power_mem_l I rank limit hQ power)
    (fun E hE => (power E).mpr (fun q hq => ((s.source.dense E hE).1 q hq).1))
  have hB := ZF.v_product_mem_l I hZF rank limit letters hQ s.source.pair
  obtain ⟨C,hC,bc,ec⟩ := v_joint_bound_l I rank hB hE
  have hA := v_subset_mem_l I rank hC (fun a ha => ((s.source.alphabet a).mp ha).elim (bc a) (ec a))
  have hF := ZF.v_fseq_mem_l I hZF rank limit hw hω hA s.source.space
  exact ⟨hQ,hE,hA,hF,v_subset_mem_l I rank hF (s.source.tree_l hZF).1⟩

/-- 一项常值图使有限列空间的任意秩界同时包含原字母集。 -/
theorem Ag_forcing_d.small_rank_l {ω κ δ X α W : M.Domain} (p : Ag_forcing_d hZF ω κ δ X)
    (hw : M.IsOmega ω) (rank : V_d I α W) (small : M.mem p.Q W) : M.mem κ W := by
  obtain ⟨β,V,hβ,hV,sub⟩ := (ZF.v_unfold_l I hZF rank p.Q).mp small
  refine (ZF.v_unfold_l I hZF rank κ).mpr ⟨β,V,hβ,hV,fun x hx => ?_⟩
  obtain ⟨b,_,hb⟩ := hw.1.1
  obtain ⟨one,succ,hone⟩ := hw.1.2 b hb
  obtain ⟨f,fn,constant⟩ := ZF.exists_constantFunction hZF I (source := one) hx
  have hf := sub f ((p.small_space f).mpr ⟨one,hone,fn⟩)
  exact (rd_entry_transitive_l (v_transitive_l I hV) hf ((constant b x).mpr ⟨succ.predecessor_mem,rfl⟩)).2

theorem Ag_system_d.small_below_rank_l {ω κ δ X ρ : M.Domain} {p : Ag_forcing_d hZF ω κ δ X}
    (s : Ag_system_d hZF p) (hw : M.IsOmega ω) (ordinal : M.IsOrdinal κ)
    (rank : Rk_d I s.A ρ) : M.mem κ ρ := by
  obtain ⟨W,hW,sub,_⟩ := rank
  have hQ := sub p.Q ((s.source.alphabet p.Q).mpr (Or.inr s.source.full))
  exact ZF.v_ordinal_height_l hZF hW ordinal (p.small_rank_l hZF hw hW hQ)

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 固定原博弈字母表时，同一小泛型向良基枝提升

整个条件域是 II 的合法字母；每个条件又是 I 落子的第二坐标。
因此原字母表逐点固定蕴含条件逐点固定，且全部旧稠密集族也固定。
目标全局稠密集遂有同一旧原像，直接给出实际泛型性和名字商的初等提升。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive Model.Forcing.Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Ag_system_d.fixed_small_l {Ω c d X R Y S j : M.Domain} (hw : M.IsOmega Ω)
    (source : Smem_d I c X R) (target : Smem_d I d Y S)
    (xt : M.TransitiveSet X) (yt : M.TransitiveSet Y) (map : Smap_d I Ω c d X Y j)
    (native : (smdl_structure_l I (R := R) source.1.2.1).Models ZF)
    {ω κ δ A : (smdl_structure_l I (R := R) source.1.2.1).Domain}
    {p : Ag_forcing_d native ω κ δ A} (s : Ag_system_d native p)
    (inh : ∃ x, (smdl_structure_l I (R := R) source.1.2.1).mem x A)
    (fixed : Rd_entry_d s.A.val s.A.val j) (point : ∀ x, M.mem x s.A.val → Rd_entry_d x x j) :
    Rd_entry_d p.Q.val p.Q.val j ∧ (∀ q, M.mem q p.Q.val → Rd_entry_d q q j) ∧ Rd_entry_d s.E.val s.E.val j := by
  let N := smdl_structure_l I (R := R) source.1.2.1
  have inj : Function.Injective (Subtype.val : N.Domain → M.Domain) := fun _ _ eq => Subtype.ext eq
  have full := smem_full_l I source xt
  have member {a b : N.Domain} : M.mem a.val b.val ↔ N.mem a b :=
    image_member_l (M := N) (N := M) Subtype.val inj full
  have dense : M.MemberSubset s.E.val s.A.val := by
    intro D hD
    obtain ⟨D₀,hD₀,rfl⟩ := (full s.E D).mp hD
    exact member.mpr ((s.source.alphabet D₀).mpr (Or.inr hD₀))
  refine ⟨point p.Q.val (member.mpr ((s.source.alphabet p.Q).mpr (Or.inr s.source.full))),?_,
    map.fixed_subset_l hZF hw xt yt source target fixed point s.E.property dense⟩
  intro q hq
  obtain ⟨q₀,hq₀,rfl⟩ := (full p.Q q).mp hq
  obtain ⟨x,hx⟩ := inh
  obtain ⟨t,pair⟩ := (kp_pair_l (ZF.modelsKP native)).total x q₀
  have ta := (s.source.alphabet t).mpr (Or.inl ((s.source.pair t).mpr ⟨x,hx,q₀,hq₀,pair⟩))
  have pair' := image_kpair_l Subtype.val full pair
  obtain ⟨a,b,_,_,ab,_,bq⟩ := map.kpair_preimage_l hZF hw xt yt source target (point t.val (member.mpr ta)) pair'
  exact ((I).injective ab pair').2 ▸ bq

theorem Ag_system_d.small_generic_l {Ω c d X R Y S j : M.Domain} (hw : M.IsOmega Ω)
    (source : Smem_d I c X R) (target : Smem_d I d Y S)
    (xt : M.TransitiveSet X) (yt : M.TransitiveSet Y) (map : Smap_d I Ω c d X Y j)
    (native : (smdl_structure_l I (R := R) source.1.2.1).Models ZF)
    (native' : (smdl_structure_l I (R := S) target.1.2.1).Models ZF)
    {ω κ δ A : (smdl_structure_l I (R := R) source.1.2.1).Domain}
    {p : Ag_forcing_d native ω κ δ A} (s : Ag_system_d native p)
    (inh : ∃ x, (smdl_structure_l I (R := R) source.1.2.1).mem x A)
    (fixed : Rd_entry_d s.A.val s.A.val j) (point : ∀ x, M.mem x s.A.val → Rd_entry_d x x j)
    {G : (smdl_structure_l I (R := R) source.1.2.1).Domain → Prop}
    (generic : Generic_d _ p.Q p.T p.Q G) :
    ∃ e : (smdl_structure_l I (R := R) source.1.2.1).Domain → (smdl_structure_l I (R := S) target.1.2.1).Domain,
      Pe_d e ∧ (∀ a, Rd_entry_d a.val (e a).val j) ∧ Generic_d _ (e p.Q) (e p.T) (e p.Q) (Em_generic_d e G) ∧
      (∀ q, Em_generic_d e G q ↔ ∃ a, G a ∧ a.val = q.val) ∧
      ∃ f : (extension_l _ native p.Q p.T p.Q G).Domain →
        (extension_l _ native' (e p.Q) (e p.T) (e p.Q) (Em_generic_d e G)).Domain,
        Function.Injective f ∧
        (∀ t x, Qval_d _ p.Q p.T p.Q G t x → Qval_d _ (e p.Q) (e p.T) (e p.Q) (Em_generic_d e G) (e t) (f x)) ∧
        ∀ {n} (φ : Formula 1 n), φ.FreeClosed → ∀ ρ, Formula.satisfies ρ φ ↔ Formula.satisfies (image_env_l f ρ) φ := by
  let N := smdl_structure_l I (R := R) source.1.2.1
  let N' := smdl_structure_l I (R := S) target.1.2.1
  obtain ⟨e,elem,values⟩ := map.project_l I hZF hw source.1 target.1
  obtain ⟨fixedQ,pointQ,fixedE⟩ := s.fixed_small_l hZF hw source target xt yt map native inh fixed point
  have eqQ : (e p.Q).val = p.Q.val := map.1.1.1.2 _ _ _ (values p.Q) fixedQ
  have eqE : (e s.E).val = s.E.val := map.1.1.1.2 _ _ _ (values s.E) fixedE
  have value (a : N.Domain) (ha : N.mem a p.Q) : (e a).val = a.val :=
    map.1.1.1.2 _ _ _ (values a) (pointQ a.val ((source.2 a.val p.Q.val).mp ha).2.2)
  have conditions (q : N'.Domain) (hq : N'.mem q (e p.Q)) : ∃ a, N.mem a p.Q ∧ e a = q := by
    have qQ : M.mem q.val p.Q.val := eqQ ▸ ((target.2 q.val (e p.Q).val).mp hq).2.2
    let a : N.Domain := ⟨q.val,xt p.Q.val p.Q.property q.val qQ⟩
    have ha : N.mem a p.Q := (source.2 a.val p.Q.val).mpr ⟨a.property,p.Q.property,qQ⟩
    exact ⟨a,ha,Subtype.ext (value a ha)⟩
  have family := em_dense_family_l e native.1 native'.1 elem s.all_dense
  have globals (D : N'.Domain) (dense : Dense_set_d N' (e p.Q) (e p.T) (e p.Q) D) : ∃ C, e C = D := by
    have hD : M.mem D.val s.E.val := eqE ▸ ((target.2 D.val (e s.E).val).mp ((family D).mpr dense)).2.2
    let C : N.Domain := ⟨D.val,xt s.E.val s.E.property D.val hD⟩
    have hC : N.mem C s.E := (source.2 C.val s.E.val).mpr ⟨C.property,s.E.property,hD⟩
    have hA := (s.source.alphabet C).mpr (Or.inr hC)
    exact ⟨C,Subtype.ext (map.1.1.1.2 _ _ _ (values C) (point C.val ((source.2 C.val s.A.val).mp hA).2.2))⟩
  have generic' := em_global_generic_l native.1 native' e elem p.small_order generic conditions globals
  have accepted a (ha : G a) : Em_generic_d e G (e a) := ⟨a,ha,rfl⟩
  refine ⟨e,elem,values,generic',?_,em_lift_l native.1 native'.1 e elem accepted,
    em_lift_injective_l native native' e elem accepted p.small_order generic generic',
    fun _ _ => em_lift_value_l native.1 native'.1 e elem accepted,
    fun φ hc ρ => em_lift_elementary_l native native' e elem accepted p.small_order generic generic' φ hc ρ⟩
  intro q
  constructor
  · rintro ⟨a,ha,rfl⟩
    exact ⟨a,ha,(value a (generic.proper a ha).1).symm⟩
  · rintro ⟨a,ha,eq⟩
    exact ⟨a,ha,Subtype.ext ((value a (generic.proper a ha).1).trans eq)⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 实际专用系统的统一分支参数

十九项依次为 ω、小条件及序、大条件及序、积及序、空条件、积顶、函数名字族、
原博弈字母、合法树、稠密名字族、第二辅助域、两个积、有限空间、辅助树和第二最小域。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project Descriptive InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
variable {ω κ δ A : M.Domain} {p : Ag_forcing_d hZF ω κ δ A}

def Ag_system_d.aux_params_l (s : Ag_system_d hZF p) : Fin 19 → M.Domain :=
  fun i => [ω,p.Q,p.T,p.P,p.U,p.C,p.R,p.b,p.c,p.N,s.A,s.R₀,p.D,s.V,s.Z,s.Y,s.F,s.S,s.V₀].get i

theorem Ag_system_d.frame_l (s : Ag_system_d hZF p) (hw : M.IsOmega ω) :
    Ag_frame_d hZF (s.aux_params_l hZF) :=
  ⟨hw,p.empty,s.auxiliary,s.auxiliary.tree_l hZF s.source.space (s.source.tree_l hZF),s.alphabet⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 同一实际良基分支的专用名字及强迫约束

原迭代锥提供唯一根腿，十九个参数及全部树规则沿该腿运输。
在同一目标中恢复满射辅助图，并逐前缀读取目标自身的强迫关系。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive Model.Forcing.Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

structure Ag_branch_d (Ω z c X Q G b : M.Domain) (v : Fin 19 → M.Domain) (f : M.Domain) where
  d : M.Domain
  N : M.Domain
  W : M.Domain
  P : M.Domain
  j : M.Domain
  target : Smem_d I d N W
  transitive : M.TransitiveSet N
  cone : It_cone_d (kp_pair_l (ZF.modelsKP hZF)) Ω b Q G d N W P
  leg : Rd_entry_d z j P
  map : Smap_d I Ω c d X N j
  fixed : Rd_entry_d (v 10) (v 10) j
  point : ∀ x, M.mem x (v 10) → Rd_entry_d x x j
  low : ∃ μ K, M.mem μ X ∧ M.mem K X ∧ Vr_d X μ K ∧ M.mem (v 10) K ∧
    ∀ x, M.mem x K → Rd_entry_d x x j
  native : (smdl_structure_l I (R := W) target.1.2.1).Models ZF
  w : Fin 19 → (smdl_structure_l I (R := W) target.1.2.1).Domain
  images : ∀ i, Rd_entry_d (v i) (w i).val j
  omega : (w 0).val = Ω
  frame : Ag_frame_d native w
  a : M.Domain
  u : M.Domain
  q : M.Domain
  input : Fn0_d Ω (w 10).val f
  first : Fn0_d Ω (w 12).val a
  onto : M.IsSetSurjectiveOnto I a Ω (w 12).val
  second : Fn0_d Ω (w 18).val u
  joined : Fn0_d Ω (w 15).val q
  branch : Branch_d (w 16).val (w 17).val q
  join : Tg_join_d I Ω f a u q
  read : Ag_read_d native (w 0) (w 1) (w 2) (w 3) (w 4) (w 5) (w 6) (w 7) (w 8) (w 9) Subtype.val f a u

def Ag_gp_d (Ω z c X : M.Domain) (v : Fin 19 → M.Domain) (f : M.Domain) : Prop :=
  ∃ ρ γ, Rk_d I (v 10) ρ ∧ M.mem ρ γ ∧ M.IsOrdinal γ ∧ ∃ T Q G E,
    It_tree_d hZF Ω c Ω T Q G E ∧ It_owned_d I Ω Q E ∧
      It_copyable_d hZF Ω c T Q G E ∧ It_critical_bound_d I γ Q E ∧
      ∀ b, It_wf_branch_d hZF Ω Ω T Q G b → Nonempty (Ag_branch_d hZF Ω z c X Q G b v f)

theorem Ag_frame_d.read_gp_l {Ω c X R z f : M.Domain} (hw : M.IsOmega Ω)
    (source : Smem_d I c X R) (trans : M.TransitiveSet X)
    (native : (smdl_structure_l I (R := R) source.1.2.1).Models ZF)
    {v : Fin 19 → (smdl_structure_l I (R := R) source.1.2.1).Domain}
    (frame : Ag_frame_d native v) (eqω : (v 0).val = Ω)
    (ff : Fn0_d Ω (v 10).val f)
    (good : Td_fixed_gp_d hZF Ω z c X (v 10).val (v 17).val f) :
    Ag_gp_d hZF Ω z c X (fun i => (v i).val) f := by
  obtain ⟨ρ,γ,rank,lower,ordinal,T,Q,G,E,tree,owned,copy,bound,branches⟩ := good
  refine ⟨ρ,γ,rank,lower,ordinal,T,Q,G,E,tree,owned,copy,bound,?_⟩
  intro b wf
  obtain ⟨d,N,W,P,j,S,Y,F,U,V,target,nt,cone,leg,image,space,closed,letters,projection,map,fixedA,pointA,low⟩ := branches b wf
  have native' := map.native_models_l hZF hw source.1 target.1 native
  obtain ⟨images,points⟩ := Classical.axiomOfChoice (fun i : Fin 19 => map.1.1.2.2 (v i).val (v i).property)
  let w : Fin 19 → (smdl_structure_l I (R := W) target.1.2.1).Domain := fun i => ⟨images i,(points i).1⟩
  have iw i : Rd_entry_d (v i).val (w i).val j := (points i).2
  have omega := map.omega_l I hZF hw trans nt source target (eqω ▸ (v 0).property)
  have eq0 : (w 0).val = Ω := map.1.1.1.2 Ω (w 0).val Ω (eqω ▸ iw 0) omega
  have r := frame.native_map_l hZF hw source.1 target.1 map native native' iw
  have inj : Function.Injective (Subtype.val : (smdl_structure_l I (R := W) target.1.2.1).Domain → M.Domain) :=
    fun _ _ h => Subtype.ext h
  have full := smem_full_l I target nt
  have triple : M.IsCartesianProduct I (w 15).val (w 10).val (w 14).val :=
    image_product_l (M := smdl_structure_l I (R := W) target.1.2.1) (N := M)
      (hEM := native'.1) (hPM := KP.exists_pair (ZF.modelsKP native'))
      (hEN := hZF.1) (hPN := KP.exists_pair (ZF.modelsKP hZF)) Subtype.val inj full r.auxiliary.triple
  have sp := image_fseq_l native' hZF Subtype.val inj full r.omega (eq0.symm ▸ hw) r.auxiliary.space
  have tr := image_tree_l Subtype.val inj full r.tree
  have alphabet := Td_alphabet_d.ground_l native' hZF Subtype.val inj full r.alphabet
    r.auxiliary.space r.tree r.auxiliary.pair r.auxiliary.triple
  have eqS : (w 17).val = S := map.1.1.1.2 _ _ _ (iw 17) image
  obtain ⟨eqU,eqV⟩ := (eqS ▸ alphabet).ext_l hZF.1 letters
  have sp' : Fseq_space_d I Ω (w 15).val (w 16).val := by simpa only [eq0] using! sp
  have tr' : Tree_d (w 16).val S := eqS ▸ tr
  have proj := projection.space_l hZF hw space sp' tr'
  have proj : Td_projection_d hZF Ω (w 12).val (w 18).val (w 15).val (w 16).val (w 17).val f := by
    simpa only [eqS,eqU,eqV] using proj
  have input := proj.input_l hZF triple ff
  obtain ⟨q,a,u,fa,onto,fu,fq,branch,join⟩ := proj
  have rules := r.auxiliary.read_l native' hZF Subtype.val inj full r.omega (eq0.symm ▸ hw) r.empty
    (by simpa only [eq0] using input) (by simpa only [eq0] using fa)
    (by simpa only [eq0] using fu) (by simpa only [eq0] using fq) branch (by simpa only [eq0] using join)
  exact ⟨⟨d,N,W,P,j,target,nt,cone,leg,map,fixedA,pointA,⟨γ,low⟩,native',w,iw,eq0,r,a,u,q,input,fa,onto,fu,fq,branch,join,rules⟩⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 给定 H 在同一实际良基分支中仍为小泛型

专用系统的条件及稠密集固定性用于该分支的同一根腿。参数像由图的唯一性
识别为已保存的十九项；所得泛型仍由环境中原 H 的成员关系定义。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive Model.Forcing.Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Ag_branch_d.small_generic_l {Ω c X R z Q G b f H : M.Domain} (hw : M.IsOmega Ω)
    (source : Smem_d I c X R) (xt : M.TransitiveSet X)
    (native : (smdl_structure_l I (R := R) source.1.2.1).Models ZF)
    {ω κ δ A : (smdl_structure_l I (R := R) source.1.2.1).Domain}
    {p : Ag_forcing_d native ω κ δ A} (s : Ag_system_d native p)
    (inh : ∃ x, (smdl_structure_l I (R := R) source.1.2.1).mem x A)
    (r : Ag_branch_d hZF Ω z c X Q G b (fun i => (s.aux_params_l native i).val) f)
    (sub : M.MemberSubset H p.Q.val)
    (generic : Generic_d (smdl_structure_l I (R := R) source.1.2.1) p.Q p.T p.Q (fun q => M.mem q.val H)) :
    Generic_d (smdl_structure_l I (R := r.W) r.target.1.2.1) (r.w 1) (r.w 2) (r.w 1) (fun q => M.mem q.val H) := by
  let N := smdl_structure_l I (R := R) source.1.2.1
  let N' := smdl_structure_l I (R := r.W) r.target.1.2.1
  obtain ⟨e,_,values,generic',same,_⟩ := s.small_generic_l hZF hw source r.target xt r.transitive r.map
    native r.native inh r.fixed r.point generic
  have eqQ : e p.Q = r.w 1 := Subtype.ext (r.map.1.1.1.2 _ _ _ (values p.Q) (r.images 1))
  have eqT : e p.T = r.w 2 := Subtype.ext (r.map.1.1.1.2 _ _ _ (values p.T) (r.images 2))
  have predicate : Em_generic_d e (fun q : N.Domain => M.mem q.val H) = (fun q : N'.Domain => M.mem q.val H) := by
    funext q
    apply propext
    apply (same q).trans
    refine ⟨fun ⟨a,ha,eq⟩ => eq ▸ ha,fun hq => ?_⟩
    exact ⟨⟨q.val,xt p.Q.val p.Q.property q.val (sub q.val hq)⟩,hq,rfl⟩
  have generic'' : Generic_d N' (e p.Q) (e p.T) (e p.Q) (fun q => M.mem q.val H) := predicate ▸ generic'
  simpa only [eqQ,eqT] using generic''

end YesMetaZFC.SetTheory.LargeCardinal
