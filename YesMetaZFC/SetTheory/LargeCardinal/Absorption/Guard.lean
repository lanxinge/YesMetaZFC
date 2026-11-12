import YesMetaZFC.SetTheory.LargeCardinal.Absorption.BranchGeneric
import YesMetaZFC.Model.Forcing.Ground.CheckPool

/-! # 旧非反驳关系的集合编码

在原模型中分离三元真值表，再把这张固定表送入扩张。
扩张只读取旧表的成员关系，不重新计算原强迫关系。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project Descriptive InnerModel Internal Model.Forcing.Internal
universe u v
variable {M : Structure.{u}}

def Ag_drel_d (Γ q p d : M.Domain) : Prop :=
  ∃ z, KPair_d M z p d ∧ Entry_d M q z Γ

def ag_drel_m {n} (Γ q p d : Term n) : Formula 1 n := set[n] ⟪∃ z,
  ⌜kpair_m⌝ₚ(z,⌜p⌝ₛ,⌜d⌝ₛ) ∧ ⌜entry_m⌝ₚ(⌜q⌝ₛ,z,⌜Γ⌝ₛ)⟫
derive_free_closed ag_drel_m

theorem ag_drel_sat_l (hE : Extensional M) {n} (ρ : Env M n) (Γ q p d : Term n) :
    Formula.satisfies ρ (ag_drel_m Γ q p d) ↔
      Ag_drel_d (Γ.eval ρ) (q.eval ρ) (p.eval ρ) (d.eval ρ) := by
  simp only [ag_drel_m,Ag_drel_d,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,
    kpair_sat_l M hE,entry_sat_l M hE,Definitional.Term.eval_weaken]
  rfl

theorem ag_demand_relation_l (hZF : M.Models ZF) (Q T b P D : M.Domain) :
    ∃ Γ, ∀ q p d, Ag_drel_d Γ q p d ↔
      M.mem q Q ∧ M.mem p P ∧ M.mem d D ∧ Ag_demand_d Q T b q p d := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨A,prod⟩ := ZF.exists_cartesianProduct hZF I P D
  obtain ⟨B,pairs⟩ := ZF.exists_cartesianProduct hZF I Q A
  let ρ : Env M 3 := ⟨fun i => [Q,T,b].get i,fun _ => Q⟩
  let φ : UnarySchema 3 := { body := set[4] ⟪∃ q p d z,
    ⌜kpair_m⌝ₚ(⌜(.newest : Term 4)⌝ₛ,q,z) ∧ ⌜kpair_m⌝ₚ(z,p,d) ∧
      ⌜ag_demand_m⌝ₚ(⌜(.bound 1 : Term 4)⌝ₛ,⌜(.bound 2 : Term 4)⌝ₛ,⌜(.bound 3 : Term 4)⌝ₛ,q,p,d)⟫ }
  have sat a : φ.denote ρ a ↔ ∃ q p d z,
      KPair_d M a q z ∧ KPair_d M z p d ∧ Ag_demand_d Q T b q p d := by
    simp only [UnarySchema.denote,φ,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,
      kpair_sat_l M hZF.1,ag_demand_sat_l hZF.1,Definitional.Term.eval_weaken]
    rfl
  obtain ⟨Γ,read⟩ := ZF.separation_exists_d hZF φ ρ B
  refine ⟨Γ,fun q p d => ⟨?_,?_⟩⟩
  · rintro ⟨z,zp,a,aq,ha⟩
    obtain ⟨hB,ht⟩ := (read a).mp ha
    obtain ⟨q',hq,z',hz,az⟩ := (pairs a).mp hB
    obtain ⟨r,s,t,w,ar,ws,hit⟩ := (sat a).mp ht
    obtain ⟨rfl,rfl⟩ := I.injective aq az
    obtain ⟨rfl,rfl⟩ := I.injective aq ar
    obtain ⟨rfl,rfl⟩ := I.injective zp ws
    obtain ⟨p',hp,d',hd,zd⟩ := (prod z).mp hz
    obtain ⟨rfl,rfl⟩ := I.injective zp zd
    exact ⟨hq,hp,hd,hit⟩
  · rintro ⟨hq,hp,hd,hit⟩
    obtain ⟨z,zp⟩ := I.total p d
    obtain ⟨a,aq⟩ := I.total q z
    exact ⟨z,zp,a,aq,(read a).mpr ⟨(pairs a).mpr ⟨q,hq,z,(prod z).mpr ⟨p,hp,d,hd,zp⟩,aq⟩,
      (sat a).mpr ⟨q,p,d,z,aq,zp,hit⟩⟩⟩

theorem ag_drel_image_l (hM : M.Models KP) {N : Structure.{v}} (hN : Extensional N)
    (j : M.Domain → N.Domain) (inj : Function.Injective j)
    (full : ∀ a y, N.mem y (j a) ↔ ∃ x, M.mem x a ∧ j x = y) {Γ q p d : M.Domain} :
    Ag_drel_d Γ q p d ↔ Ag_drel_d (j Γ) (j q) (j p) (j d) := by
  have entry := image_entry_iff_l j inj full (KP.exists_pair hM) hN
  refine ⟨fun ⟨z,zp,qz⟩ => ⟨j z,image_kpair_l j full zp,(entry q z Γ).mp qz⟩,?_⟩
  rintro ⟨z,zp,qz⟩
  obtain ⟨a,ap⟩ := (kp_pair_l hM).total p d
  have eq := kpair_unique_l N hN zp (image_kpair_l j full ap)
  exact ⟨a,ap,(entry q a Γ).mpr (eq ▸ qz)⟩

/-- 对实际小泛型集合中的全部条件，统一读取旧真值表。 -/
def Ag_safe_d (H Γ d p : M.Domain) : Prop := ∀ q, M.mem q H → Ag_drel_d Γ q p d

def ag_safe_m {n} (H Γ d p : Term n) : Formula 1 n := set[n] ⟪∀ q ∈ ⌜H⌝ₛ,
  ⌜ag_drel_m⌝ₚ(⌜Γ⌝ₛ,q,⌜p⌝ₛ,⌜d⌝ₛ)⟫
derive_free_closed ag_safe_m

theorem ag_safe_sat_l (hE : Extensional M) {n} (ρ : Env M n) (H Γ d p : Term n) :
    Formula.satisfies ρ (ag_safe_m H Γ d p) ↔
      Ag_safe_d (H.eval ρ) (Γ.eval ρ) (d.eval ρ) (p.eval ρ) := by
  simp only [ag_safe_m,Ag_safe_d,Formula.satisfies_forallMem_iff,ag_drel_sat_l hE,
    Definitional.Term.eval_weaken]
  rfl

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 辅助应答的内部有限不变量

首项是指定函数名字，其余项属于吸收得到的大泛型；每个后继条件
统一满足前一稠密名字的旧非反驳要求。整个不变量由实际一阶公式表达。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project Descriptive InnerModel Internal Model.Forcing.Internal
universe u
variable {M : Structure.{u}}

structure Ag_guard_d (b τ g U H Γ a v : M.Domain) : Prop where
  names : ∀ i p, Entry_d M i p v → (i = b → p = τ) ∧ (i ≠ b → M.mem p g)
  decreasing : ∀ i j p r, Entry_d M i p v → Entry_d M j r v → M.SuccessorOf i j →
    j ≠ b → Entry_d M p r U
  dense : ∀ i d l p, Entry_d M i d a → Entry_d M l p v → M.SuccessorOf l i → Ag_safe_d H Γ d p

def ag_guard_m {n} (b τ g U H Γ a v : Term n) : Formula 1 n := set[n] ⟪
  (∀ i p, ⌜entry_m⌝ₚ(i,p,⌜v⌝ₛ) → (i = ⌜b⌝ₛ → p = ⌜τ⌝ₛ) ∧ (i ≠ ⌜b⌝ₛ → p ∈ ⌜g⌝ₛ)) ∧
  (∀ i j p r, ⌜entry_m⌝ₚ(i,p,⌜v⌝ₛ) → ⌜entry_m⌝ₚ(j,r,⌜v⌝ₛ) →
    ⌜Formula.isSuccessor⌝ₚ(i,j) → j ≠ ⌜b⌝ₛ → ⌜entry_m⌝ₚ(p,r,⌜U⌝ₛ)) ∧
  (∀ i d l p, ⌜entry_m⌝ₚ(i,d,⌜a⌝ₛ) → ⌜entry_m⌝ₚ(l,p,⌜v⌝ₛ) →
    ⌜Formula.isSuccessor⌝ₚ(l,i) → ⌜ag_safe_m⌝ₚ(⌜H⌝ₛ,⌜Γ⌝ₛ,d,p))⟫
derive_free_closed ag_guard_m

theorem ag_guard_sat_l (hE : Extensional M) {n} (ρ : Env M n) (b τ g U H Γ a v : Term n) :
    Formula.satisfies ρ (ag_guard_m b τ g U H Γ a v) ↔
      Ag_guard_d (b.eval ρ) (τ.eval ρ) (g.eval ρ) (U.eval ρ) (H.eval ρ) (Γ.eval ρ) (a.eval ρ) (v.eval ρ) := by
  simp only [ag_guard_m,Formula.satisfies_conj_iff,Formula.satisfies_forall_iff,Formula.satisfies_imp_iff,
    entry_sat_l M hE,Formula.satisfies_extensionalEq_iff_eq hE,Formula.extensionalNe,
    Formula.satisfies_neg_iff,Formula.satisfies_mem_iff,Formula.satisfies_isSuccessor_iff,
    ag_safe_sat_l hE,Definitional.Term.eval_weaken]
  exact ⟨fun ⟨a,b,c⟩ => ⟨a,b,c⟩,fun h => ⟨h.names,h.decreasing,h.dense⟩⟩

theorem Ag_guard_d.restrict_l {b τ g U H Γ a v a' v' : M.Domain}
    (guard : Ag_guard_d b τ g U H Γ a v) (as : M.MemberSubset a' a) (vs : M.MemberSubset v' v) :
    Ag_guard_d b τ g U H Γ a' v' := by
  have edge {s t i x} (sub : M.MemberSubset s t) (ix : Entry_d M i x s) : Entry_d M i x t :=
    ix.elim fun p hp => ⟨p,hp.1,sub p hp.2⟩
  exact ⟨fun i p ip => guard.names i p (edge vs ip),
    fun i j p r ip jr => guard.decreasing i j p r (edge vs ip) (edge vs jr),
    fun i d l p id lp => guard.dense i d l p (edge as id) (edge vs lp)⟩

end YesMetaZFC.SetTheory.LargeCardinal
