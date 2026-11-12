import YesMetaZFC.Model.Forcing.Extension.Choice
import YesMetaZFC.Model.Forcing.Check.SupportBound
import YesMetaZFC.Model.Forcing.Stage.NameMap.Construction

/-! # 以规范检查名字为直接子名字的实际子集名字库

库是 {ĉ : c∈D}×B 的地模型幂集。任意扩张中的 D 子集都有库内代表，
而规范参数 B、b、D 唯一决定此库，不选择名字或泛型。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : Structure.{u}}

def Ck_bound_d (B b D t : M.Domain) : Prop := ∀ v, M.mem v t →
  ∃ s p d, KPair_d M v s p ∧ M.mem p B ∧ M.mem d D ∧ Check_d M b d s

def Ck_pool_d (B b D W : M.Domain) : Prop := ∀ t, M.mem t W ↔ Ck_bound_d B b D t

def ck_bound_m {n} (B b D t : Term n) : Formula 1 n := set[n] ⟪
  ∀ v ∈ ⌜t⌝ₛ, ∃ s p d, ⌜kpair_m⌝ₚ(v,s,p) ∧ p ∈ ⌜B⌝ₛ ∧ d ∈ ⌜D⌝ₛ ∧ ⌜check_m⌝ₚ(⌜b⌝ₛ,d,s)⟫
derive_free_closed ck_bound_m

def ck_pool_m {n} (B b D W : Term n) : Formula 1 n := .forallE
  (.iff (.mem .newest W.weaken) (ck_bound_m B.weaken b.weaken D.weaken .newest))
derive_free_closed ck_pool_m

theorem ck_bound_sat_l (hE : Extensional M) {n} (ρ : Env M n) (B b D t : Term n) :
    Formula.satisfies ρ (ck_bound_m B b D t) ↔ Ck_bound_d (B.eval ρ) (b.eval ρ) (D.eval ρ) (t.eval ρ) := by
  simp only [ck_bound_m,Ck_bound_d,Formula.satisfies_forallMem_iff,Formula.satisfies_exists_iff,
    Formula.satisfies_conj_iff,Formula.satisfies_mem_iff,kpair_sat_l M hE,check_sat_l M hE,Definitional.Term.eval_weaken]
  rfl

theorem ck_pool_sat_l (hE : Extensional M) {n} (ρ : Env M n) (B b D W : Term n) :
    Formula.satisfies ρ (ck_pool_m B b D W) ↔ Ck_pool_d (B.eval ρ) (b.eval ρ) (D.eval ρ) (W.eval ρ) := by
  simp only [ck_pool_m,Ck_pool_d,Formula.satisfies_forall_iff,Formula.satisfies_iff_iff,
    Formula.satisfies_mem_iff,ck_bound_sat_l hE,Definitional.Term.eval_weaken]
  rfl

theorem ck_pool_exists_l (hZF : M.Models ZF) {B b : M.Domain} (hb : M.mem b B) (D : M.Domain) :
    ∃ W, Ck_pool_d B b D W := by
  let I := kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))
  obtain ⟨a,check,_,_⟩ := zf_check_l M hZF hb D
  obtain ⟨S,domain⟩ := entry_domain_l M hZF a
  have checks s : M.mem s S ↔ ∃ d, M.mem d D ∧ Check_d M b d s := by
    apply (domain s).trans
    constructor
    · rintro ⟨p,v,vs,vA⟩
      obtain ⟨d,t,hd,ct,pair⟩ := (check_mem_l M hZF.1 (check_ind_l M hZF) check v).mp vA
      obtain ⟨eq,_⟩ := kpair_injective_l M vs pair
      exact ⟨d,hd,eq.symm ▸ ct⟩
    · rintro ⟨d,hd,ct⟩
      obtain ⟨v,pair⟩ := I.total s b
      exact ⟨b,v,pair,(check_mem_l M hZF.1 (check_ind_l M hZF) check v).mpr ⟨d,s,hd,ct,pair⟩⟩
  obtain ⟨C,product⟩ := ZF.exists_cartesianProduct hZF I S B
  obtain ⟨W,power⟩ := ZF.exists_powerSet hZF C
  refine ⟨W,fun t => (power t).trans ?_⟩
  constructor
  · intro sub v hv
    obtain ⟨s,hs,p,hp,pair⟩ := (product v).mp (sub v hv)
    obtain ⟨d,hd,ct⟩ := (checks s).mp hs
    exact ⟨s,p,d,pair,hp,hd,ct⟩
  · intro bounded v hv
    obtain ⟨s,p,d,pair,hp,hd,ct⟩ := bounded v hv
    exact (product v).mpr ⟨s,(checks s).mpr ⟨d,hd,ct⟩,p,hp,pair⟩

theorem Ck_pool_d.unique_l (hE : Extensional M) {B b D W V : M.Domain}
    (h : Ck_pool_d B b D W) (k : Ck_pool_d B b D V) : W = V :=
  hE.eq_of_same_members W V (fun t => (h t).trans (k t).symm)

theorem Ck_bound_d.name_l (hZF : M.Models ZF) {B b D t : M.Domain}
    (bound : Ck_bound_d B b D t) (hb : M.mem b B) : Name_d M B t := by
  apply (name_unfold_l M (name_ops_l M hZF) B t).mpr
  intro v hv
  obtain ⟨s,p,d,pair,hp,_,check⟩ := bound v hv
  exact ⟨s,p,pair,hp,check_name_l M (check_range_l M hZF) hb check⟩

theorem Ck_pool_d.name_l (hZF : M.Models ZF) {B b D W t : M.Domain}
    (pool : Ck_pool_d B b D W) (hb : M.mem b B) (ht : M.mem t W) : Name_d M B t :=
  ((pool t).mp ht).name_l hZF hb

/-- 正规化后的直接子名字确为 D 元素的检查名字，因而覆盖全部新子集。 -/
theorem Ck_pool_d.represent_l (hZF : M.Models ZF) {B R z b D W a : M.Domain}
    (pool : Ck_pool_d B b D W) (O : Cond_order_d M B R z) (hb : M.mem b B)
    (check : Check_d M b D a) {U : M.Domain → Prop} (g : Generic_d M B R z U)
    {x y : (extension_l M hZF B R z U).Domain} (value : Qval_d M B R z U a y)
    (sub : ∀ v, v ∈ x → v ∈ y) : ∃ t, M.mem t W ∧ Qval_d M B R z U t x := by
  obtain ⟨s,_,sx⟩ := value_name_l x
  obtain ⟨S,ha,hS⟩ := check_name_l M (check_range_l M hZF) hb check
  obtain ⟨t,nt,_,bound,tx⟩ := normalize_name_l O hZF g hS ha sx value sub
  refine ⟨t,(pool t).mpr ?_,tx⟩
  intro v hv
  obtain ⟨s,p,pair,hp,_⟩ := (name_unfold_l M (name_ops_l M hZF) B t).mp nt v hv
  obtain ⟨q,⟨u,up,hu⟩,_⟩ := bound s p ⟨v,pair,hv⟩
  obtain ⟨d,s',hd,cs,up'⟩ := (check_mem_l M hZF.1 (check_ind_l M hZF) check u).mp hu
  obtain ⟨eq,_⟩ := kpair_injective_l M up up'
  exact ⟨s,p,d,pair,hp,hd,eq.symm ▸ cs⟩

end YesMetaZFC.Model.Forcing.Internal

/-! ## 全部检查基点的统一子集名字库

对原条件域内每个基点使用唯一规范库，替代收集后取并。
所有有限前缀的实数名字因此有统一包络，不逐前缀另选秩界。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
include hZF

theorem ck_pools_l (B D : M.Domain) : ∃ U, ∀ t,
    M.mem t U ↔ ∃ b, M.mem b B ∧ Ck_bound_d B b D t := by
  let ρ : Env M 2 := ⟨fun i => [B,D].get i,fun _ => B⟩
  let φ : BinarySchema 2 := { body := ck_pool_m (.bound 2) (.bound 1) (.bound 3) .newest }
  have read b W : φ.denote ρ b W ↔ Ck_pool_d B b D W := ck_pool_sat_l hZF.1 ..
  obtain ⟨V,range⟩ := ZF.exists_functionalImageOn hZF φ ρ B
    (fun b hb => (ck_pool_exists_l hZF hb D).imp fun W hW => (read b W).mpr hW)
    (fun b _ W W' hW hW' => ((read b W).mp hW).unique_l hZF.1 ((read b W').mp hW'))
  obtain ⟨U,union⟩ := KP.exists_union (ZF.modelsKP hZF) V
  refine ⟨U,fun t => (union t).trans ⟨?_,?_⟩⟩
  · rintro ⟨W,hW,ht⟩
    obtain ⟨b,hb,pool⟩ := (range W).mp hW
    exact ⟨b,hb,((read b W).mp pool t).mp ht⟩
  · rintro ⟨b,hb,bound⟩
    obtain ⟨W,pool⟩ := ck_pool_exists_l hZF hb D
    exact ⟨W,(range W).mpr ⟨b,hb,(read b W).mpr pool⟩,(pool t).mpr bound⟩

end YesMetaZFC.Model.Forcing.Internal
