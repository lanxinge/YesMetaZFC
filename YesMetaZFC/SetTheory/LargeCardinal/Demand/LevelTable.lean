import YesMetaZFC.SetTheory.LargeCardinal.Demand.HistoryConstruction
import YesMetaZFC.SetTheory.LargeCardinal.Demand.Setup

/-! # 双图请求的实际实现高度

同一实现同时保存节点长度、两个标签集合和精确元数；不能从类型集合猜测元数。
继续工厂与真实重置分支直接生产这些证书，未引入额外实现前提。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

def Td_level_d (ω e δ S k κ u α a b : M.Domain) : Prop := ∃ μ Y c H d q n C V P r,
  M.SuccessorOf μ α ∧ V_d I μ Y ∧ Smem_d I c Y H ∧
  M.IsOrdinalAddition I d k k ∧ M.SuccessorOf q d ∧ M.SuccessorOf n q ∧ V_d I κ C ∧
  (∀ x, M.mem x V ↔ M.mem x C ∨ x = κ) ∧ Tt_realized_d I ω c Y H n r δ V P u ∧
  Rd_entry_d e S r ∧ Rd_entry_d q α r ∧ Td_groups_d I ω e q r a b

def td_level_m {l} (ω e δ S k κ u α a b : Term l) : Formula 1 l := set[l] ⟪∃ μ Y c H d q n C V P r,
  ⌜Formula.isSuccessor⌝ₚ(μ,⌜α⌝ₛ) ∧ ⌜(v_m kpair_convention_l)⌝ₚ(μ,Y) ∧
  ⌜(smem_m (𝒞 := kpair_convention_l))⌝ₚ(c,Y,H) ∧
  ⌜(Formula.isOrdinalAddition kpair_convention_l)⌝ₚ(d,⌜k⌝ₛ,⌜k⌝ₛ) ∧
  ⌜Formula.isSuccessor⌝ₚ(q,d) ∧ ⌜Formula.isSuccessor⌝ₚ(n,q) ∧
  ⌜(v_m kpair_convention_l)⌝ₚ(⌜κ⌝ₛ,C) ∧ ⌜tt_constants0_m⌝ₚ(⌜κ⌝ₛ,C,V) ∧
  ⌜tt_realized_m⌝ₚ(⌜ω⌝ₛ,c,Y,H,n,r,⌜δ⌝ₛ,V,P,⌜u⌝ₛ) ∧
  ⌜rd_entry0_m⌝ₚ(⌜e⌝ₛ,⌜S⌝ₛ,r) ∧ ⌜rd_entry0_m⌝ₚ(q,⌜α⌝ₛ,r) ∧
  ⌜td_groups_m⌝ₚ(⌜ω⌝ₛ,⌜e⌝ₛ,q,r,⌜a⌝ₛ,⌜b⌝ₛ)⟫
derive_free_closed td_level_m

theorem td_level_sat_l {l} (ρ : Env M l) (ω e δ S k κ u α a b : Term l) :
    Formula.satisfies ρ (td_level_m ω e δ S k κ u α a b) ↔ Td_level_d hZF
      (ω.eval ρ) (e.eval ρ) (δ.eval ρ) (S.eval ρ) (k.eval ρ) (κ.eval ρ)
      (u.eval ρ) (α.eval ρ) (a.eval ρ) (b.eval ρ) := by
  simp only [td_level_m,Td_level_d,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,
    Formula.satisfies_isSuccessor_iff,v_sat_l I hZF.1,smem_sat_l I,
    Formula.satisfies_isOrdinalAddition_iff I hZF.1,tt_constants0_sat_l hZF.1,
    tt_realized_sat_l I (ZF.modelsKP hZF),rd_entry0_sat_l hZF.1,td_groups_sat_l I hZF.1,
    Definitional.Term.eval_weaken]
  rfl

/-- 稠密命中的同一个实现与精确元数直接进入双图高度关系。 -/
theorem Td_generic_target_d.level_l {p : Tg_params_d M.Domain}
    {ℓ s k N β a b v₀ w₀ κ C v u : M.Domain}
    (h : Td_generic_target_d hZF p ℓ s k N β a b v₀ w₀ κ C v u) :
    Td_level_d hZF p.ω p.e p.δ p.S k κ u β a b := by
  obtain ⟨μ,Y,c,H,m,V,P,r,hμ,hY,model,hm,constants,full,first,last,groups,d,add,succ⟩ := h.2.2.2.1
  exact ⟨μ,Y,c,H,d,N,m,C,V,P,r,hμ,hY,model,add,succ,hm,h.2.1,constants,full,first,last,groups⟩

variable (hZFC : M.Models ZFC)
local notation "hZ" => ZFC.models_zf_l hZFC
local notation "J" => kp_pair_l (ZF.modelsKP hZ)

/-- 从实际零长度辅助走法读取原 νL 实现；两组空标签由唯一根槽自动确定。 -/
theorem Td_setup_d.level_reset_l {p : Tg_params_d M.Domain} {X n h v ℓ κ u : M.Domain}
    (setup : Td_setup_d hZFC p X) (aux : Td_aux_d hZ p n h v) (move : Td_move_d v ℓ p.e κ u) :
    Td_level_d hZ p.ω p.e p.δ p.S p.e κ u p.ν p.e p.e := by
  obtain ⟨ℓ',k,κ',u',d,q,N,m,_,s,B,U,Du,Dw,pn,pm,pp,pb,ph,_,_,_,_,_,_,_,
    parsed,_,hκ,arity,_,_,request,data,_,_,_,_,_,branch⟩ := aux
  obtain ⟨el,ek,ec,eu⟩ := parsed.unique_l move
  subst ℓ' k κ' u'
  have zero : Td_arity_d J p.e p.e p.a p.b p.c :=
    ⟨(ZF.ordinalAddition_zero_iff hZ J setup.empty).mpr rfl,setup.one,setup.two,setup.three⟩
  obtain ⟨ed,eq,en,em⟩ := arity.unique_l hZ zero
  subst d q N m
  obtain ⟨_,_,_,_,_,rank,constants,_⟩ := setup.queries.read_l hZFC hκ request data
  rcases branch with ⟨_,μ,Y,c,H,r,hμ,hY,model,full,first,last⟩ | ⟨ne,_⟩
  · have groups : Td_groups_d J p.ω p.e p.a r p.e p.e := by
      constructor <;> intro x <;> refine iff_of_false (setup.empty x) ?_ <;>
        rintro ⟨i,hi,ne,_,_⟩ <;>
        exact ((setup.one i).mp hi).elim (setup.empty i)
          (fun eq => ne (hZ.1.eq_of_same_members i p.e eq))
    exact ⟨μ,Y,c,H,p.e,p.a,p.b,B,U,Du,r,hμ,hY,model,zero.1,setup.one,setup.two,
      rank,constants,full,first,last,groups⟩
  · exact (ne rfl).elim

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 原模型内的双图有界高度表

键用四元组 (走法,长度,第一图,第二图) 编码。两图各自在 P(Z) 中，
不要求辅助图属于 Vδ；表由原语言在真实乘积与 νL+1 上分离得到。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

def Td_level_key_d (p : Tg_params_d M.Domain) (X Z U₁ U₂ v k a b α : M.Domain) : Prop :=
  M.mem v X ∧ M.mem k p.ω ∧ M.MemberSubset a Z ∧ M.MemberSubset b Z ∧
  Fn0_d k U₁ a ∧ Fn0_d k U₂ b ∧ (M.mem α p.ν ∨ α = p.ν) ∧
  ∃ ℓ κ u, Td_move_d v ℓ k κ u ∧ M.mem κ p.δ ∧ Td_level_d hZF p.ω p.e p.δ p.S k κ u α a b

def td_level_key_m {d} (ω e δ S ν X Z U₁ U₂ v k a b α : Term d) : Formula 1 d := set[d] ⟪
  ⌜v⌝ₛ ∈ ⌜X⌝ₛ ∧ ⌜k⌝ₛ ∈ ⌜ω⌝ₛ ∧ ⌜a⌝ₛ ⊆ ⌜Z⌝ₛ ∧ ⌜b⌝ₛ ⊆ ⌜Z⌝ₛ ∧
  ⌜fn0_m⌝ₚ(⌜k⌝ₛ,⌜U₁⌝ₛ,⌜a⌝ₛ) ∧ ⌜fn0_m⌝ₚ(⌜k⌝ₛ,⌜U₂⌝ₛ,⌜b⌝ₛ) ∧
  (⌜α⌝ₛ ∈ ⌜ν⌝ₛ ∨ ⌜α⌝ₛ = ⌜ν⌝ₛ) ∧
  (∃ ℓ κ u, ⌜td_move_m⌝ₚ(⌜v⌝ₛ,ℓ,⌜k⌝ₛ,κ,u) ∧ κ ∈ ⌜δ⌝ₛ ∧
    ⌜td_level_m⌝ₚ(⌜ω⌝ₛ,⌜e⌝ₛ,⌜δ⌝ₛ,⌜S⌝ₛ,⌜k⌝ₛ,κ,u,⌜α⌝ₛ,⌜a⌝ₛ,⌜b⌝ₛ))⟫
derive_free_closed td_level_key_m

theorem td_level_key_sat_l {d} (ρ : Env M d) (p : Tg_params_d (Term d)) (X Z U₁ U₂ v k a b α : Term d) :
    Formula.satisfies ρ (td_level_key_m p.ω p.e p.δ p.S p.ν X Z U₁ U₂ v k a b α) ↔
      Td_level_key_d hZF (p.map_l (fun t => t.eval ρ)) (X.eval ρ) (Z.eval ρ) (U₁.eval ρ)
        (U₂.eval ρ) (v.eval ρ) (k.eval ρ) (a.eval ρ) (b.eval ρ) (α.eval ρ) := by
  simp only [td_level_key_m,Td_level_key_d,Formula.satisfies_conj_iff,Formula.satisfies_mem_iff,
    Formula.satisfies_subset_iff,fn0_sat_l hZF.1,Formula.satisfies_disj_iff,
    Formula.satisfies_extensionalEq_iff_eq hZF.1,Formula.satisfies_exists_iff,
    td_move_sat_l hZF.1,td_level_sat_l hZF,Definitional.Term.eval_weaken,Tg_params_d.map_l]
  rfl

def Td_level_table_d (p : Tg_params_d M.Domain) (X Z U₁ U₂ R : M.Domain) : Prop := M.IsSetRelation I R ∧
  ∀ q α, Rd_entry_d q α R ↔ ∃ v k a b, Rd_quad_d q v k a b ∧ Td_level_key_d hZF p X Z U₁ U₂ v k a b α

theorem td_level_table_l (p : Tg_params_d M.Domain) (X Z U₁ U₂ : M.Domain) :
    ∃ R, Td_level_table_d hZF p X Z U₁ U₂ R := by
  obtain ⟨P,power⟩ := ZF.exists_powerSet hZF Z
  obtain ⟨D₁,prod₁⟩ := ZF.exists_cartesianProduct hZF I P P
  obtain ⟨D₂,prod₂⟩ := ZF.exists_cartesianProduct hZF I p.ω D₁
  obtain ⟨D₃,prod₃⟩ := ZF.exists_cartesianProduct hZF I X D₂
  obtain ⟨ν,succ⟩ := KP.exists_successor (ZF.modelsKP hZF) p.ν
  obtain ⟨C,union⟩ := KP.exists_unionOfTwo (ZF.modelsKP hZF) D₃ ν
  let ρ : Env M 9 := ⟨fun i => [p.ω,p.e,p.δ,p.S,p.ν,X,Z,U₁,U₂].get i,fun _ => p.ω⟩
  let φ : BinarySchema 9 := { body := set[11] ⟪∃ v k a b,
    ⌜rd_quad_m⌝ₚ(⌜(.bound 1 : Term 11)⌝ₛ,v,k,a,b) ∧
    ⌜td_level_key_m⌝ₚ(⌜(.bound 2 : Term 11)⌝ₛ,⌜(.bound 3 : Term 11)⌝ₛ,
      ⌜(.bound 4 : Term 11)⌝ₛ,⌜(.bound 5 : Term 11)⌝ₛ,⌜(.bound 6 : Term 11)⌝ₛ,
      ⌜(.bound 7 : Term 11)⌝ₛ,⌜(.bound 8 : Term 11)⌝ₛ,⌜(.bound 9 : Term 11)⌝ₛ,
      ⌜(.bound 10 : Term 11)⌝ₛ,v,k,a,b,⌜(.newest : Term 11)⌝ₛ)⟫ }
  have sat q α : φ.denote ρ q α ↔
      ∃ v k a b, Rd_quad_d q v k a b ∧ Td_level_key_d hZF p X Z U₁ U₂ v k a b α := by
    simp only [φ,BinarySchema.denote,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,
      rd_quad_sat_l hZF.1,td_level_key_m,Td_level_key_d,Formula.satisfies_mem_iff,
      Formula.satisfies_subset_iff,fn0_sat_l hZF.1,Formula.satisfies_disj_iff,
      Formula.satisfies_extensionalEq_iff_eq hZF.1,td_move_sat_l hZF.1,
      td_level_sat_l hZF,Definitional.Term.eval_weaken]
    rfl
  obtain ⟨R,rel,read⟩ := ZF.exists_setRelationOn_of_denote hZF I φ ρ C
  refine ⟨R,rel.1,fun q α => (read q α).trans ⟨fun h => (sat q α).mp h.2.2,fun h => ?_⟩⟩
  obtain ⟨v,k,a,b,code,key⟩ := h
  obtain ⟨t,ab,w,kw,vw⟩ := code
  have hq := (prod₃ q).mpr ⟨v,key.1,w,(prod₂ w).mpr ⟨k,key.2.1,t,
    (prod₁ t).mpr ⟨a,(power a).mpr key.2.2.1,b,(power b).mpr key.2.2.2.1,ab⟩,kw⟩,vw⟩
  have hα := key.2.2.2.2.2.2.1.elim (fun h => (succ α).mpr (Or.inl h))
    (fun eq => eq.symm ▸ succ.predecessor_mem)
  exact ⟨(union q).mpr (Or.inl hq),(union α).mpr (Or.inr hα),
    (sat q α).mpr ⟨v,k,a,b,⟨t,ab,w,kw,vw⟩,key⟩⟩

end YesMetaZFC.SetTheory.LargeCardinal
