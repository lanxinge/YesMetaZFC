import YesMetaZFC.Model.Forcing.Check.SupportBound
import YesMetaZFC.Model.Forcing.Extension.Isomorphism
import YesMetaZFC.Model.Forcing.Truth.Truth

/-! # 名字的成员真值所构成的实际集合图

对每个旧对象 q，收集迫使 check(q) 属于给定名字的非零条件。
图与值域都在原模型内构造；真值集合是正则的，泛型命中恰好读取名字的成员。
这里不假设这张图单射：任意泛型名字在局部条件下可能具有非平凡核。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kpair_interpretation_l M (And.left hZF) (KP.exists_pair (ZF.modelsKP hZF))

def Bv_mem_d (B R z b τ q V : M.Domain) : Prop := ∀ p, M.mem p V ↔
  M.mem p B ∧ p ≠ z ∧ ∃ a, Check_d M b q a ∧ Mem_force_d M B R z p a τ

def bv_mem_m {d} (B R z b τ q V : Term d) : Formula 1 d := set[d] ⟪
  ∀ p, p ∈ ⌜V⌝ₛ ↔ (p ∈ ⌜B⌝ₛ ∧ p ≠ ⌜z⌝ₛ ∧
    (∃ a, ⌜check_m⌝ₚ(⌜b⌝ₛ,⌜q⌝ₛ,a) ∧ ⌜mem_force_m⌝ₚ(⌜B⌝ₛ,⌜R⌝ₛ,⌜z⌝ₛ,p,a,⌜τ⌝ₛ)))⟫
derive_free_closed bv_mem_m
include hZF

theorem bv_mem_sat_l {d} (ρ : Env M d) (B R z b τ q V : Term d) :
    Formula.satisfies ρ (bv_mem_m B R z b τ q V) ↔
      Bv_mem_d (B.eval ρ) (R.eval ρ) (z.eval ρ) (b.eval ρ) (τ.eval ρ) (q.eval ρ) (V.eval ρ) := by
  simp only [bv_mem_m,Bv_mem_d,Formula.extensionalNe,Formula.satisfies_forall_iff,Formula.satisfies_iff_iff,
    Formula.satisfies_conj_iff,Formula.satisfies_mem_iff,Formula.satisfies_neg_iff,
    Formula.satisfies_extensionalEq_iff_eq hZF.1,Formula.satisfies_exists_iff,
    check_sat_l M hZF.1,mem_force_sat_l M hZF.1,Definitional.Term.eval_weaken]
  rfl

theorem bv_mem_exists_l (B R z b τ q : M.Domain) : ∃ V, Bv_mem_d B R z b τ q V := by
  let ρ : Env M 6 := ⟨fun i => [B,R,z,b,τ,q].get i,fun _ => B⟩
  let φ : UnarySchema 6 := { body := set[7] ⟪⌜(.newest : Term 7)⌝ₛ ≠ ⌜(.bound 3 : Term 7)⌝ₛ ∧
    (∃ a, ⌜check_m⌝ₚ(⌜(.bound 4 : Term 7)⌝ₛ,⌜(.bound 6 : Term 7)⌝ₛ,a) ∧
      ⌜mem_force_m⌝ₚ(⌜(.bound 1 : Term 7)⌝ₛ,⌜(.bound 2 : Term 7)⌝ₛ,⌜(.bound 3 : Term 7)⌝ₛ,
        ⌜(.newest : Term 7)⌝ₛ,a,⌜(.bound 5 : Term 7)⌝ₛ))⟫ }
  obtain ⟨V,values⟩ := ZF.separation_exists_d hZF φ ρ B
  refine ⟨V,fun p => (values p).trans (and_congr_right fun _ => ?_)⟩
  simp only [φ,Formula.extensionalNe,Formula.satisfies_conj_iff,Formula.satisfies_neg_iff,
    Formula.satisfies_extensionalEq_iff_eq hZF.1,Formula.satisfies_exists_iff,
    check_sat_l M hZF.1,mem_force_sat_l M hZF.1,Definitional.Term.eval_weaken]
  rfl

theorem Bv_mem_d.read_l {B R z b τ q V a : M.Domain} (value : Bv_mem_d B R z b τ q V)
    (check : Check_d M b q a) (p : M.Domain) :
    M.mem p V ↔ M.mem p B ∧ p ≠ z ∧ Mem_force_d M B R z p a τ := by
  apply (value p).trans
  refine and_congr_right fun _ => and_congr_right fun _ => ?_
  exact ⟨fun ⟨c,hc,force⟩ => check_unique_l M hZF.1 (check_ind_l M hZF) b q c a hc check ▸ force,
    fun force => ⟨a,check,force⟩⟩

theorem Bv_mem_d.regular_l {B R z b τ q V : M.Domain} (value : Bv_mem_d B R z b τ q V)
    (O : Cond_order_d M B R z) : Regular_d M B R z (fun p => M.mem p V) := by
  obtain ⟨a,check⟩ := check_exists_l M hZF.1 (check_ind_l M hZF) (check_ops_l M hZF) b q
  have read := value.read_l hZF check
  have regular := regular_mem_l O a τ
  refine ⟨fun p r hp hr h => (read r).mpr ⟨hr.1,hr.2.1,regular.1 p r hp hr ((read p).mp h).2.2⟩,?_⟩
  intro p hp hz dense
  exact (read p).mpr ⟨hp,hz,regular.2 p hp hz (fun r hr => (dense r hr).imp
    fun s hs => ⟨hs.1,((read s).mp hs.2).2.2⟩)⟩

theorem Bv_mem_d.value_l {B R z b τ q V a : M.Domain} (value : Bv_mem_d B R z b τ q V)
    (O : Cond_order_d M B R z) {U : M.Domain → Prop} (generic : Generic_d M B R z U)
    (check : Check_d M b q a) {x H : (extension_l M hZF B R z U).Domain}
    (vx : Qval_d M B R z U a x) (vH : Qval_d M B R z U τ H) :
    (∃ p, U p ∧ M.mem p V) ↔ (extension_l M hZF B R z U).mem x H := by
  apply Iff.trans ?_ (qval_mem_forcing_l O hZF generic vx vH)
  exact exists_congr fun p => and_congr_right fun hp =>
    (value.read_l hZF check p).trans ⟨fun h => h.2.2,fun h => ⟨(generic.proper p hp).1,(generic.proper p hp).2,h⟩⟩

theorem bv_mem_graph_l (B R z b τ Q : M.Domain) : ∃ P F, M.IsPowerSetOf P B ∧
    M.IsSetFunctionFromTo I F Q P ∧
    ∀ q V, Entry_d M q V F ↔ M.mem q Q ∧ Bv_mem_d B R z b τ q V := by
  obtain ⟨P,power⟩ := ZF.exists_powerSet hZF B
  let ρ : Env M 5 := ⟨fun i => [B,R,z,b,τ].get i,fun _ => B⟩
  let φ : BinarySchema 5 := { body := bv_mem_m (.bound 2) (.bound 3) (.bound 4) (.bound 5) (.bound 6) (.bound 1) .newest }
  have sat q V : φ.denote ρ q V ↔ Bv_mem_d B R z b τ q V := bv_mem_sat_l hZF ..
  obtain ⟨F,fn,values⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := Q) (target := P)
    (fun q _ => (bv_mem_exists_l hZF B R z b τ q).imp fun V hv => (sat q V).mpr hv)
    (fun q _ V W hv hw => hZF.1.eq_of_same_members V W (fun p => ((sat q V).mp hv p).trans ((sat q W).mp hw p).symm))
    (fun q V _ hv => (power V).mpr (fun p hp => (((sat q V).mp hv p).mp hp).1))
  exact ⟨P,F,power,fn,fun q V => (values q V).trans (and_congr_right fun _ => sat q V)⟩

end YesMetaZFC.Model.Forcing.Internal
