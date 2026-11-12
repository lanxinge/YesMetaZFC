import YesMetaZFC.Model.Forcing.Boolean.RegularSet
import YesMetaZFC.Model.Forcing.Truth.OrderCongruence

/-! # 名字命中旧集合的正则开真值

在完整正则开域上使用“τ 命中 check(U)”；不把条件域的成员图直接当作
完备代数之间的映射。图及各真值集合均由原模型的分离、替换构造。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : Structure.{u}}

def hit_body_m : Formula 1 2 := .existsE (.conj (.mem .newest (.bound 2)) (.mem .newest (.bound 1)))
theorem hit_body_closed_l : hit_body_m.FreeClosed := by
  simp only [hit_body_m,Definitional.Formula.FreeClosed]
  exact ⟨⟨rfl,rfl⟩,⟨rfl,rfl⟩⟩

def hit_force_m {n} (B R z p a τ : Term n) : Formula 1 n :=
  force_at_m hit_body_m (Fin.cases τ (fun _ => a)) B R z p

@[simp] theorem hit_force_closed_l {n} (B R z p a τ : Term n)
    (hB : B.freeSupport = []) (hR : R.freeSupport = []) (hz : z.freeSupport = [])
    (hp : p.freeSupport = []) (ha : a.freeSupport = []) (hτ : τ.freeSupport = []) :
    (hit_force_m B R z p a τ).FreeClosed :=
  force_at_closed_l _ _ _ _ _ _ hit_body_closed_l (Fin.cases hτ (fun _ => ha)) hB hR hz hp

def Hit_d (B R z b τ U p : M.Domain) : Prop := ∃ a, Check_d M b U a ∧
  Forces_d M B R z hit_body_m ⟨Fin.cases τ (fun _ => a),fun _ => τ⟩ p

def hit_m {n} (B R z b τ U p : Term n) : Formula 1 n := set[n] ⟪
  ∃ a, ⌜check_m⌝ₚ(⌜b⌝ₛ,⌜U⌝ₛ,a) ∧ ⌜hit_force_m⌝ₚ(⌜B⌝ₛ,⌜R⌝ₛ,⌜z⌝ₛ,⌜p⌝ₛ,a,⌜τ⌝ₛ)⟫
derive_free_closed hit_m

theorem hit_sat_l (hE : Extensional M) {n} (ρ : Env M n) (B R z b τ U p : Term n) :
    Formula.satisfies ρ (hit_m B R z b τ U p) ↔
      Hit_d (B.eval ρ) (R.eval ρ) (z.eval ρ) (b.eval ρ) (τ.eval ρ) (U.eval ρ) (p.eval ρ) := by
  simp only [hit_m,Hit_d,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,
    check_sat_l M hE,hit_force_m,force_at_sat_l,Definitional.Term.eval_weaken]
  refine exists_congr fun a => and_congr_right fun _ => ?_
  exact forces_env_l hE hit_body_m hit_body_closed_l _ _ (Fin.cases
    (by simp only [Fin.cases_zero,Definitional.Term.eval_weaken]) (fun _ => rfl)) _

def Bv_hit_d (B R z b τ U V : M.Domain) : Prop :=
  ∀ p, M.mem p V ↔ M.mem p B ∧ p ≠ z ∧ Hit_d B R z b τ U p

def bv_hit_m {n} (B R z b τ U V : Term n) : Formula 1 n := set[n] ⟪
  ∀ p, p ∈ ⌜V⌝ₛ ↔ (p ∈ ⌜B⌝ₛ ∧ p ≠ ⌜z⌝ₛ ∧ ⌜hit_m⌝ₚ(⌜B⌝ₛ,⌜R⌝ₛ,⌜z⌝ₛ,⌜b⌝ₛ,⌜τ⌝ₛ,⌜U⌝ₛ,p))⟫
derive_free_closed bv_hit_m

variable (hZF : M.Models ZF)
local notation "I" => kpair_interpretation_l M (And.left hZF) (KP.exists_pair (ZF.modelsKP hZF))
include hZF

theorem bv_hit_sat_l {n} (ρ : Env M n) (B R z b τ U V : Term n) :
    Formula.satisfies ρ (bv_hit_m B R z b τ U V) ↔
      Bv_hit_d (B.eval ρ) (R.eval ρ) (z.eval ρ) (b.eval ρ) (τ.eval ρ) (U.eval ρ) (V.eval ρ) := by
  simp only [bv_hit_m,Bv_hit_d,Formula.satisfies_forall_iff,Formula.satisfies_iff_iff,
    Formula.satisfies_mem_iff,Formula.satisfies_conj_iff,Formula.extensionalNe,Formula.satisfies_neg_iff,
    Formula.satisfies_extensionalEq_iff_eq hZF.1,hit_sat_l hZF.1,Definitional.Term.eval_weaken]
  rfl

theorem bv_hit_exists_l (B R z b τ U : M.Domain) : ∃ V, Bv_hit_d B R z b τ U V := by
  let ρ : Env M 6 := ⟨fun i => [B,R,z,b,τ,U].get i,fun _ => B⟩
  let φ : UnarySchema 6 := {
    body := .conj (Formula.extensionalNe .newest (.bound 3))
      (hit_m (.bound 1) (.bound 2) (.bound 3) (.bound 4) (.bound 5) (.bound 6) .newest) }
  obtain ⟨V,values⟩ := ZF.separation_exists_d hZF φ ρ B
  refine ⟨V,fun p => (values p).trans (and_congr_right fun _ => ?_)⟩
  simp only [φ,Formula.satisfies_conj_iff,Formula.extensionalNe,Formula.satisfies_neg_iff,
    Formula.satisfies_extensionalEq_iff_eq hZF.1,hit_sat_l hZF.1]
  rfl

theorem Bv_hit_d.read_l {B R z b τ U V a : M.Domain} (value : Bv_hit_d B R z b τ U V)
    (check : Check_d M b U a) (p : M.Domain) : M.mem p V ↔ M.mem p B ∧ p ≠ z ∧
      Forces_d M B R z hit_body_m ⟨Fin.cases τ (fun _ => a),fun _ => τ⟩ p := by
  apply (value p).trans
  refine and_congr_right fun _ => and_congr_right fun _ => ?_
  exact ⟨fun ⟨c,hc,force⟩ => check_unique_l M hZF.1 (check_ind_l M hZF) b U c a hc check ▸ force,
    fun force => ⟨a,check,force⟩⟩

theorem Bv_hit_d.regular_l {B R z b τ U V : M.Domain} (value : Bv_hit_d B R z b τ U V)
    (O : Cond_order_d M B R z) (hb : M.mem b B) (name : Name_d M B τ) : Ropen_d B R z V := by
  obtain ⟨a,check,na,_⟩ := zf_check_l M hZF hb U
  let ρ : Env M 2 := ⟨Fin.cases τ (fun _ => a),fun _ => τ⟩
  have names : ∀ t : Term 2, Name_d M B (t.eval ρ) := by
    intro t; cases t with
    | free _ => exact name
    | bound i => exact Fin.cases name (fun _ => na) i
  have regular := forces_regular_l O hZF hit_body_m ρ names
  have read := value.read_l hZF check
  refine ⟨fun p hp => ⟨((read p).mp hp).1,((read p).mp hp).2.1⟩,?_,?_⟩
  · intro p q hp hq h
    exact (read q).mpr ⟨hq.1,hq.2.1,regular.1 p q hp hq ((read p).mp h).2.2⟩
  · intro p hp hz dense
    exact (read p).mpr ⟨hp,hz,regular.2 p hp hz (fun q hq => (dense q hq).imp
      fun r hr => ⟨hr.1,((read r).mp hr.2).2.2⟩)⟩

theorem Bv_hit_d.value_l {B R z b τ U V : M.Domain} (value : Bv_hit_d B R z b τ U V)
    (O : Cond_order_d M B R z) {G : M.Domain → Prop} (generic : Generic_d M B R z G) (hb : G b)
    {H : (extension_l M hZF B R z G).Domain} (valueH : Qval_d M B R z G τ H)
    (j : M.Domain → (extension_l M hZF B R z G).Domain)
    (full : ∀ a y, (extension_l M hZF B R z G).mem y (j a) ↔ ∃ c, M.mem c a ∧ j c = y)
    (checks : ∀ a t, Check_d M b a t → Qval_d M B R z G t (j a)) :
    (∃ p, G p ∧ M.mem p V) ↔ ∃ q, M.mem q U ∧ (extension_l M hZF B R z G).mem (j q) H := by
  obtain ⟨a,check,_,_⟩ := zf_check_l M hZF (generic.proper b hb).1 U
  let ρ : Env M 2 := ⟨Fin.cases τ (fun _ => a),fun _ => τ⟩
  let η : Env (extension_l M hZF B R z G) 2 := ⟨Fin.cases H (fun _ => j U),fun _ => H⟩
  have values : Env_val_d hZF ρ η := by
    intro t; cases t with
    | free _ => exact valueH
    | bound i => exact Fin.cases valueH (fun _ => checks U a check) i
  apply Iff.trans (exists_congr fun p => and_congr_right fun hp =>
    (value.read_l hZF check p).trans ⟨fun h => h.2.2,fun h => ⟨(generic.proper p hp).1,(generic.proper p hp).2,h⟩⟩)
  apply (forcing_truth_l O hZF generic hit_body_m hit_body_closed_l ρ η values).trans
  change (∃ x, (extension_l M hZF B R z G).mem x (j U) ∧ (extension_l M hZF B R z G).mem x H) ↔ _
  exact ⟨fun ⟨x,hx,hH⟩ => ((full U x).mp hx).elim fun q hq => ⟨q,hq.1,hq.2.symm ▸ hH⟩,
    fun ⟨q,hq,hH⟩ => ⟨j q,(full U (j q)).mpr ⟨q,hq,rfl⟩,hH⟩⟩

theorem bv_hit_graph_l (B R z b τ K : M.Domain) : ∃ P F, M.IsPowerSetOf P B ∧
    M.IsSetFunctionFromTo I F K P ∧ ∀ U V, Entry_d M U V F ↔ M.mem U K ∧ Bv_hit_d B R z b τ U V := by
  obtain ⟨P,power⟩ := ZF.exists_powerSet hZF B
  let ρ : Env M 5 := ⟨fun i => [B,R,z,b,τ].get i,fun _ => B⟩
  let φ : BinarySchema 5 := { body := bv_hit_m (.bound 2) (.bound 3) (.bound 4) (.bound 5) (.bound 6) (.bound 1) .newest }
  have sat U V : φ.denote ρ U V ↔ Bv_hit_d B R z b τ U V := bv_hit_sat_l hZF ..
  obtain ⟨F,fn,values⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := K) (target := P)
    (fun U _ => (bv_hit_exists_l hZF B R z b τ U).imp fun V hv => (sat U V).mpr hv)
    (fun U _ V W hv hw => hZF.1.eq_of_same_members V W (fun p => ((sat U V).mp hv p).trans ((sat U W).mp hw p).symm))
    (fun U V _ hv => (power V).mpr (fun p hp => (((sat U V).mp hv p).mp hp).1))
  exact ⟨P,F,power,fn,fun U V => (values U V).trans (and_congr_right fun _ => sat U V)⟩

end YesMetaZFC.Model.Forcing.Internal
